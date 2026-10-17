/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Cluster.Defs
import SurfaceBlowup.Main

/-!
# Theorem 1.1, cluster clause

* `SurfaceBlowup.main_dvr_cluster`: over every complete DVR with finite residue field of size `q`,
  the cluster probability of type `σ` is `B_{n,σ}(q)`.
* `SurfaceBlowup.clusterDensity_eq_etale`: the cluster probability is unchanged when the event is
  restricted to separable polynomials (the étale convention).
* `SurfaceBlowup.cluster_formula_regular`: `B_{n,σ}` is regular at every prime power.
* `SurfaceBlowup.recip_cluster`: `A_n(q) = B_n(1/q)` in the paper's notation.

The cluster cell `(πO)^n` is the image of `Oⁿ` under `z ↦ π • z`, which scales the coefficient
measure by `q⁻ⁿ` (`scaling_image_borel_mass`); on it the published type event agrees with the
route-F event off the Haar-null inseparable locus (`monic_inseparable_null`), and the route-F
event is the image of the root event, whose mass is the root cell law `root_cell_law`.
-/

namespace SurfaceBlowup

open scoped ENNReal
open MeasureTheory

/-- The monic polynomial of degree `0` has type `σ` iff `σ = 0`. -/
private theorem hasPolynomialType_one_iff (O : Type) [CommRing O] [IsDomain O] (σ : FactorType) :
    HasPolynomialType O 1 σ ↔ σ = 0 := by
  constructor
  · rintro ⟨gs, hirr, -, hprod, rfl⟩
    cases gs with
    | nil => rfl
    | cons g gs =>
      exfalso
      have hg : g ∣ (g :: gs).prod := List.dvd_prod List.mem_cons_self
      rw [← hprod] at hg
      exact (hirr g List.mem_cons_self).2.not_isUnit (isUnit_of_dvd_one hg)
  · rintro rfl
    exact ⟨[], by simp, List.Pairwise.nil, by simp, rfl⟩

/-- The cluster cell is the image of `Oⁿ` under scaling by a uniformizer. -/
private theorem clusterCell_eq_image (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (n : ℕ) :
    clusterCell O n = (fun z : Fin n → O => pi • z) '' Set.univ := by
  have hI := (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).1 hpi
  ext a
  simp only [clusterCell, hI, Ideal.mem_span_singleton', Set.mem_ofPred_eq, Set.image_univ,
    Set.mem_range]
  constructor
  · intro h
    choose z hz using h
    exact ⟨z, funext fun j => by simp [mul_comm, ← hz j]⟩
  · rintro ⟨z, rfl⟩ j
    exact ⟨z j, by simp [mul_comm]⟩

/-- On the cluster cell, the route-F type event is the scaling image of the root event. -/
private theorem clusterCell_inter_eq_image (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (n : ℕ) (σ : FactorType) :
    clusterCell O n ∩ {a | HasPolynomialTypeF O (monicPolynomial O a) σ} =
      (fun z : Fin n → O => pi • z) ''
        {z | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} := by
  rw [clusterCell_eq_image O pi hpi n]
  ext a
  constructor
  · rintro ⟨⟨z, -, rfl⟩, h⟩
    exact ⟨z, h, rfl⟩
  · rintro ⟨z, h, rfl⟩
    exact ⟨⟨z, trivial, rfl⟩, h⟩

/-- **Theorem 1.1, cluster clause.** Over every complete DVR with finite residue field of size
`q`, the cluster probability of type `σ` is `B_{n,σ}(q)`. -/
theorem main_dvr_cluster (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    clusterDensity O n σ =
      densityValue (clusterExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) := by
  have hprob := coefficient_measure_probability O htop n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hC : clusterCell O 0 = Set.univ := Set.eq_univ_of_forall fun _ i => i.elim0
    have hE : {a : Fin 0 → O | HasPolynomialType O (monicPolynomial O a) σ} =
        if σ = 0 then Set.univ else ∅ := by
      ext a
      have h1 : monicPolynomial O a = 1 := by simp [monicPolynomial]
      rw [Set.mem_ofPred_eq, h1, hasPolynomialType_one_iff]
      split_ifs with h <;> simp [h]
    rw [clusterDensity, hC, hE, clusterExpr, rootLaw, if_pos rfl]
    by_cases hσ : σ = 0
    · subst hσ
      simp [lawCoeff, lawOne, Expr.sum, densityValue, Expr.eval]
    · rw [if_neg hσ]
      simp [lawCoeff, lawOne, Expr.sum, densityValue, Expr.eval, Ne.symm hσ]
  · obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨hR1, hR2⟩ := root_cell_law O htop pi hpi n hn σ
    obtain ⟨-, hU2⟩ := scaling_image_borel_mass O htop pi hpi n Set.univ MeasurableSet.univ
    obtain ⟨-, hT2⟩ := scaling_image_borel_mass O htop pi hpi n _ hR1
    have hae : (clusterCell O n ∩ {a | HasPolynomialType O (monicPolynomial O a) σ} :
        Set (Fin n → O)) =ᵐ[coefficientMeasure O n]
        (clusterCell O n ∩ {a | HasPolynomialTypeF O (monicPolynomial O a) σ} :
          Set (Fin n → O)) :=
      (measure_eq_zero_iff_ae_notMem.1 (monic_inseparable_null O htop n)).mono fun _ ha =>
        propext <| and_congr_right fun _ =>
          (hasPolynomialTypeF_iff_of_separable O (not_not.1 ha)).symm
    have hc0 : (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ n ≠ 0 :=
      pow_ne_zero _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
    have hct : (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ n ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast Nat.card_pos.ne'))
    rw [clusterDensity, measure_congr hae, clusterCell_inter_eq_image O pi hpi n σ, hT2,
      clusterCell_eq_image O pi hpi n, hU2, measure_univ, ENNReal.mul_div_mul_left _ _ hc0 hct,
      div_one, hR2, clusterExpr, rootLaw, if_neg hn.ne']

/-- The cluster probability is unchanged by restricting the event to separable polynomials
(the étale convention). -/
theorem clusterDensity_eq_etale (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    clusterDensity O n σ =
      coefficientMeasure O n (clusterCell O n ∩
        {a | (monicPolynomial O a).Separable ∧ HasPolynomialType O (monicPolynomial O a) σ}) /
        coefficientMeasure O n (clusterCell O n) :=
  congrArg (· / _) <| measure_congr <|
    (measure_eq_zero_iff_ae_notMem.1 (monic_inseparable_null O htop n)).mono fun _ ha =>
      propext <| and_congr_right fun _ => (and_iff_right (not_not.1 ha)).symm

/-- `B_{n,σ}` is regular at every prime power. -/
theorem cluster_formula_regular (n : ℕ) (σ : FactorType) :
    ∀ q : ℕ, PrimePower q → RegularAt (clusterExpr n σ).rational q := by
  intro q hq
  have hL : LawSafe (rootLaw n) := by
    unfold rootLaw
    split_ifs with h
    · intro z hz q _
      simp only [lawOne, List.mem_singleton] at hz
      subst hz
      trivial
    · exact local_law_safe _ ⟨Nat.one_pos, Nat.pos_of_ne_zero h⟩
  refine expression_regular _ _ (expression_sum_safe _ _ fun x hx => ?_)
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
  by_cases h : z.1 = σ
  · simp only [h, if_true]; exact hL z hz q (prime_power_ge_two q hq)
  · simp [h, Expr.safe]

/-- Reciprocity in the paper's notation: `A_n(q) = B_n(1/q)` (restates `recip_main`). -/
theorem recip_cluster (n : ℕ) (hn : 0 < n) (σ : FactorType) :
    (monicExpr n σ).rational = ((clusterExpr n σ).subst (.inv .var)).rational :=
  (recip_main n hn σ).1

end SurfaceBlowup
