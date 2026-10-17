/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Etale.Defs
import SurfaceBlowup.Main

/-!
# The étale convention agrees with the published densities

The two conventions for the type of a polynomial (finite integral closures versus étale algebras)
agree off a Haar-null set (paper, Remark 1.3). Formally: the non-étale binary forms are null, the
published densities equal the étale-convention densities, and hence Theorem 1.1 holds verbatim
under the étale convention.

## Main results

* `SurfaceBlowup.binary_nonEtale_null`
* `SurfaceBlowup.monicDensity_eq_etale`, `SurfaceBlowup.projectiveDensity_eq_etale`
* `SurfaceBlowup.main_dvr_etale`
-/

open MeasureTheory Polynomial
open scoped ENNReal

namespace SurfaceBlowup

section EtaleBridge

variable (O : Type) [CommRing O] [IsDomain O]

omit [IsDomain O] in
/-- The coefficient of `X^n` in `F_a(X,1)` is `a_n`. -/
theorem affinePolynomial_coeff_last {n : ℕ} (a : Fin (n + 1) → O) :
    (affinePolynomial O a).coeff n = algebraMap O (BaseField O) (a (Fin.last n)) := by
  simp only [affinePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · exact fun i _ hi => if_neg fun h => hi (Fin.ext (by simp [h]))
  · simp

omit [IsDomain O] in
/-- If `a_n ≠ 0` then `F_a(X,1)` is nonzero of degree exactly `n`. -/
theorem affinePolynomial_natDegree_of_last {n : ℕ} (a : Fin (n + 1) → O)
    (ha : a (Fin.last n) ≠ 0) :
    affinePolynomial O a ≠ 0 ∧ (affinePolynomial O a).natDegree = n := by
  have hc : (affinePolynomial O a).coeff n ≠ 0 := by
    rw [affinePolynomial_coeff_last]
    exact fun h => ha (IsFractionRing.injective O (BaseField O) (by rw [h, map_zero]))
  refine ⟨fun h => hc (by rw [h, Polynomial.coeff_zero]), ?_⟩
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ hc
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 i.2)

omit [IsDomain O] in
/-- Appending the coefficient `1` turns `F_a(X,1)` into the monic polynomial with coefficients `a`.
-/
theorem affinePolynomial_snoc_one {n : ℕ} (a : Fin n → O) :
    affinePolynomial O (Fin.snoc (α := fun _ => O) a 1) = monicPolynomial O a := by
  simp [affinePolynomial, monicPolynomial, Fin.sum_univ_castSucc, add_comm]

/-- Off `{a_n = 0} ∪ {disc = 0}` the binary form `F_a` is étale. -/
theorem isEtaleForm_of_good {n : ℕ} (a : Fin (n + 1) → O) (ha : a (Fin.last n) ≠ 0)
    (hd : MvPolynomial.eval a (MvPolynomial.map (Int.castRingHom O) (discAffine n)) ≠ 0) :
    IsEtaleForm O a := by
  obtain ⟨h0, hdeg⟩ := affinePolynomial_natDegree_of_last O a ha
  refine ⟨h0, by omega, separable_of_resultant _ n hdeg h0 ?_⟩
  rw [affine_resultant_eq]
  exact fun h => hd (IsFractionRing.injective O (BaseField O) (by rw [h, map_zero]))

variable [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
  [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]

/-- The locus `{a_n = 0} ∪ {disc = 0}` is Haar-null. -/
theorem affine_degenerate_null (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    coefficientMeasure O (n+1) ({a : Fin (n+1) → O | a (Fin.last n) = 0} ∪
      {a | MvPolynomial.eval a (MvPolynomial.map (Int.castRingHom O) (discAffine n)) = 0}) =
      0 := by
  refine measure_union_null (coordinate_hyperplane_null O htop (n+1) (Fin.last n)).2 ?_
  obtain ⟨a₀, h₀⟩ := exists_separable_monic O n
  refine coefficientMeasure_zero_null O htop (n+1) _ (Fin.snoc (α := fun _ => O) a₀ 1) ?_
  have hdeg := monic_polynomial_degree O n a₀
  have := resultant_ne_zero_of_separable (monicPolynomial O a₀) n hdeg.2 hdeg.1.ne_zero h₀
  rw [← affinePolynomial_snoc_one, affine_resultant_eq] at this
  exact fun h => this (by rw [h, map_zero])

end EtaleBridge

/-- The non-étale binary forms are Haar-null. -/
theorem binary_nonEtale_null (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    coefficientMeasure O (n+1) {a | ¬ IsEtaleForm O a} = 0 := by
  refine measure_mono_null (fun a ha => ?_) (affine_degenerate_null O htop n)
  by_contra hne
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hne
  exact ha (isEtaleForm_of_good O a hne.1 hne.2)

/-- The published monic density equals the étale-convention density (Remark 1.3). -/
theorem monicDensity_eq_etale (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    monicDensity O n σ = etaleMonicDensity O n σ :=
  measure_congr <| (measure_eq_zero_iff_ae_notMem.1 (monic_inseparable_null O htop n)).mono
    fun _ ha => propext ⟨fun h => ⟨not_not.1 ha, h⟩, fun h => h.2⟩

/-- The published projective density equals the étale-convention density (Remark 1.3). -/
theorem projectiveDensity_eq_etale (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    projectiveDensity O n σ = etaleProjectiveDensity O n σ :=
  congrArg (· / _) <| measure_congr <|
    (measure_eq_zero_iff_ae_notMem.1 (binary_nonEtale_null O htop n)).mono fun _ ha =>
      propext <| and_congr_right fun _ =>
        ⟨fun h => ⟨not_not.1 ha, h⟩, fun h => h.2⟩

/-- Theorem 1.1 under the étale convention: the monic and projective laws, with the events
restricted to étale algebras, are the universal rational functions. -/
theorem main_dvr_etale (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    etaleMonicDensity O n σ =
        densityValue (monicExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) ∧
    etaleProjectiveDensity O n σ =
        densityValue (projectiveExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) := by
  rw [← monicDensity_eq_etale O htop, ← projectiveDensity_eq_etale O htop]
  exact main_dvr O htop n σ

end SurfaceBlowup
