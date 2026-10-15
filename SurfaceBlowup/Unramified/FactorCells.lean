/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Formula.LawAlgebra
import SurfaceBlowup.Unramified.Extension

/-!
# Factor cells: residue cells of factor products and root-field isomorphisms

Building blocks for the measure of polynomial types: invariance of `(e, f)` under isomorphism of
DVR extensions; monic polynomials as coefficient vectors and the Hensel bijection between products
of residue cells and the residue cell of the product; squarefree factorizations from reducedness;
masses of normalized form cells; idempotents of products of fields and the induced matching of
factors under an isomorphism; the Chinese remainder decomposition of `K[X]/(∏ gᵢ)`; and root-field
isomorphisms along a conjugate orbit.

## Main results

* `SurfaceBlowup.dvr_algEquiv_ramification_inertia`, `SurfaceBlowup.monic_poly_reconstruct`
* `SurfaceBlowup.factor_product_bijection`, `SurfaceBlowup.monic_squarefree_factors_of_reduced`
* `SurfaceBlowup.normalized_form_cell_cylinder_mass`, `SurfaceBlowup.form_cell_product_measure`
* `SurfaceBlowup.pi_fields_algEquiv_index_bijection`,
  `SurfaceBlowup.polynomial_quotient_product_equiv`,
  `SurfaceBlowup.root_field_algEquiv_conjugate_orbit`

Provenance: Thm_SurfaceBlowupV2_{dvr_algEquiv_ramification_inertia,
monic_congruent_difference_factor, monic_poly_reconstruct, factor_product_bijection,
monic_squarefree_factors_of_reduced, normalized_form_cell_cylinder_mass,
form_cell_product_measure, pi_fields_primitive_idempotents, pi_fields_algEquiv_index_bijection,
polynomial_congruence_and_product, polynomial_quotient_product_equiv,
root_field_algEquiv_conjugate_orbit}.
-/

namespace SurfaceBlowup

open scoped ENNReal

/-! ### Invariants of DVR extensions -/

/-- `O`-isomorphic integral DVR extensions of a DVR `O` have the same ramification index and
inertia degree. -/
theorem dvr_algEquiv_ramification_inertia (O B B' : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing B']
    [IsDomain B'] [IsDiscreteValuationRing B'] [Algebra O B] [Algebra O B'] [Algebra.IsIntegral O B]
    [Algebra.IsIntegral O B'] (hinj : Function.Injective (algebraMap O B))
    (hinj' : Function.Injective (algebraMap O B')) (φ : B ≃ₐ[O] B') :
    (IsLocalRing.maximalIdeal B).ramificationIdx O = (IsLocalRing.maximalIdeal B').ramificationIdx O
      ∧ (IsLocalRing.maximalIdeal B).inertiaDeg O = (IsLocalRing.maximalIdeal B').inertiaDeg O := by
  obtain ⟨hc, hm⟩ := local_algEquiv_maximalIdeal O B B' φ
  refine ⟨?_, ?_⟩
  · have h1 := dvr_extension_maximalIdeal_map_eq_pow O B hinj
    have h2 := dvr_extension_maximalIdeal_map_eq_pow O B' hinj'
    have h3 := congrArg (Ideal.map (φ : B →+* B')) h1
    rw [Ideal.map_map, Ideal.map_pow, hm] at h3
    have hcomp : ((φ : B →+* B').comp (algebraMap O B)) = algebraMap O B' := by
      ext x; simp
    rw [hcomp, h2] at h3
    exact dvr_maximalIdeal_pow_injective B' _ _ h3.symm
  · have l1 := (integral_local_extension_unique_prime O B).1
    have l2 := (integral_local_extension_unique_prime O B').1
    have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal O) := ⟨l1.symm⟩
    have : (IsLocalRing.maximalIdeal B').LiesOver (IsLocalRing.maximalIdeal O) := ⟨l2.symm⟩
    rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal O) (IsLocalRing.maximalIdeal B),
      Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal O) (IsLocalRing.maximalIdeal B')]
    exact (Ideal.Quotient.algEquivOfEqComap (IsLocalRing.maximalIdeal O) φ
      (by rw [← hc]; rfl)).toLinearEquiv.finrank_eq

/-! ### Monic polynomials and coefficient vectors -/

/-- If monic `G, G'` of degree `n` are congruent modulo `πⁱ` (with `π` a nonzerodivisor), then
`G' - G = πⁱ H` with `deg H < n`; moreover `πⁱ x ∈ (πⁱ⁺¹)` implies `x ∈ (π)`. -/
theorem monic_congruent_difference_factor (O : Type) [CommRing O] (pi : O)
    (hreg : ∀ x : O, pi * x = 0 → x = 0) (i n : ℕ) (G G' : Polynomial O) (hG : G.Monic)
    (hG' : G'.Monic) (hn : G.natDegree = n) (hn' : G'.natDegree = n)
    (hcong : ∀ j, G'.coeff j - G.coeff j ∈ Ideal.span {pi ^ i}) :
    (∃ H : Polynomial O, G' - G = Polynomial.C (pi ^ i) * H ∧ H.degree < (n : WithBot ℕ)) ∧
      (∀ x : O, pi ^ i * x ∈ Ideal.span {pi ^ (i + 1)} → x ∈ Ideal.span {pi}) := by
  have hpow : ∀ k : ℕ, ∀ x : O, pi ^ k * x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => exact fun x hx ↦ hreg _ (ih _ (by rw [← mul_assoc, ← pow_succ]; exact hx))
  refine ⟨?_, fun x hx ↦ ?_⟩
  · obtain ⟨H, hH⟩ : Polynomial.C (pi ^ i) ∣ G' - G := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      exact fun j ↦ by rw [Polynomial.coeff_sub]; exact Ideal.mem_span_singleton.mp (hcong j)
    refine ⟨H, hH, Polynomial.degree_lt_iff_coeff_zero _ _ |>.2 fun m hm ↦ hpow i _ ?_⟩
    rw [← Polynomial.coeff_C_mul, ← hH, Polynomial.coeff_sub]
    rcases Nat.eq_or_lt_of_le hm with rfl | h
    · rw [show G'.coeff n = 1 from hn' ▸ hG'.coeff_natDegree,
        show G.coeff n = 1 from hn ▸ hG.coeff_natDegree, sub_self]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), sub_self]
  · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx
    exact Ideal.mem_span_singleton'.2 ⟨y, (sub_eq_zero.mp (hpow i _ (by
      rw [mul_sub, ← hy, pow_succ]; ring))).symm⟩

/-- `monicPolyO a = Xⁿ + Σ aᵢ Xⁱ` is monic of degree `n` with lower coefficients `a`, and every
monic polynomial of degree `n` arises from its coefficient vector. -/
theorem monic_poly_reconstruct (O : Type) [CommRing O] [Nontrivial O] (n : ℕ) (a : Fin n → O) :
    (monicPolyO a).Monic ∧ (monicPolyO a).natDegree = n
      ∧ (∀ i : Fin n, (monicPolyO a).coeff i = a i)
      ∧ (∀ F : Polynomial O, F.Monic → F.natDegree = n → monicPolyO (coeffVec n F) = F) := by
  have hdeg := Polynomial.degree_sum_fin_lt a
  refine ⟨Polynomial.monic_X_pow_add hdeg, ?_, ?_, ?_⟩
  · unfold monicPolyO
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]
    rwa [Polynomial.degree_X_pow]
  · intro i
    unfold monicPolyO
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), zero_add,
      Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg (fun h ↦ hj (Fin.ext h.symm)), mul_zero]
    · simp
  · intro F hF hn
    conv_rhs => rw [hF.as_sum, hn]
    unfold monicPolyO coeffVec
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ Polynomial.C (F.coeff i) * Polynomial.X ^ i)]

/-- Over a complete local ring, multiplying monic lifts gives a bijection from the product of the
residue cells of pairwise coprime monic `gᵢ` onto the residue cell of `∏ gᵢ` (Hensel). -/
theorem factor_product_bijection (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ι : Type) [Fintype ι]
    (g : ι → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ i, (g i).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) :
    Set.BijOn (factorProduct (fun i ↦ (g i).natDegree))
      (Set.pi Set.univ (fun i ↦ residueCell O (g i).natDegree (g i)))
      (residueCell O (∑ i, (g i).natDegree) (∏ i, g i)) := by
  have R := fun (n : ℕ) (a : Fin n → O) ↦ monic_poly_reconstruct O n a
  have hprod : ∀ a : ∀ i, Fin (g i).natDegree → O,
      monicPolyO (factorProduct (fun i ↦ (g i).natDegree) a) = ∏ i, monicPolyO (a i) := by
    intro a
    unfold factorProduct
    apply (R _ (fun _ ↦ (0 : O))).2.2.2
    · exact Polynomial.monic_prod_of_monic _ _ (fun i _ ↦ (R _ (a i)).1)
    · rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ ↦ (R _ (a i)).1)]
      exact Finset.sum_congr rfl (fun i _ ↦ (R _ (a i)).2.1)
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simp only [Set.mem_pi, Set.mem_univ, true_implies, residueCell, Set.mem_ofPred_eq] at ha ⊢
    rw [hprod, Polynomial.map_prod]
    exact Finset.prod_congr rfl (fun i _ ↦ ha i)
  · intro a ha a' ha' h
    simp only [Set.mem_pi, Set.mem_univ, true_implies, residueCell, Set.mem_ofPred_eq] at ha ha'
    have hp : ∏ i, monicPolyO (a i) = ∏ i, monicPolyO (a' i) := by
      rw [← hprod, ← hprod, h]
    have hG := hensel_family_unique O ι (fun i ↦ monicPolyO (a i))
      (fun i ↦ monicPolyO (a' i)) (fun i ↦ (R _ (a i)).1) (fun i ↦ (R _ (a' i)).1)
      (fun i ↦ by simp only [ha i, ha' i])
      (fun i j hij ↦ by simpa only [ha i, ha j] using hc i j hij) hp
    funext i j
    have := congrFun hG i
    rw [← (R _ (a i)).2.2.1 j, ← (R _ (a' i)).2.2.1 j, this]
  · intro c hc'
    simp only [residueCell, Set.mem_ofPred_eq] at hc'
    obtain ⟨G, hGm, hF, hGr, hGd⟩ := hensel_family_exists O ι (monicPolyO c)
      (R _ c).1 g hg hc hc'
    have hrec : ∀ i, monicPolyO (coeffVec (g i).natDegree (G i)) = G i :=
      fun i ↦ (R _ (fun _ ↦ (0 : O))).2.2.2 _ (hGm i) (hGd i)
    refine ⟨fun i ↦ coeffVec (g i).natDegree (G i), ?_, ?_⟩
    · simp only [Set.mem_pi, Set.mem_univ, true_implies, residueCell, Set.mem_ofPred_eq]
      intro i
      rw [hrec i, hGr i]
    · unfold factorProduct
      simp only [hrec]
      rw [← hF]
      funext j
      simp only [coeffVec]
      exact (R _ c).2.2.1 j

/-- A monic `F` over a field with `K[X]/(F)` reduced is a product of distinct monic irreducibles. -/
theorem monic_squarefree_factors_of_reduced (K : Type) [Field K] (F : Polynomial K)
    (hF : F.Monic) (hred : IsReduced (AdjoinRoot F)) :
    ∃ gs : List (Polynomial K), (∀ g ∈ gs, g.Monic ∧ Irreducible g) ∧
      gs.Pairwise (fun g h ↦ g ≠ h) ∧ F = gs.prod := by
  classical
  open UniqueFactorizationMonoid in
  have hF0 : F ≠ 0 := hF.ne_zero
  have hsq : Squarefree F := by
    rintro g ⟨h, rfl⟩
    have hgh : g * h ≠ 0 := by rintro h0; apply hF0; rw [mul_assoc, h0, mul_zero]
    have h0 := (show IsNilpotent (AdjoinRoot.mk (g * g * h) (g * h)) from
      ⟨2, by rw [← map_pow, AdjoinRoot.mk_eq_zero]; exact ⟨h, by ring⟩⟩).eq_zero
    rw [AdjoinRoot.mk_eq_zero, mul_assoc] at h0
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hgh).1 (by simpa using h0))
  set M := normalizedFactors F
  have hmon : ∀ g ∈ M, g.Monic := fun g hg ↦ by
    rw [← normalize_normalized_factor g hg]
    exact Polynomial.monic_normalize (irreducible_of_normalized_factor g hg).ne_zero
  refine ⟨M.toList, fun g hg ↦ ?_, ?_, ?_⟩
  · rw [Multiset.mem_toList] at hg
    exact ⟨hmon g hg, irreducible_of_normalized_factor g hg⟩
  · change List.Nodup _
    rw [← Multiset.coe_nodup, Multiset.coe_toList]
    exact (squarefree_iff_nodup_normalizedFactors hF0).1 hsq
  · rw [Multiset.prod_toList]
    exact (Polynomial.eq_of_monic_of_associated
      (by simpa using Polynomial.monic_multiset_prod_of_monic M id hmon) hF
      (prod_normalizedFactors hF0)).symm

/-! ### Normalized form cells -/

/-- The normalized form cell of `g` (residues prescribed, coordinate `ν` normalized to `1`) is a
nonempty measurable residue class of mass `q^{-d}`; its normalized cell measure is a probability
measure giving each congruence ball mod `m^L` mass `q^{-d(L-1)}`. -/
theorem normalized_form_cell_cylinder_mass (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (d : ℕ) (ν : Fin (d + 1))
    (g : Fin (d + 1) → IsLocalRing.ResidueField O) (hgν : g ν = 1) :
    (∀ b : Fin d → O, b ∈ reducedFormCell O d ν g ↔
        ∀ j, IsLocalRing.residue O (b j) = g (ν.succAbove j)) ∧
      (∀ b ∈ reducedFormCell O d ν g,
        reducedFormCell O d ν g = {b' | ∀ j, b' j - b j ∈ (IsLocalRing.maximalIdeal O)}) ∧
      (reducedFormCell O d ν g).Nonempty ∧ MeasurableSet (reducedFormCell O d ν g) ∧
      coefficientMeasure O d (reducedFormCell O d ν g) =
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ d ∧
      MeasureTheory.IsProbabilityMeasure (cellMeasure O d (reducedFormCell O d ν g)) ∧
      ∀ (L : ℕ) (b : Fin d → O), 1 ≤ L → b ∈ reducedFormCell O d ν g →
        cellMeasure O d (reducedFormCell O d ν g)
            {b' | ∀ j, b' j - b j ∈ (IsLocalRing.maximalIdeal O) ^ L} =
          (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (d * (L - 1)) := by
  set C := reducedFormCell O d ν g with hCdef
  set q : ℝ≥0∞ := (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)
  have h1 : ∀ b : Fin d → O, b ∈ C ↔ ∀ j, IsLocalRing.residue O (b j) = g (ν.succAbove j) := by
    intro b
    simp only [hCdef, reducedFormCell, normalizedFormCell, insertOne, Set.mem_ofPred_eq,
      Fin.insertNth_apply_same, true_and]
    refine ⟨fun h j ↦ by
      simpa [residueVector, Fin.insertNth_apply_succAbove] using congrFun h (ν.succAbove j),
      fun h ↦ funext fun i ↦ ?_⟩
    rcases Fin.eq_self_or_eq_succAbove ν i with rfl | ⟨j, rfl⟩
    · simp [residueVector, hgν]
    · simp [residueVector, Fin.insertNth_apply_succAbove, h j]
  have h2 : ∀ b ∈ C, C = {b' | ∀ j, b' j - b j ∈ (IsLocalRing.maximalIdeal O)} := by
    intro b hb
    ext b'
    rw [h1] at hb
    rw [h1, Set.mem_ofPred_eq]
    exact forall_congr' fun j ↦ by rw [← hb j]; exact Ideal.Quotient.eq
  obtain ⟨b0, hb0⟩ : C.Nonempty :=
    ⟨fun j ↦ (IsLocalRing.residue_surjective (g (ν.succAbove j))).choose,
      (h1 _).2 fun j ↦ (IsLocalRing.residue_surjective (g (ν.succAbove j))).choose_spec⟩
  have hball : ∀ L (b : Fin d → O),
      MeasurableSet {b' : Fin d → O | ∀ j, b' j - b j ∈ (IsLocalRing.maximalIdeal O) ^ L} := by
    intro L b
    have hm := finite_coordinate_borel_cylinders O (IsLocalRing.maximalIdeal O) htop d
    have : @MeasurableSet _ (adicCylinderSpace (IsLocalRing.maximalIdeal O) (Fin d → O))
        {b' : Fin d → O | ∀ j, b' j - b j ∈ (IsLocalRing.maximalIdeal O) ^ L} :=
      MeasurableSpace.measurableSet_generateFrom <| Or.inr ⟨L, b, by
        ext y
        simp only [Set.mem_ofPred_eq]
        rw [finite_coordinate_adic_congruence]⟩
    rwa [← hm] at this
  have hC1 : C = {b' | ∀ j, b' j - b0 j ∈ (IsLocalRing.maximalIdeal O) ^ 1} := by
    rw [h2 b0 hb0]; simp
  have h4 : MeasurableSet C := by rw [hC1]; exact hball 1 b0
  have h5 : coefficientMeasure O d C = q⁻¹ ^ d := by
    rw [hC1, coefficient_cylinder_mass O htop, mul_one]
  have hμ0 : q⁻¹ ^ d ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
  have hμt : q⁻¹ ^ d ≠ ⊤ := ENNReal.pow_ne_top <| ENNReal.inv_ne_top.mpr <| by
    simp only [q]; exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField O)).ne'
  refine ⟨h1, h2, ⟨b0, hb0⟩, h4, h5, ?_, ?_⟩
  · constructor
    rw [cellMeasure, MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, h5, smul_eq_mul, ENNReal.inv_mul_cancel hμ0 hμt]
  · intro L b hL hb
    have hsub : {b' : Fin d → O | ∀ j, b' j - b j ∈ (IsLocalRing.maximalIdeal O) ^ L} ⊆ C := by
      rw [h2 b hb]
      exact fun y hy j ↦ Ideal.pow_le_self (by omega) (hy j)
    rw [cellMeasure, MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.restrict_apply (hball L b),
      Set.inter_eq_left.mpr hsub, h5, coefficient_cylinder_mass O htop, smul_eq_mul]
    obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
    rw [Nat.add_sub_cancel, mul_add, mul_one, pow_add, ← mul_assoc, mul_comm, ← mul_assoc,
      ENNReal.mul_inv_cancel hμ0 hμt, one_mul]

/-- The product of the normalized cell measures of a family of form cells is a probability
measure concentrated on the product cell, giving each congruence box mod `m^L` mass
`q^{-(Σ dᵢ)(L-1)}`. -/
theorem form_cell_product_measure (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (ι : Type) [Fintype ι] (d : ι → ℕ)
    (ν : ∀ i, Fin (d i + 1)) (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (hgν : ∀ i, g i (ν i) = 1)
    [hσ : ∀ i,
      MeasureTheory.SigmaFinite (cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i)))] :
    MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi
          (fun i ↦ cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i)))) ∧
      (MeasureTheory.Measure.pi (fun i ↦ cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i))))
        (Set.pi Set.univ (fun i ↦ reducedFormCell O (d i) (ν i) (g i)))ᶜ = 0 ∧
      ∀ (L : ℕ), 1 ≤ L → ∀ a' ∈ Set.pi Set.univ (fun i ↦ reducedFormCell O (d i) (ν i) (g i)),
        (MeasureTheory.Measure.pi
            (fun i ↦ cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i))))
          (Set.pi Set.univ (fun i ↦
            {b : Fin (d i) → O | ∀ j, b j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L})) =
          (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ ((∑ i, d i) * (L - 1)) := by
  have H := fun i ↦ normalized_form_cell_cylinder_mass O htop (d i) (ν i) (g i) (hgν i)
  have : ∀ i, MeasureTheory.IsProbabilityMeasure
      (cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i))) := fun i ↦ (H i).2.2.2.2.2.1
  refine ⟨inferInstance, ?_, ?_⟩
  · have hcompl : ∀ i, cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i))
        (reducedFormCell O (d i) (ν i) (g i))ᶜ = 0 := by
      intro i
      unfold cellMeasure
      rw [MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.restrict_apply (H i).2.2.2.1.compl, Set.compl_inter_self]
      simp
    have hone : ∀ i, cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i))
        (reducedFormCell O (d i) (ν i) (g i)) = 1 := fun i ↦
      (MeasureTheory.prob_compl_eq_zero_iff (H i).2.2.2.1).1 (hcompl i)
    rw [MeasureTheory.prob_compl_eq_zero_iff (MeasurableSet.univ_pi fun i ↦ (H i).2.2.2.1),
      MeasureTheory.Measure.pi_pi]
    simp [hone]
  · intro L hL a' ha'
    rw [MeasureTheory.Measure.pi_pi]
    have : ∀ i, cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i))
        {b : Fin (d i) → O | ∀ j, b j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L} =
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (d i * (L - 1)) :=
      fun i ↦ (H i).2.2.2.2.2.2 L (a' i) hL (ha' i (Set.mem_univ i))
    simp only [this]
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_mul]

/-! ### Products of fields -/

/-- The primitive idempotents of a finite product of fields `∏ Lᵢ` are the unit vectors
`Pi.single i 1`, which are pairwise orthogonal. -/
private theorem pi_fields_primitive_idempotents (ι : Type) [DecidableEq ι] (L : ι → Type)
    [∀ i, Field (L i)] (x : ∀ i, L i) :
    ((IsIdempotentElem x ∧ x ≠ 0 ∧ ∀ y : (∀ i, L i), IsIdempotentElem y → y * x = y →
      y = 0 ∨ y = x) ↔ ∃ i, x = Pi.single i (1 : L i)) ∧
    ∀ i j : ι, i ≠ j → (Pi.single i (1 : L i) : ∀ i, L i) * Pi.single j (1 : L j) = 0 := by
  have idem : ∀ i, IsIdempotentElem (Pi.single i (1 : L i) : ∀ i, L i) := fun i ↦ by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  refine ⟨⟨?_, ?_⟩, fun i j hij ↦ ?_⟩
  · rintro ⟨hx, hne, hp⟩
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hne (funext h)
    have hi1 : x i = 1 :=
      (IsIdempotentElem.iff_eq_zero_or_one.mp (congrFun hx i)).resolve_left hi
    refine ⟨i, ?_⟩
    have hy : Pi.single i (1 : L i) * x = Pi.single i 1 := by
      funext l
      by_cases h : l = i
      · subst h; simp [hi1]
      · simp [Pi.single_eq_of_ne h]
    rcases hp _ (idem i) hy with h | h
    · simpa using congrFun h i
    · exact h.symm
  · rintro ⟨i, rfl⟩
    refine ⟨idem i, fun h ↦ by simpa using congrFun h i, fun y hy hyx ↦ ?_⟩
    have hj : ∀ j, j ≠ i → y j = 0 := fun j hj ↦ by
      simpa [Pi.single_eq_of_ne hj] using (congrFun hyx j).symm
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (congrFun hy i) with h | h
    · left
      funext l
      by_cases hl : l = i
      · subst hl; simpa using h
      · simpa using hj l hl
    · right
      funext l
      by_cases hl : l = i
      · subst hl; simpa using h
      · simp [Pi.single_eq_of_ne hl, hj l hl]
  · funext l
    by_cases h : l = i
    · subst h; simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne h]

/-- Ring isomorphisms transport primitive idempotents. -/
private lemma isPrimitiveIdempotent_map {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) (x : A)
    (h : IsIdempotentElem x ∧ x ≠ 0 ∧ ∀ y, IsIdempotentElem y → y * x = y → y = 0 ∨ y = x) :
    IsIdempotentElem (f x) ∧ f x ≠ 0 ∧
      ∀ y, IsIdempotentElem y → y * f x = y → y = 0 ∨ y = f x := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.map f, by simpa using h2, fun y hy hyx ↦ ?_⟩
  rcases h3 (f.symm y) (hy.map f.symm) (by rw [← f.symm_apply_apply x, ← map_mul, hyx]) with h | h
  · exact .inl (by simpa using congrArg f h)
  · exact .inr (by simpa using congrArg f h)

/-- The unit vectors `Pi.single j 1` of a product of fields are pairwise distinct. -/
private lemma pi_single_one_injective {ι : Type} [DecidableEq ι] (L : ι → Type) [∀ i, Field (L i)]
    (j j' : ι) (h : (Pi.single j (1 : L j) : ∀ i, L i) = Pi.single j' (1 : L j')) : j = j' := by
  by_contra hne
  have := congrFun h j
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
  exact one_ne_zero this

/-- If `e` sends the `i`-th unit vector to the `j`-th one, it sends the `i`-th factor into
the `j`-th factor. -/
private lemma algEquiv_single_eq_single {K ι ι' : Type} [Field K] [DecidableEq ι] [DecidableEq ι']
    (L : ι → Type) (L' : ι' → Type) [∀ i, Field (L i)] [∀ i, Field (L' i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra K (L' i)] (e : (∀ i, L i) ≃ₐ[K] (∀ i, L' i))
    (i : ι) (j : ι') (hij : e (Pi.single i (1 : L i)) = Pi.single j (1 : L' j)) (x : L i) :
    e (Pi.single i x) = Pi.single j (e (Pi.single i x) j) := by
  have h2 : e (Pi.single i x) = e (Pi.single i x) * Pi.single j 1 := by
    conv_lhs => rw [← mul_one x, Pi.single_mul]
    rw [map_mul, hij]
  funext k
  by_cases hk : k = j
  · subst hk; simp
  · rw [h2, Pi.mul_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, mul_zero]

open scoped Classical in
/-- A `K`-algebra isomorphism of finite products of fields `∏ Lᵢ ≃ ∏ L'ⱼ` is induced by a
bijection `π` of the index sets and isomorphisms `Lᵢ ≃ L'_{π i}`. -/
theorem pi_fields_algEquiv_index_bijection (K ι ι' : Type) [Field K]
    (L : ι → Type) (L' : ι' → Type) [∀ i, Field (L i)] [∀ i, Field (L' i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra K (L' i)] (e : (∀ i, L i) ≃ₐ[K] (∀ i, L' i)) :
    ∃ π : ι ≃ ι', ∀ i, e (Pi.single i (1 : L i)) = Pi.single (π i) (1 : L' (π i)) ∧
      ∃ φ : L i ≃ₐ[K] L' (π i), ∀ x : L i, e (Pi.single i x) = Pi.single (π i) (φ x) := by
  have hj : ∀ i, ∃ j, e (Pi.single i (1 : L i)) = Pi.single j (1 : L' j) := fun i ↦
    (pi_fields_primitive_idempotents ι' L' _).1.1
      (isPrimitiveIdempotent_map e.toRingEquiv _
        ((pi_fields_primitive_idempotents ι L _).1.2 ⟨i, rfl⟩))
  have hj' : ∀ j, ∃ i, e.symm (Pi.single j (1 : L' j)) = Pi.single i (1 : L i) := fun j ↦
    (pi_fields_primitive_idempotents ι L _).1.1
      (isPrimitiveIdempotent_map e.symm.toRingEquiv _
        ((pi_fields_primitive_idempotents ι' L' _).1.2 ⟨j, rfl⟩))
  choose f hf using hj
  choose g hg using hj'
  let π : ι ≃ ι' :=
    { toFun := f
      invFun := g
      left_inv := fun i ↦ pi_single_one_injective L _ _ <| by
        rw [← hg, ← hf, AlgEquiv.symm_apply_apply]
      right_inv := fun j ↦ pi_single_one_injective L' _ _ <| by
        rw [← hf, ← hg, AlgEquiv.apply_symm_apply] }
  refine ⟨π, fun i ↦ ⟨hf i, ?_⟩⟩
  have hs := algEquiv_single_eq_single L L' e i (f i) (hf i)
  let φ₀ : L i →ₐ[K] L' (f i) :=
    { toFun := fun x ↦ e (Pi.single i x) (f i)
      map_one' := by simp only [hf i, Pi.single_eq_same]
      map_mul' := fun x y ↦ by simp only [Pi.single_mul, map_mul, Pi.mul_apply]
      map_zero' := by simp
      map_add' := fun x y ↦ by simp only [Pi.single_add, map_add, Pi.add_apply]
      commutes' := fun c ↦ by
        simp only [Algebra.algebraMap_eq_smul_one, Pi.single_smul, map_smul, hf i,
          Pi.smul_apply, Pi.single_eq_same] }
  have hbij : Function.Bijective φ₀ := by
    refine ⟨φ₀.toRingHom.injective, fun y ↦ ⟨e.symm (Pi.single (f i) y) i, ?_⟩⟩
    have := congrArg e (algEquiv_single_eq_single L' L e.symm (f i) i
      (by rw [← hf i, AlgEquiv.symm_apply_apply]) y)
    rw [AlgEquiv.apply_symm_apply, hs] at this
    exact (Pi.single_injective (f i) this).symm
  exact ⟨AlgEquiv.ofBijective φ₀ hbij, hs⟩

/-! ### Polynomial congruences and the Chinese remainder theorem -/

/-- Two polynomials agree modulo `I` iff their coefficients do, and coefficientwise congruence
mod `I` is preserved by finite products. -/
theorem polynomial_congruence_and_product (O : Type) [CommRing O] (I : Ideal O) :
    (∀ P Q : Polynomial O, P.map (Ideal.Quotient.mk I) = Q.map (Ideal.Quotient.mk I) ↔
        ∀ j, P.coeff j - Q.coeff j ∈ I) ∧
      (∀ (ι : Type) [Fintype ι] (F F' : ι → Polynomial O),
        (∀ i j, (F i).coeff j - (F' i).coeff j ∈ I) →
          ∀ j, (∏ i, F i).coeff j - (∏ i, F' i).coeff j ∈ I) := by
  have h1 : ∀ P Q : Polynomial O, P.map (Ideal.Quotient.mk I) = Q.map (Ideal.Quotient.mk I) ↔
      ∀ j, P.coeff j - Q.coeff j ∈ I := fun P Q ↦ by
    simp only [Polynomial.ext_iff, Polynomial.coeff_map, Ideal.Quotient.eq]
  refine ⟨h1, fun ι _ F F' h ↦ ?_⟩
  rw [← h1, Polynomial.map_prod, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun i _ ↦ (h1 _ _).2 (h i)

/-- For distinct monic irreducibles `gᵢ` over a field, `K[X]/(∏ gᵢ) ≃ ∏ K[X]/(gᵢ)` (Chinese
remainder), compatibly with `mk`. -/
theorem polynomial_quotient_product_equiv (K : Type) [Field K] (gs : List (Polynomial K))
    (hgs : ∀ g ∈ gs, g.Monic ∧ Irreducible g) (hd : gs.Pairwise (fun g h ↦ g ≠ h)) :
    ∃ e : AdjoinRoot gs.prod ≃ₐ[K] (∀ i : Fin gs.length, AdjoinRoot (gs.get i)),
      ∀ (P : Polynomial K) (i : Fin gs.length),
        e (AdjoinRoot.mk gs.prod P) i = AdjoinRoot.mk (gs.get i) P := by
  have hcop : ∀ i j : Fin gs.length, i ≠ j → IsCoprime (gs.get i) (gs.get j) := fun i j hij ↦
    distinct_monic_irreducible_coprime K _ _ (hgs _ (List.get_mem gs i)).1
      (hgs _ (List.get_mem gs j)).1 (hgs _ (List.get_mem gs i)).2 (hgs _ (List.get_mem gs j)).2
      fun h ↦ hij (List.Nodup.injective_get hd h)
  let f : Fin gs.length → Ideal (Polynomial K) := fun i ↦ Ideal.span {gs.get i}
  have heq : Ideal.span {gs.prod} = ⨅ i, f i := by
    rw [Ideal.iInf_span_singleton hcop, ← List.prod_ofFn, List.ofFn_get]
  let e1 : AdjoinRoot gs.prod ≃+* (∀ i : Fin gs.length, AdjoinRoot (gs.get i)) :=
    (Ideal.quotEquivOfEq heq).trans (Ideal.quotientInfRingEquivPiQuotient f fun i j hij ↦
      (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop i j hij))
  have hmk : ∀ P : Polynomial K, ∀ i, e1 (AdjoinRoot.mk gs.prod P) i = AdjoinRoot.mk (gs.get i) P :=
    fun P i ↦ rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := e1) fun c ↦ funext fun i ↦ ?_, hmk⟩
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply, hmk]
  rfl

/-! ### Root fields along a conjugate orbit -/

/-- If `L/K` is finite of degree `d`, `g` is monic irreducible over `L` dividing the monic
irreducible `H` over `K`, and `deg H = d · deg g`, then `K[X]/(H) ≃ L[X]/(g)` over `K`. -/
private theorem adjoinRoot_algEquiv_of_dvd_map (K L : Type) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (d : ℕ) (hd : Module.finrank K L = d)
    (g : Polynomial L) (hg : g.Monic) (hgi : Irreducible g)
    (H : Polynomial K) (hH : H.Monic) (hHi : Irreducible H)
    (hdiv : g ∣ H.map (algebraMap K L)) (hdeg : H.natDegree = d * g.natDegree) :
    Nonempty (AdjoinRoot H ≃ₐ[K] AdjoinRoot g) := by
  have : Fact (Irreducible H) := ⟨hHi⟩
  have : Fact (Irreducible g) := ⟨hgi⟩
  have h₀ : H.eval₂ (algebraMap K (AdjoinRoot g)) (AdjoinRoot.root g) = 0 := by
    obtain ⟨Q, hQ⟩ := hdiv
    rw [IsScalarTower.algebraMap_eq K L (AdjoinRoot g), ← Polynomial.eval₂_map, hQ,
      Polynomial.eval₂_mul, show g.eval₂ (algebraMap L (AdjoinRoot g)) (AdjoinRoot.root g) = 0 from
        AdjoinRoot.eval₂_root g, zero_mul]
  let φ := AdjoinRoot.liftAlgHom H (Algebra.ofId K (AdjoinRoot g)) (AdjoinRoot.root g) h₀
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have : Module.Finite L (AdjoinRoot g) := (AdjoinRoot.powerBasis hg.ne_zero).finite
  have : Module.Finite K (AdjoinRoot g) := .trans L (AdjoinRoot g)
  have : Module.Finite K (AdjoinRoot H) := (AdjoinRoot.powerBasis hH.ne_zero).finite
  have hsurj : Function.Surjective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [(AdjoinRoot.powerBasis hH.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
        ← Module.finrank_mul_finrank K L (AdjoinRoot g), (AdjoinRoot.powerBasis hg.ne_zero).finrank,
        AdjoinRoot.powerBasis_dim, hd, hdeg])).mp hinj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

/-- For the unramified extension `Kδ/K` of degree `δ = deg Φ`, a monic irreducible `g` over `Kδ`
dividing a monic irreducible `H` over `K` of degree `δ · deg g` has `K[X]/(H) ≃ Kδ[X]/(g)`. -/
theorem root_field_algEquiv_conjugate_orbit (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O)
    [IsDomain (AdjoinRoot Φ)] (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
    (hfin : letI := ι.toAlgebra; Module.Finite (BaseField O) (BaseField (AdjoinRoot Φ))
    ∧ Module.finrank (BaseField O) (BaseField (AdjoinRoot Φ)) = Φ.natDegree)
    (g : Polynomial (BaseField (AdjoinRoot Φ))) (hg : g.Monic) (hgi : Irreducible g)
    (H : Polynomial (BaseField O)) (hH : H.Monic) (hHi : Irreducible H) (hdiv : g ∣ H.map ι)
    (hdeg : H.natDegree = Φ.natDegree * g.natDegree) :
    letI := ι.toAlgebra; Nonempty (AdjoinRoot H ≃ₐ[BaseField O] AdjoinRoot g) := by
  let := ι.toAlgebra
  have := hfin.1
  exact adjoinRoot_algEquiv_of_dvd_map (BaseField O) (BaseField (AdjoinRoot Φ)) Φ.natDegree hfin.2
      g hg hgi H hH
    hHi hdiv hdeg

end SurfaceBlowup
