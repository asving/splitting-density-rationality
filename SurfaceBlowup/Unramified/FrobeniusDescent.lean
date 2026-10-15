/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Unramified.PolynomialTypes

/-!
# Frobenius descent for unramified extensions

Let `O` be a complete discrete valuation ring with finite residue field and let `Φ` be an
unramified lift (a monic polynomial over `O` with irreducible residue polynomial). This file
first computes the Haar mass of projective cells, then develops the ring `O_δ = O[X]/(Φ)`: it is a
complete discrete valuation ring, unramified over `O`, carrying a Frobenius automorphism of order
`δ = deg Φ` with fixed ring `O`. Finally it proves Frobenius descent for blocks: monic residue
cells of `residuePoly Φ ^ r` over `O` correspond bijectively, and congruence-preservingly, to block
cells over `O_δ`.

## Main results

* `SurfaceBlowup.projective_cell_mass`, `SurfaceBlowup.projective_cell_conditional_density`:
  the mass of a projective cell and its density inside the primitive locus.
* `SurfaceBlowup.unramified_is_dvr`: `O_δ` is a complete DVR with uniformizer any uniformizer of
  `O` and residue field of cardinality `q ^ δ`.
* `SurfaceBlowup.frobenius_pow_degree_eq_id`, `SurfaceBlowup.frobenius_fixed_ring`: the Frobenius
  has order dividing `δ` and its fixed points are exactly `O`.
* `SurfaceBlowup.block_descent_bijection`, `SurfaceBlowup.block_descent_congruence_iff`: the
  descent bijection between residue cells and block cells, and its compatibility with congruences.

Provenance: `Thm_SurfaceBlowupV2_{projective_cell_mass, projective_cell_mass_mul_normalizer,
projective_cell_conditional_density, unramified_base_invariants, inertiaDeg_unramified_tower,
ramificationIdx_unramified_tower, unramified_fraction_field_lift, unramified_free_module,
unramified_adic_complete, base_ideal_maximal_local, simple_root_derivative_unit,
frobenius_root_exists, frobenius_root_spec, frobenius_residue_action, frobenius_fixed_mod_pow,
frobenius_fixed_ring, root_unique_of_congruent, frobenius_pow_degree_eq_id, unramified_is_domain,
conjugate_product_invariant, descend_block_mem_cell, unramified_is_dvr, block_conjugates,
block_conjugates_coprime, block_splitting, block_descent_bijection, block_descent_congruence_iff}`.
-/

namespace SurfaceBlowup

open scoped BigOperators ENNReal

/-! ### Projective cells -/

/-- The projective cell of a nonzero residue vector `v` is measurable, of Haar mass
`(q - 1) * q⁻¹ ^ (n + 1)`. -/
theorem projective_cell_mass (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (v : Fin (n + 1) → IsLocalRing.ResidueField O) (hv : v ≠ 0) :
    MeasurableSet (projectiveCell O n v) ∧
      coefficientMeasure O (n+1) (projectiveCell O n v) =
        ((Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞) - 1) *
          (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (n+1) := by
  obtain ⟨hcard, hne, hfin⟩ := scalar_class_card (IsLocalRing.ResidueField O) n v hv
  set S := hfin.toFinset with hS
  have heq : projectiveCell O n v = ⋃ w ∈ S, {a : Fin (n+1) → O | residueVector O a = w} := by
    ext a
    simp only [projectiveCell, Set.mem_ofPred_eq, Set.mem_iUnion, hS, Set.Finite.mem_toFinset,
      exists_prop, exists_eq_right']
    exact ⟨fun h => h.2, fun h => ⟨(primitive_iff_residue_ne_zero O n a).2 (hne _ h), h⟩⟩
  have hmeas : ∀ w ∈ S, MeasurableSet {a : Fin (n+1) → O | residueVector O a = w} :=
    fun w _ => (residue_vector_fiber_mass O htop n w).1
  refine ⟨heq ▸ Finset.measurableSet_biUnion S hmeas, ?_⟩
  rw [heq, MeasureTheory.measure_biUnion_finset _ hmeas]
  · simp only [fun w => (residue_vector_fiber_mass O htop n w).2]
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    have : S.card = Nat.card (IsLocalRing.ResidueField O) - 1 := by
      rw [← hcard, hS, Nat.card_eq_card_finite_toFinset hfin]
    rw [this, ENNReal.natCast_sub]
    simp
  · exact fun w _ w' _ hww' => Set.disjoint_left.2 fun a h h' => hww' (h.symm.trans h')

/-- The mass of a projective cell times `∑_{i ≤ n} q ^ i` is the mass of the primitive locus. -/
private theorem projective_cell_mass_mul_normalizer (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (v : Fin (n + 1) → IsLocalRing.ResidueField O) (hv : v ≠ 0) :
    coefficientMeasure O (n+1) (projectiveCell O n v) *
        (∑ i ∈ Finset.range (n+1), (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞) ^ i) =
      coefficientMeasure O (n+1) {a : Fin (n+1) → O | primitive O a} := by
  rw [(projective_cell_mass O htop n v hv).2, primitive_locus_mass O htop n]
  set q := Nat.card (IsLocalRing.ResidueField O)
  have hq : 1 < q := Finite.one_lt_card
  have hN : (q - 1) * ∑ i ∈ Finset.range (n+1), q ^ i = q ^ (n+1) - 1 := by
    have h1 : 1 ≤ q ^ (n+1) := Nat.one_le_pow _ _ (by omega)
    zify [hq.le, h1]
    rw [mul_comm]; exact_mod_cast geom_sum_mul (q : ℤ) (n+1)
  have hE : ((q : ℝ≥0∞) - 1) * ∑ i ∈ Finset.range (n+1), (q : ℝ≥0∞) ^ i
      = (q : ℝ≥0∞) ^ (n+1) - 1 := by
    have := congrArg (fun m : ℕ => (m : ℝ≥0∞)) hN
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow] at this
    rw [ENNReal.natCast_sub, ENNReal.natCast_sub] at this
    simpa [Nat.cast_pow] using this
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqt : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  calc ((q : ℝ≥0∞) - 1) * (q : ℝ≥0∞)⁻¹ ^ (n+1) * ∑ i ∈ Finset.range (n+1), (q : ℝ≥0∞) ^ i
      = (((q : ℝ≥0∞) - 1) * ∑ i ∈ Finset.range (n+1), (q : ℝ≥0∞) ^ i) *
          (q : ℝ≥0∞)⁻¹ ^ (n+1) := by ring
    _ = ((q : ℝ≥0∞) ^ (n+1) - 1) * (q : ℝ≥0∞)⁻¹ ^ (n+1) := by rw [hE]
    _ = 1 - (q : ℝ≥0∞)⁻¹ ^ (n+1) := by
      rw [ENNReal.sub_mul (fun _ _ => ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hq0)),
        ← mul_pow, ENNReal.mul_inv_cancel hq0 hqt, one_pow, one_mul]

/-- The conditional density of a projective cell inside the primitive locus is the value of
`1 / projectiveNormalizer n` at `q`. -/
theorem projective_cell_conditional_density (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (v : Fin (n + 1) → IsLocalRing.ResidueField O) (hv : v ≠ 0) :
    coefficientMeasure O (n+1) (projectiveCell O n v) /
        coefficientMeasure O (n+1) {a : Fin (n+1) → O | primitive O a} =
      densityValue (Expr.inv (projectiveNormalizer n)) (Nat.card (IsLocalRing.ResidueField O)) := by
  have hmul := projective_cell_mass_mul_normalizer O htop n v hv
  have hP := primitive_locus_mass O htop n
  have hev := (projective_normalizer_eval (Nat.card (IsLocalRing.ResidueField O) : ℚ) n).1
  set q := Nat.card (IsLocalRing.ResidueField O)
  have hq1 : 1 < q := Finite.one_lt_card
  set C := coefficientMeasure O (n+1) (projectiveCell O n v)
  set P := coefficientMeasure O (n+1) {a : Fin (n+1) → O | primitive O a}
  set D : ℝ≥0∞ := ∑ i ∈ Finset.range (n+1), (q : ℝ≥0∞) ^ i with hD
  have hD0 : D ≠ 0 := by
    intro h
    rw [hD, Finset.sum_eq_zero_iff] at h
    simpa using h 0 (by simp)
  have hDtop : D ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun i _ => ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  have hPtop : P ≠ ⊤ := by rw [hP]; exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hP0 : P ≠ 0 := by
    rw [hP]
    apply ne_of_gt
    rw [tsub_pos_iff_lt]
    apply pow_lt_one₀ (zero_le) _ (Nat.succ_ne_zero _)
    rw [ENNReal.inv_lt_one]
    exact_mod_cast hq1
  have hC0 : C ≠ 0 := by rintro h; rw [h, zero_mul] at hmul; exact hP0 hmul.symm
  have hCtop : C ≠ ⊤ := by
    rintro h; rw [h, ENNReal.top_mul hD0] at hmul; exact hPtop hmul.symm
  have lhs : C / P = D⁻¹ := by
    rw [← hmul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hC0) (Or.inl hCtop), mul_comm C⁻¹,
      mul_assoc, ENNReal.inv_mul_cancel hC0 hCtop, mul_one]
  rw [lhs, densityValue]
  change D⁻¹ = ENNReal.ofReal (((projectiveNormalizer n).eval (q : ℚ))⁻¹ : ℚ)
  rw [hev]
  have hpos : (0 : ℝ) < ((∑ i ∈ Finset.range (n+1), (q : ℚ) ^ i : ℚ) : ℝ) := by
    push_cast
    exact Finset.sum_pos (fun i _ => by positivity) ⟨0, by simp⟩
  rw [Rat.cast_inv, ENNReal.ofReal_inv_of_pos hpos]
  congr 1
  rw [hD]; push_cast
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  exact Finset.sum_congr rfl fun i _ => by rw [ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast]

/-! ### Unramified extensions of discrete valuation rings -/

/-- A finite free extension of DVRs of rank `δ` in which a uniformizer stays irreducible has
ramification index `1` and inertia degree `δ`. -/
private theorem unramified_base_invariants (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ)
    (hrank : Module.finrank O Oδ = δ) (pi : O) (hpi : Irreducible pi)
    (hpiδ : Irreducible (algebraMap O Oδ pi)) :
    (IsLocalRing.maximalIdeal Oδ).ramificationIdx O = 1 ∧
      (IsLocalRing.maximalIdeal Oδ).inertiaDeg O = δ := by
  have hinj : Function.Injective (algebraMap O Oδ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hpi
    rw [map_mul, map_pow] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact (Units.map (algebraMap O Oδ : O →* Oδ) u).ne_zero h
    · exact hpiδ.ne_zero (pow_eq_zero_iff'.mp h).1
  have : Algebra.IsIntegral O Oδ := Algebra.IsIntegral.of_finite O Oδ
  have h512 := dvr_extension_maximalIdeal_map_eq_pow O Oδ hinj
  have h1 : (IsLocalRing.maximalIdeal O).map (algebraMap O Oδ) =
      (IsLocalRing.maximalIdeal Oδ) ^ 1 := by
    rw [pow_one, hpi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      ← hpiδ.maximalIdeal_eq]
  have he : (IsLocalRing.maximalIdeal Oδ).ramificationIdx O = 1 :=
    dvr_maximalIdeal_pow_injective Oδ _ _ (h512.symm.trans h1)
  have : Module.Flat O Oδ := Module.Flat.of_free
  have h251 := finite_flat_local_ramification_degree O Oδ
  rw [he, hrank, one_mul] at h251
  exact ⟨he, h251⟩

/-- In a tower `O → O_δ → B` with `O_δ` unramified of rank `δ` over `O`, inertia degrees over `O`
are `δ` times inertia degrees over `O_δ`. -/
theorem inertiaDeg_unramified_tower (O Oδ B : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O Oδ] [Algebra O B]
    [Algebra Oδ B] [IsScalarTower O Oδ B] [Module.Finite O Oδ] [Module.Free O Oδ]
    [Module.Finite Oδ B] (δ : ℕ) (hrank : Module.finrank O Oδ = δ) (pi : O)
    (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi)) :
    (IsLocalRing.maximalIdeal B).inertiaDeg O =
      δ * (IsLocalRing.maximalIdeal B).inertiaDeg Oδ := by
  have : Algebra.IsIntegral Oδ B := Algebra.IsIntegral.of_finite Oδ B
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal Oδ) :=
    ⟨(integral_local_extension_unique_prime Oδ B).1.symm⟩
  rw [Ideal.inertiaDeg_tower (R := O) (S := Oδ) (IsLocalRing.maximalIdeal Oδ)
    (IsLocalRing.maximalIdeal B), (unramified_base_invariants O Oδ δ hrank pi hpi hpiδ).2]

/-- In a tower `O → O_δ → B` with `O_δ` unramified over `O`, ramification indices over `O` and
over `O_δ` agree. -/
theorem ramificationIdx_unramified_tower (O Oδ B : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O Oδ] [Algebra O B]
    [Algebra Oδ B] [IsScalarTower O Oδ B] [Module.Finite O Oδ] [Module.Free O Oδ]
    [Module.Finite Oδ B] (δ : ℕ) (hrank : Module.finrank O Oδ = δ) (pi : O)
    (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi)) [Module.Free Oδ B] :
    (IsLocalRing.maximalIdeal B).ramificationIdx O =
      (IsLocalRing.maximalIdeal B).ramificationIdx Oδ := by
  have : Algebra.IsIntegral Oδ B := Algebra.IsIntegral.of_finite Oδ B
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal Oδ) :=
    ⟨(integral_local_extension_unique_prime Oδ B).1.symm⟩
  rw [Ideal.ramificationIdx_tower (R := O) (S := Oδ) (T := B) (IsLocalRing.maximalIdeal Oδ)
    (IsLocalRing.maximalIdeal B), (unramified_base_invariants O Oδ δ hrank pi hpi hpiδ).1,
    one_mul]

/-- For an unramified lift `Φ` with `O[X]/(Φ)` a domain, there is a unique ring map of fraction
fields extending `O → O[X]/(Φ)`; it is injective and makes the target a field extension of degree
`deg Φ`. -/
theorem unramified_fraction_field_lift (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] :
    ∃ ι : BaseField O →+* BaseField (AdjoinRoot Φ),
      (∀ c : O, ι (algebraMap O (BaseField O) c) =
        algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c)) ∧
      Function.Injective ι ∧
      (∀ ι' : BaseField O →+* BaseField (AdjoinRoot Φ),
        (∀ c : O, ι' (algebraMap O (BaseField O) c) =
          algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c)) →
        ι' = ι) ∧
      (letI := ι.toAlgebra; Module.Finite (BaseField O) (BaseField (AdjoinRoot Φ)) ∧
        Module.finrank (BaseField O) (BaseField (AdjoinRoot Φ)) = Φ.natDegree) := by
  have hmon : Φ.Monic := hΦ.1
  let pb := AdjoinRoot.powerBasis' hmon
  have : Module.Free O (AdjoinRoot Φ) := Module.Free.of_basis pb.basis
  have : Module.Finite O (AdjoinRoot Φ) := pb.finite
  let j : O →+* BaseField (AdjoinRoot Φ) :=
    (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))).comp (algebraMap O (AdjoinRoot Φ))
  have hj : Function.Injective j :=
    (IsFractionRing.injective (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))).comp
      (FaithfulSMul.algebraMap_injective O (AdjoinRoot Φ))
  refine ⟨IsFractionRing.lift hj, fun c => IsFractionRing.lift_algebraMap hj c,
    RingHom.injective (IsFractionRing.lift hj : BaseField O →+* BaseField (AdjoinRoot Φ)),
    fun ι' h => ?_, ?_⟩
  · exact IsFractionRing.ringHom_ext (A := O) (K := BaseField O) fun c => by
      rw [h, IsFractionRing.lift_algebraMap hj c]; rfl
  · let _ : Algebra (BaseField O) (BaseField (AdjoinRoot Φ)) := (IsFractionRing.lift hj).toAlgebra
    have : IsScalarTower O (BaseField O) (BaseField (AdjoinRoot Φ)) :=
      IsScalarTower.of_algebraMap_eq fun c => by
        change _ = IsFractionRing.lift hj _
        rw [IsFractionRing.lift_algebraMap hj c]
        exact IsScalarTower.algebraMap_apply O (AdjoinRoot Φ) _ c
    have hrank : Module.finrank (BaseField O) (BaseField (AdjoinRoot Φ)) = Φ.natDegree := by
      rw [IsFractionRing.finrank_eq O (BaseField O) (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)),
        pb.finrank]
      exact AdjoinRoot.powerBasis'_dim hmon
    refine ⟨?_, hrank⟩
    apply Module.finite_of_finrank_pos
    rw [hrank, ← hmon.natDegree_map (IsLocalRing.residue O)]
    exact Irreducible.natDegree_pos hΦ.2

/-- For monic `Φ`, `O[X]/(Φ)` is a free `O`-module of finite rank `deg Φ`. -/
theorem unramified_free_module (O : Type) [CommRing O] [Nontrivial O] (Φ : Polynomial O)
    (hΦ : Φ.Monic) :
    Module.Free O (AdjoinRoot Φ) ∧ Module.Finite O (AdjoinRoot Φ) ∧
      Module.finrank O (AdjoinRoot Φ) = Φ.natDegree :=
  ⟨hΦ.free_adjoinRoot, hΦ.finite_adjoinRoot, by simp [(AdjoinRoot.powerBasis' hΦ).finrank]⟩

/-- For monic `Φ` over a complete local ring, `O[X]/(Φ)` is complete and separated for the
extended ideal `𝔪 O[X]/(Φ)`, and regular elements of `O` stay regular in it. -/
private theorem unramified_adic_complete (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Φ : Polynomial O) (hΦ : Φ.Monic) :
    IsAdicComplete (baseIdeal O Φ) (AdjoinRoot Φ) ∧
      (∀ x : AdjoinRoot Φ, (∀ L, x ∈ (baseIdeal O Φ)^L) → x = 0) ∧
      (∀ c : O, (∀ y : O, c * y = 0 → y = 0) →
        ∀ x : AdjoinRoot Φ, algebraMap O (AdjoinRoot Φ) c * x = 0 → x = 0) := by
  obtain ⟨hfree, hfin, -⟩ := unramified_free_module O Φ hΦ
  refine ⟨?_, ?_, ?_⟩
  · exact (IsAdicComplete.map_algebraMap_iff (S := AdjoinRoot Φ) (M := AdjoinRoot Φ)
      (I := IsLocalRing.maximalIdeal O)).2 (finite_free_adic_complete O (AdjoinRoot Φ) _)
  · intro x hx
    apply (AdjoinRoot.powerBasis' hΦ).basis.repr.injective
    ext i
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    have hi : ∀ L, (AdjoinRoot.powerBasis' hΦ).basis.repr x i ∈ (IsLocalRing.maximalIdeal O)^L :=
      fun L => (base_ideal_coordinates O Φ hΦ L x).1 (hx L) i
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := IsLocalRing.maximalIdeal O))
    intro n
    simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hi n
  · intro c hc x hx
    rw [← Algebra.smul_def] at hx
    apply (AdjoinRoot.powerBasis' hΦ).basis.repr.injective
    ext i
    have := congrArg (fun y => (AdjoinRoot.powerBasis' hΦ).basis.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    exact hc _ this

/-- For an unramified lift `Φ`, the extended ideal `𝔪 O[X]/(Φ)` is maximal, units can be detected
modulo it, and `O[X]/(Φ)` is local with that maximal ideal. -/
theorem base_ideal_maximal_local (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    (baseIdeal O Φ).IsMaximal ∧ (∀ x : AdjoinRoot Φ, IsUnit (baseReduce O Φ x) → IsUnit x) ∧
      ∃ _ : IsLocalRing (AdjoinRoot Φ),
        IsLocalRing.maximalIdeal (AdjoinRoot Φ) = baseIdeal O Φ := by
  have hF := (residue_extension_field O Φ hΦ).1
  have hmax : (baseIdeal O Φ).IsMaximal := Ideal.Quotient.maximal_of_isField _ hF
  have hC := (unramified_adic_complete O Φ hΦ.1).1
  have hloc : IsLocalHom (baseReduce O Φ) :=
    isLocalHom_of_le_jacobson_bot _ (IsAdicComplete.le_jacobson_bot _)
  have hunit : ∀ x : AdjoinRoot Φ, IsUnit (baseReduce O Φ x) → IsUnit x :=
    fun x hx => IsUnit.of_map (baseReduce O Φ) x hx
  let _ : Field (residueExtension O Φ) := hF.toField
  have : Nontrivial (AdjoinRoot Φ) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hmax.ne_top (Subsingleton.elim _ _)
  have : IsLocalRing (AdjoinRoot Φ) := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    by_cases ha : baseReduce O Φ a = 0
    · right; apply hunit; simp [map_sub, ha]
    · left; exact hunit a (Ne.isUnit ha)
  exact ⟨hmax, hunit, inferInstance, (IsLocalRing.eq_maximalIdeal hmax).symm⟩

/-- An approximate root of `Φ` in `O[X]/(Φ)` (a root modulo `𝔪`) is a simple root: the derivative
of `Φ` there is a unit, already modulo `𝔪`. -/
theorem simple_root_derivative_unit (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (a : AdjoinRoot Φ)
    (ha : baseReduce O Φ ((Φ.map (AdjoinRoot.of Φ)).eval a) = 0) :
    IsUnit (baseReduce O Φ ((Φ.map (AdjoinRoot.of Φ)).derivative.eval a)) ∧
      IsUnit ((Φ.map (AdjoinRoot.of Φ)).derivative.eval a) := by
  have hle : IsLocalRing.maximalIdeal O ≤ (baseIdeal O Φ).comap (AdjoinRoot.of Φ) :=
    Ideal.map_le_iff_le_comap.1 le_rfl
  let ρ : IsLocalRing.ResidueField O →+* residueExtension O Φ :=
    Ideal.quotientMap (baseIdeal O Φ) (AdjoinRoot.of Φ) hle
  have hcomp : (baseReduce O Φ).comp (AdjoinRoot.of Φ) = ρ.comp (IsLocalRing.residue O) :=
    (Ideal.quotientMap_comp_mk hle).symm
  have key : ∀ p : Polynomial O, baseReduce O Φ ((p.map (AdjoinRoot.of Φ)).eval a)
      = (p.map (IsLocalRing.residue O)).eval₂ ρ (baseReduce O Φ a) := fun p => by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp]
  let _ : Field (residueExtension O Φ) := (residue_extension_field O Φ hΦ).1.toField
  have hsep : (residuePoly O Φ).Separable := PerfectField.separable_of_irreducible hΦ.2
  have h1 : IsUnit (baseReduce O Φ ((Φ.map (AdjoinRoot.of Φ)).derivative.eval a)) := by
    rw [Polynomial.derivative_map, key, ← Polynomial.derivative_map]
    rw [key] at ha
    exact isUnit_iff_ne_zero.mpr (hsep.eval₂_derivative_ne_zero ρ ha)
  exact ⟨h1, (base_ideal_maximal_local O Φ hΦ).2.1 _ h1⟩

/-! ### The Frobenius automorphism -/

/-- Hensel's lemma produces a root of `Φ` in `O[X]/(Φ)` congruent to `X ^ q` modulo `𝔪`. -/
private theorem frobenius_root_exists (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    ∃ a : AdjoinRoot Φ, (Φ.map (AdjoinRoot.of Φ)).IsRoot a ∧
      a - (AdjoinRoot.root Φ) ^ residueCard O ∈ baseIdeal O Φ := by
  have : IsAdicComplete (baseIdeal O Φ) (AdjoinRoot Φ) := (unramified_adic_complete O Φ hΦ.1).1
  have : HenselianRing (AdjoinRoot Φ) (baseIdeal O Φ) := IsAdicComplete.henselianRing _ _
  have hker : ∀ c ∈ IsLocalRing.maximalIdeal O,
      ((baseReduce O Φ).comp (AdjoinRoot.of Φ)) c = 0 := fun c hc => by
    simp only [RingHom.comp_apply, baseReduce, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hc
  let ρ : IsLocalRing.ResidueField O →+* residueExtension O Φ :=
    Ideal.Quotient.lift _ ((baseReduce O Φ).comp (AdjoinRoot.of Φ)) hker
  have key : ∀ x : AdjoinRoot Φ, baseReduce O Φ ((Φ.map (AdjoinRoot.of Φ)).eval x)
      = (residuePoly O Φ).eval₂ ρ (baseReduce O Φ x) := fun x => by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, residuePoly, Polynomial.eval₂_map]
    congr 1
  have h0 : baseReduce O Φ
      ((Φ.map (AdjoinRoot.of Φ)).eval (AdjoinRoot.root Φ ^ residueCard O)) = 0 := by
    rw [key, map_pow, residueCard, eval_at_pow_card (IsLocalRing.ResidueField O) _ ρ
      (residuePoly O Φ) (baseReduce O Φ (AdjoinRoot.root Φ)), ← key,
      show (Φ.map (AdjoinRoot.of Φ)).eval (AdjoinRoot.root Φ) = 0 from AdjoinRoot.isRoot_root Φ,
      map_zero, zero_pow Nat.card_pos.ne']
  exact HenselianRing.is_henselian (Φ.map (AdjoinRoot.of Φ)) (hΦ.1.map _)
    (AdjoinRoot.root Φ ^ residueCard O) (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    (simple_root_derivative_unit O Φ hΦ _ h0).1

/-- The Frobenius root is a root of `Φ` congruent to `X ^ q`, and the Frobenius is the
`O`-algebra endomorphism sending `X` to it. -/
private theorem frobenius_root_spec (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    (Φ.map (AdjoinRoot.of Φ)).IsRoot (frobeniusRoot O Φ) ∧
      frobeniusRoot O Φ - (AdjoinRoot.root Φ) ^ residueCard O ∈ baseIdeal O Φ ∧
      unramifiedFrobenius O Φ (AdjoinRoot.root Φ) = frobeniusRoot O Φ ∧
      ∀ c : O, unramifiedFrobenius O Φ (algebraMap O (AdjoinRoot Φ) c) =
        algebraMap O (AdjoinRoot Φ) c := by
  have h := frobenius_root_exists O Φ hΦ
  have hr : frobeniusRoot O Φ = Classical.choose h := dif_pos h
  exact ⟨hr ▸ (Classical.choose_spec h).1, hr ▸ (Classical.choose_spec h).2,
    AdjoinRoot.liftAlgHom_root _ _ _ _, (unramifiedFrobenius O Φ).commutes⟩

/-- Modulo `𝔪`, the Frobenius acts as `x ↦ x ^ q`, and its `i`-th iterate as `x ↦ x ^ (q ^ i)`. -/
private theorem frobenius_residue_action (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    (∀ x : AdjoinRoot Φ,
      baseReduce O Φ (unramifiedFrobenius O Φ x) = (baseReduce O Φ x) ^ residueCard O) ∧
    (∀ (i : ℕ) (x : AdjoinRoot Φ),
      baseReduce O Φ (frobeniusIter O Φ i x) = (baseReduce O Φ x) ^ (residueCard O ^ i)) := by
  obtain ⟨-, hcong, hroot, -⟩ := frobenius_root_spec O Φ hΦ
  have hle : IsLocalRing.maximalIdeal O ≤
      RingHom.ker ((baseReduce O Φ).comp (AdjoinRoot.of Φ)) := fun c hc => by
    rw [RingHom.mem_ker, RingHom.comp_apply, baseReduce, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hc
  let ρ : IsLocalRing.ResidueField O →+* residueExtension O Φ :=
    Ideal.Quotient.lift _ ((baseReduce O Φ).comp (AdjoinRoot.of Φ)) hle
  have hρ : ρ.comp (IsLocalRing.residue O) = (baseReduce O Φ).comp (AdjoinRoot.of Φ) := by
    ext c; rfl
  have key : ∀ (p : Polynomial O) (a : AdjoinRoot Φ),
      baseReduce O Φ (Polynomial.aeval a p) =
        (p.map (IsLocalRing.residue O)).eval₂ ρ (baseReduce O Φ a) := fun p a => by
    rw [Polynomial.eval₂_map, hρ, Polynomial.aeval_def, Polynomial.hom_eval₂]
    rfl
  have h1 : ∀ x : AdjoinRoot Φ, baseReduce O Φ (unramifiedFrobenius O Φ x) =
      (baseReduce O Φ x) ^ residueCard O := by
    intro x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, hroot, key, key]
    have : baseReduce O Φ (frobeniusRoot O Φ) =
        (baseReduce O Φ (AdjoinRoot.root Φ)) ^ residueCard O := by
      rw [← map_pow, baseReduce, Ideal.Quotient.eq]; exact hcong
    rw [this]
    exact eval_at_pow_card _ _ ρ _ _
  refine ⟨h1, fun i => ?_⟩
  induction i with
  | zero => intro x; simp [frobeniusIter]
  | succ i ih =>
    intro x
    change baseReduce O Φ (unramifiedFrobenius O Φ (frobeniusIter O Φ i x)) = _
    rw [h1, ih, ← pow_mul, pow_succ]

private theorem natDegree_pos_of_isUnramifiedLift {O : Type} [CommRing O] [IsLocalRing O]
    {Φ : Polynomial O} (hΦ : IsUnramifiedLift O Φ) : 0 < Φ.natDegree := by
  have := hΦ.2.natDegree_pos
  rwa [residuePoly, hΦ.1.natDegree_map] at this

/-- An element of `O[X]/(Φ)` fixed by the Frobenius modulo `𝔪 ^ L` is congruent to an element of
`O` modulo `𝔪 ^ L`. -/
private theorem frobenius_fixed_mod_pow (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (L : ℕ) (a : AdjoinRoot Φ)
    (ha : unramifiedFrobenius O Φ a - a ∈ (baseIdeal O Φ) ^ L) :
    ∃ c : O, a - algebraMap O (AdjoinRoot Φ) c ∈ (baseIdeal O Φ)^L := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set σ := unramifiedFrobenius O Φ
  have hpow : ∀ j : ℕ, (baseIdeal O Φ) ^ j = Ideal.span {algebraMap O (AdjoinRoot Φ) ϖ ^ j} :=
    fun j => by
      rw [baseIdeal, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_pow]
      rfl
  have hmem1 : ∀ x, x ∈ baseIdeal O Φ ↔ ∃ e, x = e * algebraMap O (AdjoinRoot Φ) ϖ := fun x => by
    rw [← pow_one (baseIdeal O Φ), hpow, pow_one, Ideal.mem_span_singleton']
    exact ⟨fun ⟨e, he⟩ => ⟨e, he.symm⟩, fun ⟨e, he⟩ => ⟨e, he.symm⟩⟩
  have htf := (unramified_adic_complete O Φ hΦ.1).2.2
  obtain ⟨hfield, -, -⟩ := residue_extension_field O Φ hΦ
  let _ : Field (residueExtension O Φ) := hfield.toField
  have hres := (frobenius_residue_action O Φ hΦ).1
  let ρ : IsLocalRing.ResidueField O →+* residueExtension O Φ :=
    Ideal.quotientMap (baseIdeal O Φ) (AdjoinRoot.of Φ) Ideal.le_comap_map
  induction L generalizing a with
  | zero => exact ⟨0, by simp⟩
  | succ L ih =>
    obtain ⟨c, hc⟩ := ih a (Ideal.pow_le_pow_right (Nat.le_succ L) ha)
    rw [hpow, Ideal.mem_span_singleton'] at hc ha
    obtain ⟨b, hb⟩ := hc
    obtain ⟨d, hd⟩ := ha
    have ha' : a = algebraMap O (AdjoinRoot Φ) c + b * algebraMap O (AdjoinRoot Φ) ϖ ^ L := by
      rw [hb]; ring
    have hσa : σ a - a = algebraMap O (AdjoinRoot Φ) (ϖ ^ L) * (σ b - b) := by
      rw [ha', map_add, map_mul, map_pow, AlgHom.commutes, AlgHom.commutes, map_pow]; ring
    have hkey : σ b - b = algebraMap O (AdjoinRoot Φ) ϖ * d := by
      have h0 : algebraMap O (AdjoinRoot Φ) (ϖ ^ L) *
          (σ b - b - algebraMap O (AdjoinRoot Φ) ϖ * d) = 0 := by
        rw [mul_sub, ← hσa, ← hd, map_pow]; ring
      exact sub_eq_zero.1 (htf _ (fun y hy => (mul_eq_zero.1 hy).resolve_left
        (pow_ne_zero _ hϖ.ne_zero)) _ h0)
    have hfix : (baseReduce O Φ b) ^ Nat.card (IsLocalRing.ResidueField O) = baseReduce O Φ b := by
      rw [← hres b]
      exact Ideal.Quotient.eq.2 ((hmem1 _).2 ⟨d, by rw [hkey, mul_comm]⟩)
    obtain ⟨r, hr⟩ := (finite_field_frobenius_fixed_points _ _ ρ _).1 hfix
    obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective r
    have hbc : b - algebraMap O (AdjoinRoot Φ) c' ∈ baseIdeal O Φ := by
      apply Ideal.Quotient.eq.1
      rw [← hr]; rfl
    obtain ⟨e, he⟩ := (hmem1 _).1 hbc
    refine ⟨c + ϖ ^ L * c', ?_⟩
    rw [hpow, Ideal.mem_span_singleton']
    refine ⟨e, ?_⟩
    rw [ha', show b = algebraMap O (AdjoinRoot Φ) c' + e * algebraMap O (AdjoinRoot Φ) ϖ by
      rw [← he]; ring, map_add, map_mul, map_pow]
    ring

/-- The elements of `O[X]/(Φ)` fixed by the Frobenius are exactly the elements of `O`. -/
theorem frobenius_fixed_ring (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (a : AdjoinRoot Φ)
    (ha : unramifiedFrobenius O Φ a = a) :
    ∃ c : O, algebraMap O (AdjoinRoot Φ) c = a := by
  have hc : ∀ L : ℕ, ∃ c : O, a - algebraMap O (AdjoinRoot Φ) c ∈ (baseIdeal O Φ)^L :=
    fun L => frobenius_fixed_mod_pow O Φ hΦ L a (by rw [ha, sub_self]; exact Submodule.zero_mem _)
  choose c hc using hc
  set m := IsLocalRing.maximalIdeal O
  have hpure := base_ideal_pure O Φ hΦ.1 (natDegree_pos_of_isUnramifiedLift hΦ)
  have hcompat : ∀ {L L' : ℕ}, L ≤ L' → c L ≡ c L' [SMOD (m ^ L • ⊤ : Submodule O O)] := by
    intro L L' hLL'
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← hpure]
    have : algebraMap O (AdjoinRoot Φ) (c L - c L') =
        (a - algebraMap O (AdjoinRoot Φ) (c L')) - (a - algebraMap O (AdjoinRoot Φ) (c L)) := by
      rw [map_sub]; ring
    rw [this]; exact Ideal.sub_mem _ (Ideal.pow_le_pow_right hLL' (hc L')) (hc L)
  obtain ⟨c0, hc0⟩ := IsPrecomplete.prec (I := m) inferInstance hcompat
  refine ⟨c0, ?_⟩
  rw [← sub_eq_zero, ← neg_sub, neg_eq_zero]
  refine (unramified_adic_complete O Φ hΦ.1).2.1 _ fun L => ?_
  have h3 : c L - c0 ∈ m ^ L := by
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hc0 L
  rw [← hpure] at h3
  have : a - algebraMap O (AdjoinRoot Φ) c0 =
      (a - algebraMap O (AdjoinRoot Φ) (c L)) + algebraMap O (AdjoinRoot Φ) (c L - c0) := by
    rw [map_sub]; ring
  rw [this]; exact Ideal.add_mem _ (hc L) h3

/-- Two roots of `Φ` in `O[X]/(Φ)` that are congruent modulo `𝔪` are equal. -/
private theorem root_unique_of_congruent (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (a b : AdjoinRoot Φ)
    (ha : (Φ.map (AdjoinRoot.of Φ)).IsRoot a) (hb : (Φ.map (AdjoinRoot.of Φ)).IsRoot b)
    (hab : a - b ∈ baseIdeal O Φ) :
    a = b := by
  set Φ' := Φ.map (AdjoinRoot.of Φ)
  set d := b - a with hd
  have hdI : d ∈ baseIdeal O Φ := by simpa [hd] using (baseIdeal O Φ).neg_mem hab
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion Φ' a d
  rw [show a + d = b by simp [hd]] at hk
  have h0 : d * (Φ'.derivative.eval a + k * d) = 0 := by
    rw [show Φ'.eval b = 0 from hb, show Φ'.eval a = 0 from ha] at hk
    linear_combination -hk
  obtain ⟨v, hv⟩ := (simple_root_derivative_unit O Φ hΦ a (by
    change baseReduce O Φ (Φ'.eval a) = 0
    rw [show Φ'.eval a = 0 from ha, map_zero])).2
  have hC := (unramified_adic_complete O Φ hΦ.1).1
  have hJ : baseIdeal O Φ ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  have hkd : (↑v⁻¹ : AdjoinRoot Φ) * (k * d) ∈ baseIdeal O Φ :=
    (baseIdeal O Φ).mul_mem_left _ ((baseIdeal O Φ).mul_mem_left _ hdI)
  have h1 : IsUnit ((↑v⁻¹ : AdjoinRoot Φ) * (k * d) + 1) := by
    simpa using Ideal.mem_jacobson_bot.mp (hJ hkd) 1
  have h2 : IsUnit (Φ'.derivative.eval a + k * d) := by
    have : Φ'.derivative.eval a + k * d = v * ((↑v⁻¹ : AdjoinRoot Φ) * (k * d) + 1) := by
      rw [← hv, mul_add, ← mul_assoc, Units.mul_inv, one_mul, mul_one, add_comm]
    rw [this]; exact v.isUnit.mul h1
  have : d = 0 := h2.mul_right_cancel (by rw [h0, zero_mul])
  exact (sub_eq_zero.mp this).symm

/-- The `deg Φ`-th iterate of the Frobenius is the identity; in particular the Frobenius is
bijective. -/
theorem frobenius_pow_degree_eq_id (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    frobeniusIter O Φ Φ.natDegree = AlgHom.id O (AdjoinRoot Φ) ∧
      Function.Bijective (unramifiedFrobenius O Φ) := by
  -- roots are preserved by algebra maps
  have hroot : ∀ f : AdjoinRoot Φ →ₐ[O] AdjoinRoot Φ,
      (Φ.map (AdjoinRoot.of Φ)).IsRoot (f (AdjoinRoot.root Φ)) := by
    intro f
    have h0 : Polynomial.aeval (AdjoinRoot.root Φ) Φ = 0 := AdjoinRoot.aeval_eq Φ ▸ by simp
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← AdjoinRoot.algebraMap_eq,
      ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, h0, map_zero]
  have hid : frobeniusIter O Φ Φ.natDegree = AlgHom.id O (AdjoinRoot Φ) := by
    apply AdjoinRoot.algHom_ext
    obtain ⟨hF, hFin, hcard⟩ := residue_extension_field O Φ hΦ
    let _ := hF.toField
    let _ := Fintype.ofFinite (residueExtension O Φ)
    have hc : Fintype.card (residueExtension O Φ) = residueCard O ^ Φ.natDegree := by
      rw [← Nat.card_eq_fintype_card, hcard]
    have h2 := (frobenius_residue_action O Φ hΦ).2 Φ.natDegree (AdjoinRoot.root Φ)
    rw [← hc, FiniteField.pow_card] at h2
    exact root_unique_of_congruent O Φ hΦ _ _ (hroot _) (hroot (AlgHom.id O _))
      (Ideal.Quotient.eq.mp h2)
  refine ⟨hid, ?_⟩
  have hcomm : ∀ i, frobeniusIter O Φ (i+1) =
      (frobeniusIter O Φ i).comp (unramifiedFrobenius O Φ) := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih =>
      change (unramifiedFrobenius O Φ).comp (frobeniusIter O Φ (n+1)) = _
      conv_lhs => rw [ih]
      rw [← AlgHom.comp_assoc]; rfl
  obtain ⟨d, hd⟩ : ∃ d, Φ.natDegree = d + 1 :=
    ⟨Φ.natDegree - 1, by have := natDegree_pos_of_isUnramifiedLift hΦ; omega⟩
  rw [Function.bijective_iff_has_inverse]
  refine ⟨frobeniusIter O Φ d, fun x => ?_, fun x => ?_⟩
  · have := congrArg (fun f : AdjoinRoot Φ →ₐ[O] AdjoinRoot Φ => f x) hid
    simp only [hd, hcomm] at this
    exact this
  · have := congrArg (fun f : AdjoinRoot Φ →ₐ[O] AdjoinRoot Φ => f x) hid
    simp only [hd] at this
    exact this

/-- For an unramified lift `Φ`, the ring `O[X]/(Φ)` is an integral domain. -/
private theorem unramified_is_domain (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    IsDomain (AdjoinRoot Φ) := by
  classical
  obtain ⟨hcomp, hsep, htors⟩ := unramified_adic_complete O Φ hΦ.1
  obtain ⟨hfield, -, -⟩ := residue_extension_field O Φ hΦ
  let _ : Field (residueExtension O Φ) := hfield.toField
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set c : AdjoinRoot Φ := algebraMap O (AdjoinRoot Φ) ϖ with hc
  have hI : baseIdeal O Φ = Ideal.span {c} := by
    rw [baseIdeal, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hc,
      AdjoinRoot.algebraMap_eq]
  have hIpow : ∀ L : ℕ, (baseIdeal O Φ) ^ L = Ideal.span {c ^ L} := fun L => by
    rw [hI, Ideal.span_singleton_pow]
  have key : ∀ x : AdjoinRoot Φ, x ≠ 0 → ∃ (i : ℕ) (x' : AdjoinRoot Φ),
      x = c ^ i * x' ∧ x' ∉ baseIdeal O Φ := by
    intro x hx
    have hex : ∃ L, x ∉ (baseIdeal O Φ) ^ L := by
      by_contra h
      push Not at h
      exact hx (hsep x h)
    have hspec := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := fun h0 => hspec (by simp [h0])
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hmem : x ∈ (baseIdeal O Φ) ^ i := by
      simpa using Nat.find_min hex (show i < Nat.find hex by omega)
    rw [hIpow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨x', hx'⟩ := hmem
    refine ⟨i, x', by rw [← hx', mul_comm], fun hx'I => ?_⟩
    rw [hI, Ideal.mem_span_singleton'] at hx'I
    obtain ⟨d, hd⟩ := hx'I
    apply hspec
    rw [hi, hIpow, Ideal.mem_span_singleton']
    exact ⟨d, by rw [← hx', ← hd, pow_succ]; ring⟩
  have hnt : Nontrivial (AdjoinRoot Φ) := (baseReduce O Φ).domain_nontrivial
  have hnzd : NoZeroDivisors (AdjoinRoot Φ) := by
    constructor
    intro a b hab
    by_contra hne
    push Not at hne
    obtain ⟨i, a', rfl, ha'⟩ := key a hne.1
    obtain ⟨j, b', rfl, hb'⟩ := key b hne.2
    have h1 : algebraMap O (AdjoinRoot Φ) (ϖ ^ (i + j)) * (a' * b') = 0 := by
      rw [map_pow, ← hc, ← hab]; ring
    have h2 := htors _ (fun y hy => (mul_eq_zero.1 hy).resolve_left
      (pow_ne_zero _ hϖ.ne_zero)) _ h1
    have h3 : baseReduce O Φ a' * baseReduce O Φ b' = 0 := by
      rw [← map_mul, h2, map_zero]
    rcases mul_eq_zero.1 h3 with h | h
    · exact ha' (Ideal.Quotient.eq_zero_iff_mem.1 h)
    · exact hb' (Ideal.Quotient.eq_zero_iff_mem.1 h)
  exact NoZeroDivisors.to_isDomain _

/-! ### Conjugate products and descent of blocks -/

/-- For a block `b`, the product of the Frobenius conjugates of its monic polynomial is
Frobenius-invariant with coefficients in `O`, monic of degree `δ * r`, and reduces to
`∏ i, (X - θ̄ ^ (q ^ i)) ^ r`. -/
private theorem conjugate_product_invariant (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ)
    (b : Fin r → AdjoinRoot Φ) (hb : b ∈ blockCell O Φ r) :
    (conjugateProduct O Φ (monicPolyO b)).map (unramifiedFrobenius O Φ).toRingHom =
        conjugateProduct O Φ (monicPolyO b) ∧
      (∀ j, ∃ c : O,
        algebraMap O (AdjoinRoot Φ) c = (conjugateProduct O Φ (monicPolyO b)).coeff j) ∧
      (conjugateProduct O Φ (monicPolyO b)).Monic ∧
      (conjugateProduct O Φ (monicPolyO b)).natDegree = Φ.natDegree * r ∧
      (conjugateProduct O Φ (monicPolyO b)).map (baseReduce O Φ) =
        ∏ i : Fin Φ.natDegree, conjugateFactor O Φ i ^ r := by
  have := unramified_is_domain O Φ hΦ
  obtain ⟨hBm, hBd, -, -⟩ := monic_poly_reconstruct (AdjoinRoot Φ) r b
  set B := monicPolyO b
  set δ := Φ.natDegree
  have hid := (frobenius_pow_degree_eq_id O Φ hΦ).1
  have hcomp : ∀ a c : ℕ,
      frobeniusIter O Φ (a + c) = (frobeniusIter O Φ a).comp (frobeniusIter O Φ c) := by
    intro a c
    induction a with
    | zero => simp [frobeniusIter]
    | succ a ih =>
      rw [show a + 1 + c = (a + c) + 1 by omega]
      simp only [frobeniusIter, ih]
      rfl
  have hmul : ∀ m : ℕ, frobeniusIter O Φ (δ * m) = AlgHom.id O (AdjoinRoot Φ) := by
    intro m
    induction m with
    | zero => simp [frobeniusIter]
    | succ m ih => rw [Nat.mul_succ, hcomp, ih, hid]; rfl
  have hmod : ∀ n : ℕ, frobeniusIter O Φ n = frobeniusIter O Φ (n % δ) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n δ]
    rw [hcomp, hmul]; rfl
  have hP : ∀ i : Fin δ, (B.map (frobeniusIter O Φ i).toRingHom).Monic ∧
      (B.map (frobeniusIter O Φ i).toRingHom).natDegree = r := fun i =>
    ⟨hBm.map _, by rw [hBm.natDegree_map, hBd]⟩
  have hinv : (conjugateProduct O Φ B).map (unramifiedFrobenius O Φ).toRingHom =
      conjugateProduct O Φ B := by
    unfold conjugateProduct
    rw [Polynomial.map_prod]
    simp_rw [Polynomial.map_map]
    refine Fintype.prod_equiv (finRotate δ) _ _ (fun i => ?_)
    congr 1
    have hi := i.neZero
    rw [finRotate_apply, hmod ((i + 1 : Fin δ) : ℕ), Fin.val_add]
    have : (unramifiedFrobenius O Φ).toRingHom.comp (frobeniusIter O Φ i).toRingHom
        = (frobeniusIter O Φ ((i : ℕ) + 1)).toRingHom := rfl
    rw [this, hmod]
    congr 2
    simp [Nat.add_mod]
  refine ⟨hinv, fun j => ?_, Polynomial.monic_prod_of_monic _ _ (fun i _ => (hP i).1), ?_, ?_⟩
  · apply frobenius_fixed_ring O Φ hΦ
    simpa [Polynomial.coeff_map] using congrArg (fun p => Polynomial.coeff p j) hinv
  · unfold conjugateProduct
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => (hP i).1),
      Finset.sum_congr rfl (fun i _ => (hP i).2)]
    simp [mul_comm]
  · have hres := (frobenius_residue_action O Φ hΦ).2
    unfold conjugateProduct
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hle : baseIdeal O Φ ≤ (baseIdeal O Φ).comap (frobeniusIter O Φ i).toRingHom := by
      rw [← Ideal.map_le_iff_le_comap, baseIdeal, Ideal.map_map]
      apply le_of_eq
      congr 1
      exact RingHom.ext fun c => (frobeniusIter O Φ i).commutes c
    let g := Ideal.quotientMap (baseIdeal O Φ) (frobeniusIter O Φ i).toRingHom hle
    have hg : (baseReduce O Φ).comp (frobeniusIter O Φ i).toRingHom =
        g.comp (baseReduce O Φ) := by
      ext x <;> simp [g, Ideal.quotientMap_mk]
    rw [Polynomial.map_map, hg, ← Polynomial.map_map, hb, conjugateFactor, conjugateFactor,
      Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 3
    change g (baseReduce O Φ (AdjoinRoot.root Φ) ^ residueCard O ^ 0) = _
    rw [pow_zero, pow_one]
    simp only [g, Ideal.quotientMap_mk]
    exact hres i _

/-- The descent of a block lies in the residue cell of `residuePoly Φ ^ r`, and its monic
polynomial lifts to the conjugate product of the block. -/
theorem descend_block_mem_cell (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ) (b : Fin r → AdjoinRoot Φ)
    (hb : b ∈ blockCell O Φ r) :
    descendBlock O Φ r b ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r) ∧
      (monicPolyO (descendBlock O Φ r b)).map (AdjoinRoot.of Φ) =
        conjugateProduct O Φ (monicPolyO b) := by
  obtain ⟨_, hdesc, hPm, hPdeg, hPred⟩ := conjugate_product_invariant O Φ hΦ r b hb
  obtain ⟨hcompat, hinj, _, _, hfac, _⟩ := conjugate_roots_distinct O Φ hΦ
  obtain ⟨hFm, hFdeg, hFcoeff, _⟩ :=
    monic_poly_reconstruct O (Φ.natDegree * r) (descendBlock O Φ r b)
  set P := conjugateProduct O Φ (monicPolyO b)
  set F := monicPolyO (descendBlock O Φ r b)
  have hlift : F.map (AdjoinRoot.of Φ) = P := by
    ext j
    rw [Polynomial.coeff_map]
    by_cases hj : j < Φ.natDegree * r
    · rw [show F.coeff j = _ from hFcoeff ⟨j, hj⟩]
      change (AdjoinRoot.of Φ) (descendCoeff O Φ (P.coeff j)) = P.coeff j
      unfold descendCoeff
      rw [dif_pos (hdesc j)]
      exact Classical.choose_spec (hdesc j)
    · rcases (not_lt.mp hj).eq_or_lt with h | h
      · subst h
        have h1 : F.coeff (Φ.natDegree * r) = 1 := by
          have := hFm.coeff_natDegree; rwa [hFdeg] at this
        have h2 : P.coeff (Φ.natDegree * r) = 1 := by
          have := hPm.coeff_natDegree; rwa [hPdeg] at this
        rw [h1, h2, map_one]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hFdeg]; exact h),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hPdeg]; exact h), map_zero]
  refine ⟨?_, hlift⟩
  change F.map (IsLocalRing.residue O) = residuePoly O Φ ^ r
  apply Polynomial.map_injective _ hinj
  have hcomp : (residueEmbed O Φ).comp (IsLocalRing.residue O)
      = (baseReduce O Φ).comp (AdjoinRoot.of Φ) := by
    ext c; exact hcompat c
  rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, hlift, hPred, Polynomial.map_pow, hfac,
    Finset.prod_pow]

/-- For an unramified lift `Φ`, `O[X]/(Φ)` is a complete DVR with maximal ideal `𝔪 O[X]/(Φ)`, in
which every uniformizer of `O` stays a uniformizer, with finite residue field of cardinality
`q ^ deg Φ`. -/
theorem unramified_is_dvr (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    ∃ (_ : IsDomain (AdjoinRoot Φ)) (_ : IsLocalRing (AdjoinRoot Φ)),
      IsDiscreteValuationRing (AdjoinRoot Φ) ∧
      IsLocalRing.maximalIdeal (AdjoinRoot Φ) = baseIdeal O Φ ∧
      (∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O (AdjoinRoot Φ) ϖ)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (AdjoinRoot Φ)) (AdjoinRoot Φ) ∧
      Finite (IsLocalRing.ResidueField (AdjoinRoot Φ)) ∧
      Nat.card (IsLocalRing.ResidueField (AdjoinRoot Φ)) = residueCard O ^ Φ.natDegree := by
  have hdom : IsDomain (AdjoinRoot Φ) := unramified_is_domain O Φ hΦ
  obtain ⟨-, -, hloc, hmax⟩ := base_ideal_maximal_local O Φ hΦ
  obtain ⟨hcomp, -, htors⟩ := unramified_adic_complete O Φ hΦ.1
  obtain ⟨-, hfin, hcard⟩ := residue_extension_field O Φ hΦ
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible O
  -- the maximal ideal is generated by the image of any uniformizer
  have hspan : ∀ ϖ : O, Irreducible ϖ →
      IsLocalRing.maximalIdeal (AdjoinRoot Φ) = Ideal.span {algebraMap O (AdjoinRoot Φ) ϖ} := by
    intro ϖ hϖ
    rw [hmax, baseIdeal, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    rfl
  have hnf : ¬ IsField (AdjoinRoot Φ) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hspan ϖ₀ hϖ₀, Ideal.span_singleton_eq_bot]
    intro h
    exact one_ne_zero (htors ϖ₀ (fun y hy => (mul_eq_zero.1 hy).resolve_left hϖ₀.ne_zero) 1
      (by rw [h, zero_mul]))
  have hdvr : IsDiscreteValuationRing (AdjoinRoot Φ) := by
    have := (IsDiscreteValuationRing.TFAE (AdjoinRoot Φ) hnf).out 0 4
    exact this.2 ⟨⟨_, hspan ϖ₀ hϖ₀⟩⟩
  have e : IsLocalRing.ResidueField (AdjoinRoot Φ) ≃ residueExtension O Φ :=
    (Ideal.quotEquivOfEq hmax).toEquiv
  refine ⟨hdom, hloc, hdvr, hmax, fun ϖ hϖ =>
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (hspan ϖ hϖ), hmax ▸ hcomp,
    Finite.of_equiv _ e.symm, by rw [Nat.card_congr e, hcard]⟩

/-- Reducing modulo the maximal ideal of `O[X]/(Φ)` agrees with reducing modulo `𝔪 O[X]/(Φ)`. -/
private theorem map_residue_eq_map_baseReduce {O : Type} [CommRing O] [IsLocalRing O]
    {Φ : Polynomial O} [IsLocalRing (AdjoinRoot Φ)]
    (hmax : IsLocalRing.maximalIdeal (AdjoinRoot Φ) = baseIdeal O Φ)
    (P : Polynomial (AdjoinRoot Φ)) :
    P.map (IsLocalRing.residue (AdjoinRoot Φ)) =
      (P.map (baseReduce O Φ)).map (Ideal.quotEquivOfEq hmax.symm).toRingHom := by
  rw [Polynomial.map_map]
  rfl

private theorem map_residue_eq_of_map_baseReduce_eq {O : Type} [CommRing O] [IsLocalRing O]
    {Φ : Polynomial O} [IsLocalRing (AdjoinRoot Φ)]
    (hmax : IsLocalRing.maximalIdeal (AdjoinRoot Φ) = baseIdeal O Φ)
    {P Q : Polynomial (AdjoinRoot Φ)} (h : P.map (baseReduce O Φ) = Q.map (baseReduce O Φ)) :
    P.map (IsLocalRing.residue (AdjoinRoot Φ)) = Q.map (IsLocalRing.residue (AdjoinRoot Φ)) := by
  rw [map_residue_eq_map_baseReduce hmax, map_residue_eq_map_baseReduce hmax, h]

private theorem isCoprime_map_residue {O : Type} [CommRing O] [IsLocalRing O]
    {Φ : Polynomial O} [IsLocalRing (AdjoinRoot Φ)]
    (hmax : IsLocalRing.maximalIdeal (AdjoinRoot Φ) = baseIdeal O Φ)
    {P Q : Polynomial (AdjoinRoot Φ)}
    (h : IsCoprime (P.map (baseReduce O Φ)) (Q.map (baseReduce O Φ))) :
    IsCoprime (P.map (IsLocalRing.residue (AdjoinRoot Φ)))
      (Q.map (IsLocalRing.residue (AdjoinRoot Φ))) := by
  rw [map_residue_eq_map_baseReduce hmax, map_residue_eq_map_baseReduce hmax]
  exact h.map (Polynomial.mapRingHom (Ideal.quotEquivOfEq hmax.symm).toRingHom)

/-- Applying the `i`-th Frobenius iterate to a polynomial reducing to `(X - θ̄) ^ r` gives a
polynomial reducing to `(X - θ̄ ^ (q ^ i)) ^ r`. -/
private theorem map_frobeniusIter_baseReduce (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r i : ℕ) (B : Polynomial (AdjoinRoot Φ))
    (hB : B.map (baseReduce O Φ) = conjugateFactor O Φ 0 ^ r) :
    (B.map (frobeniusIter O Φ i).toRingHom).map (baseReduce O Φ) = conjugateFactor O Φ i ^ r := by
  obtain ⟨-, hinj, -, -, -, -⟩ := conjugate_roots_distinct O Φ hΦ
  have hfrob := (frobenius_residue_action O Φ hΦ).2
  let K := residueExtension O Φ
  let : Fintype (IsLocalRing.ResidueField O) := Fintype.ofFinite _
  obtain ⟨p, hpc⟩ := CharP.exists (IsLocalRing.ResidueField O)
  obtain ⟨n, hp, hq⟩ := FiniteField.card (IsLocalRing.ResidueField O) p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_injective_ringHom hinj p
  let fr : K →+* K := iterateFrobenius K p ((n : ℕ) * i)
  have hfr : ∀ x : K, fr x = x ^ (residueCard O ^ i) := fun x => by
    rw [residueCard, Nat.card_eq_fintype_card, hq, ← pow_mul]; rfl
  have hcomp' : (baseReduce O Φ).comp (frobeniusIter O Φ i).toRingHom =
      fr.comp (baseReduce O Φ) := RingHom.ext fun x => by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hfr, hfrob]
  rw [Polynomial.map_map, hcomp', ← Polynomial.map_map, hB, Polynomial.map_pow]
  simp [conjugateFactor, hfr]

/-- If monic polynomials `B i` over `O[X]/(Φ)` of degree `r`, with `B i` reducing to
`(X - θ̄ ^ (q ^ i)) ^ r`, multiply to the lift of `monicPolyO a`, then each `B i` is the `i`-th
Frobenius conjugate of `B 0`. -/
private theorem block_conjugates (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ) (a : Fin (Φ.natDegree * r) → O)
    (hδ : 0 < Φ.natDegree)
    (B : Fin Φ.natDegree → Polynomial (AdjoinRoot Φ)) (hB : ∀ i, (B i).Monic)
    (hBr : ∀ i, (B i).map (baseReduce O Φ) = conjugateFactor O Φ i ^ r)
    (hBp : ∏ i, B i = (monicPolyO a).map (AdjoinRoot.of Φ)) :
    ∀ i : Fin Φ.natDegree, B i = (B ⟨0, hδ⟩).map (frobeniusIter O Φ i).toRingHom := by
  intro i
  obtain ⟨_, _, -, hmax, -, hcomp, -, -⟩ := unramified_is_dvr O Φ hΦ
  have hcop := (conjugate_roots_distinct O Φ hΦ).2.2.2.2.2
  set τ := frobeniusIter O Φ (i : ℕ)
  set F' := (monicPolyO a).map (AdjoinRoot.of Φ) with hF'
  set D := (B ⟨0, hδ⟩).map τ.toRingHom with hD
  have hτF : F'.map τ.toRingHom = F' := by
    rw [hF', Polynomial.map_map]
    congr 1
    ext x
    simp [← AdjoinRoot.algebraMap_eq]
  have hDred : D.map (baseReduce O Φ) = conjugateFactor O Φ i ^ r :=
    map_frobeniusIter_baseReduce O Φ hΦ r i _ (hBr _)
  have hprod1 : B i * ∏ j ∈ Finset.univ.erase i, B j = F' := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i), hBp]
  have hprod2 : D * ∏ j ∈ Finset.univ.erase ⟨0, hδ⟩, (B j).map τ.toRingHom = F' := by
    rw [hD, Finset.mul_prod_erase (f := fun j => (B j).map τ.toRingHom) _ (Finset.mem_univ _),
      ← Polynomial.map_prod, hBp, hτF]
  have hc0 : IsCoprime ((B i).map (baseReduce O Φ))
      ((∏ j ∈ Finset.univ.erase i, B j).map (baseReduce O Φ)) := by
    rw [Polynomial.map_prod, hBr]
    exact IsCoprime.prod_right fun j hj => by
      rw [hBr]; exact (hcop i j (Finset.ne_of_mem_erase hj).symm).pow
  exact (hensel_factor_unique_of_dvd (AdjoinRoot Φ) _ _ _ _ (hB i)
    (Polynomial.monic_prod_of_monic _ _ fun j _ => hB j) ((hB _).map _)
    (Polynomial.monic_prod_of_monic _ _ fun j _ => (hB j).map _) (hprod1.trans hprod2.symm)
    (map_residue_eq_of_map_baseReduce_eq hmax (by rw [hBr, hDred]))
    (isCoprime_map_residue hmax hc0)).1

/-- Distinct Frobenius conjugates of the monic polynomial of a block are coprime over the
fraction field of `O[X]/(Φ)`. -/
theorem block_conjugates_coprime (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] (r : ℕ) (b : Fin r → AdjoinRoot Φ) (hb : b ∈ blockCell O Φ r) :
    ∀ i j : Fin Φ.natDegree, i ≠ j →
      IsCoprime (((monicPolyO b).map (frobeniusIter O Φ i).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))))
        (((monicPolyO b).map (frobeniusIter O Φ j).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) := by
  intro i j hij
  obtain ⟨_, _, hdvr, hmax, -, -, -, -⟩ := unramified_is_dvr O Φ hΦ
  have hBm : (monicPolyO b).Monic := (monic_poly_reconstruct (AdjoinRoot Φ) r b).1
  refine coprime_of_coprime_residue_dvr (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) _ _
    (hBm.map _) (hBm.map _) (isCoprime_map_residue hmax ?_)
  rw [map_frobeniusIter_baseReduce O Φ hΦ r i _ hb, map_frobeniusIter_baseReduce O Φ hΦ r j _ hb]
  exact ((conjugate_roots_distinct O Φ hΦ).2.2.2.2.2 i j hij).pow

/-- Hensel splitting: for `a` in the residue cell of `residuePoly Φ ^ r`, the lift of
`monicPolyO a` to `O[X]/(Φ)` factors uniquely as a product of monic polynomials `B i` of degree
`r` with `B i` reducing to `(X - θ̄ ^ (q ^ i)) ^ r`. -/
private theorem block_splitting (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ) (a : Fin (Φ.natDegree * r) → O)
    (ha : a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r)) :
    ∃! B : Fin Φ.natDegree → Polynomial (AdjoinRoot Φ), (∀ i, (B i).Monic) ∧
      (∀ i, (B i).natDegree = r) ∧
      (∀ i, (B i).map (baseReduce O Φ) = conjugateFactor O Φ i ^ r) ∧
      ∏ i, B i = (monicPolyO a).map (AdjoinRoot.of Φ) := by
  obtain ⟨_, _, _, hm, -, hcomp, -, -⟩ := unramified_is_dvr O Φ hΦ
  obtain ⟨hcompat, -, -, -, hfact, hcop⟩ := conjugate_roots_distinct O Φ hΦ
  obtain ⟨hFm, -, -, -⟩ := monic_poly_reconstruct O _ a
  set F := monicPolyO a
  let e : IsLocalRing.ResidueField (AdjoinRoot Φ) ≃+* residueExtension O Φ :=
    Ideal.quotEquivOfEq hm
  have hmapE : ∀ P : Polynomial (AdjoinRoot Φ),
      (P.map (IsLocalRing.residue _)).map (e : _ →+* _) = P.map (baseReduce O Φ) := fun P => by
    rw [Polynomial.map_map]; rfl
  have hinj : Function.Injective (Polynomial.map
      (e : IsLocalRing.ResidueField (AdjoinRoot Φ) →+* residueExtension O Φ)) :=
    Polynomial.map_injective _ e.injective
  have hNt : Nontrivial (residueExtension O Φ) := e.symm.toEquiv.nontrivial
  let g : Fin Φ.natDegree → Polynomial (residueExtension O Φ) := fun i => conjugateFactor O Φ i ^ r
  have hgm : ∀ i, (g i).Monic := fun i => (Polynomial.monic_X_sub_C _).pow r
  have hgc : ∀ i j, i ≠ j → IsCoprime (g i) (g j) := fun i j h => (hcop i j h).pow
  have hgd : ∀ i, (g i).natDegree = r := fun i => by
    simp only [g, conjugateFactor]
    rw [(Polynomial.monic_X_sub_C _).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hred : (F.map (AdjoinRoot.of Φ)).map (baseReduce O Φ) = ∏ i, g i := by
    have h1 : (baseReduce O Φ).comp (AdjoinRoot.of Φ) =
        (residueEmbed O Φ).comp (IsLocalRing.residue O) := by
      ext c; exact (hcompat c).symm
    rw [Polynomial.map_map, h1, ← Polynomial.map_map,
      show F.map (IsLocalRing.residue O) = residuePoly O Φ ^ r from ha, Polynomial.map_pow, hfact,
      ← Finset.prod_pow]
  have hsymm : ∀ P : Polynomial (residueExtension O Φ),
      (P.map (e.symm : residueExtension O Φ →+* IsLocalRing.ResidueField (AdjoinRoot Φ))).map
        (e : IsLocalRing.ResidueField (AdjoinRoot Φ) →+* residueExtension O Φ) = P := fun P => by
    simp [Polynomial.map_map]
  let g' : Fin Φ.natDegree → Polynomial (IsLocalRing.ResidueField (AdjoinRoot Φ)) :=
    fun i => (g i).map (e.symm : residueExtension O Φ →+* IsLocalRing.ResidueField (AdjoinRoot Φ))
  have hg'c : ∀ i j, i ≠ j → IsCoprime (g' i) (g' j) := fun i j h =>
    (hgc i j h).map (Polynomial.mapRingHom
      (e.symm : residueExtension O Φ →+* IsLocalRing.ResidueField (AdjoinRoot Φ)))
  have hred' : (F.map (AdjoinRoot.of Φ)).map (IsLocalRing.residue _) = ∏ i, g' i := by
    apply hinj
    simp only [hmapE, g', Polynomial.map_prod, hsymm, hred]
  obtain ⟨G, hGm, hGp, hGr, hGd⟩ := hensel_family_exists (AdjoinRoot Φ) (Fin Φ.natDegree)
    (F.map (AdjoinRoot.of Φ)) (hFm.map _) g' (fun i => (hgm i).map _) hg'c hred'
  refine ⟨G, ⟨hGm, fun i => ?_, fun i => ?_, hGp.symm⟩, ?_⟩
  · rw [hGd i, (hgm i).natDegree_map, hgd i]
  · rw [← hmapE, hGr i, hsymm]
  · rintro B ⟨hBm, -, hBr, hBp⟩
    have hBr' : ∀ i, (B i).map (IsLocalRing.residue _) = g' i := fun i => by
      apply hinj; rw [hmapE, hBr i, hsymm]
    exact hensel_family_unique (AdjoinRoot Φ) (Fin Φ.natDegree) B G hBm hGm
      (fun i => by rw [hBr' i, hGr i]) (fun i j h => by rw [hBr' i, hBr' j]; exact hg'c i j h)
      (by rw [hBp, hGp])

/-- `selectBlock` picks block `0` of the Hensel splitting of the lift of `monicPolyO a`, which is
the unique monic divisor of degree `r` reducing to `(X - θ̄) ^ r`. -/
private theorem selectBlock_spec (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (r : ℕ) (hδ : 0 < Φ.natDegree) (a : Fin (Φ.natDegree * r) → O)
    (ha : a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r)) :
    ∃ B : Fin Φ.natDegree → Polynomial (AdjoinRoot Φ), (∀ i, (B i).Monic) ∧
      (∀ i, (B i).natDegree = r) ∧
      (∀ i, (B i).map (baseReduce O Φ) = conjugateFactor O Φ i ^ r) ∧
      ∏ i, B i = (monicPolyO a).map (AdjoinRoot.of Φ) ∧
      (∀ B₀ : Polynomial (AdjoinRoot Φ), B₀.Monic → B₀.natDegree = r →
        B₀.map (baseReduce O Φ) = conjugateFactor O Φ 0 ^ r →
        B₀ ∣ (monicPolyO a).map (AdjoinRoot.of Φ) → B₀ = B ⟨0, hδ⟩) ∧
      selectBlock O Φ r a = coeffVec r (B ⟨0, hδ⟩) ∧
      monicPolyO (selectBlock O Φ r a) = B ⟨0, hδ⟩ := by
  obtain ⟨B, ⟨hBm, hBd, hBr, hBp⟩, -⟩ := block_splitting O Φ hΦ r a ha
  obtain ⟨_, _, _, hmax, -, hcomp, -, -⟩ := unramified_is_dvr O Φ hΦ
  set i0 : Fin Φ.natDegree := ⟨0, hδ⟩
  have huniq : ∀ B₀ : Polynomial (AdjoinRoot Φ), B₀.Monic → B₀.natDegree = r →
      B₀.map (baseReduce O Φ) = conjugateFactor O Φ 0 ^ r →
      B₀ ∣ (monicPolyO a).map (AdjoinRoot.of Φ) → B₀ = B i0 := by
    intro B₀ hB₀m hB₀d hB₀r hdvd
    obtain ⟨C₀, hC₀⟩ := hdvd
    have hC₀m : C₀.Monic := Polynomial.Monic.of_mul_monic_left hB₀m
      (hC₀ ▸ (monic_poly_reconstruct O _ a).1.map _)
    set C := ∏ j ∈ Finset.univ.erase i0, B j
    have hprod : B i0 * C = B₀ * C₀ := by
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ _), hBp, hC₀]
    have hcop := (conjugate_roots_distinct O Φ hΦ).2.2.2.2.2
    refine (hensel_factor_unique_of_dvd (AdjoinRoot Φ) (B i0) C B₀ C₀ (hBm i0)
      (Polynomial.monic_prod_of_monic _ _ (fun j _ => hBm j)) hB₀m hC₀m hprod
      (map_residue_eq_of_map_baseReduce_eq hmax (by rw [hBr, hB₀r]))
      (isCoprime_map_residue hmax ?_)).1.symm
    rw [Polynomial.map_prod]
    refine IsCoprime.prod_right (fun j hj => ?_)
    rw [hBr, hBr]
    exact (hcop i0 j (Finset.ne_of_mem_erase hj).symm).pow
  have hw : ∃ B₀ : Polynomial (AdjoinRoot Φ), B₀.Monic ∧ B₀.natDegree = r ∧
      B₀.map (baseReduce O Φ) = conjugateFactor O Φ 0 ^ r ∧
      B₀ ∣ (monicPolyO a).map (AdjoinRoot.of Φ) :=
    ⟨B i0, hBm i0, hBd i0, hBr i0, hBp ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ _)⟩
  have hs : selectBlock O Φ r a = coeffVec r (B i0) := by
    unfold selectBlock
    rw [dif_pos hw]
    obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec hw
    rw [huniq _ h1 h2 h3 h4]
  refine ⟨B, hBm, hBd, hBr, hBp, huniq, hs, ?_⟩
  rw [hs]
  exact (monic_poly_reconstruct _ r (coeffVec r (B i0))).2.2.2 _ (hBm i0) (hBd i0)

/-- Frobenius descent: `selectBlock` is a bijection from the residue cell of `residuePoly Φ ^ r`
over `O` onto the block cell over `O[X]/(Φ)`, with inverse `descendBlock`; the selected monic
polynomial divides the lift of `monicPolyO a`. -/
theorem block_descent_bijection (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (r : ℕ) :
    Set.BijOn (selectBlock O Φ r) (residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r))
      (blockCell O Φ r) ∧
    (∀ a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r),
      descendBlock O Φ r (selectBlock O Φ r a) = a) ∧
    (∀ b ∈ blockCell O Φ r, selectBlock O Φ r (descendBlock O Φ r b) = b) ∧
    (∀ a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r),
      (monicPolyO (selectBlock O Φ r a)).Monic ∧
        monicPolyO (selectBlock O Φ r a) ∣ (monicPolyO a).map (AdjoinRoot.of Φ)) := by
  obtain ⟨hdom, -, -, -, -, -, -, -⟩ := unramified_is_dvr O Φ hΦ
  have hδ := natDegree_pos_of_isUnramifiedLift hΦ
  have hinj : Function.Injective (algebraMap O (AdjoinRoot Φ)) := by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree hΦ.1.ne_zero]
    exact_mod_cast hδ.ne'
  have hdesc : ∀ c : O, descendCoeff O Φ (algebraMap O (AdjoinRoot Φ) c) = c := by
    intro c
    have h : ∃ c' : O, algebraMap O (AdjoinRoot Φ) c' = algebraMap O (AdjoinRoot Φ) c := ⟨c, rfl⟩
    unfold descendCoeff
    rw [dif_pos h]
    exact hinj (Classical.choose_spec h)
  have hleft : ∀ a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r),
      descendBlock O Φ r (selectBlock O Φ r a) = a := by
    intro a ha
    obtain ⟨B, hBm, hBd, hBr, hBp, -, -, hmp⟩ := selectBlock_spec O Φ hΦ r hδ a ha
    have hconj := block_conjugates O Φ hΦ r a hδ B hBm hBr hBp
    have hcp : conjugateProduct O Φ (monicPolyO (selectBlock O Φ r a)) =
        (monicPolyO a).map (AdjoinRoot.of Φ) := by
      rw [hmp, conjugateProduct, ← hBp]
      exact Finset.prod_congr rfl (fun i _ => (hconj i).symm)
    funext j
    unfold descendBlock
    rw [hcp, Polynomial.coeff_map, (monic_poly_reconstruct O _ a).2.2.1 j,
      ← AdjoinRoot.algebraMap_eq, hdesc]
  have hright : ∀ b ∈ blockCell O Φ r, selectBlock O Φ r (descendBlock O Φ r b) = b := by
    intro b hb
    obtain ⟨hcell, hF⟩ := descend_block_mem_cell O Φ hΦ r b hb
    obtain ⟨B, hBm, hBd, hBr, hBp, huniq, hs, -⟩ := selectBlock_spec O Φ hΦ r hδ _ hcell
    have hb' := monic_poly_reconstruct (AdjoinRoot Φ) r b
    have heq : monicPolyO b = B ⟨0, hδ⟩ := by
      refine huniq _ hb'.1 hb'.2.1 hb ?_
      rw [hF, conjugateProduct]
      have : monicPolyO b =
          (monicPolyO b).map (frobeniusIter O Φ ((⟨0, hδ⟩ : Fin _) : ℕ)).toRingHom :=
        Polynomial.map_id.symm
      conv_lhs => rw [this]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    rw [hs, ← heq]
    exact funext hb'.2.2.1
  refine ⟨⟨fun a ha => ?_, fun a ha a' ha' h => ?_, fun b hb => ?_⟩, hleft, hright, fun a ha => ?_⟩
  · obtain ⟨B, -, -, hBr, -, -, -, hmp⟩ := selectBlock_spec O Φ hΦ r hδ a ha
    change (monicPolyO (selectBlock O Φ r a)).map (baseReduce O Φ) = conjugateFactor O Φ 0 ^ r
    rw [hmp, hBr]
  · rw [← hleft a ha, ← hleft a' ha', h]
  · exact ⟨_, (descend_block_mem_cell O Φ hΦ r b hb).1, hright b hb⟩
  · obtain ⟨B, hBm, -, -, hBp, -, -, hmp⟩ := selectBlock_spec O Φ hΦ r hδ a ha
    rw [hmp]
    exact ⟨hBm _, hBp ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ _)⟩

/-- Frobenius descent preserves congruences: `a ≡ a' (mod 𝔪 ^ L)` coordinatewise if and only if
the selected blocks are congruent modulo `(𝔪 O[X]/(Φ)) ^ L`. -/
theorem block_descent_congruence_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (r : ℕ) (L : ℕ) (a a' : Fin (Φ.natDegree * r) → O)
    (ha : a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r))
    (ha' : a' ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r)) :
    (∀ j, a j - a' j ∈ (IsLocalRing.maximalIdeal O) ^ L) ↔
      ∀ j, selectBlock O Φ r a j - selectBlock O Φ r a' j ∈ (baseIdeal O Φ) ^ L := by
  obtain ⟨hdom, hloc, -, hmax, hirr, -, -, -⟩ := unramified_is_dvr O Φ hΦ
  have hδ := natDegree_pos_of_isUnramifiedLift hΦ
  obtain ⟨B, hBm, hBd, hBr, hBp, -, hs, -⟩ := selectBlock_spec O Φ hΦ r hδ a ha
  obtain ⟨B', hBm', hBd', hBr', hBp', -, hs', -⟩ := selectBlock_spec O Φ hΦ r hδ a' ha'
  rw [hs, hs']
  have hpure := base_ideal_pure O Φ hΦ.1 hδ L
  have hA := monic_poly_reconstruct O _ a
  have hA' := monic_poly_reconstruct O _ a'
  -- coefficientwise congruence of the lifted polynomials
  have hlift : (∀ j, a j - a' j ∈ (IsLocalRing.maximalIdeal O) ^ L) ↔
      ∀ j, ((monicPolyO a).map (AdjoinRoot.of Φ)).coeff j -
        ((monicPolyO a').map (AdjoinRoot.of Φ)).coeff j ∈ (baseIdeal O Φ) ^ L := by
    simp only [Polynomial.coeff_map, ← map_sub, ← AdjoinRoot.algebraMap_eq, hpure]
    refine ⟨fun h => (monic_coeff_sub_mem_iff _ _ _ _ hA.1 hA'.1 hA.2.1 hA'.2.1).1
      (fun j => by rw [hA.2.2.1, hA'.2.2.1]; exact h j), fun h j => ?_⟩
    simpa only [hA.2.2.1, hA'.2.2.1] using h j
  rw [hlift]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hspan : IsLocalRing.maximalIdeal (AdjoinRoot Φ) =
      Ideal.span {algebraMap O (AdjoinRoot Φ) ϖ} := by
    rw [hmax, baseIdeal, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      AdjoinRoot.algebraMap_eq]
  have hreg : ∀ x : AdjoinRoot Φ, algebraMap O (AdjoinRoot Φ) ϖ * x = 0 → x = 0 :=
    fun x hx => (mul_eq_zero.mp hx).resolve_left (hirr ϖ hϖ).ne_zero
  have hcop := (conjugate_roots_distinct O Φ hΦ).2.2.2.2.2
  constructor
  · intro h j
    have := hensel_family_unique_mod_pow (AdjoinRoot Φ) (Fin Φ.natDegree) _ hspan hreg B B' hBm
      hBm' (fun i => map_residue_eq_of_map_baseReduce_eq hmax (by rw [hBr, hBr']))
      (fun i j hij => isCoprime_map_residue hmax (by rw [hBr, hBr]; exact (hcop i j hij).pow)) L
      (by rw [hBp, hBp', hmax]; exact h) ⟨0, hδ⟩ j
    rwa [hmax] at this
  · intro h
    have h0 : ∀ j, (B ⟨0, hδ⟩).coeff j - (B' ⟨0, hδ⟩).coeff j ∈ (baseIdeal O Φ) ^ L :=
      (monic_coeff_sub_mem_iff _ _ _ _ (hBm _) (hBm' _) (hBd _) (hBd' _)).1 h
    have hconj := block_conjugates O Φ hΦ r a hδ B hBm hBr hBp
    have hconj' := block_conjugates O Φ hΦ r a' hδ B' hBm' hBr' hBp'
    have hJ : (baseIdeal O Φ) ^ L =
        ((IsLocalRing.maximalIdeal O) ^ L).map (algebraMap O (AdjoinRoot Φ)) := by
      rw [baseIdeal, Ideal.map_pow, AdjoinRoot.algebraMap_eq]
    have hall : ∀ i j, (B i).coeff j - (B' i).coeff j ∈ (baseIdeal O Φ) ^ L := by
      intro i j
      rw [hconj i, hconj' i, Polynomial.coeff_map, Polynomial.coeff_map, ← map_sub]
      have hm := Ideal.mem_map_of_mem (frobeniusIter O Φ i).toRingHom (h0 j)
      rw [hJ, Ideal.map_map] at hm
      rw [hJ]
      convert hm using 2
      exact ((frobeniusIter O Φ i).comp_algebraMap).symm
    have := (polynomial_congruence_and_product (AdjoinRoot Φ) ((baseIdeal O Φ) ^ L)).2
      (Fin Φ.natDegree) B B' hall
    rwa [hBp, hBp'] at this

end SurfaceBlowup
