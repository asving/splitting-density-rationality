/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Measure.AdicCylinders

/-!
# Adic congruences, adic perturbations and transport of cylinder measures

Let `I` be an ideal of `R` and `M` an `R`-module. Congruence modulo `I^j M` is an equivalence
relation, adic cylinders form a π-system, and perturbing by a map `r` that raises adic order
preserves and reflects these congruences. If `M` is `I`-adically complete, the adic perturbation
`x ↦ x + r x` is a bijection, is measurable for the adic cylinder
σ-algebra, and preserves every invariant probability measure with finite adic quotients. Also:
finite measures agreeing on adic cylinders are equal, and an invariant probability measure gives
each fibre of a surjection onto a finite group mass `1/|Q|`.

## Main results

* `SurfaceBlowup.adic_congruence_rules`, `SurfaceBlowup.adic_cylinders_intersection`,
  `SurfaceBlowup.adic_perturb_congruence_iff`
* `SurfaceBlowup.chart_image_measurable_chart_sigma`
* `SurfaceBlowup.adic_perturb_bijective`, `SurfaceBlowup.adic_perturb_measurable`,
  `SurfaceBlowup.adic_perturb_measure_preserving`
* `SurfaceBlowup.finite_measures_from_cylinders`
* `SurfaceBlowup.finite_quotient_fiber_mass`, `SurfaceBlowup.finite_quotient_event_mass`

Provenance: `Thm_SurfaceBlowupV2_{adic_congruence_rules, adic_cylinders_intersection,
adic_perturb_congruence_iff, chart_image_measurable_chart_sigma, digit_iter_successive,
digit_iter_cauchy, digit_iter_limit, digit_limit_solves, adic_perturb_bijective,
adic_perturb_cylinder_preimage, adic_perturb_measurable, finite_measures_from_cylinders,
finite_quotient_fiber_mass, adic_perturb_measure_preserving, finite_quotient_event_mass}` (moved
from `Blowup/Charts.lean` and `Blowup/CurveOrders.lean`).
-/

namespace SurfaceBlowup

open scoped ENNReal

/-! ### Adic congruences -/

/-- Congruence modulo `I^j M` is an equivalence relation, coarser for smaller `j`, and trivial
for `j = 0`. -/
theorem adic_congruence_rules (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    :
    (∀ j (x : M), adicCongr I j x x) ∧ (∀ j (x y : M), adicCongr I j x y → adicCongr I j y x) ∧
        (∀ j (x y z : M), adicCongr I j x y → adicCongr I j y z → adicCongr I j x z) ∧
        (∀ i j (x y : M), i ≤ j → adicCongr I j x y → adicCongr I i x y) ∧
        (∀ x y : M, adicCongr I 0 x y) := by
  unfold adicCongr
  exact ⟨fun _ _ => by simp, fun _ _ _ h => by simpa using neg_mem h,
    fun _ _ _ _ h1 h2 => by simpa using add_mem h1 h2,
    fun _ _ _ _ hij h => Submodule.smul_mono_left (Ideal.pow_le_pow_right hij) h, fun _ _ => by
        simp⟩

/-- Adic cylinders form a π-system. -/
theorem adic_cylinders_intersection (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    IsPiSystem (adicCylinders I M) := by
  have mono : ∀ i j : ℕ, i ≤ j → (I ^ j • ⊤ : Submodule R M) ≤ I ^ i • ⊤ :=
    fun i j h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  have key : ∀ (i j : ℕ) (x x' z : M), i ≤ j → adicCongr I i z x → adicCongr I j z x' →
      {y | adicCongr I i y x} ∩ {y | adicCongr I j y x'} = {y | adicCongr I j y z} := by
    intro i j x x' z hij hx hx'
    unfold adicCongr at *
    ext y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, h2⟩ => by simpa using sub_mem h2 hx',
      fun h => ⟨by simpa using add_mem (mono i j hij h) hx, by simpa using add_mem h hx'⟩⟩
  rintro s hs t ht ⟨z, hzs, hzt⟩
  rcases hs with rfl | ⟨i, x, rfl⟩
  · simp at hzs
  rcases ht with rfl | ⟨j, x', rfl⟩
  · simp at hzt
  right
  rcases le_total i j with h | h
  · exact ⟨j, z, key i j x x' z h hzs hzt⟩
  · refine ⟨i, z, ?_⟩
    rw [Set.inter_comm]
    exact key j i x' x z h hzt hzs

/-- Perturbing by a map that raises adic order preserves and reflects congruence modulo
`I^j M`. -/
theorem adic_perturb_congruence_iff (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (r : M → M) (hr : RaisesAdicOrder I r) (j : ℕ) (x y : M) :
    adicCongr I j (adicPerturb r x) (adicPerturb r y) ↔ adicCongr I j x y := by
  have mono : ∀ k, (I ^ (k+1) • ⊤ : Submodule R M) ≤ I ^ k • ⊤ := fun k =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ k))
  have eq : adicPerturb r x - adicPerturb r y = (x - y) + (r x - r y) := by
    simp only [adicPerturb]; abel
  constructor
  · intro h
    induction j with
    | zero => simp [adicCongr]
    | succ k ih =>
      have h' : adicCongr I k (adicPerturb r x) (adicPerturb r y) := mono k h
      have hk := hr k x y (ih h')
      unfold adicCongr at h hk ⊢
      rw [eq] at h
      simpa using sub_mem h hk
  · intro h
    have hk := mono j (hr j x y h)
    unfold adicCongr at h hk ⊢
    rw [eq]
    exact Submodule.add_mem _ h hk

/-- The image of a measurable set of coordinates under a division chart is measurable for
the chart σ-algebra on ideals. -/
theorem chart_image_measurable_chart_sigma (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    [MeasurableSpace O] (pi : O) (n : ℕ) (f : R) (b : Fin n → R)
    (hchart : IsDivisionChart O R pi f b) (S : Set (Fin n → O)) (hS : MeasurableSet S) :
    @MeasurableSet (Ideal R) (idealChartSigma O R pi) (coordinateIdeal pi f b '' S) :=
  MeasurableSpace.measurableSet_generateFrom ⟨n, f, b, S, hchart, hS, rfl⟩
/-! ### Adic perturbations and measures -/

/-- Successive digit iterates are congruent modulo `I^j M`. -/
private theorem digit_iter_successive (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (r : M → M) (hr : RaisesAdicOrder I r) (y : M) :
    ∀ j, adicCongr I j (digitIter r y (j+1)) (digitIter r y j) := by
  intro j
  induction j with
  | zero => simp [adicCongr]
  | succ n ih =>
    have h := hr n _ _ ih
    unfold adicCongr at h ⊢
    have e : digitIter r y (n + 1 + 1) - digitIter r y (n + 1)
        = -(r (digitIter r y (n + 1)) - r (digitIter r y n)) := by
      change (y - r (digitIter r y (n + 1))) - (y - r (digitIter r y n)) = _
      abel
    rw [e]
    exact neg_mem h

/-- The digit iterates form an `I`-adic Cauchy sequence. -/
private theorem digit_iter_cauchy (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (r : M → M) (hr : RaisesAdicOrder I r) (y : M) :
    ∀ i j, i ≤ j → adicCongr I i (digitIter r y i) (digitIter r y j) := by
  obtain ⟨hrefl, hsymm, htrans, hmono, -⟩ := adic_congruence_rules R M I
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact hrefl _ _
  | succ j hij ih =>
    exact htrans _ _ _ _ ih
      (hsymm _ _ _ (hmono _ _ _ _ hij
        (digit_iter_successive R M I r hr y j)))

/-- In an `I`-adically complete module the digit iterates converge. -/
private theorem digit_iter_limit (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (r : M → M) (hr : RaisesAdicOrder I r) [IsAdicComplete I M] (y : M) :
    ∃ x : M, ∀ j, adicCongr I j (digitIter r y j) x := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := M) (f := digitIter r y) inferInstance
    (fun {m n} hmn => SModEq.sub_mem.mpr
      (digit_iter_cauchy R M I r hr y m n hmn))
  exact ⟨L, fun j => SModEq.sub_mem.mp (hL j)⟩

/-- The limit of the digit iterates of `y` solves `x + r x = y`. -/
private theorem digit_limit_solves (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (r : M → M) (hr : RaisesAdicOrder I r) [IsAdicComplete I M] (y x : M)
    (hx : ∀ j, adicCongr I j (digitIter r y j) x) :
    adicPerturb r x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro j
  rw [SModEq.sub_mem]
  have hmono : (I ^ (j+1) • ⊤ : Submodule R M) ≤ I ^ j • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ j))
  have h1 := hmono (hx (j+1))
  have h2 := hmono (hr j _ _ (hx j))
  unfold adicCongr at *
  have key : adicPerturb r x - y
      = -((digitIter r y (j+1) - x) + (r (digitIter r y j) - r x)) := by
    simp only [adicPerturb, digitIter]; abel
  rw [key]
  exact neg_mem (add_mem h1 h2)

/-- On an `I`-adically complete module, `x ↦ x + r x` is bijective when `r` raises adic order. -/
theorem adic_perturb_bijective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (r : M → M) (hr : RaisesAdicOrder I r) [IsAdicComplete I M] :
    Function.Bijective (adicPerturb r) := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have h : ∀ j, adicCongr I j x y := fun j =>
      (adic_perturb_congruence_iff R M I r hr j x y).1 (by
        rw [hxy]; simp [adicCongr])
    exact sub_eq_zero.1 <| IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I) (M := M))
      (x - y) fun n => by rw [SModEq.sub_mem, sub_zero]; exact h n
  · obtain ⟨x, hx⟩ := digit_iter_limit R M I r hr y
    exact ⟨x, digit_limit_solves R M I r hr y x hx⟩

/-- The preimage of an adic cylinder under an adic perturbation is an adic cylinder. -/
private theorem adic_perturb_cylinder_preimage (R M : Type) [CommRing R] [AddCommGroup M]
    [Module R M]
    (I : Ideal R) (r : M → M) (hr : RaisesAdicOrder I r) [IsAdicComplete I M] (j : ℕ) (z : M) :
    ∃ x : M, adicPerturb r x = z ∧ (adicPerturb r) ⁻¹' {w | adicCongr I j w z} =
        {y | adicCongr I j y x} := by
  obtain ⟨x, hx⟩ := (adic_perturb_bijective R M I r hr).2 z
  refine ⟨x, hx, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [← hx]
  exact adic_perturb_congruence_iff R M I r hr j y x

/-- An adic perturbation is measurable for the adic cylinder σ-algebra. -/
theorem adic_perturb_measurable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (r : M → M) (hr : RaisesAdicOrder I r) [IsAdicComplete I M] [MeasurableSpace M]
    (hgen : ‹MeasurableSpace M› = adicCylinderSpace I M) :
    Measurable (adicPerturb r) := by
  subst hgen
  let : MeasurableSpace M := adicCylinderSpace I M
  apply measurable_generateFrom
  rintro s (rfl | ⟨j, z, rfl⟩)
  · simp
  · obtain ⟨x, -, hx⟩ :=
      adic_perturb_cylinder_preimage R M I r hr j z
    rw [hx]
    exact MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨j, x, rfl⟩)

/-- Two finite measures that agree on adic cylinders are equal, if the cylinders generate. -/
theorem finite_measures_from_cylinders (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) [MeasurableSpace M] (mu nu : MeasureTheory.Measure M)
    [MeasureTheory.IsFiniteMeasure mu] (hgen : ‹MeasurableSpace M› = adicCylinderSpace I M)
    (heq : ∀ j x, mu {y | adicCongr I j y x} = nu {y | adicCongr I j y x}) :
    mu = nu := by
  refine MeasureTheory.ext_of_generate_finite (adicCylinders I M) hgen
    (adic_cylinders_intersection R M I) ?_ ?_
  · rintro s (rfl | ⟨j, x, rfl⟩)
    · simp
    · exact heq j x
  · have h : {y : M | adicCongr I 0 y 0} = Set.univ := by ext; simp [adicCongr]
    exact h ▸ heq 0 0

/-- Under an invariant probability measure, each fibre of a surjection onto a finite group
has mass `1/|Q|`. -/
theorem finite_quotient_fiber_mass (G Q : Type) [AddCommGroup G] [AddCommGroup Q] [Finite Q]
    [MeasurableSpace G] [MeasurableAdd G] (mu : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure mu] [MeasureTheory.Measure.IsAddLeftInvariant mu]
    (pi : G →+ Q) (hpi : Function.Surjective pi) (hm : ∀ a, MeasurableSet {x | pi x = a}) (a : Q) :
    mu {x | pi x = a} = (Nat.card Q : ℝ≥0∞)⁻¹ := by
  have hfib : ∀ b, mu {x | pi x = b} = mu {x | pi x = a} := by
    intro b
    obtain ⟨t, ht⟩ := hpi (a - b)
    have : {x | pi x = b} = (fun h => t + h) ⁻¹' {x | pi x = a} := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_add, ht]
      constructor
      · intro h; rw [h]; abel
      · intro h
        have h2 : pi x = a - (a - b) := eq_sub_of_add_eq' h
        rw [h2]; abel
    rw [this, MeasureTheory.measure_preimage_add]
  have := Fintype.ofFinite Q
  have hU : (⋃ b : Q, {x | pi x = b}) = Set.univ := by
    ext x; simp
  have hsum : mu Set.univ = ∑ b : Q, mu {x | pi x = b} := by
    rw [← hU, MeasureTheory.measure_iUnion _ hm, tsum_fintype]
    intro i j hij
    exact Set.disjoint_left.mpr fun x hi hj => hij (hi.symm.trans hj)
  simp only [hfib, MeasureTheory.measure_univ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  rw [Nat.card_eq_fintype_card]
  have hpos : (Fintype.card Q : ℝ≥0∞) ≠ 0 := by simp
  rw [← one_mul (mu _), ← ENNReal.inv_mul_cancel hpos (by simp), mul_assoc, ← hsum, mul_one]

/-- An adic perturbation preserves an invariant probability measure with finite adic
quotients. -/
theorem adic_perturb_measure_preserving (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (r : M → M) (hr : RaisesAdicOrder I r) [IsAdicComplete I M] [MeasurableSpace M]
    [MeasurableAdd M] (mu : MeasureTheory.Measure M) [MeasureTheory.IsProbabilityMeasure mu]
    [MeasureTheory.Measure.IsAddLeftInvariant mu] (hgen : ‹MeasurableSpace M› = adicCylinderSpace I
    M) (hfinite : ∀ j, Finite (AdicQuotient I M j)) :
    MeasureTheory.MeasurePreserving (adicPerturb r) mu mu := by
  have hmeas : Measurable (adicPerturb r) :=
    adic_perturb_measurable R M I r hr hgen
  have hball : ∀ j (x : M), MeasurableSet {y | adicCongr I j y x} := by
    intro j x
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨j, x, rfl⟩)
  have hfib : ∀ j (x : M),
      {y | (adicReduce I j : M →ₗ[R] AdicQuotient I M j).toAddMonoidHom y
        = (adicReduce I j : M →ₗ[R] AdicQuotient I M j) x} = {y | adicCongr I j y x} := by
    intro j x
    ext y
    simp only [Set.mem_ofPred_eq, adicReduce, adicCongr, LinearMap.toAddMonoidHom_coe,
      Submodule.mkQ_apply]
    exact Submodule.Quotient.eq _
  have hmass : ∀ j (x : M), mu {y | adicCongr I j y x}
      = (Nat.card (AdicQuotient I M j) : ℝ≥0∞)⁻¹ := by
    intro j x
    have := hfinite j
    rw [← hfib j x]
    refine finite_quotient_fiber_mass M (AdicQuotient I M j) mu
      (adicReduce I j : M →ₗ[R] AdicQuotient I M j).toAddMonoidHom
      (Submodule.mkQ_surjective _) ?_ _
    intro a
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective (I ^ j • ⊤ : Submodule R M) a
    have := hfib j x'
    simp only [adicReduce] at this ⊢
    rw [this]
    exact hball j x'
  refine ⟨hmeas, finite_measures_from_cylinders R M I _ _ hgen fun j z => ?_⟩
  obtain ⟨x, -, hx⟩ := adic_perturb_cylinder_preimage R M I r hr j z
  rw [MeasureTheory.Measure.map_apply hmeas (hball j z), hx, hmass, hmass]

/-- Under an invariant probability measure, the preimage of `S ⊆ Q` under a surjection onto a
finite group has mass `|S|/|Q|`. -/
theorem finite_quotient_event_mass (G Q : Type) [AddCommGroup G] [AddCommGroup Q] [Finite Q]
    [MeasurableSpace G] [MeasurableAdd G] (mu : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure mu] [MeasureTheory.Measure.IsAddLeftInvariant mu]
    (pi : G →+ Q) (hpi : Function.Surjective pi) (hm : ∀ a, MeasurableSet {x | pi x = a})
    (S : Set Q) :
    mu (pi ⁻¹' S) = (Nat.card S : ℝ≥0∞) / Nat.card Q := by
  have hS : S.Finite := Set.toFinite S
  have hU : pi ⁻¹' S = ⋃ a ∈ hS.toFinset, {x | pi x = a} := by
    ext x; simp
  rw [hU, MeasureTheory.measure_biUnion_finset]
  · simp_rw [finite_quotient_fiber_mass G Q mu pi hpi hm]
    rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, Nat.card_eq_card_finite_toFinset hS]
  · intro a _ b _ hab
    exact Set.disjoint_left.mpr (fun x hx hy => hab (hx.symm.trans hy))
  · intro a _; exact hm a

end SurfaceBlowup
