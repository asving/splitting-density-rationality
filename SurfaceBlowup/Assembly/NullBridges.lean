/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Measure.Haar

/-!
# Strict-transform measures, type events and the projective null bridge

This file computes the Haar measure of preimages under the strict-transform chart maps of the
blow-up recursion: the scaled strict map multiplies measure by `q^(a n + k)` (`q` the residue
field cardinality), the child coordinate map by a further `q⁻¹^n`, and on the ball of radius
`|pi|^(s+a-1)` the net factor is `q⁻¹^(tri d)`. It then defines the coefficient-space type
events and the `RootCellLaw` interface consumed by the density assembly, and proves that the
original monic and projective densities agree with the route-F ones: the numerator events differ
only on the Haar-null inseparable locus (and `{a_n = 0}` in the projective case).

## Main results

* `SurfaceBlowup.strict_normalizer_preimage_measure`,
  `SurfaceBlowup.child_coordinate_preimage_measure`,
  `SurfaceBlowup.strict_chart_one_ball_measure`, `SurfaceBlowup.strict_transform_translate_measure`
* `SurfaceBlowup.RootCellLaw`, `SurfaceBlowup.typeEvent`, `SurfaceBlowup.binaryTypeEvent`,
  `SurfaceBlowup.affineTypeEvent`, `SurfaceBlowup.HasArray`, `SurfaceBlowup.arrayLaw`
* `SurfaceBlowup.orig_monicDensity_eq`, `SurfaceBlowup.orig_projectiveDensity_eq`

Provenance: `Thm_SurfaceBlowupV2_{strict_normalizer_preimage_measure,
child_coordinate_preimage_measure, strict_chart_one_ball_measure,
strict_transform_translate_measure}`,
`Def_SurfaceBlowupV2_{RootCellLaw, TypeEvents}`, `Thm_Gen_ProjBridge`.
-/

noncomputable section

namespace SurfaceBlowup

/-! ### Measures of strict-transform preimages -/

section StrictMeasures

open scoped BigOperators ENNReal

/-- The scaled strict map multiplies Haar measure by `q^(a n + k)`, where `q` is the residue
field cardinality and `k` the length of the cokernel of the normalizer's linear part. -/
theorem strict_normalizer_preimage_measure (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (H : (Fin n → O) →ₗ[O] R) (k : ℕ)
    (ha : k < a) (Q : (Fin n → O) →ₗ[O] (Fin n → O))
    (hQ : ∀ w, normalizationLinearPart E H (Q w) = (pi ^ k) • w)
    (hD : Function.Injective (normalizationLinearPart E H)) [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (hpi : Irreducible pi)
    (hk : Module.length O ((Fin n → O) ⧸ LinearMap.range (normalizationLinearPart E H)) = k)
    [IsAdicComplete (Ideal.span {pi}) (Fin n → O)] [TopologicalSpace (Fin n → O)]
    [IsTopologicalAddGroup (Fin n → O)] [CompactSpace (Fin n → O)] [T2Space (Fin n → O)]
    [MeasurableSpace (Fin n → O)] [BorelSpace (Fin n → O)] [MeasurableAdd (Fin n → O)]
    (hgen : ‹MeasurableSpace (Fin n → O)› = adicCylinderSpace (Ideal.span {pi}) (Fin n → O))
    (mu : MeasureTheory.Measure (Fin n → O)) [MeasureTheory.IsProbabilityMeasure mu]
    [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (hfinite : ∀ j, Finite (AdicQuotient (Ideal.span {pi}) (Fin n → O) j))
    (hcont : Continuous (fun z : Fin n → O => (pi^a) • normalizationLinearPart E H z))
    (T : Set (Fin n → O)) (hT : MeasurableSet T) :
    mu (scaledStrictMap pi a b E H ⁻¹' T) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)^(a*n + k) *
        mu (T ∩ Set.range (scaledStrictMap pi a b E H)) := by
  set D := normalizationLinearPart E H
  set L : (Fin n → O) →+ (Fin n → O) := ((pi^a) • D).toAddMonoidHom
  have hLm : Measurable (fun z : Fin n → O => (pi^a) • D z) := hcont.measurable
  have h1 : mu (scaledStrictMap pi a b E H ⁻¹' T) = mu (L ⁻¹' T) := by
    rw [← MeasureTheory.Measure.map_apply
        (scaled_strict_map_measurable O R n pi a b E H k ha Q hQ hgen hcont) hT,
      strict_normalizer_pushforward_linear O R n pi a b E H k ha Q hQ hgen mu hfinite hLm,
      MeasureTheory.Measure.map_apply hLm hT]
    rfl
  have hidx' : L.range.index = (Nat.card (IsLocalRing.ResidueField O))^(a*n + k) := by
    rw [show L.range = (LinearMap.range ((pi^a) • D)).toAddSubgroup by ext x; simp [L],
      scaled_linear_image_index O pi hpi n a k D hk]
  have : L.range.FiniteIndex := ⟨by rw [hidx']; exact pow_ne_zero _ Nat.card_pos.ne'⟩
  have : Finite ((Fin n → O) ⧸ L.range) := AddSubgroup.finite_quotient_of_finiteIndex
  have hinj : Function.Injective L := fun z w hzw =>
    hD (smul_right_injective (Fin n → O) (pow_ne_zero a hpi.ne_zero) hzw)
  have h2 := compact_injective_image_measure (Fin n → O) (Fin n → O) L hcont hinj mu mu
    (L ⁻¹' T)
  rw [Set.image_preimage_eq_inter_range, hidx'] at h2
  push_cast at h2
  have hRL : Set.range L = Set.range (scaledStrictMap pi a b E H) := by
    rw [strict_normalizer_lattice_image O R n pi a b E H k ha Q hQ]; rfl
  rw [h1, ← hRL, h2, ← mul_assoc, ENNReal.mul_inv_cancel, one_mul]
  · simp [Nat.card_pos.ne']
  · simp

/-- Membership in `(π)^j • M` means divisibility by `π^j`. -/
private theorem mem_span_pow_smul_top_iff {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (pi : O) (j : ℕ) (x : M) :
    x ∈ (Ideal.span {pi} ^ j • ⊤ : Submodule O M) ↔ ∃ y : M, pi ^ j • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- A set stable under translation by `pi^j M` is measurable for the adic cylinder σ-algebra. -/
private theorem measurableSet_of_adic_invariant {O M : Type} [CommRing O] [AddCommGroup M]
    [Module O M] [m : MeasurableSpace M] (pi : O)
    (hgen : m = adicCylinderSpace (Ideal.span {pi}) M) (j : ℕ)
    [Finite (AdicQuotient (Ideal.span {pi}) M j)] (S : Set M)
    (hS : ∀ x ∈ S, ∀ y, y - x ∈ (Ideal.span {pi} ^ j • ⊤ : Submodule O M) → y ∈ S) :
    MeasurableSet S := by
  set P := (Ideal.span {pi} ^ j • ⊤ : Submodule O M)
  have hSeq : S = ⋃ c ∈ (Submodule.Quotient.mk (p := P)) '' S,
      (Submodule.Quotient.mk (p := P)) ⁻¹' {c} := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
      exists_prop]
    refine ⟨fun hy => ⟨_, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
    rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
    exact hS x hx y ((Submodule.Quotient.eq P).1 h)
  rw [hSeq]
  refine MeasurableSet.biUnion (Set.to_countable _) ?_
  rintro _ ⟨x, -, rfl⟩
  have : (Submodule.Quotient.mk (p := P)) ⁻¹' {Submodule.Quotient.mk x} =
      {y | adicCongr (Ideal.span {pi}) j y x} := by
    ext y; simp [adicCongr, Submodule.Quotient.eq, P]
  rw [this, hgen]
  exact MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨j, x, rfl⟩)

/-- Multiplication by `π` maps the ball of radius `j` around `x` onto the ball of radius `j + 1`
around `π x`. -/
private theorem smul_image_adicCongr {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (pi : O) (j : ℕ) (x : M) :
    (fun w : M => pi • w) '' {y | adicCongr (Ideal.span {pi}) j y x}
      = {z | adicCongr (Ideal.span {pi}) (j+1) z (pi • x)} := by
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq, adicCongr, mem_span_pow_smul_top_iff]
  constructor
  · rintro ⟨y, ⟨w, hw⟩, rfl⟩
    exact ⟨w, by rw [pow_succ', mul_smul, hw, smul_sub]⟩
  · rintro ⟨w, hw⟩
    refine ⟨x + pi ^ j • w, ⟨w, by abel⟩, ?_⟩
    rw [smul_add, ← mul_smul, ← pow_succ', hw]
    abel

/-- Multiplication by `pi` (when injective) maps adic-measurable sets to measurable sets. -/
theorem measurableSet_smul_image {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (pi : O) [MeasurableSpace M]
    (hgen : ‹MeasurableSpace M› = adicCylinderSpace (Ideal.span {pi}) M)
    (hinj : Function.Injective (fun w : M => pi • w)) (S : Set M) (hS : MeasurableSet S) :
    MeasurableSet ((fun w : M => pi • w) '' S) := by
  have hcylm : ∀ j (x : M), MeasurableSet {z | adicCongr (Ideal.span {pi}) j z x} := by
    intro j x
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨j, x, rfl⟩)
  have huniv : MeasurableSet ((fun w : M => pi • w) '' Set.univ) := by
    have : (Set.univ : Set M) = {y | adicCongr (Ideal.span {pi}) 0 y 0} := by
      ext y; simp [adicCongr]
    rw [this, smul_image_adicCongr pi]
    exact hcylm _ _
  rw [hgen] at hS
  refine MeasurableSpace.generateFrom_induction _
    (fun S _ => MeasurableSet ((fun w : M => pi • w) '' S)) ?_ ?_ ?_ ?_ S hS
  · rintro t (rfl | ⟨j, x, rfl⟩) _
    · simp
    · rw [smul_image_adicCongr pi]; exact hcylm _ _
  · simp
  · intro t _ ht
    rw [Set.compl_eq_univ_sdiff, Set.image_sdiff hinj]
    exact huniv.diff ht
  · intro s _ hs
    rw [Set.image_iUnion]
    exact MeasurableSet.iUnion hs

/-- The child coordinate map multiplies Haar measure by `q^(a n + k) q⁻¹^n`. -/
theorem child_coordinate_preimage_measure (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    (H : (Fin n → O) →ₗ[O] R) [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (k : ℕ)
    (ha : k < a) (Q : (Fin n → O) →ₗ[O] (Fin n → O))
    (hQ : ∀ w, normalizationLinearPart E H (Q w) = (pi ^ k) • w)
    (hD : Function.Injective (normalizationLinearPart E H)) [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (hpi : Irreducible pi)
    (hk : Module.length O ((Fin n → O) ⧸ LinearMap.range (normalizationLinearPart E H)) = k)
    [IsAdicComplete (Ideal.span {pi}) (Fin n → O)] [TopologicalSpace (Fin n → O)]
    [IsTopologicalAddGroup (Fin n → O)] [CompactSpace (Fin n → O)] [T2Space (Fin n → O)]
    [MeasurableSpace (Fin n → O)] [BorelSpace (Fin n → O)] [MeasurableAdd (Fin n → O)]
    (hgen : ‹MeasurableSpace (Fin n → O)› = adicCylinderSpace (Ideal.span {pi}) (Fin n → O))
    (mu : MeasureTheory.Measure (Fin n → O)) [MeasureTheory.IsProbabilityMeasure mu]
    [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (hfinite : ∀ j, Finite (AdicQuotient (Ideal.span {pi}) (Fin n → O) j))
    (hcont : Continuous (fun z : Fin n → O => (pi^a) • normalizationLinearPart E H z))
    (hscale : ∀ (m : ℕ) (S : Set (Fin n → O)), MeasurableSet S →
      mu ((fun w : Fin n → O => (pi^m) • w) '' S) =
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(m*n) * mu S)
    (T : Set (Fin n → O)) (hT : MeasurableSet T) :
    mu (childCoordinateMap pi a b E H ⁻¹' T) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)^(a*n + k) *
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^n *
          mu (T ∩ Set.range (childCoordinateMap pi a b E H)) := by
  set s : (Fin n → O) → (Fin n → O) := fun w => pi • w with hs_def
  have hinj : Function.Injective s := smul_right_injective _ hpi.ne_zero
  obtain ⟨-, hrange, hpre⟩ := child_coordinate_map_scaled O R n pi a b E H (by omega) hinj
  have hsmeas : Measurable s := by
    have hm : @Measurable _ _ _ (adicCylinderSpace (Ideal.span {pi}) (Fin n → O)) s := by
      refine measurable_generateFrom ?_
      rintro t (rfl | ⟨j, x, rfl⟩)
      · simp
      · refine measurableSet_of_adic_invariant pi hgen j _ fun w hw y hy => ?_
        change pi • y - x ∈ (Ideal.span {pi} ^ j • ⊤ : Submodule O (Fin n → O))
        rw [show pi • y - x = (pi • w - x) + pi • (y - w) by rw [smul_sub]; abel]
        exact Submodule.add_mem _ hw (Submodule.smul_mem _ _ hy)
    rwa [← hgen] at hm
  have hrs : MeasurableSet (Set.range (scaledStrictMap pi a b E H)) := by
    rw [strict_normalizer_lattice_image O R n pi a b E H k ha Q hQ]
    refine measurableSet_of_adic_invariant pi hgen (a+k) _ ?_
    rintro _ ⟨u, rfl⟩ y hy
    obtain ⟨v, hv⟩ := (mem_span_pow_smul_top_iff pi (a+k) _).1 hy
    refine ⟨u + Q v, ?_⟩
    simp only [map_add, hQ, smul_add, smul_smul, ← pow_add, hv]
    abel
  have hrσ : MeasurableSet (Set.range (childCoordinateMap pi a b E H)) := by
    rw [← Set.preimage_image_eq (Set.range _) hinj, ← hrange]; exact hsmeas hrs
  rw [← hpre T, strict_normalizer_preimage_measure O R n pi a b E H k ha Q hQ hD hpi hk hgen mu
    hfinite hcont _ (measurableSet_smul_image pi hgen hinj T hT), hrange,
    ← Set.image_inter hinj]
  have h1 := hscale 1 _ (hT.inter hrσ)
  simp only [pow_one, one_mul] at h1
  rw [h1, mul_assoc]

/-- On the ball of radius `|pi|^(s+a-1)`, the child coordinate preimage of `T` has measure
`q⁻¹^(tri d)` times that of `T` inside the chart image. -/
theorem strict_chart_one_ball_measure (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    (H : (Fin n → O) →ₗ[O] R) [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (k : ℕ)
    (ha : k < a) (Q : (Fin n → O) →ₗ[O] (Fin n → O))
    (hQ : ∀ w, normalizationLinearPart E H (Q w) = (pi ^ k) • w)
    (hD : Function.Injective (normalizationLinearPart E H)) [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (hpi : Irreducible pi)
    (hk : Module.length O ((Fin n → O) ⧸ LinearMap.range (normalizationLinearPart E H)) = k)
    [IsAdicComplete (Ideal.span {pi}) (Fin n → O)] [TopologicalSpace (Fin n → O)]
    [IsTopologicalAddGroup (Fin n → O)] [CompactSpace (Fin n → O)] [T2Space (Fin n → O)]
    [MeasurableSpace (Fin n → O)] [BorelSpace (Fin n → O)] [MeasurableAdd (Fin n → O)]
    (hgen : ‹MeasurableSpace (Fin n → O)› = adicCylinderSpace (Ideal.span {pi}) (Fin n → O))
    (mu : MeasureTheory.Measure (Fin n → O)) [MeasureTheory.IsProbabilityMeasure mu]
    [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (hfinite : ∀ j, Finite (AdicQuotient (Ideal.span {pi}) (Fin n → O) j))
    (hcont : Continuous (fun z : Fin n → O => (pi^a) • normalizationLinearPart E H z))
    (hscale : ∀ (m : ℕ) (S : Set (Fin n → O)), MeasurableSet S →
      mu ((fun w : Fin n → O => (pi^m) • w) '' S) =
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(m*n) * mu S)
    (s d : ℕ) (htri : tri d ≤ s*n) (hkd : k = s*n - tri d) (T : Set (Fin n → O))
    (hT : MeasurableSet T) :
    mu (coordinateScale pi (s+a-1) '' (childCoordinateMap pi a b E H ⁻¹' T)) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(tri d) *
        mu (T ∩ Set.range (childCoordinateMap pi a b E H)) := by
  have hinj : Function.Injective (fun w : Fin n → O => pi • w) :=
    smul_right_injective _ hpi.ne_zero
  obtain ⟨_, _, hpre⟩ := child_coordinate_map_scaled O R n pi a b E H (by omega) hinj
  have hmeasS : MeasurableSet (childCoordinateMap pi a b E H ⁻¹' T) := by
    rw [← hpre]
    exact scaled_strict_map_measurable O R n pi a b E H k ha Q hQ hgen hcont
      (measurableSet_smul_image pi hgen hinj T hT)
  rw [← show (fun w : Fin n → O => pi^(s+a-1) • w) = coordinateScale pi (s+a-1) from rfl,
    hscale (s+a-1) _ hmeasS, child_coordinate_preimage_measure O R n pi a b E H k ha Q hQ hD hpi
      hk hgen mu hfinite hcont hscale T hT]
  set q : ℝ≥0∞ := (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)
  have hq0 : q ≠ 0 := by simp [q, Nat.card_pos.ne']
  have he : (s+a-1)*n + n = (a*n + k) + tri d := by
    rw [show (s+a-1)*n + n = (s+a-1+1)*n by ring, show s+a-1+1 = s+a by omega, add_mul]; omega
  have hcancel : q^(a*n+k) * q⁻¹^(a*n+k) = 1 := by
    rw [← ENNReal.inv_pow]
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  calc q⁻¹ ^ ((s + a - 1) * n) * (q ^ (a * n + k) * q⁻¹ ^ n *
          mu (T ∩ Set.range (childCoordinateMap pi a b E H)))
      = (q^(a*n+k) * q⁻¹^(a*n+k)) * q⁻¹^(tri d) *
          mu (T ∩ Set.range (childCoordinateMap pi a b E H)) := by
        rw [mul_assoc (q^(a*n+k)) (q⁻¹^(a*n+k)), ← pow_add, ← he, pow_add]; ring
    _ = _ := by rw [hcancel, one_mul]

/-- Translating the strict-transform chart computation: the preimage of a set of chart
coordinates under the strict transform on the ball of radius `|pi|^(s+a-1)` has measure
`q⁻¹^(tri d)` times that of its image under the coordinate ideal map. -/
theorem strict_transform_translate_measure (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (n : ℕ) (pi : O) (s a d : ℕ) (alpha : R →ₐ[O] C) (f : R)
    (g e c : C) (b : Fin n → R) (hf : alpha f = e ^ d * g)
    (hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (he : Function.Injective (fun z : C => e*z)) (ha : 0 < a)
    (hjac : algebraMap O C pi ∈ Ideal.jacobson (⊥ : Ideal C)) (bc : Fin n → C)
    (E : C ≃ₗ[O] ((Fin n → O) × C)) (hE : ∀ w, E.symm w = divisionMap g bc w)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × C)]
    (hΨ : Function.Injective (coordinateIdeal pi g bc)) (k : ℕ) (hk : k < a)
    (Q : (Fin n → O) →ₗ[O] (Fin n → O))
    (hQ : ∀ w, normalizationLinearPart E (pulledVariation alpha c b) (Q w) = (pi^k) • w)
    (hD : Function.Injective (normalizationLinearPart E (pulledVariation alpha c b)))
    [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    (hpiO : Irreducible pi)
    (hkl : Module.length O ((Fin n → O) ⧸
      LinearMap.range (normalizationLinearPart E (pulledVariation alpha c b))) = k)
    [IsAdicComplete (Ideal.span {pi}) (Fin n → O)] [TopologicalSpace (Fin n → O)]
    [IsTopologicalAddGroup (Fin n → O)] [CompactSpace (Fin n → O)] [T2Space (Fin n → O)]
    [MeasurableSpace (Fin n → O)] [BorelSpace (Fin n → O)] [MeasurableAdd (Fin n → O)]
    (hgen : ‹MeasurableSpace (Fin n → O)› = adicCylinderSpace (Ideal.span {pi}) (Fin n → O))
    (mu : MeasureTheory.Measure (Fin n → O)) [MeasureTheory.IsProbabilityMeasure mu]
    [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (hfinite : ∀ j, Finite (AdicQuotient (Ideal.span {pi}) (Fin n → O) j))
    (hcont : Continuous (fun z : Fin n → O =>
      (pi^a) • normalizationLinearPart E (pulledVariation alpha c b) z))
    (hscale : ∀ (m : ℕ) (S : Set (Fin n → O)), MeasurableSet S →
      mu ((fun w : Fin n → O => (pi^m) • w) '' S) =
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(m*n) * mu S)
    (htri : tri d ≤ s*n) (hkd : k = s*n - tri d) (T : Set (Fin n → O)) (hT : MeasurableSet T) :
    mu (coordinateIdeal pi f b ⁻¹' (strictTransformIdeal alpha e d ⁻¹'
        (coordinateIdeal pi g bc '' T)) ∩ Set.range (coordinateScale pi (s+a-1))) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(tri d) *
        mu (coordinateIdeal pi g bc ⁻¹' (coordinateIdeal pi g bc '' T ∩
          strictTransformIdeal alpha e d ''
            (coordinateIdeal pi f b '' Set.range (coordinateScale pi (s+a-1))))) := by
  have hcomm := strict_chart_coordinates_commute O R C n pi s a d alpha f g e c b hf hpi he ha
    hjac bc E hE
  have h3 : coordinateIdeal pi g bc ⁻¹' (coordinateIdeal pi g bc '' T ∩
      strictTransformIdeal alpha e d ''
        (coordinateIdeal pi f b '' Set.range (coordinateScale pi (s+a-1)))) =
      T ∩ Set.range (childCoordinateMap pi a bc E (pulledVariation alpha c b)) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨⟨x, hx, hxw⟩, y, ⟨u, ⟨z, rfl⟩, rfl⟩, hy⟩
      exact ⟨hΨ hxw ▸ hx, z, hΨ ((hcomm z).symm.trans hy)⟩
    · rintro ⟨hw, z, rfl⟩
      exact ⟨⟨_, hw, rfl⟩, _, ⟨_, ⟨z, rfl⟩, rfl⟩, hcomm z⟩
  rw [h3, strict_chart_preimage_set_identity O R C n pi s a d alpha f g e c b hf hpi he ha hjac bc
    E hE hΨ T]
  exact strict_chart_one_ball_measure O C n pi a bc E (pulledVariation alpha c b) k hk Q hQ hD
    hpiO hkl hgen mu hfinite hcont hscale s d htri hkd T hT

end StrictMeasures

/-! ### The root-cell law interface -/

section RootCell

open IsLocalRing MeasureTheory

/-- `RootCellLaw`: for every complete DVR `O` with finite residue field and a compact adic
Borel structure, every uniformizer `pi`, every `r ≥ 1` and every type `σ`, the event
`{z : Fin r → O | X^r + ∑ (pi z_i) X^i has type σ}` is measurable and has normalized
coefficient Haar mass `coeff_σ(stateLaw (S(1;r)))(q)`, `q = |k|`. It is the interface between the
measured recursion (which proves it) and the polynomial/projective assembly (which consumes it). -/
def RootCellLaw : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O],
    IsAdic (maximalIdeal O) → ∀ (pi : O), Irreducible pi → ∀ (r : ℕ), 0 < r → ∀ (σ : FactorType),
      MeasurableSet {z : Fin r → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} ∧
      coefficientMeasure O r {z : Fin r → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} =
        densityValue (lawCoeff (stateLaw (State.single 1 r)) σ) (Nat.card (ResidueField O))

end RootCell

/-! ### Type events -/

section TypeEvents

open Polynomial IsLocalRing
open scoped BigOperators

section
variable (O : Type) [CommRing O] [IsDomain O]
/-- The classical monic type event in degree `n`: coefficient vectors whose monic polynomial has
type `σ`. -/
def typeEvent (n : ℕ) (σ : FactorType) : Set (Fin n → O) :=
  {a | HasPolynomialTypeF O (monicPolynomial O a) σ}
/-- The primitive binary type event (the numerator event of `projectiveDensityF`). -/
def binaryTypeEvent (n : ℕ) (σ : FactorType) : Set (Fin (n+1) → O) :=
  {a | primitive O a ∧ HasBinaryTypeF O a σ}
/-- The affine-chart type event: the top coefficient is nonzero and the monic normalization of the
affine polynomial has classical type `σ`. -/
def affineTypeEvent (n : ℕ) (σ : FactorType) : Set (Fin (n+1) → O) :=
  {a | a (Fin.last n) ≠ 0 ∧ HasPolynomialTypeF O
    (C (algebraMap O (BaseField O) (a (Fin.last n)))⁻¹ * affinePolynomial O a) σ}
/-- The repeated-root event of `RootCellLaw`: `z` with `X^r + ∑ (pi z_i) X^i` of type `σ`. -/
def rootEvent (pi : O) (r : ℕ) (σ : FactorType) : Set (Fin r → O) :=
  {z | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ}
/-- The infinity block event in reduced coordinates: for the reversed block
`R_b = 1 + ∑ b_j X^(j+1)` (the dehomogenization of the normalized form `insertOne 0 b`), the top
coefficient `b_(r-1)` is nonzero and the monic normalization of `R_b` has type `σ`. -/
def infinityBlockEvent (r : ℕ) (σ : FactorType) : Set (Fin r → O) :=
  {b | (formPoly (insertOne (0 : Fin (r+1)) b)).coeff r ≠ 0 ∧ HasPolynomialTypeF O
    (C (algebraMap O (BaseField O) ((formPoly (insertOne (0 : Fin (r+1)) b)).coeff r))⁻¹ *
      (formPoly (insertOne (0 : Fin (r+1)) b)).map (algebraMap O (BaseField O))) σ}
end

section
variable (O : Type) [CommRing O] [IsLocalRing O] (Φ : Polynomial O)
/-- The point chart of a nonrational point: select the block above `θ̄` and translate it to the
`X^r` cell over `O_δ`. -/
def pointChart (r : ℕ) (a : Fin (Φ.natDegree * r) → O) : Fin r → AdjoinRoot Φ :=
  translateBlock O Φ r (selectBlock O Φ r a)
end

section
variable (k : Type) [Field k]
/-- `HasArray k n D m`: the divisor `D` has exactly `m (δ-1, r-1)` closed points of degree `δ`
and multiplicity `r`, for all `1 ≤ δ, r ≤ n`; infinity is counted like every other point. -/
def HasArray (n : ℕ) (D : ExceptionalDivisor k) (m : Pattern n) : Prop :=
  ∀ ij : Fin n × Fin n,
    Nat.card {Q : ClosedDirection k // directionDegree k Q = ij.1.val + 1 ∧ D Q = ij.2.val + 1} =
      (m ij).val
/-- An affine divisor of degree `n`: no multiplicity at infinity and total degree `n`. -/
def AffineDivisor (n : ℕ) (D : ExceptionalDivisor k) : Prop :=
  D (infinityDirection k) = 0 ∧ exceptionalDegree k D = n
/-- The residue vector of a divisor in degree `n`: the coefficients of its affine polynomial, read
as a binary form of degree `n` (the multiplicity at infinity is `n - natDegree`). -/
def divisorVector (n : ℕ) (D : ExceptionalDivisor k) : Fin (n+1) → k :=
  fun i => (divisorAffinePolynomial k D).coeff i
end

/-- The law attached to an array: the product over its points of the descended repeated-root laws
`T_δ B_r` — the inner factor of `globalLaw`. -/
def arrayLaw {n : ℕ} (m : Pattern n) : Law :=
  lawProd ((otherChildren 1 m).map fun z => lawDescend z.1 (stateLaw z.2))

end TypeEvents

/-! ### The projective null bridge -/

section ProjBridge

open MeasureTheory Polynomial
open scoped BigOperators ENNReal

variable (O : Type) [CommRing O] [IsDomain O]

omit [IsDomain O] in
private theorem affine_natDegree {n : ℕ} (a : Fin (n + 1) → O) (ha : a (Fin.last n) ≠ 0) :
    (affinePolynomial O a).natDegree = n := by
  have hc : (affinePolynomial O a).coeff n = algebraMap O (BaseField O) (a (Fin.last n)) := by
    simp only [affinePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp
    · exact fun i _ hi => if_neg fun h => hi (Fin.ext (by simp [h]))
    · simp
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 i.2)
  · rw [hc]
    exact fun h => ha (IsFractionRing.injective O (BaseField O) (by rw [h, map_zero]))

omit [IsDomain O] in
private theorem affine_snoc_eq {n : ℕ} (a : Fin n → O) :
    affinePolynomial O (Fin.snoc (α := fun _ => O) a 1) = monicPolynomial O a := by
  simp [affinePolynomial, monicPolynomial, Fin.sum_univ_castSucc, add_comm]

variable [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]

private theorem affine_bad_null (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    coefficientMeasure O (n+1) ({a : Fin (n+1) → O | a (Fin.last n) = 0} ∪
      {a | MvPolynomial.eval a (MvPolynomial.map (Int.castRingHom O) (discAffine n)) = 0}) = 0 := by
  refine measure_union_null (coordinate_hyperplane_null O htop (n+1) (Fin.last n)).2 ?_
  obtain ⟨a₀, h₀⟩ := exists_separable_monic O n
  refine coefficientMeasure_zero_null O htop (n+1) _ (Fin.snoc (α := fun _ => O) a₀ 1) ?_
  have hdeg := monic_polynomial_degree O n a₀
  have := resultant_ne_zero_of_separable (monicPolynomial O a₀) n hdeg.2 hdeg.1.ne_zero h₀
  rw [← affine_snoc_eq, affine_resultant_eq] at this
  exact fun h => this (by rw [h, map_zero])

/-- The original monic density equals the separable-type monic density: the two events agree
off the Haar-null inseparable locus. -/
theorem orig_monicDensity_eq (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    monicDensity O n σ = monicDensityF O n σ :=
  measure_congr <| (measure_eq_zero_iff_ae_notMem.1 (monic_inseparable_null O htop n)).mono
    fun _ ha => propext (hasPolynomialTypeF_iff_of_separable O (not_not.1 ha)).symm

/-- The original projective density equals the route-F one: the two numerator events differ
only inside `{a_n = 0} ∪ {disc = 0}`, which is Haar-null. -/
theorem orig_projectiveDensity_eq (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (σ : FactorType) :
    SurfaceBlowup.projectiveDensity O n σ = projectiveDensityF O n σ := by
  refine congrArg (· / _) <| measure_congr <|
    (measure_eq_zero_iff_ae_notMem.1 (affine_bad_null O htop n)).mono fun a ha => ?_
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at ha
  refine propext <| and_congr_right fun _ => and_congr_right fun h1 => and_congr_right fun _ =>
    and_congr_right fun _ => exists_congr fun _ => and_congr_left fun _ => Iff.symm <|
      hasPolynomialTypeF_iff_of_separable O <| Separable.unit_mul
        (isUnit_C.2 <| isUnit_iff_ne_zero.2 (inv_ne_zero (leadingCoeff_ne_zero.2 h1))) <|
      separable_of_resultant _ n (affine_natDegree O a ha.1) h1 ?_
  rw [affine_resultant_eq]
  exact fun h => ha.2 (IsFractionRing.injective O (BaseField O) (by rw [h, map_zero]))

end ProjBridge

end SurfaceBlowup
