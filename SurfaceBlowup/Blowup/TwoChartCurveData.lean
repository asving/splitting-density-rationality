/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.CurveSections

/-!
# Two-chart curve data

Two-chart curve data records a curve on the blow-up of a regular parameter pair `(t, x)` through
finitely many points of the two charts and of their overlap, with local equations and completed
local isomorphisms. This file compares the level kernels of the two charts on the overlap, builds
glued generators from such data, identifies the quotients of curve sections and the curve order
limit with products of local level quotients (hence with the child order), and computes the
cokernel of the twisted Čech differential in the negative range.

## Main results

* `SurfaceBlowup.two_chart_kernels_agree_on_overlap`: both chart kernels extend to the common
  kernel.
* `SurfaceBlowup.curve_sections_quot_equiv_product`,
  `SurfaceBlowup.curve_limit_equiv_product_threads`: local descriptions of curve sections and of the
  curve order limit.
* `SurfaceBlowup.child_order_equiv_linear`: the curve order limit is linearly isomorphic to the
  child order.
* `SurfaceBlowup.glued_generators_of_two_chart_curve_data`: glued generators from two-chart data.
* `SurfaceBlowup.actual_negative_layer_coker_exact`: the cokernel tower in the negative range.

Provenance: `Thm_SurfaceBlowupV2_{two_chart_kernels_agree_on_overlap,
two_chart_level_generators_agree_on_overlap, two_chart_right_points_maximal,
curve_sections_quot_equiv_product, curve_limit_equiv_product_threads, child_order_equiv_linear,
glued_generators_of_two_chart_curve_data, strict_transform_right_point_equation,
global_function_strict_transform_at_right_point, two_chart_left_generators_regular_on_overlap,
two_chart_level_generators_exist, two_term_coker_map_representative,
actual_negative_layer_coker_exact, two_term_coker_map_surjective}`.
-/

namespace SurfaceBlowup

/-! ### Comparing the charts on the overlap -/

private theorem map_inf_eq_of_isUnit_pow_mem {A S : Type} [CommRing A] [CommRing S] (f : A →+* S)
    (I K : Ideal A) (m : A) (N : ℕ) (hm : IsUnit (f m)) (hK : m ^ N ∈ K) :
    (I ⊓ K).map f = I.map f := by
  refine le_antisymm (Ideal.map_mono inf_le_left) ?_
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap]
  have h1 : m ^ N * a ∈ I ⊓ K := ⟨I.mul_mem_left _ ha, K.mul_mem_right _ hK⟩
  have h2 := Ideal.mem_map_of_mem f h1
  obtain ⟨u, hu⟩ := hm.pow N
  have : f a = ↑u⁻¹ * f (m ^ N * a) := by
    rw [map_mul, map_pow, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h2

private theorem exists_pow_mem_iInf {A : Type} [CommRing A] {κ : Type} [Finite κ]
    (J : κ → Ideal A) (m : A) (L : κ → ℕ) (hL : ∀ k, m ^ L k ∈ J k) :
    ∃ N, m ^ N ∈ ⨅ k, J k := by
  have := Fintype.ofFinite κ
  refine ⟨∑ k, L k, ?_⟩
  rw [Ideal.mem_iInf]
  intro k
  exact (J k).pow_mem_of_pow_mem (hL k)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))

private theorem leftLevelIdeal_map_leftIso_symm {R : Type} [CommRing R] {t x : R}
    {beta : BlowupRestriction R t x} (D : TwoChartCurveData R t x beta) (j : ℕ) (i : D.ι) :
    (finiteLocalCurveIdeal (BlowupChart R t x)
      ((D.Q i).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)))
      (chartBase R t x t) (D.leftIso i (D.g i)) j).map (D.leftIso i).symm =
      commonLevelIdeal D j i := by
  unfold commonLevelIdeal finiteLocalCurveIdeal
  rw [Ideal.map_span, Set.image_pair, RingEquiv.symm_apply_apply, map_pow,
    (RingEquiv.symm_apply_eq _).2 (D.leftIso_compat i (chartBase R t x t)).symm]
  rfl

private theorem rightLevelIdeal_map_rightIso_symm {R : Type} [CommRing R] {t x : R}
    {beta : BlowupRestriction R t x} (D : TwoChartCurveData R t x beta) (j : ℕ) (i : D.ι) :
    (finiteLocalCurveIdeal (BlowupChart R x t) ((D.Q i).comap beta.right.toRingHom)
      (chartBase R x t x) (D.rightIso i (D.g i)) j).map (D.rightIso i).symm =
      commonLevelIdeal D j i := by
  have hZ : IsUnit (overlapSlope R t x) := IsLocalization.Away.algebraMap_isUnit _
  unfold commonLevelIdeal finiteLocalCurveIdeal
  rw [Ideal.map_span, Set.image_pair, RingEquiv.symm_apply_apply, map_pow,
    (RingEquiv.symm_apply_eq _).2 (D.rightIso_compat i (chartBase R x t x)).symm,
    beta_right_chartBase_self, map_mul, mul_pow, Ideal.span_insert, Ideal.span_insert,
    Ideal.span_singleton_mul_right_unit ((hZ.map _).pow _)]

/-- Localizing away from `m` sends the kernel of finitely many local level ideals onto the kernel
of the transported ideals at the surviving points, provided `m` lies in every collapsing point. -/
private theorem finiteSupportKernel_map_away {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (m : A) [IsLocalization.Away m S] {ι κ : Type} [Finite ι] [Finite κ] (P : ι ⊕ κ → Ideal A)
    [∀ s, (P s).IsPrime] (J : ∀ s, Ideal (CompletedLocalAt A (P s))) (Q : ι → Ideal S)
    [∀ i, (Q i).IsPrime] (J' : ∀ i, Ideal (CompletedLocalAt S (Q i)))
    (Φ : ∀ i, CompletedLocalAt A (P (Sum.inl i)) ≃+* CompletedLocalAt S (Q i))
    (hΦ : ∀ i a, Φ i (completedPointMap A (P (Sum.inl i)) a) =
      completedPointMap S (Q i) (algebraMap A S a))
    (hJ : ∀ i, (J (Sum.inl i)).map (Φ i) = J' i) (hm : ∀ k, m ∈ P (Sum.inr k))
    (hmax : ∀ s, (P s).IsMaximal) (hJL : ∀ s, ∃ L : ℕ,
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (P s))).map
        (localCompletionMap (Localization.AtPrime (P s)))) ^ L ≤ J s) :
    (finiteSupportKernel A (ι ⊕ κ) P J).map (algebraMap A S) = finiteSupportKernel S ι Q J' := by
  choose L hL' using hJL
  have hL : ∀ s, P s ^ L s ≤ (J s).comap (completedPointMap A (P s)) := fun s =>
    have := hmax s
    completed_point_power_contraction _ _ _ _ (hL' s)
  obtain ⟨N, hN⟩ := exists_pow_mem_iInf
    (fun k => (J (Sum.inr k)).comap (completedPointMap A (P (Sum.inr k)))) m
    (fun k => L (Sum.inr k)) (fun k => hL (Sum.inr k) (Ideal.pow_mem_pow (hm k) _))
  unfold finiteSupportKernel
  rw [iInf_sum, map_inf_eq_of_isUnit_pow_mem _ _ _ m N
    (IsLocalization.Away.algebraMap_isUnit _) hN]
  have key := finite_support_kernel_localize A S (Submonoid.powers m) ι (fun i => P (Sum.inl i))
    (fun i => J (Sum.inl i)) (fun _ => True) (fun i => CompletedLocalAt S (Q i))
    (fun i => completedPointMap S (Q i)) Φ (fun i _ a => hΦ i a) (fun i h => absurd trivial h)
    (fun i => L (Sum.inl i)) (fun i => hL (Sum.inl i))
  unfold finiteSupportKernel at key
  rw [key]
  refine le_antisymm (le_iInf fun i => ?_) (le_iInf fun i => ?_)
  · exact (iInf_le _ ⟨i, trivial⟩).trans (by rw [hJ])
  · exact (iInf_le _ i.val).trans (by rw [hJ])

/-- The level-`j` kernels of the two charts both extend to the common level-`j` kernel on the
overlap. -/
theorem two_chart_kernels_agree_on_overlap (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (j : ℕ) :
    (leftKernel D j).map (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) = commonKernel D j ∧
      (rightKernel D j).map beta.right.toRingHom = commonKernel D j := by
  constructor
  · exact finiteSupportKernel_map_away (chartSlope R t x) (leftPoint D) (leftLevelIdeal D j) D.Q
      (commonLevelIdeal D j) (fun i => (D.leftIso i).symm)
      (fun i a => (RingEquiv.symm_apply_eq _).2 (D.leftIso_compat i a).symm)
      (leftLevelIdeal_map_leftIso_symm D j) D.slope0 (two_chart_left_points_maximal R t x beta D).1
      (two_chart_left_data_transverse_finite R t x beta D j).2
  · let _ : Algebra (BlowupChart R x t) (BlowupOverlap R t x) := beta.right.toRingHom.toAlgebra
    have := blowup_overlap_isLocalization_right R t x beta
    exact finiteSupportKernel_map_away (chartSlope R x t) (rightPoint D) (rightLevelIdeal D j) D.Q
      (commonLevelIdeal D j) (fun i => (D.rightIso i).symm)
      (fun i a => (RingEquiv.symm_apply_eq _).2 (D.rightIso_compat i a).symm)
      (rightLevelIdeal_map_rightIso_symm D j) D.slopeinf
      (fun s => match s with
        | Sum.inl i =>
          (overlap_exceptional_point_comap_maximal_right R t x beta (D.Q i) (D.onE i)).1
        | Sum.inr l => D.maximalinf l)
      (two_chart_right_data_transverse_finite R t x beta D j).2

private theorem span_mk_map_eq_map_map {A C : Type} [CommRing A] [CommRing C] (f : A →+* C) (a : A)
    (c : C)
    (h : f a ∈ Ideal.span {c}) (j : ℕ) (K : Ideal A) (F : A)
    (hF : K.map (Ideal.Quotient.mk ((Ideal.span {a}) ^ j)) =
      Ideal.span {Ideal.Quotient.mk ((Ideal.span {a})^j) F}) :
    Ideal.span {Ideal.Quotient.mk ((Ideal.span {c})^j) (f F)}
      = (K.map f).map (Ideal.Quotient.mk ((Ideal.span {c})^j)) := by
  have cond : ∀ z ∈ (Ideal.span {a})^j,
      ((Ideal.Quotient.mk ((Ideal.span {c})^j)).comp f) z = 0 := by
    intro z hz
    simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    have h1 : f z ∈ ((Ideal.span {a})^j).map f := Ideal.mem_map_of_mem f hz
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h1
    exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).2 h) j h1
  let φ := Ideal.Quotient.lift ((Ideal.span {a})^j)
    ((Ideal.Quotient.mk ((Ideal.span {c})^j)).comp f) cond
  have hφ : ∀ z, φ (Ideal.Quotient.mk ((Ideal.span {a})^j) z) =
      Ideal.Quotient.mk ((Ideal.span {c})^j) (f z) := fun z => rfl
  have := congrArg (Ideal.map φ) hF
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, hφ] at this
  rw [← this, Ideal.map_map]
  rfl

/-- Generators of the level-`j` kernels of the two charts generate the same ideal on the overlap
modulo the `j`-th power of the exceptional ideal. -/
theorem two_chart_level_generators_agree_on_overlap (R : Type) [CommRing R] (t x : R) (beta :
    BlowupRestriction R t x) (D : TwoChartCurveData R t x beta)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (FA : ℕ → BlowupChart R t x) (hFA : ∀ j : ℕ,
    leftLevelKernel D j =
    Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R t x t})^j) (FA j)}) (FB : ℕ →
    BlowupChart R x t) (hFB : ∀ j : ℕ, rightLevelKernel D j =
    Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R x t x})^j) (FB j)}) (j : ℕ) :
    Ideal.span {Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (FA j))} =
      Ideal.span {Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
        (beta.right (FB j))} := by
  obtain ⟨h1, h2⟩ := two_chart_kernels_agree_on_overlap R t x beta D j
  have e1 := span_mk_map_eq_map_map (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))
    (chartBase R t x t) (overlapException R t x) (by simp [overlapException]) j (leftKernel D j)
    (FA j)
    (by rw [← hFA j]; rfl)
  have hx : beta.right.toRingHom (chartBase R x t x) ∈ Ideal.span {overlapException R t x} := by
    change beta.right _ ∈ _
    rw [beta_right_chartBase_self]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have e2 := span_mk_map_eq_map_map beta.right.toRingHom (chartBase R x t x)
    (overlapException R t x) hx j (rightKernel D j) (FB j)
    (by rw [← hFB j]; rfl)
  rw [e1, h1]
  rw [h2] at e2
  exact e2.symm

/-- The points of the second chart in two-chart curve data are distinct maximal ideals lying on the
exceptional divisor. -/
theorem two_chart_right_points_maximal (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] :
    (∀ s, (rightPoint D s).IsMaximal) ∧ Function.Injective (rightPoint D) ∧ ∀ s, chartBase R x t x ∈
      rightPoint D s := by
  have key : ∀ i, ((D.Q i).comap beta.right.toRingHom).IsMaximal ∧
      chartSlope R x t ∉ (D.Q i).comap beta.right.toRingHom ∧
      chartBase R x t x ∈ (D.Q i).comap beta.right.toRingHom :=
    fun i => overlap_exceptional_point_comap_maximal_right R t x beta (D.Q i) (D.onE i)
  let _ : Algebra (BlowupChart R x t) (BlowupOverlap R t x) := beta.right.toRingHom.toAlgebra
  have := blowup_overlap_isLocalization_right R t x beta
  refine ⟨?_, ?_, ?_⟩
  · rintro (i | k)
    · exact (key i).1
    · exact D.maximalinf k
  · rintro (i | i) (j | j) h
    · congr 1
      apply D.inj
      have h' : (D.Q i).comap (algebraMap (BlowupChart R x t) (BlowupOverlap R t x)) =
          (D.Q j).comap (algebraMap (BlowupChart R x t) (BlowupOverlap R t x)) := h
      have := congrArg (Ideal.map (algebraMap (BlowupChart R x t) (BlowupOverlap R t x))) h'
      rwa [IsLocalization.map_under (Submonoid.powers (chartSlope R x t)),
        IsLocalization.map_under (Submonoid.powers (chartSlope R x t))] at this
    · exfalso
      have h' : (D.Q i).comap beta.right.toRingHom = D.Pinf j := h
      exact (key i).2.1 (h' ▸ D.slopeinf j)
    · exfalso
      have h' : D.Pinf i = (D.Q j).comap beta.right.toRingHom := h
      exact (key j).2.1 (h' ▸ D.slopeinf i)
    · congr 1
      exact D.injinf h
  · rintro (i | k)
    · exact (key i).2.2
    · exact D.onEinf k

section CurveProduct
variable {R : Type} [CommRing R] {t x : R} {beta : BlowupRestriction R t x}
  (D : TwoChartCurveData R t x beta) (j : ℕ)

private theorem mem_commonLevelIdeal_iff_left (i : D.ι)
    (y : CompletedLocalAt (BlowupOverlap R t x) (D.Q i)) :
    y ∈ commonLevelIdeal D j i ↔ D.leftIso i y ∈ leftLevelIdeal D j (Sum.inl i) := by
  rw [← leftLevelIdeal_map_leftIso_symm D j i, Ideal.map_symm]
  rfl

private theorem mem_commonLevelIdeal_iff_right (i : D.ι)
    (y : CompletedLocalAt (BlowupOverlap R t x) (D.Q i)) :
    y ∈ commonLevelIdeal D j i ↔ D.rightIso i y ∈ rightLevelIdeal D j (Sum.inl i) := by
  rw [← rightLevelIdeal_map_rightIso_symm D j i, Ideal.map_symm]
  rfl

/-- Finitely many local functions at distinct maximal ideals are simultaneously approximated by a
global function, modulo ideals containing a power of the maximal ideal. -/
private theorem exists_sub_mem_of_finite_support {A : Type} [CommRing A] [IsNoetherianRing A]
    {ι : Type} [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsPrime] (hmax : ∀ i, (P i).IsMaximal)
    (hP : Function.Injective P) (L : ι → ℕ) (J : ∀ i, Ideal (CompletedLocalAt A (P i)))
    (hJ : ∀ i, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
      (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ J i)
    (w : ∀ i, CompletedLocalAt A (P i)) :
    ∃ a : A, ∀ i, completedPointMap A (P i) a - w i ∈ J i := by
  obtain ⟨a, ha⟩ := finite_support_quotient_surjective_of_isPrime A ι P hmax hP L J hJ
    fun i => Ideal.Quotient.mk _ (w i)
  exact ⟨a, fun i => Ideal.Quotient.eq.1 (congrFun ha i)⟩

/-- A pair of chart functions maps to zero in the local product iff all its local components lie
in the local level ideals. -/
private theorem sectionsToProduct_eq_zero_iff (p : ChartPair R t x) :
    sectionsToProduct D j p = 0 ↔
      (∀ i, completedPointMap _ (D.Q i) (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
        p.1) ∈ commonLevelIdeal D j i) ∧
      (∀ k, completedPointMap _ (leftPoint D (Sum.inr k)) p.1 ∈ leftLevelIdeal D j (Sum.inr k)) ∧
      ∀ l, completedPointMap _ (rightPoint D (Sum.inr l)) p.2 ∈
        rightLevelIdeal D j (Sum.inr l) := by
  simp only [funext_iff, Sum.forall, Pi.zero_apply, sectionsToProduct, RingHom.pi_apply,
    RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  rfl

variable [(Ideal.span ({t,x} : Set R)).IsMaximal]

/-- Local functions at the points of the `t`-chart are approximated by a single chart function. -/
private theorem exists_left_chart_lift [IsNoetherianRing (BlowupChart R t x)]
    (y : ∀ i, CompletedLocalAt (BlowupOverlap R t x) (D.Q i))
    (y0 : ∀ k, CompletedLocalAt (BlowupChart R t x) (leftPoint D (Sum.inr k))) :
    ∃ a : BlowupChart R t x,
      (∀ i, completedPointMap _ (D.Q i) (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) a) -
        y i ∈ commonLevelIdeal D j i) ∧
      ∀ k, completedPointMap _ (leftPoint D (Sum.inr k)) a - y0 k ∈
        leftLevelIdeal D j (Sum.inr k) := by
  choose L hL using (two_chart_left_data_transverse_finite R t x beta D j).2
  obtain ⟨a, ha⟩ := exists_sub_mem_of_finite_support (leftPoint D)
    (two_chart_left_points_maximal R t x beta D).1
    (two_chart_left_points_maximal R t x beta D).2.1 L (leftLevelIdeal D j) hL fun s =>
      match s with
      | Sum.inl i => D.leftIso i (y i)
      | Sum.inr k => y0 k
  refine ⟨a, fun i => ?_, fun k => ha (Sum.inr k)⟩
  rw [mem_commonLevelIdeal_iff_left, map_sub, D.leftIso_compat]
  exact ha (Sum.inl i)

/-- Local functions at the points of the `x`-chart are approximated by a single chart function. -/
private theorem exists_right_chart_lift [IsNoetherianRing (BlowupChart R x t)]
    (y : ∀ i, CompletedLocalAt (BlowupOverlap R t x) (D.Q i))
    (y1 : ∀ l, CompletedLocalAt (BlowupChart R x t) (rightPoint D (Sum.inr l))) :
    ∃ b : BlowupChart R x t,
      (∀ i, completedPointMap _ (D.Q i) (beta.right b) - y i ∈ commonLevelIdeal D j i) ∧
      ∀ l, completedPointMap _ (rightPoint D (Sum.inr l)) b - y1 l ∈
        rightLevelIdeal D j (Sum.inr l) := by
  choose L hL using (two_chart_right_data_transverse_finite R t x beta D j).2
  obtain ⟨b, hb⟩ := exists_sub_mem_of_finite_support (rightPoint D)
    (two_chart_right_points_maximal R t x beta D).1
    (two_chart_right_points_maximal R t x beta D).2.1 L (rightLevelIdeal D j) hL fun s =>
      match s with
      | Sum.inl i => D.rightIso i (y i)
      | Sum.inr l => y1 l
  refine ⟨b, fun i => ?_, fun l => hb (Sum.inr l)⟩
  rw [mem_commonLevelIdeal_iff_right, map_sub, D.rightIso_compat]
  exact hb (Sum.inl i)

/-- Every element of the local product is the image of a pair of chart functions whose local
components agree on the overlap modulo the common level ideals. -/
private theorem exists_sectionsToProduct_eq [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (u : curveProduct D j) :
    ∃ p : ChartPair R t x, (∀ i, completedPointMap _ (D.Q i)
        (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) p.1 - beta.right p.2) ∈
        commonLevelIdeal D j i) ∧ sectionsToProduct D j p = u := by
  choose w hw using fun q => Ideal.Quotient.mk_surjective (u q)
  obtain ⟨a, hLi, hA⟩ := exists_left_chart_lift D j (fun i => w (Sum.inl i))
    (fun k => w (Sum.inr (Sum.inl k)))
  obtain ⟨b, hRi, hB⟩ := exists_right_chart_lift D j (fun i => w (Sum.inl i))
    (fun l => w (Sum.inr (Sum.inr l)))
  refine ⟨(a, b), fun i => ?_, funext fun s => ?_⟩
  · rw [map_sub, ← Ideal.Quotient.eq]
    exact (Ideal.Quotient.eq.2 (hLi i)).trans (Ideal.Quotient.eq.2 (hRi i)).symm
  rw [← hw s]
  refine Ideal.Quotient.eq.2 ?_
  rcases s with i | k | l
  exacts [hLi i, hA k, hB l]

end CurveProduct

/-- The level-`j` quotient of curve sections is additively isomorphic to the product of the local
level quotients at all points, compatibly with `sectionsToProduct`. -/
theorem curve_sections_quot_equiv_product (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x) (D : TwoChartCurveData R
    t x beta) (d : ℕ) (G : GluedGenerators R t x beta d) (hG : ∀ j : ℕ,
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D j)
    (j : ℕ) :
    ∃ E : curveSectionsQuot R t x beta G j ≃+ curveProduct D j, ∀ q : curveSectionsQuot R t x beta G
      j, ∀ p : BlowupChart R t x × BlowupChart R x t,
      (q : (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G j) =
      (curveIdealLattice R t x beta G j).mkQ p → E q = sectionsToProduct D j p := by
  -- Strategy: identify the curve lattices with the local kernels, descend `sectionsToProduct` to
  -- the quotient, and check injectivity locally and surjectivity by chart-wise approximation.
  set α := algebraMap (BlowupChart R t x) (BlowupOverlap R t x) with hα
  have hmemL := mem_commonLevelIdeal_iff_left D j
  have hmemR := mem_commonLevelIdeal_iff_right D j
  -- the overlap curve ideal is the common kernel
  have hover : overlapCurveIdeal R t x beta G j = commonKernel D j := by
    rw [← (two_chart_kernels_agree_on_overlap R t x beta D j).1,
      ← (curve_ideal_lattice_eq_kernels R t x beta D d G hG j).1]
    rw [leftCurveIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, chartExceptional,
      Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl
  have hlat : ∀ p : BlowupChart R t x × BlowupChart R x t, p ∈ curveIdealLattice R t x beta G j ↔
      p.1 ∈ leftKernel D j ∧ p.2 ∈ rightKernel D j := by
    intro p
    rw [← (curve_ideal_lattice_eq_kernels R t x beta D d G hG j).1,
      ← (curve_ideal_lattice_eq_kernels R t x beta D d G hG j).2]
    rfl
  have hsec : ∀ p : BlowupChart R t x × BlowupChart R x t, p ∈ curveSections R t x beta G j ↔
      α p.1 - beta.right p.2 ∈ commonKernel D j := by
    intro p
    rw [← hover]
    change α p.1 - (IsLocalization.Away.invSelf (chartSlope R t x))^0 * beta.right p.2 ∈
      overlapCurveIdeal R t x beta G j ↔ _
    rw [pow_zero, one_mul]
  have hkerL : ∀ a, a ∈ leftKernel D j ↔
      ∀ s, completedPointMap _ (leftPoint D s) a ∈ leftLevelIdeal D j s := fun a => by
    simp only [leftKernel, finiteSupportKernel, Ideal.mem_iInf, Ideal.mem_comap]
  have hkerR : ∀ b, b ∈ rightKernel D j ↔
      ∀ s, completedPointMap _ (rightPoint D s) b ∈ rightLevelIdeal D j s := fun b => by
    simp only [rightKernel, finiteSupportKernel, Ideal.mem_iInf, Ideal.mem_comap]
  have hkerC : ∀ c, c ∈ commonKernel D j ↔
      ∀ i, completedPointMap _ (D.Q i) c ∈ commonLevelIdeal D j i := fun c => by
    simp only [commonKernel, finiteSupportKernel, Ideal.mem_iInf, Ideal.mem_comap]
  -- `sectionsToProduct` descends to the quotient by the curve ideal lattice
  let φ : (BlowupChart R t x × BlowupChart R x t) →+ curveProduct D j :=
    (sectionsToProduct D j).toAddMonoidHom
  have hN : (curveIdealLattice R t x beta G j).toAddSubgroup ≤ φ.ker := by
    intro p hp
    rw [AddMonoidHom.mem_ker]
    obtain ⟨h1, h2⟩ := (hlat p).1 hp
    rw [hkerL] at h1
    rw [hkerR] at h2
    refine (sectionsToProduct_eq_zero_iff D j p).2
      ⟨fun i => ?_, fun k => h1 (Sum.inr k), fun l => h2 (Sum.inr l)⟩
    rw [hmemL, D.leftIso_compat]
    exact h1 (Sum.inl i)
  let Ψ : ((BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G j) →+
      curveProduct D j := QuotientAddGroup.lift _ φ hN
  have hΨ : ∀ p, Ψ ((curveIdealLattice R t x beta G j).mkQ p) = sectionsToProduct D j p :=
    fun p => rfl
  let E₀ : curveSectionsQuot R t x beta G j →+ curveProduct D j :=
    Ψ.comp (curveSectionsQuot R t x beta G j).subtype.toAddMonoidHom
  have hinj : Function.Injective E₀ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨q, hq⟩ h0
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hq
    obtain ⟨hc1, hc2, hc3⟩ := (sectionsToProduct_eq_zero_iff D j p).1 h0
    apply Subtype.ext
    change (curveIdealLattice R t x beta G j).mkQ p = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hlat]
    have hA : p.1 ∈ leftKernel D j := by
      rw [hkerL]
      rintro (i | k)
      · have h := hc1 i
        rwa [hmemL, D.leftIso_compat] at h
      · exact hc2 k
    refine ⟨hA, ?_⟩
    rw [hkerR]
    rintro (i | l)
    · have hs := (hkerC _).1 ((hsec p).1 hp) i
      have hb : completedPointMap _ (D.Q i) (beta.right p.2) ∈ commonLevelIdeal D j i := by
        have := Ideal.sub_mem _ (hc1 i) hs
        rwa [map_sub, sub_sub_cancel] at this
      rw [hmemR, D.rightIso_compat] at hb
      exact hb
    · exact hc3 l
  have hsurj : Function.Surjective E₀ := by
    intro u
    obtain ⟨p, hp, rfl⟩ := exists_sectionsToProduct_eq D j u
    have hs : p ∈ curveSections R t x beta G j := by
      rw [hsec, hkerC]
      exact hp
    exact ⟨⟨(curveIdealLattice R t x beta G j).mkQ p, Submodule.mem_map_of_mem hs⟩, rfl⟩
  refine ⟨AddEquiv.ofBijective E₀ ⟨hinj, hsurj⟩, ?_⟩
  intro q p hqp
  change Ψ q = _
  rw [hqp]
  exact hΨ p

section Limit

variable {R : Type} [CommRing R] {t x : R} {beta : BlowupRestriction R t x} {d : ℕ}
  {G : GluedGenerators R t x beta d}

/-- Consecutive terms of a curve thread have the same class modulo the curve ideal lattice. -/
private theorem curveThreads_mkQ_succ (p : curveThreads R t x beta G) (j : ℕ) :
    (curveIdealLattice R t x beta G j).mkQ (p.val j) =
      (curveIdealLattice R t x beta G j).mkQ (p.val (j+1)) := by
  have h := p.2.2 j (Set.mem_univ _)
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa [towerDelta] using h

/-- Two curve threads have the same class in the curve order limit iff they agree levelwise
modulo the curve ideal lattices. -/
private theorem curveLimitMk_eq_iff (p p' : curveThreads R t x beta G) :
    curveLimitMk R t x beta G p = curveLimitMk R t x beta G p' ↔
      ∀ j, (curveIdealLattice R t x beta G j).mkQ (p.val j) =
        (curveIdealLattice R t x beta G j).mkQ (p'.val j) := by
  change (Submodule.Quotient.mk p : curveThreads R t x beta G ⧸ curveNullThreads R t x beta G)
    = Submodule.Quotient.mk p' ↔ _
  rw [Submodule.Quotient.eq]
  simp only [curveNullThreads, Submodule.mem_comap, curveNull, Submodule.mem_pi, Set.mem_univ,
    true_implies, Submodule.coe_subtype]
  refine forall_congr' fun j => ?_
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  rfl

end Limit

/-- The curve order limit is in bijection with compatible threads in the product of the local level
quotients, compatibly with the maps from curve threads. -/
theorem curve_limit_equiv_product_threads (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x) (D : TwoChartCurveData R
    t x beta) (d : ℕ) (G : GluedGenerators R t x beta d) (hG : ∀ j : ℕ,
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D j)
    :
    ∃ E : CurveOrderLimit R t x beta G ≃ curveProductThreads D, ∀ p : curveThreads R t x beta G, ∀ j
      : ℕ, (E (curveLimitMk R t x beta G p)).val j = sectionsToProduct D j (p.val j) := by
  choose Ej hEj using fun j => curve_sections_quot_equiv_product R t x beta D d G hG j
  choose ρ hρ using fun j => curve_sections_quot_reduction_exists R t x beta d G j
  -- key: equal classes, one in curveSections, give equal images
  have key : ∀ j (a b : ChartPair R t x), a ∈ curveSections R t x beta G j →
      (curveIdealLattice R t x beta G j).mkQ a = (curveIdealLattice R t x beta G j).mkQ b →
        sectionsToProduct D j a = sectionsToProduct D j b := by
    intro j a b ha hab
    have hm : (curveIdealLattice R t x beta G j).mkQ a ∈ curveSectionsQuot R t x beta G j :=
      ⟨a, ha, rfl⟩
    rw [← hEj j ⟨_, hm⟩ a rfl, ← hEj j ⟨_, hm⟩ b hab]
  have red : ∀ j (q : ChartPair R t x),
      curveProductReduction D j (sectionsToProduct D (j+1) q) = sectionsToProduct D j q := by
    intro j q; rfl
  have secs : ∀ (p : curveThreads R t x beta G) j, p.val j ∈ curveSections R t x beta G j :=
    fun p j => p.2.1 j (Set.mem_univ _)
  let F : curveThreads R t x beta G → curveProductThreads D := fun p =>
    ⟨fun j => sectionsToProduct D j (p.val j), fun j => by
      rw [red]; exact (key j _ _ (secs p j) (curveThreads_mkQ_succ p j)).symm⟩
  let Φ : CurveOrderLimit R t x beta G → curveProductThreads D :=
    Quotient.lift F (by
      intro p p' h
      have h' : curveLimitMk R t x beta G p = curveLimitMk R t x beta G p' := Quotient.sound h
      rw [curveLimitMk_eq_iff] at h'
      apply Subtype.ext; funext j
      exact key j _ _ (secs p j) (h' j))
  have hΦ : ∀ p, Φ (curveLimitMk R t x beta G p) = F p := fun p => rfl
  have inj : Function.Injective Φ := by
    intro a b hab
    induction a using Quotient.inductionOn with | _ p => ?_
    induction b using Quotient.inductionOn with | _ p' => ?_
    change Φ (curveLimitMk R t x beta G p) = Φ (curveLimitMk R t x beta G p') at hab
    change curveLimitMk R t x beta G p = curveLimitMk R t x beta G p'
    rw [hΦ, hΦ] at hab
    rw [curveLimitMk_eq_iff]; intro j
    have hj := congrArg (fun u : curveProductThreads D => u.val j) hab
    simp only [F] at hj
    have e1 := hEj j ⟨_, ⟨p.val j, secs p j, rfl⟩⟩ (p.val j) rfl
    have e2 := hEj j ⟨_, ⟨p'.val j, secs p' j, rfl⟩⟩ (p'.val j) rfl
    have := (Ej j).injective (e1.trans (hj.trans e2.symm))
    exact congrArg Subtype.val this
  have surj : Function.Surjective Φ := by
    intro u
    -- representatives
    have hrep : ∀ j, ∃ r ∈ curveSections R t x beta G j,
        (curveIdealLattice R t x beta G j).mkQ r =
          (((Ej j).symm (u.val j) : curveSectionsQuot R t x beta G j) : _) :=
      fun j => ((Ej j).symm (u.val j)).2
    choose r hr hre using hrep
    have hs : ∀ j, sectionsToProduct D j (r j) = u.val j := by
      intro j
      rw [← hEj j ((Ej j).symm (u.val j)) (r j) (hre j).symm, AddEquiv.apply_symm_apply]
    have mem : r ∈ curveThreads R t x beta G := by
      refine ⟨fun j _ => hr j, ?_⟩
      intro j _
      have e := hρ j ((Ej (j+1)).symm (u.val (j+1))) (r (j+1)) (hre (j+1)).symm
      have e2 := hEj j _ (r (j+1)) e
      rw [← red j (r (j+1)), hs (j+1), u.2 j, ← hs j] at e2
      have e3 := hEj j ((Ej j).symm (u.val j)) (r j) (hre j).symm
      have e4 : ρ j ((Ej (j+1)).symm (u.val (j+1))) = (Ej j).symm (u.val j) :=
        (Ej j).injective (by rw [e2, e3])
      have e5 : (curveIdealLattice R t x beta G j).mkQ (r (j+1)) =
          (curveIdealLattice R t x beta G j).mkQ (r j) := by
        rw [← e, e4, hre]
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at e5
      have e6 := (curveIdealLattice R t x beta G j).neg_mem e5
      rw [neg_sub] at e6
      change r j - r (j+1) ∈ _
      exact e6
    refine ⟨curveLimitMk R t x beta G ⟨r, mem⟩, ?_⟩
    rw [hΦ]; apply Subtype.ext; funext j; exact hs j
  refine ⟨Equiv.ofBijective Φ ⟨inj, surj⟩, fun p j => rfl⟩

/-! ### The child order as a linear equivalence -/

section ChildOrder

variable {R : Type} [CommRing R] {t x : R} {beta : BlowupRestriction R t x}
  (D : TwoChartCurveData R t x beta)

private theorem sectionsToProduct_surface_eq (j : ℕ) (r : R) (p : AllPoints D) :
    sectionsToProduct D j (surfaceToChartPair R t x r) p =
      Ideal.Quotient.mk _ (localFromSurface D p r) := by
  rcases p with i | k | l <;> rfl

private def childThreadsEquiv : curveProductThreads D ≃ ∀ p, {u : ∀ j, localQuotient D j p //
    ∀ j, levelReduction (localException D p) (localCurve D p) j (u (j+1)) = u j} where
  toFun u p := ⟨fun j => u.1 j p, fun j => congrFun (u.2 j) p⟩
  invFun v := ⟨fun j p => (v p).1 j, fun j => funext fun p => (v p).2 j⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem localSection_smul (q : AllPoints D) (r : R) (c : ChartPair R t x) :
    localSection D q (r • c) = localFromSurface D q r * localSection D q c := by
  rw [show r • c = algebraMap R _ r * c from Algebra.smul_def r c, map_mul]
  congr 1
  rcases q with i | k | l <;> rfl

end ChildOrder

/-- The curve order limit is `O`-linearly isomorphic to the child order, compatibly with the maps
from surface functions. -/
theorem child_order_equiv_linear (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x) (D : TwoChartCurveData R
    t x beta) (d : ℕ) (G : GluedGenerators R t x beta d) (hG : ∀ j : ℕ,
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D j)
    [∀ p : AllPoints D, IsLocalRing (localRing D p)] [∀ p : AllPoints D,
    IsNoetherianRing (localRing D p)] [∀ p : AllPoints D,
    IsAdicComplete (IsLocalRing.maximalIdeal (localRing D p)) (localRing D p)] (he : ∀ p : AllPoints
    D, localException D p ∈ IsLocalRing.maximalIdeal (localRing D p)) (O : Type) [CommRing O]
    [Algebra O R] [∀ p : AllPoints D, Algebra O (localRing D p)] (hO : ∀ (p : AllPoints D) (o : O),
    localFromSurface D p (algebraMap O R o) = algebraMap O (localRing D p) o) :
    ∃ E : CurveOrderLimit R t x beta G ≃ₗ[O] childOrder D, ∀ (p : curveThreads R t x beta G)
      (r : R), (∀ j : ℕ, p.val j = surfaceToChartPair R t x r) → E (curveLimitMk R t x beta G p) =
      childOrderMap D r := by
  obtain ⟨E₁, hE₁⟩ := curve_limit_equiv_product_threads R t x beta D d G hG
  choose Φ hΦ using fun p => curve_quotient_complete_equiv_threads _ _ (localCurve D p) (he p)
  let E : CurveOrderLimit R t x beta G ≃ childOrder D :=
    E₁.trans ((childThreadsEquiv D).trans (Equiv.piCongrRight fun p => (Φ p).symm))
  have key : ∀ u q j, ((Φ q) (E u q)).val j = (E₁ u).val j q := by
    intro u q j
    change ((Φ q) ((Φ q).symm _)).val j = _
    rw [Equiv.apply_symm_apply]
    rfl
  have hmk : ∀ (p : curveThreads R t x beta G) q j,
      ((Φ q) (E (curveLimitMk R t x beta G p) q)).val j =
        Ideal.Quotient.mk _ (localSection D q (p.val j)) := by
    intro p q j
    rw [key, hE₁]
    rfl
  have hsurj : ∀ u : CurveOrderLimit R t x beta G, ∃ p, curveLimitMk R t x beta G p = u :=
    Submodule.mkQ_surjective _
  have fadd : ∀ q j (y z : localRing D q ⧸ Ideal.span {localCurve D q}),
      ((Φ q) (y + z)).val j = ((Φ q) y).val j + ((Φ q) z).val j := by
    intro q j y z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_add, hΦ, hΦ, hΦ, map_add]
  have fsmul : ∀ q j (a : localRing D q) (y : localRing D q ⧸ Ideal.span {localCurve D q})
      (s' : localRing D q),
      ((Φ q) y).val j = Ideal.Quotient.mk _ s' →
      ((Φ q) (Ideal.Quotient.mk _ a * y)).val j = Ideal.Quotient.mk _ (a * s') := by
    intro q j a y s' h
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, hΦ, map_mul, map_mul, ← h, hΦ]
  have hadd : ∀ u v, E (u + v) = E u + E v := by
    intro u v
    obtain ⟨p, rfl⟩ := hsurj u
    obtain ⟨p', rfl⟩ := hsurj v
    funext q
    apply (Φ q).injective
    apply Subtype.ext
    funext j
    change ((Φ q) (E (curveLimitMk R t x beta G p + curveLimitMk R t x beta G p') q)).val j =
      ((Φ q) (E (curveLimitMk R t x beta G p) q + E (curveLimitMk R t x beta G p') q)).val j
    rw [fadd, ← map_add, hmk, hmk, hmk, Submodule.coe_add, Pi.add_apply, map_add, map_add]
  have hsmulR : ∀ (r : R) u q,
      E (r • u) q = Ideal.Quotient.mk _ (localFromSurface D q r) * E u q := by
    intro r u q
    obtain ⟨p, rfl⟩ := hsurj u
    apply (Φ q).injective
    apply Subtype.ext
    funext j
    rw [fsmul _ _ _ _ _ (hmk p q j), ← map_smul, hmk, Submodule.coe_smul, Pi.smul_apply,
      localSection_smul]
  refine ⟨{ E with map_add' := hadd, map_smul' := ?_ }, ?_⟩
  · intro o u
    change E (o • u) = o • E u
    rw [← algebraMap_smul R o u]
    funext q
    rw [hsmulR, hO]
    exact (Algebra.smul_def o (E u q)).symm
  · intro p r hp
    funext q
    change (Φ q).symm ((childThreadsEquiv D) (E₁ (curveLimitMk R t x beta G p)) q) = _
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    funext j
    change (E₁ (curveLimitMk R t x beta G p)).val j q = _
    rw [hE₁, hp, sectionsToProduct_surface_eq]
    change _ = ((Φ q) (Ideal.Quotient.mk _ (localFromSurface D q r))).val j
    rw [hΦ]

/-- Two-chart curve data with normalized level generators yield glued generators whose level ideals
are the level kernels of the two charts. -/
theorem glued_generators_of_two_chart_curve_data (R : Type) [CommRing R] (t x : R) (beta :
    BlowupRestriction R t x) (D : TwoChartCurveData R t x beta)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsLocalRing R] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (hreg : RegularParameterPair R t x) (hregSwap :
    RegularParameterPair R x t) (d : ℕ) (FA : ℕ → BlowupChart R t x) (hFA : ∀ j : ℕ, leftLevelKernel
    D j = Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R t x t})^j) (FA j)}) (FB : ℕ →
    BlowupChart R x t) (hFB : ∀ j : ℕ, rightLevelKernel D j =
    Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R x t x})^j) (FB j)}) (hnorm : ∃ u : Rˣ,
    (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (FA 1) - algebraMap
    R (BlowupOverlap R t x) (u : R) * ((overlapSlope R t x)^d * beta.right (FB 1)) ∈
    (Ideal.span {overlapException R t x})) :
    ∃ G : GluedGenerators R t x beta d, ∀ j : ℕ,
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} =
        rightLevelKernel D j := by
  obtain ⟨hLmax, hLinj, hLe⟩ := two_chart_left_points_maximal R t x beta D
  obtain ⟨hRmax, hRinj, hRe⟩ := two_chart_right_points_maximal R t x beta D
  have _ : ∀ s, (leftPoint D s).IsMaximal := hLmax
  have _ : ∀ s, (rightPoint D s).IsMaximal := hRmax
  have _ : (Ideal.span ({x,t} : Set R)).IsMaximal := by
    rw [Set.pair_comm]; infer_instance
  choose LA hLA using (two_chart_left_data_transverse_finite R t x beta D 1).2
  choose LB hLB using (two_chart_right_data_transverse_finite R t x beta D 1).2
  obtain ⟨G, hG⟩ := glued_generators_exist R t x beta hreg d FA FB
    (fun j => finite_support_generators_compatible (BlowupChart R t x) _ (leftPoint D) hLinj
      (chartBase R t x t) (leftData D) LA hLA FA hFA j)
    (fun j => finite_support_generators_compatible (BlowupChart R x t) _ (rightPoint D) hRinj
      (chartBase R x t x) (rightData D) LB hLB FB hFB j)
    (fun j => finite_support_level_generator_regular R t x _ (leftPoint D) hLe (leftData D) LA hLA
      hreg FA hFA j)
    (fun j => finite_support_level_generator_regular R x t _ (rightPoint D) hRe (rightData D) LB hLB
      hregSwap FB hFB j)
    (fun j => two_chart_level_generators_agree_on_overlap R t x beta D FA hFA FB hFB j)
    (fun j => overlap_level_generator_regular R t x hreg hregSwap beta _ (rightPoint D) hRe
      (rightData D) LB hLB FB hFB j)
    hnorm
  exact ⟨G, fun j => ⟨(hG j).1.trans (hFA j).symm, (hG j).2.trans (hFB j).symm⟩⟩

/-- At a point of the second chart, the pullback of the surface function `f` factors in the
completed local ring as `xᵈ · (local equation) · unit`. -/
private theorem strict_transform_right_point_equation (R : Type) [CommRing R] (t x : R) [(Ideal.span
    ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)] [IsNoetherianRing
    (BlowupChart R x t)] (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta) (d : ℕ)
    (G : GluedGenerators R t x beta d) (hG : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk
    ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧ Ideal.span {Ideal.Quotient.mk
    ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D j) (f : R) (hf : ∀ j : ℕ,
    surfaceToCechInput R t x j f = (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j)) (s
    : D.ι ⊕ D.ιinf) [IsNoetherianRing (CompletedLocalAt (BlowupChart R x t) (rightPoint D s))]
    (hereg : Function.Injective (fun a : (CompletedLocalAt (BlowupChart R x t) (rightPoint D s)) =>
    (completedPointMap (BlowupChart R x t) (rightPoint D s)) (chartBase R x t x) * a)) (hgreg :
    Function.Injective (fun a : (CompletedLocalAt (BlowupChart R x t) (rightPoint D s)) ⧸ Ideal.span
    {(completedPointMap (BlowupChart R x t) (rightPoint D s)) (chartBase R x t x)} =>
    Ideal.Quotient.mk
    (Ideal.span {(completedPointMap (BlowupChart R x t) (rightPoint D s)) (chartBase R x t x)})
    (rightData D s) * a)) :
    ∃ v : (CompletedLocalAt (BlowupChart R x t) (rightPoint D s))ˣ,
      (completedPointMap (BlowupChart R x t) (rightPoint D s)) (algebraMap R (BlowupChart R x t) f)
      = ((completedPointMap (BlowupChart R x t) (rightPoint D s)) (chartBase R x t x))^d * rightData
      D s * (v : (CompletedLocalAt (BlowupChart R x t) (rightPoint D s))) := by
  obtain ⟨hmax, hinj, hmem⟩ := two_chart_right_points_maximal R t x beta D
  have : ∀ s, (rightPoint D s).IsMaximal := hmax
  exact strict_transform_equation_of_kernels (rightPoint D) hinj _ hmem (rightData D)
    (fun j => (two_chart_right_data_transverse_finite R t x beta D j).2) G.right
    (fun j => (curve_ideal_lattice_eq_kernels R t x beta D d G hG j).2) d _
    (glued_function_right_chart R t x beta d G f hf) s hereg hgreg

/-- At a point of the second chart, the strict transform of `(f)` is generated by the local equation
of the two-chart curve data. -/
theorem global_function_strict_transform_at_right_point (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x) (D : TwoChartCurveData R
    t x beta) (d : ℕ) (G : GluedGenerators R t x beta d) (hG : ∀ j : ℕ, Ideal.span
    {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧ Ideal.span
    {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D j) (f : R) (hf
    : ∀ j : ℕ, surfaceToCechInput R t x j f = (cechInputLattice R t x j).mkQ (gluedFunctionPair R t
    x G j)) (s : D.ι ⊕ D.ιinf) [IsNoetherianRing (CompletedLocalAt (BlowupChart R x t)
    (rightPoint D s))] (hereg : Function.Injective (fun a :
    (CompletedLocalAt (BlowupChart R x t) (rightPoint D s)) =>
    (completedPointMap (BlowupChart R x t) (rightPoint D s)) (chartBase R x t x) * a)) (hgreg :
    Function.Injective (fun a : (CompletedLocalAt (BlowupChart R x t) (rightPoint D s)) ⧸ Ideal.span
    {(completedPointMap (BlowupChart R x t) (rightPoint D s)) (chartBase R x t x)} =>
    Ideal.Quotient.mk
    (Ideal.span {(completedPointMap (BlowupChart R x t) (rightPoint D s)) (chartBase R x t x)})
    (rightData D s) * a)) :
    strictTransformAt R x t (rightPoint D s) d (Ideal.span {f}) = Ideal.span {rightData D s} := by
  obtain ⟨v, hv⟩ := strict_transform_right_point_equation R t x beta D d G hG f hf s hereg hgreg
  unfold strictTransformAt
  rw [principal_ideal_image]
  simp only [RingHom.comp_apply]
  have hv' : completedPointMap (BlowupChart R x t) (rightPoint D s) (chartBase R x t f) =
      (completedPointMap (BlowupChart R x t) (rightPoint D s) (chartBase R x t x)) ^ d *
        rightData D s * (v : CompletedLocalAt (BlowupChart R x t) (rightPoint D s)) := hv
  clear hv
  generalize completedPointMap (BlowupChart R x t) (rightPoint D s) (chartBase R x t x) = c at *
  generalize rightData D s = g at *
  generalize completedPointMap (BlowupChart R x t) (rightPoint D s) (chartBase R x t f) = y at *
  have hcd : Function.Injective (fun a => c ^ d * a) := IsLeftRegular.pow d hereg
  subst hv'
  have hu := v.mul_inv
  generalize (v⁻¹ : (CompletedLocalAt (BlowupChart R x t) (rightPoint D s))ˣ).val = vi at hu
  generalize v.val = vv at hu ⊢
  ext u
  rw [Submodule.mem_colon_singleton, Ideal.mem_span_singleton', Ideal.mem_span_singleton']
  simp only [smul_eq_mul]
  constructor
  · rintro ⟨w, hw⟩
    have h1 : c ^ d * u = c ^ d * (w * vv * g) := by
      have : u * c ^ d = w * (c ^ d * g * vv) := hw.symm
      linear_combination this
    exact ⟨w * vv, (hcd h1).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w * vi, by
      calc _ = (w * g * c ^ d) * (vv * vi) := by ring
        _ = _ := by rw [hu]; ring⟩

private theorem injective_mul_of_span_eq (A : Type) [CommRing A] (f g : A)
    (hf : Function.Injective (fun c : A => f * c))
    (h : Ideal.span {f} = Ideal.span {g}) : Function.Injective (fun c : A => g * c) := by
  obtain ⟨u, hu⟩ := regular_principal_generators_associated A f g
    (fun a b hab => hf (by simpa only [mul_comm] using hab)) h
  intro a b hab
  apply hf
  have : (u : A) * (f * a) = (u : A) * (f * b) := by
    simp only [← mul_assoc, ← hu]; exact hab
  exact u.isUnit.mul_right_injective this

/-- The first-chart glued generators are nonzerodivisors on the overlap modulo every power of the
exceptional ideal. -/
theorem two_chart_left_generators_regular_on_overlap (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x) (D : TwoChartCurveData R
    t x beta) (d : ℕ) (G : GluedGenerators R t x beta d) (hG : ∀ j : ℕ,
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D j)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t) (j : ℕ) :
    Function.Injective (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c) := by
  have h788 := two_chart_level_generators_agree_on_overlap R t x beta D G.left
    (fun j => (hG j).1.symm) G.right (fun j => (hG j).2.symm) j
  obtain ⟨hmax, -, hbase⟩ := two_chart_right_points_maximal R t x beta D
  have _ : ∀ s, (rightPoint D s).IsMaximal := hmax
  obtain ⟨htr, hfin⟩ := two_chart_right_data_transverse_finite R t x beta D 1
  have hreg2 := overlap_level_generator_regular R t x hreg hregSwap beta (D.ι ⊕ D.ιinf)
    (rightPoint D) hbase (rightData D) (fun s => (hfin s).choose) (fun s => (hfin s).choose_spec)
    G.right
    (fun j => (hG j).2.symm) j
  exact injective_mul_of_span_eq _ _ _ hreg2 h788.symm

/-- The level kernels of both charts are principal modulo the powers of the exceptional ideals. -/
theorem two_chart_level_generators_exist (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] :
    (∃ FA : ℕ → BlowupChart R t x, ∀ j : ℕ, leftLevelKernel D j =
      Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R t x t})^j) (FA j)}) ∧ (∃ FB : ℕ →
      BlowupChart R x t, ∀ j : ℕ, rightLevelKernel D j =
      Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R x t x})^j) (FB j)}) := by
  constructor
  · obtain ⟨hm, hinj, hte⟩ := two_chart_left_points_maximal R t x beta D
    have _ : ∀ s, (leftPoint D s).IsMaximal := hm
    exact finite_support_level_kernels_principal R t x (D.ι ⊕ D.ι0) (leftPoint D) hinj hte
      (leftData D)
      (fun s => (two_chart_left_data_transverse_finite R t x beta D 0).1 s)
      (fun j s => (two_chart_left_data_transverse_finite R t x beta D j).2 s)
  · have _ : (Ideal.span ({x,t} : Set R)).IsMaximal := by
      rw [Set.pair_comm]; infer_instance
    obtain ⟨hm, hinj, hte⟩ := two_chart_right_points_maximal R t x beta D
    have _ : ∀ s, (rightPoint D s).IsMaximal := hm
    exact finite_support_level_kernels_principal R x t (D.ι ⊕ D.ιinf) (rightPoint D) hinj hte
      (rightData D)
      (fun s => (two_chart_right_data_transverse_finite R t x beta D 0).1 s)
      (fun j s => (two_chart_right_data_transverse_finite R t x beta D j).2 s)

/-- The map induced on cokernels sends the class of `a` to the class of `u1 a`. -/
private theorem two_term_coker_map_representative (O : Type) [CommRing O] (A0 A1 B0 B1 : Type)
    [AddCommGroup A0] [Module O A0] [AddCommGroup A1] [Module O A1] [AddCommGroup B0] [Module O B0]
    [AddCommGroup B1] [Module O B1] (dA : A0 →ₗ[O] A1) (dB : B0 →ₗ[O] B1) (u0 : A0 →ₗ[O] B0)
    (u1 : A1 →ₗ[O] B1) (h : u1.comp dA = dB.comp u0) (a : A1) :
    twoTermCokerMap dA dB u0 u1 h ((LinearMap.range dA).mkQ a) = (LinearMap.range dB).mkQ (u1 a) :=
  rfl

/-! ### The negative-twist cokernel -/

section LayerCoordinates

variable (R : Type) [CommRing R] (t x : R)

local notation "A" => BlowupChart R t x
local notation "O" => BlowupOverlap R t x
local notation "tO" => algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t)
local notation "z" => selfZPow (chartSlope R t x) (BlowupOverlap R t x)

private theorem layer_xO_eq : algebraMap A O (chartBase R t x x) = tO * z 1 := by
  rw [← blowup_chart_relation, map_mul]
  have := selfZPow_natCast (chartSlope R t x) (BlowupOverlap R t x) 1
  simp only [Nat.cast_one, pow_one] at this
  rw [this]

private theorem layer_invSelf_pow (n : ℕ) :
    (IsLocalization.Away.invSelf (chartSlope R t x) : O) ^ n = z (-n) := by
  rw [selfZPow_neg_natCast, IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow, one_pow]
  congr 1

private theorem layer_slope_pow (n : ℕ) : (algebraMap A O (chartSlope R t x)) ^ n = z n :=
  (selfZPow_natCast _ _ n).symm

private theorem layer_z_nat (n : ℕ) : z (n:ℤ) = (z 1) ^ n := by
  rw [selfZPow_natCast]; have := selfZPow_natCast (chartSlope R t x) (BlowupOverlap R t x) 1
  simp only [Nat.cast_one, pow_one] at this; rw [this]

private theorem layer_tO_pow_mem (j : ℕ) (o : O) : tO ^ j * o ∈ (Ideal.span {tO}) ^ j :=
  Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) j)

private theorem layer_beta_right (beta : BlowupRestriction R t x) (c : R) (n : ℕ) :
    beta.right (chartBase R x t c * chartSlope R x t ^ n) =
      algebraMap A O (chartBase R t x c) * z (-(n:ℤ)) := by
  rw [map_mul, map_pow, beta.slope, layer_invSelf_pow]
  congr 1
  exact beta.right.commutes c

end LayerCoordinates

section LayerLifts

variable {R : Type} [CommRing R] {t x : R}

local notation "A" => BlowupChart R t x
local notation "O" => BlowupOverlap R t x
local notation "tO" => algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t)

/-- A linear map on the overlap whose values at all integral powers `z ℓ` of the slope lie in a
submodule takes all its values in that submodule. -/
private theorem layer_map_mem_of_slope_pows {Q : Type} [AddCommGroup Q] [Module R Q]
    (Φ : O →ₗ[R] Q) (N : Submodule R Q) (z : ℤ → O)
    (hznat : ∀ n : ℕ, (algebraMap A O (chartSlope R t x)) ^ n = z n)
    (hzadd : ∀ a b : ℤ, z (a + b) = z a * z b) (hz0 : z 0 = 1) (hmono : ∀ ℓ : ℤ, Φ (z ℓ) ∈ N)
    (o : O) : Φ o ∈ N := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (chartSlope R t x) o
  have ho : o = algebraMap A O a * z (-(n:ℤ)) := by
    rw [← ha, hznat, mul_assoc, ← hzadd]; simp [hz0]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [ho]
  clear ha ho
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_mul, map_add]; exact add_mem hp hq
  | monomial m c =>
    have : algebraMap A O (Ideal.Quotient.mk _ (Polynomial.monomial m c)) * z (-(n:ℤ)) =
        c • z (m + -(n:ℤ)) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul (Ideal.Quotient.mk _),
        map_pow (Ideal.Quotient.mk _), hzadd, ← hznat, Algebra.smul_def]
      change algebraMap A O (chartBase R t x c * chartSlope R t x ^ m) * _ =
        algebraMap A O (chartBase R t x c) * _
      rw [map_mul, map_pow]; ring
    rw [this, map_smul]; exact Submodule.smul_mem _ _ (hmono _)

/-- A linear map on the overlap killing all multiples of `t` is `(t, x)`-torsion valued. -/
private theorem layer_span_le_ker {Q : Type} [AddCommGroup Q] [Module R Q] (Φ : O →ₗ[R] Q)
    (hΦt : ∀ o, Φ (tO * o) = 0) (e : O) :
    Ideal.span {t,x} ≤ LinearMap.ker (LinearMap.toSpanSingleton R Q (Φ e)) := by
  rw [Ideal.span_le]
  rintro c hc
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  rw [← map_smul, Algebra.smul_def]
  rcases hc with h | h <;> (try rw [Set.mem_singleton_iff] at h) <;> rw [h]
  · exact hΦt e
  · change Φ (algebraMap A O (chartBase R t x x) * e) = 0
    rw [layer_xO_eq, mul_assoc]; exact hΦt _

private theorem principalLayerMap_tO_apply (j : ℕ) (a : O) :
    principalLayerMap O tO j a = Ideal.Quotient.mk _ (tO ^ j * a) := by
  rw [mul_comm]; rfl

/-- Laurent coordinates of the `j`-th layer classes of functions on the `t`-chart: they have no
negative coefficients. -/
private theorem layer_left_laurent_lift (j : ℕ) (z : ℤ → O)
    (hznat : ∀ n : ℕ, (algebraMap A O (chartSlope R t x)) ^ n = z n)
    (L : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer O tO j)
    (hL : ∀ r : R, ∀ ell : ℤ, (L (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap O tO j (algebraMap A O (chartBase R t x r) *
        z ell))
    (p : Polynomial R) :
    ∃ F : LaurentPolynomial (R ⧸ Ideal.span {t,x}), (∀ ℓ : ℤ, ℓ < 0 → F.coeff ℓ = 0) ∧
      (L F).val = Ideal.Quotient.mk _ (tO ^ j * algebraMap A O (Ideal.Quotient.mk _ p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨F1, h1, e1⟩ := hp
    obtain ⟨F2, h2, e2⟩ := hq
    refine ⟨F1 + F2, fun ℓ hℓ => ?_, ?_⟩
    · rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h1 ℓ hℓ, h2 ℓ hℓ, add_zero]
    · rw [map_add, Submodule.coe_add, e1, e2, map_add, map_add, mul_add, map_add]
  | monomial m c =>
    refine ⟨LaurentPolynomial.C (Ideal.Quotient.mk _ c) * LaurentPolynomial.T m, fun ℓ hℓ => ?_,
      ?_⟩
    · rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, if_neg (by omega)]
    · have hmonoA : Ideal.Quotient.mk (Ideal.span {blowupRelation R t x}) (Polynomial.monomial m c)
          = chartBase R t x c * chartSlope R t x ^ m := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]; rfl
      rw [hL, principalLayerMap_tO_apply, hmonoA, map_mul (algebraMap _ _),
        map_pow (algebraMap _ _), hznat]

/-- Laurent coordinates of the `j`-th layer classes of twisted functions on the `x`-chart: they
vanish above degree `j - d`. -/
private theorem layer_right_laurent_lift (beta : BlowupRestriction R t x) (d j : ℕ) (z : ℤ → O)
    (hzadd : ∀ a b : ℤ, z (a + b) = z a * z b)
    (hbeta : ∀ (c : R) (n : ℕ), beta.right (chartBase R x t c * chartSlope R x t ^ n) =
      algebraMap A O (chartBase R t x c) * z (-(n:ℤ)))
    (L : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer O tO j)
    (hL : ∀ r : R, ∀ ell : ℤ, (L (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap O tO j (algebraMap A O (chartBase R t x r) *
        z ell))
    (q : Polynomial R) :
    ∃ F : LaurentPolynomial (R ⧸ Ideal.span {t,x}), (∀ ℓ : ℤ, (j:ℤ) - d < ℓ → F.coeff ℓ = 0) ∧
      (L F).val = Ideal.Quotient.mk _ (tO ^ j * (z ((j:ℤ) - d) *
        beta.right (Ideal.Quotient.mk _ q))) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨F1, h1, e1⟩ := hp
    obtain ⟨F2, h2, e2⟩ := hq
    refine ⟨F1 + F2, fun ℓ hℓ => ?_, ?_⟩
    · rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h1 ℓ hℓ, h2 ℓ hℓ, add_zero]
    · rw [map_add, Submodule.coe_add, e1, e2, map_add, map_add, mul_add, mul_add, map_add]
  | monomial m c =>
    refine ⟨LaurentPolynomial.C (Ideal.Quotient.mk _ c) * LaurentPolynomial.T ((j:ℤ) - d - m),
      fun ℓ hℓ => ?_, ?_⟩
    · rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, if_neg (by omega)]
    · have hmonoB : Ideal.Quotient.mk (Ideal.span {blowupRelation R x t}) (Polynomial.monomial m c)
          = chartBase R x t c * chartSlope R x t ^ m := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]; rfl
      rw [hL, principalLayerMap_tO_apply, hmonoB, hbeta,
        show (j:ℤ) - d - m = ((j:ℤ) - d) + -(m:ℤ) by ring, hzadd]
      congr 1; ring

/-- A linear map on the overlap which kills `t^j`-multiples of Čech differentials maps every
integral power `z ℓ` of the slope into a submodule containing the images of the window powers
`z (-a-1)`, `a < d - j - 1`. -/
private theorem layer_slope_pow_mem (beta : BlowupRestriction R t x) (d j : ℕ) {Q : Type}
    [AddCommGroup Q] [Module R Q] (Φ : O →ₗ[R] Q) (N : Submodule R Q) (z : ℤ → O)
    (hznat : ∀ n : ℕ, (algebraMap A O (chartSlope R t x)) ^ n = z n)
    (hzadd : ∀ a b : ℤ, z (a + b) = z a * z b) (hz1 : ∀ n : ℕ, z n = z 1 ^ n)
    (hinv : ∀ n : ℕ, (IsLocalization.Away.invSelf (chartSlope R t x) : O) ^ n = z (-n))
    (hxO : algebraMap A O (chartBase R t x x) = tO * z 1)
    (hbeta : ∀ (c : R) (n : ℕ), beta.right (chartBase R x t c * chartSlope R x t ^ n) =
      algebraMap A O (chartBase R t x c) * z (-(n:ℤ)))
    (hΦD : ∀ (o : O) (w : A × BlowupChart R x t), tO ^ j * o = fullCechDifferential R t x beta d w →
      Φ o = 0)
    (hwin : ∀ a : ℕ, a < d - j - 1 → Φ (z (-(a:ℤ) - 1)) ∈ N) (ℓ : ℤ) : Φ (z ℓ) ∈ N := by
  have hDab : ∀ a b, fullCechDifferential R t x beta d (a, b) = algebraMap A O a -
      (IsLocalization.Away.invSelf (chartSlope R t x))^d * beta.right b := fun _ _ => rfl
  by_cases h0 : 0 ≤ ℓ
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have : tO ^ j * z n = fullCechDifferential R t x beta d
        ((chartBase R t x t)^j * chartSlope R t x ^ n, 0) := by
      rw [hDab, map_zero, mul_zero, sub_zero, map_mul, map_pow, map_pow, hznat]
    rw [hΦD _ _ this]; exact Submodule.zero_mem _
  by_cases h1 : ℓ ≤ (j:ℤ) - d
  · obtain ⟨s, hs⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (j:ℤ) - d - ℓ by omega)
    have : tO ^ j * z ℓ = fullCechDifferential R t x beta d
        (0, -(chartBase R x t x ^ j * chartSlope R x t ^ s)) := by
      rw [hDab, map_zero, zero_sub, map_neg, mul_neg, neg_neg, ← map_pow (chartBase R x t) x j,
        hbeta, hinv, map_pow, map_pow, hxO]
      rw [show ℓ = -(d:ℤ) + j + -(s:ℤ) by omega, hzadd, hzadd, hz1]
      ring
    rw [hΦD _ _ this]; exact Submodule.zero_mem _
  · push Not at h0 h1
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -ℓ - 1 by omega)
    rw [show ℓ = -(a:ℤ) - 1 by omega]
    exact hwin a (by omega)

/-- In a Laurent polynomial identity `F_A = F_B + ∑ₐ vₐ T^(-a-1)` (`a < d - j - 1`) where `F_A` has
no negative coefficients and `F_B` none above degree `j - d`, all `vₐ` vanish. -/
private theorem laurent_window_coeffs_eq_zero {K : Type} [CommRing K] (d j : ℕ)
    (FA FB : LaurentPolynomial K) (hFA0 : ∀ ℓ : ℤ, ℓ < 0 → FA.coeff ℓ = 0)
    (hFB0 : ∀ ℓ : ℤ, (j:ℤ) - d < ℓ → FB.coeff ℓ = 0) (v : Fin (d-j-1) → K)
    (hF : FA = FB + ∑ a : Fin (d-j-1), LaurentPolynomial.C (v a) *
      LaurentPolynomial.T (-((a:ℕ):ℤ) - 1)) (a : Fin (d-j-1)) : v a = 0 := by
  have hlt := a.isLt
  have := congrArg (fun F : LaurentPolynomial K => F.coeff (-((a:ℕ):ℤ) - 1)) hF
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hFA0 _ (by omega), hFB0 _ (by omega),
    zero_add, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single a] at this
  · rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same] at this
    exact this.symm
  · intro b _ hb
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      if_neg]
    intro h; apply hb; ext; omega
  · simp

/-- Laurent coordinates of the window sums `t^j ∑ₐ vₐ z^(-a-1)`. -/
private theorem layer_window_sum_eq {j : ℕ} (d : ℕ) (z : ℤ → O)
    (L : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer O tO j)
    (hL : ∀ r : R, ∀ ell : ℤ, (L (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap O tO j (algebraMap A O (chartBase R t x r) *
        z ell))
    (v' : Fin (d-j-1) → R) :
    (L (∑ a : Fin (d-j-1), LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) (v' a)) *
      LaurentPolynomial.T (-((a:ℕ):ℤ) - 1))).val =
      Ideal.Quotient.mk _ (tO ^ j * ∑ a : Fin (d-j-1), v' a • z (-((a:ℕ):ℤ) - 1)) := by
  rw [map_sum, Submodule.coe_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hL, principalLayerMap_tO_apply, Algebra.smul_def]; rfl

/-- Laurent-coordinate core of `layer_window_coeffs_eq_zero_of_mem`: if
`t^j (p - z^(j-d) q) ≡ t^j ∑ₐ vₐ z^(-a-1)` modulo `(t)^(j+1)`, then all `vₐ` vanish modulo
`(t, x)`. -/
private theorem layer_window_coeffs_eq_zero_of_layer_eq (beta : BlowupRestriction R t x) (d j : ℕ)
    (z : ℤ → O) (hznat : ∀ n : ℕ, (algebraMap A O (chartSlope R t x)) ^ n = z n)
    (hzadd : ∀ a b : ℤ, z (a + b) = z a * z b)
    (hbeta : ∀ (c : R) (n : ℕ), beta.right (chartBase R x t c * chartSlope R x t ^ n) =
      algebraMap A O (chartBase R t x c) * z (-(n:ℤ)))
    (L : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer O tO j)
    (hL : ∀ r : R, ∀ ell : ℤ, (L (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap O tO j (algebraMap A O (chartBase R t x r) *
        z ell))
    (v' : Fin (d-j-1) → R) (p q : Polynomial R)
    (hq : tO ^ j * (algebraMap A O (Ideal.Quotient.mk _ p) -
        z ((j:ℤ) - d) * beta.right (Ideal.Quotient.mk _ q)) -
      tO ^ j * ∑ a : Fin (d-j-1), v' a • z (-((a:ℕ):ℤ) - 1) ∈ (Ideal.span {tO}) ^ (j+1))
    (a : Fin (d-j-1)) : Ideal.Quotient.mk (Ideal.span {t,x}) (v' a) = 0 := by
  obtain ⟨FA, hFA0, hFA⟩ := layer_left_laurent_lift j z hznat L hL p
  obtain ⟨FB, hFB0, hFB⟩ := layer_right_laurent_lift beta d j z hzadd hbeta L hL q
  have hFG := layer_window_sum_eq d z L hL v'
  set FG := ∑ a : Fin (d-j-1), LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) (v' a)) *
    LaurentPolynomial.T (-((a:ℕ):ℤ) - 1)
  have heq : L FA = L (FB + FG) := by
    apply Subtype.ext
    rw [map_add, Submodule.coe_add, hFA, hFB, hFG, ← map_add, Ideal.Quotient.eq]
    convert hq using 1; ring
  exact laurent_window_coeffs_eq_zero d j FA FB hFA0 hFB0 _ (L.injective heq) a

/-- If a Čech input pair has differential congruent to `t^j ∑ₐ vₐ z^(-a-1)` modulo `(t)^(j+1)`
(`a < d - j - 1`), then all `vₐ` vanish modulo `(t, x)`. -/
private theorem layer_window_coeffs_eq_zero_of_mem (hreg : RegularParameterPair R t x)
    (beta : BlowupRestriction R t x) (hregSwap : RegularParameterPair R x t) (d j : ℕ) (hj : j < d)
    (hnow : cechInputLattice R t x j ≤
      (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d))
    (z : ℤ → O) (hznat : ∀ n : ℕ, (algebraMap A O (chartSlope R t x)) ^ n = z n)
    (hzadd : ∀ a b : ℤ, z (a + b) = z a * z b) (hz1 : ∀ n : ℕ, z n = z 1 ^ n)
    (hinv : ∀ n : ℕ, (IsLocalization.Away.invSelf (chartSlope R t x) : O) ^ n = z (-n))
    (hxO : algebraMap A O (chartBase R t x x) = tO * z 1)
    (hbeta : ∀ (c : R) (n : ℕ), beta.right (chartBase R x t c * chartSlope R x t ^ n) =
      algebraMap A O (chartBase R t x c) * z (-(n:ℤ)))
    (L : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer O tO j)
    (hL : ∀ r : R, ∀ ell : ℤ, (L (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap O tO j (algebraMap A O (chartBase R t x r) *
        z ell))
    (v' : Fin (d-j-1) → R) (w : A × BlowupChart R x t)
    (hq : fullCechDifferential R t x beta d w -
      tO ^ j * ∑ a : Fin (d-j-1), v' a • z (-((a:ℕ):ℤ) - 1) ∈ (Ideal.span {tO}) ^ (j+1))
    (a : Fin (d-j-1)) : Ideal.Quotient.mk (Ideal.span {t,x}) (v' a) = 0 := by
  set G := ∑ a : Fin (d-j-1), v' a • z (-((a:ℕ):ℤ) - 1)
  have hw0 : finiteCechDifferential R t x beta d j hnow (Submodule.Quotient.mk w) = 0 := by
    change Submodule.Quotient.mk (p := cechOutputLattice R t x j)
      (fullCechDifferential R t x beta d w) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change _ ∈ (Ideal.span {tO}) ^ j
    rw [← sub_add_cancel (fullCechDifferential R t x beta d w) (tO ^ j * G)]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ j) hq) (layer_tO_pow_mem R t x j G)
  have hw : Submodule.Quotient.mk (p := cechInputLattice R t x j) w = 0 :=
    actual_negative_twist_kernel_zero R t x hreg beta hregSwap d j hj.le hnow
      (hw0.trans (map_zero _).symm)
  rw [Submodule.Quotient.mk_eq_zero] at hw
  obtain ⟨w1, w2⟩ := w
  obtain ⟨h1, h2⟩ := hw
  change w1 ∈ (Ideal.span {chartBase R t x t}) ^ j at h1
  change w2 ∈ (Ideal.span {chartBase R x t x}) ^ j at h2
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1 h2
  obtain ⟨a', rfl⟩ := h1
  obtain ⟨b', rfl⟩ := h2
  have hDab : ∀ a b, fullCechDifferential R t x beta d (a, b) = algebraMap A O a -
      (IsLocalization.Away.invSelf (chartSlope R t x))^d * beta.right b := fun _ _ => rfl
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b'
  have hbx : beta.right (chartBase R x t x) = tO * z 1 := (beta.right.commutes x).trans hxO
  have hDw : fullCechDifferential R t x beta d
      (Ideal.Quotient.mk _ p * chartBase R t x t ^ j,
        Ideal.Quotient.mk _ q * chartBase R x t x ^ j) =
      tO ^ j * (algebraMap A O (Ideal.Quotient.mk _ p) -
        z ((j:ℤ) - d) * beta.right (Ideal.Quotient.mk _ q)) := by
    rw [hDab, map_mul, map_mul beta.right, map_pow beta.right, hbx, hinv, map_pow,
      show (j:ℤ) - d = -(d:ℤ) + j by ring, hzadd, hz1]
    ring
  rw [hDw] at hq
  exact layer_window_coeffs_eq_zero_of_layer_eq beta d j z hznat hzadd hbeta L hL v' p q hq a

end LayerLifts

/-- If `i (v mod I) = Φ (∑ₐ vₐ • wₐ)` for all `v`, then every `Φ wₐ` lies in the range of `i`. -/
private theorem window_mem_range {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup Q] [Module R Q] {I : Ideal R} {n : ℕ} (i : (Fin n → R ⧸ I) →ₗ[R] Q)
    (Φ : M →ₗ[R] Q) (w : Fin n → M)
    (hi : ∀ v : Fin n → R, i (fun a => Ideal.Quotient.mk I (v a)) = Φ (∑ a, v a • w a))
    (a : Fin n) : Φ (w a) ∈ LinearMap.range i := by
  refine ⟨fun b => Ideal.Quotient.mk I ((Pi.single a (1:R) : Fin n → R) b), ?_⟩
  rw [hi, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same, one_smul]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The projection of the overlap onto the level-`(j + 1)` Čech cokernel. -/
private noncomputable def layerCokerProj (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ) (hnext : cechInputLattice R t x (j + 1) ≤
      (cechOutputLattice R t x (j + 1)).comap (fullCechDifferential R t x beta d)) :
    BlowupOverlap R t x →ₗ[R] (CechLevelOutput R t x (j+1) ⧸
      LinearMap.range (finiteCechDifferential R t x beta d (j+1) hnext)) :=
  (LinearMap.range _).mkQ ∘ₗ (cechOutputLattice R t x (j+1)).mkQ

/-- The window map from `(R ⧸ (t, x))^(d - j - 1)` to the level-`(j + 1)` Čech cokernel, sending the
`a`-th basis vector to the class of `t^j z^(-a-1)`; its image contains every class of `t^j o`. -/
private theorem exists_layer_window_map (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ) (hnext : cechInputLattice R t x (j + 1) ≤
      (cechOutputLattice R t x (j + 1)).comap (fullCechDifferential R t x beta d)) :
    ∃ i : (Fin (d-j-1) → (R ⧸ Ideal.span {t,x})) →ₗ[R] (CechLevelOutput R t x (j+1) ⧸
      LinearMap.range (finiteCechDifferential R t x beta d (j+1) hnext)),
      (∀ v : Fin (d-j-1) → R, i (fun a => Ideal.Quotient.mk _ (v a)) =
        (LinearMap.range (finiteCechDifferential R t x beta d (j+1) hnext)).mkQ
          ((cechOutputLattice R t x (j+1)).mkQ
            (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ^ j *
              ∑ a, v a • selfZPow (chartSlope R t x) (BlowupOverlap R t x) (-((a:ℕ):ℤ)-1)))) ∧
      ∀ o : BlowupOverlap R t x,
        (LinearMap.range (finiteCechDifferential R t x beta d (j+1) hnext)).mkQ
          ((cechOutputLattice R t x (j+1)).mkQ
            (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ^ j * o)) ∈
          LinearMap.range i := by
  set D := fullCechDifferential R t x beta d with hD
  set D1 := finiteCechDifferential R t x beta d (j+1) hnext with hD1
  set tO := algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) with htO
  have hxO := layer_xO_eq R t x
  have hinv := layer_invSelf_pow R t x
  have hznat : ∀ n : ℕ,
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x)) ^ n =
      selfZPow (chartSlope R t x) (BlowupOverlap R t x) n := layer_slope_pow R t x
  have hz1 := layer_z_nat R t x
  have hzadd : ∀ a b : ℤ, selfZPow (chartSlope R t x) (BlowupOverlap R t x) (a + b) =
      selfZPow (chartSlope R t x) (BlowupOverlap R t x) a *
        selfZPow (chartSlope R t x) (BlowupOverlap R t x) b :=
    fun a b => selfZPow_add _ _
  have hz0 := selfZPow_zero (chartSlope R t x) (BlowupOverlap R t x)
  have hbeta := layer_beta_right R t x beta
  set z := selfZPow (chartSlope R t x) (BlowupOverlap R t x)
  clear_value z
  set Q := CechLevelOutput R t x (j+1) ⧸ LinearMap.range D1
  let ψ := layerCokerProj R t x beta d j hnext
  let Φ := ψ ∘ₗ LinearMap.mulLeft R (tO ^ j)
  have hΦ : ∀ o, Φ o = ψ (tO ^ j * o) := fun o => rfl
  have hψD : ∀ w, ψ (D w) = 0 := by
    intro w
    change (LinearMap.range D1).mkQ (D1 (Submodule.Quotient.mk w)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨_, rfl⟩
  have hΦt : ∀ o, Φ (tO * o) = 0 := by
    intro o
    rw [hΦ]
    change (LinearMap.range D1).mkQ (Submodule.Quotient.mk _) = 0
    rw [(Submodule.Quotient.mk_eq_zero _).2, map_zero]
    change _ ∈ (Ideal.span {tO}) ^ (j+1)
    rw [← mul_assoc, ← pow_succ]
    exact layer_tO_pow_mem R t x (j+1) o
  have hI := layer_span_le_ker Φ hΦt
  let i : (Fin (d-j-1) → (R ⧸ Ideal.span {t,x})) →ₗ[R] Q :=
    ∑ a : Fin (d-j-1), (Submodule.liftQ (Ideal.span {t,x})
      (LinearMap.toSpanSingleton R Q (Φ (z (-((a:ℕ):ℤ)-1)))) (hI _)) ∘ₗ LinearMap.proj a
  have hi : ∀ v : Fin (d-j-1) → R, i (fun a => Ideal.Quotient.mk _ (v a)) =
      Φ (∑ a, v a • z (-((a:ℕ):ℤ)-1)) := by
    intro v
    simp only [i, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum,
      map_smul]
    rfl
  have hmono : ∀ ℓ : ℤ, Φ (z ℓ) ∈ LinearMap.range i := by
    refine layer_slope_pow_mem beta d j Φ _ z hznat hzadd hz1 hinv hxO hbeta
      (fun o w h => by rw [hΦ, h, hψD]) fun a har =>
        window_mem_range i Φ (fun b : Fin (d-j-1) => z (-((b:ℕ):ℤ)-1)) hi ⟨a, har⟩
  exact ⟨i, hi, layer_map_mem_of_slope_pows Φ _ z hznat hzadd hz0 hmono⟩

/-- Exactness half of `actual_negative_layer_coker_exact`: a map whose range consists of exactly
the classes of `t^j o` is exact at the level-`(j + 1)` cokernel. -/
private theorem layer_coker_exact_of_range (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ) (hnext : cechInputLattice R t x (j + 1) ≤
      (cechOutputLattice R t x (j + 1)).comap (fullCechDifferential R t x beta d))
    (hnow : cechInputLattice R t x j ≤
      (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d))
    (hcomm : (cechOutputReduction R t x j).comp
      (finiteCechDifferential R t x beta d (j + 1) hnext) =
      (finiteCechDifferential R t x beta d j hnow).comp (cechInputReduction R t x j))
    {M : Type} [AddCommGroup M] [Module R M] (i : M →ₗ[R] (CechLevelOutput R t x (j + 1) ⧸
      LinearMap.range (finiteCechDifferential R t x beta d (j + 1) hnext)))
    (hall : ∀ o : BlowupOverlap R t x,
      (LinearMap.range (finiteCechDifferential R t x beta d (j + 1) hnext)).mkQ
        ((cechOutputLattice R t x (j + 1)).mkQ
          (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ^ j * o)) ∈
        LinearMap.range i)
    (hi0 : ∀ v, ∃ o : BlowupOverlap R t x,
      i v = (LinearMap.range (finiteCechDifferential R t x beta d (j + 1) hnext)).mkQ
        ((cechOutputLattice R t x (j + 1)).mkQ
          (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ^ j * o))) :
    Function.Exact i (twoTermCokerMap (finiteCechDifferential R t x beta d (j + 1) hnext)
      (finiteCechDifferential R t x beta d j hnow) (cechInputReduction R t x j)
      (cechOutputReduction R t x j) hcomm) := by
  intro y
  refine ⟨fun hy => ?_, ?_⟩
  swap
  · rintro ⟨v, rfl⟩
    obtain ⟨o, ho⟩ := hi0 v
    rw [ho]
    refine (two_term_coker_map_representative R _ _ _ _ _ _ _ _ hcomm _).trans ?_
    change (LinearMap.range _).mkQ (Submodule.Quotient.mk (p := cechOutputLattice R t x j)
      (_ ^ j * o)) = 0
    rw [(Submodule.Quotient.mk_eq_zero _).2, map_zero]
    exact layer_tO_pow_mem R t x j o
  let ψ := layerCokerProj R t x beta d j hnext
  have hψD : ∀ w, ψ (fullCechDifferential R t x beta d w) = 0 := fun w =>
    (Submodule.Quotient.mk_eq_zero _).2 ⟨Submodule.Quotient.mk w, rfl⟩
  obtain ⟨y1, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨y0, rfl⟩ := Submodule.Quotient.mk_surjective _ y1
  have hred : twoTermCokerMap (finiteCechDifferential R t x beta d (j + 1) hnext)
      (finiteCechDifferential R t x beta d j hnow) (cechInputReduction R t x j)
      (cechOutputReduction R t x j) hcomm (ψ y0) =
      (LinearMap.range (finiteCechDifferential R t x beta d j hnow)).mkQ
        (Submodule.Quotient.mk y0) :=
    two_term_coker_map_representative R _ _ _ _ _ _ _ _ hcomm _
  change twoTermCokerMap _ _ _ _ hcomm (ψ y0) = 0 at hy
  rw [hred, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨q, hq⟩ := hy
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change Submodule.Quotient.mk (fullCechDifferential R t x beta d w) =
    Submodule.Quotient.mk y0 at hq
  rw [Submodule.Quotient.eq] at hq
  change _ ∈ (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
    (chartBase R t x t)}) ^ j at hq
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hq
  obtain ⟨o, ho⟩ := hq
  obtain ⟨v, hv⟩ := hall (-o)
  refine ⟨v, ?_⟩
  rw [hv]
  change ψ (_ ^ j * -o) = ψ y0
  rw [show y0 = fullCechDifferential R t x beta d w +
    (-o) * algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ^ j by
      linear_combination ho, map_add, hψD, zero_add, mul_comm]

/-- In the negative range `j < d`, the reduction map between the cokernels at levels `j + 1` and `j`
has kernel the image of an injection from `(R ⧸ (t, x))^(d - j - 1)`. -/
theorem actual_negative_layer_coker_exact (R : Type) [CommRing R] (t x : R) (hreg :
    RegularParameterPair R t x) (beta : BlowupRestriction R t x) (hregSwap : RegularParameterPair R
    x t) (d j : ℕ) (hj : j < d) (hnext : cechInputLattice R t x (j + 1) ≤
    (cechOutputLattice R t x (j + 1)).comap (fullCechDifferential R t x beta d)) (hnow :
    cechInputLattice R t x j ≤
    (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d)) (hcomm :
    (cechOutputReduction R t x j).comp (finiteCechDifferential R t x beta d (j + 1) hnext) =
    (finiteCechDifferential R t x beta d j hnow).comp (cechInputReduction R t x j)) :
    ∃ i : (Fin (d-j-1) → (R ⧸ Ideal.span {t,x})) →ₗ[R] (CechLevelOutput R t x (j+1) ⧸
      LinearMap.range (finiteCechDifferential R t x beta d (j+1) hnext)), Function.Injective i ∧
      Function.Exact i (twoTermCokerMap (finiteCechDifferential R t x beta d (j+1) hnext)
      (finiteCechDifferential R t x beta d j hnow) (cechInputReduction R t x j)
      (cechOutputReduction R t x j) hcomm) := by
  -- Strategy: `i` sends `v` to the class of `tO ^ j * Σ v a • z (-a - 1)`; injectivity is the
  -- vanishing of Laurent window coefficients, exactness the description of the layer by windows.
  set D := fullCechDifferential R t x beta d with hD
  set D1 := finiteCechDifferential R t x beta d (j+1) hnext with hD1
  set D0 := finiteCechDifferential R t x beta d j hnow with hD0
  obtain ⟨i, hi, hall⟩ := exists_layer_window_map R t x beta d j hnext
  set tO := algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) with htO
  have hxO := layer_xO_eq R t x
  have hinv := layer_invSelf_pow R t x
  have hznat : ∀ n : ℕ,
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x)) ^ n =
      selfZPow (chartSlope R t x) (BlowupOverlap R t x) n := layer_slope_pow R t x
  have hz1 := layer_z_nat R t x
  have hzadd : ∀ a b : ℤ, selfZPow (chartSlope R t x) (BlowupOverlap R t x) (a + b) =
      selfZPow (chartSlope R t x) (BlowupOverlap R t x) a *
        selfZPow (chartSlope R t x) (BlowupOverlap R t x) b :=
    fun a b => selfZPow_add _ _
  obtain ⟨L, hL⟩ := overlap_layer_laurent_coordinates R t x hreg j
  have hbeta := layer_beta_right R t x beta
  set z := selfZPow (chartSlope R t x) (BlowupOverlap R t x)
  clear_value z
  have hmemO : ∀ (n : ℕ) (o : BlowupOverlap R t x),
      o ∈ cechOutputLattice R t x n ↔ o ∈ (Ideal.span {tO}) ^ n :=
    fun _ _ => Iff.rfl
  have hlift : ∀ v : Fin (d-j-1) → (R ⧸ Ideal.span {t,x}), ∃ v' : Fin (d-j-1) → R,
      (fun a => Ideal.Quotient.mk _ (v' a)) = v :=
    fun v => ⟨fun a => (Ideal.Quotient.mk_surjective (v a)).choose,
      funext fun a => (Ideal.Quotient.mk_surjective (v a)).choose_spec⟩
  refine ⟨i, ?_, layer_coker_exact_of_range R t x beta d j hnext hnow hcomm i hall fun v => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨v', rfl⟩ := hlift v
    rw [hi] at hv
    set G := ∑ a : Fin (d-j-1), v' a • z (-((a:ℕ):ℤ) - 1) with hG
    change (LinearMap.range D1).mkQ (Submodule.Quotient.mk (tO ^ j * G)) = 0 at hv
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hv
    obtain ⟨q, hq⟩ := hv
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change Submodule.Quotient.mk (D w) = Submodule.Quotient.mk (tO ^ j * G) at hq
    rw [Submodule.Quotient.eq, hmemO] at hq
    funext a
    exact layer_window_coeffs_eq_zero_of_mem hreg beta hregSwap d j hj hnow z hznat hzadd hz1 hinv
      hxO hbeta L hL v' w hq a
  · obtain ⟨v', rfl⟩ := hlift v
    exact ⟨_, hi v'⟩

/-- The map induced on cokernels is surjective when `u1` is surjective. -/
theorem two_term_coker_map_surjective (O : Type) [CommRing O] (A0 A1 B0 B1 : Type) [AddCommGroup A0]
    [Module O A0] [AddCommGroup A1] [Module O A1] [AddCommGroup B0] [Module O B0] [AddCommGroup B1]
    [Module O B1] (dA : A0 →ₗ[O] A1) (dB : B0 →ₗ[O] B1) (u0 : A0 →ₗ[O] B0) (u1 : A1 →ₗ[O] B1)
    (h : u1.comp dA = dB.comp u0) (hu1 : Function.Surjective u1) :
    Function.Surjective (twoTermCokerMap dA dB u0 u1 h) := by
  intro y
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range dB) y
  obtain ⟨a, rfl⟩ := hu1 b
  exact ⟨(LinearMap.range dA).mkQ a, rfl⟩

end SurfaceBlowup
