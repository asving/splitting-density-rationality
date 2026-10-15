/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.H0Comparison
import SurfaceBlowup.Blowup.StrictNormalizer

/-!
# Curve sections on the two-chart blow-up

Let `(t, x)` be a regular parameter pair of `R` and consider the two affine charts of the blow-up
of `(t, x)` together with their overlap. This file studies the lattices of curve sections cut out
by a compatible system of glued generators: it identifies their pullbacks to the surface, proves
that the layer-by-layer reduction maps are surjective (via a Laurent-polynomial description of the
exceptional layers of the overlap), constructs glued generators from compatible chart generators,
and establishes the basic transversality and finiteness properties of two-chart curve data.

## Main results

* `SurfaceBlowup.surface_to_curve_quotient_kernel`: a surface function lies in the level-`j` curve
  lattice iff it lies in `(f) + (t, x)^j`.
* `SurfaceBlowup.two_chart_layer_correction`: every element of the `j`-th exceptional layer of the
  overlap is a twisted Čech coboundary modulo the next layer.
* `SurfaceBlowup.curve_limit_level_map_surjective`: the projection from the curve order limit to
  each level is surjective.
* `SurfaceBlowup.glued_generators_exist`: compatible chart generators glue to glued generators.
* `SurfaceBlowup.mul_injective_quotient_transport`,
  `SurfaceBlowup.exists_pow_le_span_pair_transport`: transversality and finite contact transport
  along a ring isomorphism sending the exceptional parameter to a unit multiple of another.
* `SurfaceBlowup.strict_transform_equation_of_kernels`: the chart-independent strict-transform
  equation `f = eᵈ · g · unit` at a point of finite support.
* `SurfaceBlowup.two_chart_left_data_transverse_finite`,
  `SurfaceBlowup.two_chart_right_data_transverse_finite`: transversality and finiteness of the local
  data of two-chart curve data at the points of the two charts.

Provenance: `Thm_SurfaceBlowupV2_{surface_to_curve_quotient_kernel,
parent_ideal_unique_of_level_lattice, surface_to_curve_limit_kernel, two_chart_layer_correction,
curve_sections_reduction_surjective, curve_limit_level_map_surjective,
two_chart_additive_approximation, curve_sections_cover_overlap, two_chart_layer_correction_positive,
glued_generators_step, glued_generators_exist, two_chart_left_data_transverse_finite,
two_chart_left_points_maximal, strict_transform_left_point_equation,
two_chart_right_data_transverse_finite}` (the node `glued_generators_step` is the private
`glued_generators_succ` here).
-/

namespace SurfaceBlowup

/-! ### Transport between the charts and the overlap -/

section Transport

variable {R : Type} [CommRing R] {t x : R}

/-- The right chart map sends `x` to `e · z` on the overlap. -/
theorem beta_right_chartBase_self (beta : BlowupRestriction R t x) :
    beta.right (chartBase R x t x) = overlapException R t x * overlapSlope R t x := by
  rw [beta_right_chartBase, ← blowup_chart_relation, map_mul]
  rfl

private theorem algebraMap_mem_overlap_pow (j : ℕ) (a : BlowupChart R t x)
    (ha : a ∈ (chartExceptional R t x) ^ j) :
    algebraMap (BlowupChart R t x) (BlowupOverlap R t x) a ∈
      (Ideal.span {overlapException R t x})^j := by
  have := Ideal.mem_map_of_mem (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) ha
  rwa [Ideal.map_pow, chartExceptional, Ideal.map_span, Set.image_singleton] at this

private theorem beta_right_mem_overlap_pow (beta : BlowupRestriction R t x) (j : ℕ)
    (b : BlowupChart R x t) (hb : b ∈ (chartExceptional R x t) ^ j) :
    beta.right b ∈ (Ideal.span {overlapException R t x})^j := by
  have := Ideal.mem_map_of_mem (beta.right : BlowupChart R x t →+* BlowupOverlap R t x) hb
  rw [Ideal.map_pow, chartExceptional, Ideal.map_span, Set.image_singleton] at this
  refine Ideal.pow_right_mono ?_ j this
  rw [Ideal.span_singleton_le_span_singleton]
  change _ ∣ beta.right (chartBase R x t x)
  rw [beta_right_chartBase_self]
  exact dvd_mul_right _ _

end Transport

/-! ### Curve lattices and the surface -/

private theorem algebraMap_sub_mul_mem {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) (T g a c : A) (d : ℕ) {r f s : R}
    (hyc : a * g + c = algebraMap R A r) (hs : a - T ^ d * algebraMap R A s ∈ I) (hc : c ∈ I)
    (hf : algebraMap R A f - T ^ d * g ∈ I) : algebraMap R A (r - f * s) ∈ I := by
  have : algebraMap R A (r - f * s) =
      g * (a - T ^ d * algebraMap R A s) + c -
        (algebraMap R A f - T ^ d * g) * algebraMap R A s := by
    rw [map_sub, map_mul, ← hyc]; ring
  rw [this]
  exact sub_mem (add_mem (Ideal.mul_mem_left _ _ hs) hc) (Ideal.mul_mem_right _ _ hf)

private theorem algebraMap_mem_span_sup {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) (T g : A) (d : ℕ) {f : R} (hf : algebraMap R A f - T ^ d * g ∈ I) :
    algebraMap R A f ∈ Ideal.span {g} ⊔ I := by
  rw [← sub_add_cancel (algebraMap R A f) (T ^ d * g)]
  exact add_mem (Ideal.mem_sup_right hf)
    (Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr (dvd_mul_left _ _)))

/-- A surface function `r` lies in the level-`j` curve lattice of the glued generators `G` iff
`r ∈ (f) + (t, x)^j`, where `f` is a surface function inducing `G` at every level. -/
theorem surface_to_curve_quotient_kernel (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t) (j : ℕ)
    (hregF : Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    (r : R) :
    surfaceToChartPair R t x r ∈ curveIdealLattice R t x beta G j ↔ r ∈ Ideal.span {f} ⊔
      (Ideal.span {t,x})^j := by
  have hker := surface_to_cech_kernel R t x hreg j
  have hfA := glued_function_left_chart R t x beta d G f hf j
  have hfB := glued_function_right_chart R t x beta d G f hf j
  -- kernel elements map into the input lattice
  have hlat : ∀ u : R, u ∈ (Ideal.span {t,x})^j ↔
      surfaceToChartPair R t x u ∈ cechInputLattice R t x j := by
    intro u
    rw [← hker, LinearMap.mem_ker]
    change (cechInputLattice R t x j).mkQ _ = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hin : cechInputLattice R t x j ≤ curveIdealLattice R t x beta G j := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact ⟨Ideal.mem_sup_right ha, Ideal.mem_sup_right hb⟩
  constructor
  · intro h
    obtain ⟨hA, hB⟩ := h
    change algebraMap R (BlowupChart R t x) r ∈ Ideal.span {G.left j} ⊔ _ at hA
    change algebraMap R (BlowupChart R x t) r ∈ Ideal.span {G.right j} ⊔ _ at hB
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.mp hA
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨y', hy', c', hc', hyc'⟩ := Submodule.mem_sup.mp hB
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hy'
    set alpha := algebraMap (BlowupChart R t x) (BlowupOverlap R t x) with halpha
    set Zi := IsLocalization.Away.invSelf (chartSlope R t x) (S := BlowupOverlap R t x) with hZi
    set I := (Ideal.span {overlapException R t x})^j with hI
    have hZ : overlapSlope R t x * Zi = 1 := IsLocalization.Away.mul_invSelf _
    have hZd : overlapSlope R t x ^ d * Zi ^ d = 1 := by rw [← mul_pow, hZ, one_pow]
    have h1 : alpha (a * G.left j + c) = beta.right (b * G.right j + c') := by
      rw [hyc, hyc', AlgHom.commutes, halpha, ← IsScalarTower.algebraMap_apply]
    rw [map_add, map_add, map_mul, map_mul] at h1
    have hov := G.overlap j
    have hmem : alpha (G.left j) * (alpha a - Zi ^ d * beta.right b) ∈ I := by
      have heq : alpha (G.left j) * (alpha a - Zi ^ d * beta.right b) =
          beta.right c' - alpha c - Zi ^ d * beta.right b *
            (alpha (G.left j) - overlapSlope R t x ^ d * beta.right (G.right j)) := by
        linear_combination h1 - (beta.right b * beta.right (G.right j)) * hZd
      rw [heq]
      exact sub_mem (sub_mem (beta_right_mem_overlap_pow beta j c' hc')
        (algebraMap_mem_overlap_pow j c hc)) (Ideal.mul_mem_left _ _ hov)
    have hcl : alpha a - Zi ^ d * beta.right b ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      apply hregF
      simp only [mul_zero]
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    have hle : cechInputLattice R t x j ≤
        (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d) := by
      rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩
      change alpha a₁ - Zi ^ d * beta.right b₁ ∈ I
      exact sub_mem (algebraMap_mem_overlap_pow j a₁ ha₁)
        (Ideal.mul_mem_left _ _ (beta_right_mem_overlap_pow beta j b₁ hb₁))
    obtain ⟨s, hs⟩ := twisted_kernel_from_surface R t x hreg hregSwap beta d j hle
      ((cechInputLattice R t x j).mkQ (a, b)) (by
        rw [finiteCechDifferential, Submodule.mkQ_apply, Submodule.mapQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact hcl)
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hs
    obtain ⟨hsA, hsB⟩ := hs
    refine Submodule.mem_sup.mpr ⟨f * s, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f),
      r - f * s, ?_, by ring⟩
    rw [hlat]
    exact ⟨algebraMap_sub_mul_mem _ _ _ a c d hyc hsA hc hfA,
      algebraMap_sub_mul_mem _ _ _ b c' d hyc' hsB hc' hfB⟩
  · intro h
    obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [map_add]
    refine add_mem ?_ (hin ((hlat u).mp hu))
    rw [show s * f = s • f from rfl, map_smul]
    exact Submodule.smul_mem _ _
      ⟨algebraMap_mem_span_sup _ _ _ d hfA, algebraMap_mem_span_sup _ _ _ d hfB⟩

/-- In a regular local ring, a surface function `f'` lying in every curve lattice of `G` and of
multiplicity at most `d` generates the same principal ideal as the function `f` inducing `G`. -/
theorem parent_ideal_unique_of_level_lattice (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsLocalRing R] [IsNoetherianRing R]
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hregF : ∀ j : ℕ, Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    (f' : R) (hf' : ∀ j : ℕ, surfaceToChartPair R t x f' ∈ curveIdealLattice R t x beta G j)
    (hmult : f' ∉ (Ideal.span {t,x})^(d+1)) :
    Ideal.span {f'} = Ideal.span {f} := by
  have hm : Ideal.span ({t,x} : Set R) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal inferInstance
  have h1 : f' ∈ Ideal.span {f} := by
    have := ideal_closed_noetherian_local R (Ideal.span {f})
    rw [← this, Ideal.mem_iInf]
    intro j
    rw [← hm]
    exact (surface_to_curve_quotient_kernel R t x beta d G hreg hregSwap j (hregF j) f hf f').mp
      (hf' j)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h1
  have hfd := glued_function_order R t x beta d G hreg f hf
  have hru : IsUnit r := by
    by_contra hn
    apply hmult
    rw [hm] at hfd ⊢
    have : r ∈ IsLocalRing.maximalIdeal R := by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hn
    rw [← hr, pow_succ, mul_comm]
    exact Ideal.mul_mem_mul this hfd
  obtain ⟨u, rfl⟩ := hru
  rw [← hr]
  exact principal_ideal_unit_invariance R f u

/-- If `(f)` is closed in the `(t, x)`-adic topology, the kernel of a section `σ` of the map from
the surface to the curve order limit is the principal ideal `(f)`. -/
theorem surface_to_curve_limit_kernel (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t)
    (hregF : ∀ j : ℕ, Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    (hclosed : (⨅ j : ℕ, (Ideal.span {f} ⊔ (Ideal.span {t,x})^j)) = Ideal.span {f})
    (σ : R →ₗ[R] CurveOrderLimit R t x beta G)
    (hσ : ∀ r : R, ∃ p : curveThreads R t x beta G, σ r = curveLimitMk R t x beta G p ∧ ∀ j : ℕ,
      p.val j = surfaceToChartPair R t x r) :
    LinearMap.ker σ = (Ideal.span {f} : Submodule R R) := by
  ext r
  obtain ⟨p, hp, hpj⟩ := hσ r
  have key : σ r = 0 ↔ ∀ j, r ∈ Ideal.span {f} ⊔ (Ideal.span {t,x})^j := by
    rw [hp]
    change Submodule.Quotient.mk p = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    change (∀ j ∈ (Set.univ : Set ℕ), p.val j ∈ curveIdealLattice R t x beta G j) ↔ _
    simp only [Set.mem_univ, forall_true_left]
    refine forall_congr' fun j => ?_
    rw [hpj j]
    exact surface_to_curve_quotient_kernel R t x beta d G hreg hregSwap j (hregF j) f hf r
  rw [LinearMap.mem_ker, key]
  rw [← Submodule.mem_iInf, hclosed]

/-! ### Exceptional layers of the overlap -/

private theorem principalLayerMap_apply' {A : Type} [CommRing A] (e : A) (j : ℕ) (a : A) :
    principalLayerMap A e j a = Ideal.Quotient.mk ((Ideal.span {e})^(j+1)) (a * e^j) := by
  simp [principalLayerMap, LinearMap.toSpanSingleton_apply, Algebra.smul_def]

/-- Twisted layer correction with an arbitrary integral twist `k ≥ -1 - j`: an element of the
`j`-th power of the exceptional ideal of the overlap is, modulo the `(j + 1)`-st power,
of the form `a - z^k β(b)` with `a`, `b` in the `j`-th powers of the exceptional ideals of the
charts (`z` the slope). -/
private theorem two_chart_layer_correction_zpow (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (beta : BlowupChart R x t →+* BlowupOverlap R t x)
    (hbase : ∀ r : R, beta (chartBase R x t r) =
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x r))
    (hslope : beta (chartSlope R x t) = IsLocalization.Away.invSelf (chartSlope R t x))
    (j : ℕ) (k : ℤ) (hk : -1 ≤ (j : ℤ) + k) (w : BlowupOverlap R t x)
    (hw : w ∈ (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
      (chartBase R t x t)})^j) :
    ∃ a ∈ (chartExceptional R t x)^j, ∃ b ∈ (chartExceptional R x t)^j,
      w - (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) a -
        selfZPow (chartSlope R t x) (BlowupOverlap R t x) k * beta b) ∈
      (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
        (chartBase R t x t)})^(j+1) := by
  obtain ⟨L, hL⟩ := overlap_layer_laurent_coordinates R t x hreg j
  have hP : ∀ P : Polynomial (R ⧸ Ideal.span {t, x}), ∃ a ∈ (chartExceptional R t x)^j,
      (L P.toLaurent).val = Ideal.Quotient.mk ((Ideal.span {algebraMap (BlowupChart R t x)
          (BlowupOverlap R t x) (chartBase R t x t)})^(j+1))
        (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) a) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a1, ha1, h1⟩ := hp
      obtain ⟨a2, ha2, h2⟩ := hq
      refine ⟨a1 + a2, add_mem ha1 ha2, ?_⟩
      rw [map_add, map_add, Submodule.coe_add, h1, h2, map_add, map_add]
    | monomial n c =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨chartBase R t x r * chartSlope R t x ^ n * chartBase R t x t ^ j,
        Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) j), ?_⟩
      rw [Polynomial.toLaurent_C_mul_T, hL, principalLayerMap_apply']
      simp only [map_mul, map_pow, selfZPow_natCast]
  have hQ : ∀ Q : Polynomial (R ⧸ Ideal.span {t, x}), ∃ b ∈ (chartExceptional R x t)^j,
      (L (LaurentPolynomial.T ((j : ℤ) + k) * LaurentPolynomial.invert Q.toLaurent)).val
        = Ideal.Quotient.mk ((Ideal.span {algebraMap (BlowupChart R t x)
          (BlowupOverlap R t x) (chartBase R t x t)})^(j+1))
          (selfZPow (chartSlope R t x) (BlowupOverlap R t x) k * beta b) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a1, ha1, h1⟩ := hp
      obtain ⟨a2, ha2, h2⟩ := hq
      refine ⟨a1 + a2, add_mem ha1 ha2, ?_⟩
      rw [map_add, map_add, mul_add, map_add, Submodule.coe_add, h1, h2, map_add, mul_add, map_add]
    | monomial n c =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨chartBase R x t r * chartBase R x t x ^ j * chartSlope R x t ^ n,
        Ideal.mul_mem_right _ _
          (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) j)), ?_⟩
      have hT : LaurentPolynomial.T ((j : ℤ) + k) * LaurentPolynomial.invert
          (Polynomial.toLaurent (Polynomial.monomial n (Ideal.Quotient.mk (Ideal.span {t, x}) r)))
          = LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t, x}) r)
            * LaurentPolynomial.T ((j : ℤ) + k + -(n : ℤ)) := by
        rw [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_C,
          LaurentPolynomial.invert_T, mul_left_comm, ← LaurentPolynomial.T_add]
      rw [hT, hL, principalLayerMap_apply']
      congr 1
      rw [map_mul, map_mul, map_pow, map_pow, hbase, hbase, hslope,
        ← blowup_chart_relation R t x, map_mul, selfZPow_add, selfZPow_add, selfZPow_natCast,
        invSelf_pow_eq_selfZPow]
      ring
  obtain ⟨P, Q, hF⟩ := laurent_split_nonnegative_twist (R ⧸ Ideal.span {t, x}) ((j : ℤ) + k) hk
    (L.symm ⟨Ideal.Quotient.mk ((Ideal.span {algebraMap (BlowupChart R t x)
          (BlowupOverlap R t x) (chartBase R t x t)})^(j+1)) w, by
      rw [LinearMap.mem_ker]
      unfold principalPowerReduction
      rw [AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hw⟩)
  obtain ⟨a, ha, hPa⟩ := hP P
  obtain ⟨b, hb, hQb⟩ := hQ Q
  refine ⟨a, ha, b, hb, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have := congrArg (fun F => (L F).val) hF
  simp only [LinearEquiv.apply_symm_apply, map_sub, Submodule.coe_sub] at this
  rw [hPa, hQb] at this
  rw [map_sub, this, map_sub, sub_self]

/-- Layer correction with negative twist: for `d ≤ j + 1`, every `w` in the `j`-th power of the
exceptional ideal of the overlap agrees modulo the `(j + 1)`-st power with `a - z⁻ᵈ β(b)`, where
`a`, `b` lie in the `j`-th powers of the exceptional ideals of the two charts. -/
theorem two_chart_layer_correction (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (beta : (BlowupChart R x t) →+* (BlowupOverlap R t x))
    (hbase : ∀ r : R, beta (chartBase R x t r) =
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x r))
    (hslope : beta (chartSlope R x t) = IsLocalization.Away.invSelf (chartSlope R t x)) (j d : ℕ)
    (hd : d ≤ j+1) (w : (BlowupOverlap R t x))
    (hw : w ∈
      (Ideal.span {(algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)})^j) :
    ∃ a : (BlowupChart R t x), ∃ b : (BlowupChart R x t), a ∈ (chartExceptional R t x)^j ∧ b ∈
      (chartExceptional R x t)^j ∧ w - ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a -
      (IsLocalization.Away.invSelf (chartSlope R t x))^d * beta b) ∈ (Ideal.span
      {(algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)})^(j+1) := by
  obtain ⟨a, ha, b, hb, h⟩ :=
    two_chart_layer_correction_zpow R t x hreg beta hbase hslope j (-d) (by omega) w hw
  exact ⟨a, b, ha, hb, by rwa [← invSelf_pow_eq_selfZPow] at h⟩

/-- The reduction map from the level-`(j + 1)` to the level-`j` quotient of curve sections is
surjective. -/
private theorem curve_sections_reduction_surjective (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (j : ℕ)
    (ρ : curveSectionsQuot R t x beta G (j + 1) →ₗ[R] curveSectionsQuot R t x beta G j)
    (hρ : ∀ q : curveSectionsQuot R t x beta G (j+1), ∀ p : BlowupChart R t x × BlowupChart R x t,
      (q : (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G (j+1)) =
      (curveIdealLattice R t x beta G (j+1)).mkQ p → ((ρ q : curveSectionsQuot R t x beta G j) :
      (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G j) =
      (curveIdealLattice R t x beta G j).mkQ p) :
    Function.Surjective ρ := by
  set α := algebraMap (BlowupChart R t x) (BlowupOverlap R t x) with hα
  set E : Ideal (BlowupOverlap R t x) := Ideal.span {α (chartBase R t x t)} with hE
  have hbase : ∀ r : R, beta.right.toRingHom (chartBase R x t r) = α (chartBase R t x r) :=
    beta_right_chartBase beta
  have hdiff : ∀ p : BlowupChart R t x × BlowupChart R x t,
      fullCechDifferential R t x beta 0 p = α p.1 - beta.right p.2 := by
    intro p
    change α p.1 - (IsLocalization.Away.invSelf (chartSlope R t x))^0 * beta.right p.2 = _
    simp
  rintro ⟨y, hy⟩
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
  have hp' : α p.1 - beta.right p.2 ∈ overlapCurveIdeal R t x beta G j := by
    rw [← hdiff]; exact hp
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hp'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  have hEeq : Ideal.span {overlapException R t x} = E := rfl
  rw [hEeq] at hv
  have hcompat : α (G.left j) - α (G.left (j+1)) ∈ E ^ j := by
    have := Ideal.mem_map_of_mem α (G.left_compat j)
    rw [chartExceptional, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at this
    rw [← neg_sub, ← map_sub]
    exact neg_mem this
  set w := α p.1 - beta.right p.2 - c * α (G.left (j+1)) with hw
  have hwmem : w ∈ E ^ j := by
    have : w = c * (α (G.left j) - α (G.left (j+1))) + v := by
      rw [hw, ← huv]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hcompat) hv
  obtain ⟨a₁, b₁, ha₁, hb₁, hres⟩ := two_chart_layer_correction R t x hreg beta.right.toRingHom
    hbase beta.slope j 0 (by omega) w hwmem
  simp only [pow_zero, one_mul] at hres
  set p' : BlowupChart R t x × BlowupChart R x t := (p.1 - a₁, p.2 - b₁) with hp'def
  have hp'mem : p' ∈ curveSections R t x beta G (j+1) := by
    change fullCechDifferential R t x beta 0 p' ∈ overlapCurveIdeal R t x beta G (j+1)
    rw [hdiff]
    have : α p'.1 - beta.right p'.2 = c * α (G.left (j+1)) +
        (w - (α a₁ - beta.right.toRingHom b₁)) := by
      simp only [hp'def, hw, map_sub]; change _ = _ + (_ - (_ - beta.right b₁))
      ring
    rw [this]
    exact add_mem (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
      (Submodule.mem_sup_right hres)
  refine ⟨⟨(curveIdealLattice R t x beta G (j+1)).mkQ p', Submodule.mem_map_of_mem hp'mem⟩, ?_⟩
  apply Subtype.ext
  rw [hρ _ p' rfl]
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  refine ⟨?_, ?_⟩
  · change p.1 - a₁ - p.1 ∈ leftCurveIdeal R t x beta G j
    rw [sub_sub_cancel_left]
    exact Submodule.mem_sup_right (neg_mem ha₁)
  · change p.2 - b₁ - p.2 ∈ rightCurveIdeal R t x beta G j
    rw [sub_sub_cancel_left]
    exact Submodule.mem_sup_right (neg_mem hb₁)

/-- The projection from the curve order limit to the level-`J` quotient of curve sections is
surjective. -/
theorem curve_limit_level_map_surjective (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (J : ℕ)
    (π : CurveOrderLimit R t x beta G →ₗ[R] curveSectionsQuot R t x beta G J)
    (hπ : ∀ p : curveThreads R t x beta G,
      ((π (curveLimitMk R t x beta G p) : curveSectionsQuot R t x beta G J) :
      (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G J) =
      (curveIdealLattice R t x beta G J).mkQ (p.val J)) :
    Function.Surjective π := by
  classical
  -- key lifting step
  have key : ∀ j : ℕ, ∀ a, a ∈ curveSections R t x beta G j →
      ∃ b, b ∈ curveSections R t x beta G (j+1) ∧ a - b ∈ curveIdealLattice R t x beta G j := by
    intro j a ha
    obtain ⟨ρ, hρ⟩ := curve_sections_quot_reduction_exists R t x beta d G j
    have hs := curve_sections_reduction_surjective R t x beta d G hreg j ρ hρ
    obtain ⟨q', hq'⟩ := hs ⟨(curveIdealLattice R t x beta G j).mkQ a, Submodule.mem_map_of_mem ha⟩
    obtain ⟨b, hb, hbq⟩ := Submodule.mem_map.mp q'.2
    refine ⟨b, hb, ?_⟩
    have h1 := hρ q' b hbq.symm
    rw [hq'] at h1
    have h2 : (curveIdealLattice R t x beta G j).mkQ (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h1
    exact (Submodule.Quotient.mk_eq_zero _).mp h2
  have anti : Antitone (fun j => curveSections R t x beta G j) :=
    antitone_nat_of_succ_le (fun j => (curve_lattices_antitone R t x beta d G j).2)
  intro q
  obtain ⟨a, ha, haq⟩ := Submodule.mem_map.mp q.2
  let f : ℕ → ChartPair R t x := fun n => Nat.rec a (fun n fn =>
    if h : fn ∈ curveSections R t x beta G (J+n) then Classical.choose (key (J+n) fn h) else 0) n
  have f0 : f 0 = a := rfl
  have fmem : ∀ n, f n ∈ curveSections R t x beta G (J+n) ∧
      f n - f (n+1) ∈ curveIdealLattice R t x beta G (J+n) := by
    have hs : ∀ n (h : f n ∈ curveSections R t x beta G (J+n)),
        f (n+1) = Classical.choose (key (J+n) (f n) h) := fun n h => dif_pos h
    intro n
    induction n with
    | zero => exact ⟨ha, by rw [hs 0 ha]; exact (Classical.choose_spec (key _ _ ha)).2⟩
    | succ n ih =>
      have h : f (n+1) ∈ curveSections R t x beta G (J+(n+1)) := by
        rw [hs n ih.1]; exact (Classical.choose_spec (key _ _ ih.1)).1
      exact ⟨h, by rw [hs (n+1) h]; exact (Classical.choose_spec (key _ _ h)).2⟩
  let p : ℕ → ChartPair R t x := fun j => f (j - J)
  have hp : p ∈ curveThreads R t x beta G := by
    refine ⟨?_, ?_⟩
    · intro j _
      exact anti (show j ≤ J + (j - J) by omega) (fmem (j - J)).1
    · intro j _
      change p j - LinearMap.id (p (j+1)) ∈ curveIdealLattice R t x beta G j
      simp only [LinearMap.id_apply, p]
      by_cases hj : j < J
      · rw [show j - J = 0 by omega, show j + 1 - J = 0 by omega, sub_self]
        exact Submodule.zero_mem _
      · rw [show j + 1 - J = (j - J) + 1 by omega]
        have := (fmem (j - J)).2
        rwa [show J + (j - J) = j by omega] at this
  refine ⟨curveLimitMk R t x beta G ⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  rw [hπ]
  change (curveIdealLattice R t x beta G J).mkQ (f (J - J)) = _
  rw [Nat.sub_self, f0, haq]

/-- Every element of the overlap is, modulo the `n`-th power of the exceptional ideal, a
difference `a - β(b)` of functions on the two charts. -/
private theorem two_chart_additive_approximation (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (beta : (BlowupChart R x t) →+* (BlowupOverlap R t x))
    (hbase : ∀ r : R, beta (chartBase R x t r) =
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x r))
    (hslope : beta (chartSlope R x t) = IsLocalization.Away.invSelf (chartSlope R t x)) (n : ℕ)
    (w : (BlowupOverlap R t x)) :
    ∃ a : (BlowupChart R t x), ∃ b : (BlowupChart R x t),
      w - ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a - beta b) ∈
        (Ideal.span {(algebraMap (BlowupChart R t x) (BlowupOverlap R t x))
          (chartBase R t x t)})^n := by
  induction n with
  | zero => exact ⟨0, 0, by simp⟩
  | succ n ih =>
    obtain ⟨a, b, hab⟩ := ih
    obtain ⟨c, d, -, -, hcd⟩ := two_chart_layer_correction R t x hreg beta hbase
      hslope n 0 (Nat.zero_le _) _ hab
    refine ⟨a + c, b + d, ?_⟩
    simp only [pow_zero, one_mul] at hcd
    convert hcd using 1
    rw [map_add, map_add]; ring

/-- Every multiple `G.left j * c` on the overlap is the untwisted Čech differential of a level-`j`
curve section, modulo the `j`-th power of the exceptional ideal. -/
theorem curve_sections_cover_overlap (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (j : ℕ) (c : BlowupOverlap R t x) :
    ∃ p ∈ curveSections R t x beta G j, fullCechDifferential R t x beta 0 p -
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * c ∈
      (Ideal.span {overlapException R t x})^j := by
  obtain ⟨a, b, hab⟩ := two_chart_additive_approximation R t x hreg
    (beta.right : BlowupChart R x t →+* BlowupOverlap R t x) (beta_right_chartBase beta)
    beta.slope j
    ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * c)
  have hdiff : fullCechDifferential R t x beta 0 (a, b)
      = (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a - beta.right b := by
    simp [fullCechDifferential, ringCechDifferential]
  have key : fullCechDifferential R t x beta 0 (a, b)
      - (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * c
      ∈ (Ideal.span {overlapException R t x})^j := by
    rw [hdiff]
    have := (Ideal.neg_mem_iff _).2 hab
    convert this using 1
    · rfl
    · change _ - beta.right b - _ = -(_ - (_ - beta.right b)); ring
  refine ⟨(a, b), ?_, key⟩
  change fullCechDifferential R t x beta 0 (a, b) ∈ overlapCurveIdeal R t x beta G j
  have : fullCechDifferential R t x beta 0 (a, b)
      = (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * c
        + (fullCechDifferential R t x beta 0 (a, b)
          - (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * c) := by ring
  rw [this]
  exact Ideal.add_mem _
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
    (Ideal.mem_sup_right key)

/-- Layer correction with nonnegative twist: every `w` in the `j`-th power of the exceptional ideal
of the overlap agrees modulo the `(j + 1)`-st power with `a - zᵈ β(b)`, where `a`, `b` lie in the
`j`-th powers of the exceptional ideals of the two charts. -/
private theorem two_chart_layer_correction_positive (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (hreg : RegularParameterPair R t x) (j d : ℕ)
    (w : BlowupOverlap R t x) (hw : w ∈ (Ideal.span {overlapException R t x}) ^ j) :
    ∃ a ∈ (chartExceptional R t x)^j, ∃ b ∈ (chartExceptional R x t)^j, w -
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a - (overlapSlope R t x)^d *
      beta.right b) ∈ (Ideal.span {overlapException R t x})^(j+1) := by
  obtain ⟨a, ha, b, hb, h⟩ := two_chart_layer_correction_zpow R t x hreg beta.right
    (beta_right_chartBase beta) beta.slope j d (by omega) w hw
  exact ⟨a, ha, b, hb, by rwa [selfZPow_natCast] at h⟩

/-! ### Gluing generators level by level -/

private theorem isUnit_mk_map {A C : Type} [CommRing A] [CommRing C] (f : A →+* C) (I : Ideal A)
    (J : Ideal C) (h : ∀ a ∈ I, f a ∈ J) (a : A) (ha : IsUnit (Ideal.Quotient.mk I a)) :
    IsUnit (Ideal.Quotient.mk J (f a)) :=
  ha.map (Ideal.quotientMap J f h)

private theorem injective_unit_mul_mul {Q : Type} [CommRing Q] (U g : Q) (hU : IsUnit U)
    (hg : Function.Injective (fun c : Q => g * c)) :
    Function.Injective (fun c : Q => (U * g) * c) := by
  obtain ⟨u, rfl⟩ := hU
  intro a b hab
  apply hg
  simpa [mul_assoc] using congrArg (fun y => (↑u⁻¹ : Q) * y) hab

private theorem exists_unit_eq_mul_of_span_eq {Q : Type} [CommRing Q] (g F : Q)
    (hg : Function.Injective (fun c : Q => g * c)) (h : Ideal.span {F} = Ideal.span {g}) :
    ∃ u : Qˣ, F = (u : Q) * g := by
  apply regular_principal_generators_associated Q g F
  · intro a b hab; apply hg; simpa [mul_comm] using hab
  · exact h.symm

private theorem chart_generator_step {A : Type} [CommRing A] (T : A) (j : ℕ) (hj : 1 ≤ j)
    (g g' F : A)
    (hg' : Ideal.span {Ideal.Quotient.mk ((Ideal.span {T})^j) g'} =
      Ideal.span {Ideal.Quotient.mk ((Ideal.span {T})^j) g})
    (hreg : Function.Injective (fun c : A ⧸ (Ideal.span {T})^j =>
      Ideal.Quotient.mk ((Ideal.span {T})^j) g * c))
    (hF : Ideal.span {Ideal.Quotient.mk ((Ideal.span {T})^j) F} =
      Ideal.span {Ideal.Quotient.mk ((Ideal.span {T})^j) g}) :
    ∃ w : A, IsUnit (Ideal.Quotient.mk ((Ideal.span {T})^(j+1)) w) ∧
      w * g' - F ∈ (Ideal.span {T})^j ∧
      Ideal.span {Ideal.Quotient.mk ((Ideal.span {T})^(j+1)) (w * g')} =
        Ideal.span {Ideal.Quotient.mk ((Ideal.span {T})^(j+1)) g'} := by
  obtain ⟨u1, hu1⟩ := exists_unit_eq_mul_of_span_eq _ _ hreg hg'
  obtain ⟨u, hu⟩ := exists_unit_eq_mul_of_span_eq _ _ hreg hF
  obtain ⟨w, hwu, hw⟩ := principal_power_unit_lift A T j hj
    ((u * u1⁻¹ : _ˣ) : A ⧸ (Ideal.span {T})^j) (Units.isUnit _)
  refine ⟨w, hwu, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, map_mul, hw, hu1, hu]
    simp only [Units.val_mul]
    rw [mul_assoc, Units.inv_mul_cancel_left]
  · obtain ⟨v, hv⟩ := hwu
    rw [map_mul, ← hv]
    exact Ideal.span_singleton_mul_left_unit v.isUnit _

private theorem span_mk_mul_eq_of_mul_one_add {S : Type} [CommRing S] (I : Ideal S)
    (a' a F g : S) (h : a' * (1 + a) - 1 ∈ I)
    (hF : Ideal.span {Ideal.Quotient.mk I F} = Ideal.span {Ideal.Quotient.mk I g}) :
    Ideal.span {Ideal.Quotient.mk I (a' * F)} = Ideal.span {Ideal.Quotient.mk I g} := by
  have h1 : Ideal.Quotient.mk I a' * Ideal.Quotient.mk I (1 + a) = 1 := by
    rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact h
  rw [map_mul]
  exact (Ideal.span_singleton_mul_left_unit ⟨⟨_, _, h1, by rw [mul_comm, h1]⟩, rfl⟩ _).trans hF

private theorem glued_step_combination {S : Type} [CommRing S] (J : Ideal S) (X aF Y P v γ β : S)
    (hv : aF - v * P ∈ J) (hcd : v - 1 - (γ - β) ∈ J) (h3 : X * (1 + γ) - 1 ∈ J)
    (h4 : Y * (1 + β) - 1 ∈ J) (h5 : (v - 1) * β ∈ J) : X * aF - Y * P ∈ J := by
  have : X * aF - Y * P = X * (aF - v * P) + P * (-(X * v) * (Y * (1 + β) - 1) +
      Y * (X * (1 + γ) - 1) + X * Y * ((v - 1 - (γ - β)) + (v - 1) * β)) := by ring
  rw [this]
  refine J.add_mem (J.mul_mem_left _ hv) (J.mul_mem_left _ ?_)
  exact J.add_mem (J.add_mem (J.mul_mem_left _ h4) (J.mul_mem_left _ h3))
    (J.mul_mem_left _ (J.add_mem hcd h5))

private theorem mul_mem_pow_succ {S : Type} [CommRing S] (I : Ideal S) {j : ℕ} (hj : 1 ≤ j)
    {a b : S} (ha : a ∈ I ^ j) (hb : b ∈ I ^ j) : a * b ∈ I ^ (j + 1) := by
  have := Ideal.mul_mem_mul ha hb
  rw [← pow_add] at this
  exact Ideal.pow_le_pow_right (by omega) this

/-- For `a ∈ I^j` (`j ≥ 1`), `1 + a` is invertible modulo `I^(j+1)` with inverse `≡ 1 mod I^j`. -/
private theorem exists_inv_one_add {S : Type} [CommRing S] (I : Ideal S) {j : ℕ} (hj : 1 ≤ j)
    {a : S} (ha : a ∈ I ^ j) : ∃ a' : S, a' * (1 + a) - 1 ∈ I ^ (j + 1) ∧ a' - 1 ∈ I ^ j := by
  have hn : IsNilpotent (Ideal.Quotient.mk (I ^ (j + 1)) a) :=
    ⟨2, by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_two]; exact mul_mem_pow_succ I hj ha ha⟩
  have hu := hn.isUnit_one_add
  obtain ⟨a', ha'⟩ :=
    Ideal.Quotient.mk_surjective ((hu.unit⁻¹ : (S ⧸ I ^ (j + 1))ˣ) : S ⧸ I ^ (j + 1))
  have h1 : a' * (1 + a) - 1 ∈ I ^ (j + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha', map_add, map_one,
      hu.val_inv_mul, sub_self]
  refine ⟨a', h1, ?_⟩
  rw [show a' - 1 = (a' * (1 + a) - 1) - a' * a by ring]
  exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (Nat.le_succ j) h1) (Ideal.mul_mem_left _ _ ha)

/-- If `g` is regular modulo `I` and `F` generates the same ideal as `g` there, then a unit
multiple of `f F` is regular modulo `J` whenever `f g` is. -/
private theorem injective_mk_mul_of_span_eq {A C : Type} [CommRing A] [CommRing C] (f : A →+* C)
    (I : Ideal A) (J : Ideal C) (hIJ : ∀ a ∈ I, f a ∈ J) (g F : A) (z : C)
    (hz : IsUnit (Ideal.Quotient.mk J z))
    (hreg : Function.Injective (fun c : A ⧸ I => Ideal.Quotient.mk I g * c))
    (hF : Ideal.span {Ideal.Quotient.mk I F} = Ideal.span {Ideal.Quotient.mk I g})
    (hregJ : Function.Injective (fun c : C ⧸ J => Ideal.Quotient.mk J (f g) * c)) :
    Function.Injective (fun c : C ⧸ J => Ideal.Quotient.mk J (z * f F) * c) := by
  obtain ⟨u, hu⟩ := exists_unit_eq_mul_of_span_eq _ _ hreg hF
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u : A ⧸ I)
  have hbu : IsUnit (Ideal.Quotient.mk J (f b)) :=
    isUnit_mk_map f I J hIJ b (by rw [hb]; exact u.isUnit)
  have hdiff : F - b * g ∈ I := by rw [← Ideal.Quotient.eq, map_mul, hb, hu]
  have hdiff' := hIJ _ hdiff
  rw [map_sub, ← Ideal.Quotient.eq, map_mul] at hdiff'
  have : Ideal.Quotient.mk J (z * f F) =
      (Ideal.Quotient.mk J z * Ideal.Quotient.mk J (f b)) * Ideal.Quotient.mk J (f g) := by
    rw [map_mul, hdiff', map_mul, mul_assoc]
  rw [this]
  exact injective_unit_mul_mul _ _ (hz.mul hbu) hregJ

/-- If `p ≡ u q` modulo `J` for a unit `u` and `b`, `z` are units modulo `J`, then `a p` is
congruent modulo `J` to some multiple of `z (b q)`. -/
private theorem exists_mul_sub_mul_mem {C : Type} [CommRing C] (J : Ideal C) (a b p q z : C)
    (hb : IsUnit (Ideal.Quotient.mk J b)) (hz : IsUnit (Ideal.Quotient.mk J z))
    (u : (C ⧸ J)ˣ) (hu : Ideal.Quotient.mk J p = u * Ideal.Quotient.mk J q) :
    ∃ v : C, a * p - v * (z * (b * q)) ∈ J := by
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk J a * (u : C ⧸ J) * ((hb.unit⁻¹ : (C ⧸ J)ˣ) : C ⧸ J) *
      ((hz.unit⁻¹ : (C ⧸ J)ˣ) : C ⧸ J))
  refine ⟨v, ?_⟩
  rw [← Ideal.Quotient.eq, map_mul, map_mul, map_mul, map_mul, hu, hv]
  have e1 := hb.mul_val_inv
  have e2 := hz.mul_val_inv
  linear_combination (Ideal.Quotient.mk J a * (u : C ⧸ J) * Ideal.Quotient.mk J q) *
    (-(Ideal.Quotient.mk J z * ((hz.unit⁻¹ : (C ⧸ J)ˣ) : C ⧸ J)) * e1 - e2)

/-- One step of the gluing: chart representatives `FA`, `FB` of the level-`j` generators that agree
on the overlap modulo the `j`-th exceptional power can be corrected, modulo the `j`-th powers, to
representatives of the level-`(j + 1)` generators agreeing modulo the `(j + 1)`-st power. -/
private theorem glued_generators_succ (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (hreg : RegularParameterPair R t x) (d : ℕ)
    (gA : ℕ → BlowupChart R t x) (gB : ℕ → BlowupChart R x t)
    (hA : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA (j+1))} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA j)})
    (hB : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB (j+1))} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB j)})
    (hregA : ∀ j : ℕ, Function.Injective (fun c : BlowupChart R t x ⧸ (chartExceptional R t x)^j =>
      Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA j) * c))
    (hregBc : ∀ j : ℕ, Function.Injective (fun c : BlowupChart R x t ⧸ (chartExceptional R x t)^j =>
      Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB j) * c))
    (hoverlap : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (gA j))} =
      Ideal.span {Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j) (beta.right (gB j))})
    (hregC : ∀ j : ℕ, Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j) (beta.right (gB j)) * c))
    (j : ℕ) (hj : 1 ≤ j) (FA : BlowupChart R t x) (FB : BlowupChart R x t)
    (hIA : Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) FA} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA j)})
    (hIB : Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) FB} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB j)})
    (hIC : (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) FA - (overlapSlope R t x)^d *
      beta.right FB ∈ (Ideal.span {overlapException R t x})^j) :
    ∃ (FA' : BlowupChart R t x) (FB' : BlowupChart R x t), FA' - FA ∈ (chartExceptional R t x)^j ∧
      FB' - FB ∈ (chartExceptional R x t)^j ∧
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^(j+1)) FA'} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^(j+1)) (gA (j+1))} ∧
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^(j+1)) FB'} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^(j+1)) (gB (j+1))} ∧
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) FA' - (overlapSlope R t x)^d *
      beta.right FB' ∈ (Ideal.span {overlapException R t x})^(j+1) := by
  set α := algebraMap (BlowupChart R t x) (BlowupOverlap R t x) with hα
  set E := Ideal.span {overlapException R t x} with hE
  set Z := overlapSlope R t x with hZ
  have TA : ∀ m (a : BlowupChart R t x), a ∈ (chartExceptional R t x)^m → α a ∈ E^m :=
    algebraMap_mem_overlap_pow
  have TB : ∀ m (b : BlowupChart R x t), b ∈ (chartExceptional R x t)^m → beta.right b ∈ E^m :=
    beta_right_mem_overlap_pow beta
  have hZu : ∀ m, IsUnit (Ideal.Quotient.mk (E^m) (Z^d)) :=
    fun _ => ((IsLocalization.Away.algebraMap_isUnit _).pow d).map _
  -- normalize the level-`(j + 1)` generators on each chart
  obtain ⟨wA, hwAu, hwA, hwAI⟩ := chart_generator_step (chartBase R t x t) j hj (gA j)
    (gA (j+1)) FA (hA j) (hregA j) hIA
  obtain ⟨wB, hwBu, hwB, hwBI⟩ := chart_generator_step (chartBase R x t x) j hj (gB j)
    (gB (j+1)) FB (hB j) (hregBc j) hIB
  -- the transition unit `v` between the normalized representatives on the overlap
  obtain ⟨u2, hu2⟩ := exists_unit_eq_mul_of_span_eq _ _ (hregC (j+1)) (hoverlap (j+1))
  obtain ⟨v, hv⟩ := exists_mul_sub_mul_mem (E^(j+1)) (α wA) (beta.right wB) (α (gA (j+1)))
    (beta.right (gB (j+1))) (Z^d)
    (isUnit_mk_map beta.right.toRingHom _ _ (fun y hy => TB (j+1) y hy) wB hwBu) (hZu _) u2 hu2
  rw [← map_mul, ← map_mul] at hv
  have hv1 : v - 1 ∈ E^j := transition_unit_congruent_one R t x beta d j FA _ FB _ hwA hwB hIC
    (injective_mk_mul_of_span_eq beta.right.toRingHom _ _ (fun y hy => TB j y hy) _ FB _
      (hZu j) (hregBc j) hIB (hregC j))
    v (Ideal.pow_le_pow_right (Nat.le_succ j) hv)
  -- correct `v` by a Čech coboundary `c - d1`
  obtain ⟨c, hc, d1, hd1, hcd⟩ :=
    two_chart_layer_correction_positive R t x beta hreg j 0 (v - 1) hv1
  rw [pow_zero, one_mul] at hcd
  obtain ⟨c', hc'1, hc'2⟩ := exists_inv_one_add _ hj hc
  obtain ⟨d', hd'1, hd'2⟩ := exists_inv_one_add _ hj hd1
  refine ⟨c' * (wA * gA (j+1)), d' * (wB * gB (j+1)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [show c' * (wA * gA (j+1)) - FA = (c' - 1) * (wA * gA (j+1)) + (wA * gA (j+1) - FA) by
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc'2) hwA
  · rw [show d' * (wB * gB (j+1)) - FB = (d' - 1) * (wB * gB (j+1)) + (wB * gB (j+1) - FB) by
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hd'2) hwB
  · exact span_mk_mul_eq_of_mul_one_add _ c' c _ (gA (j+1)) hc'1 hwAI
  · exact span_mk_mul_eq_of_mul_one_add _ d' d1 _ (gB (j+1)) hd'1 hwBI
  · have h3 := TA (j+1) _ hc'1
    have h4 := TB (j+1) _ hd'1
    rw [map_sub, map_mul, map_add, map_one] at h3 h4
    rw [map_mul α c', map_mul beta.right d', mul_left_comm (Z^d)]
    exact glued_step_combination _ (α c') _ (beta.right d') _ v (α c) (beta.right d1) hv hcd h3 h4
      (mul_mem_pow_succ E hj hv1 (TB j d1 hd1))

/-- Compatible systems of chart generators `gA`, `gB` that are regular, agree on the overlap and are
normalized at level one can be replaced by glued generators generating the same ideals at every
level. -/
theorem glued_generators_exist (R : Type) [CommRing R] (t x : R) (beta : BlowupRestriction R t x)
    (hreg : RegularParameterPair R t x) (d : ℕ)
    (gA : ℕ → BlowupChart R t x) (gB : ℕ → BlowupChart R x t)
    (hA : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA (j+1))} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA j)})
    (hB : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB (j+1))} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB j)})
    (hregA : ∀ j : ℕ, Function.Injective (fun c : BlowupChart R t x ⧸ (chartExceptional R t x)^j =>
      Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA j) * c))
    (hregBc : ∀ j : ℕ, Function.Injective (fun c : BlowupChart R x t ⧸ (chartExceptional R x t)^j =>
      Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB j) * c))
    (hoverlap : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (gA j))} =
      Ideal.span {Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j) (beta.right (gB j))})
    (hregC : ∀ j : ℕ, Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j) (beta.right (gB j)) * c))
    (hnorm : ∃ u : Rˣ, (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (gA 1) - algebraMap
      R (BlowupOverlap R t x) (u : R) * ((overlapSlope R t x)^d * beta.right (gB 1)) ∈
      (Ideal.span {overlapException R t x})) :
    ∃ G : GluedGenerators R t x beta d, ∀ j : ℕ,
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA j)} ∧
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB j)} := by
  let A := BlowupChart R t x
  let B := BlowupChart R x t
  let Inv : ℕ → A × B → Prop := fun j p =>
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) p.1} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (gA j)} ∧
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) p.2} =
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (gB j)} ∧
    algebraMap (BlowupChart R t x) (BlowupOverlap R t x) p.1 - (overlapSlope R t x)^d *
      beta.right p.2 ∈ (Ideal.span {overlapException R t x})^j
  have hstep : ∀ n : ℕ, ∀ p : {p : A × B // Inv (n+1) p}, ∃ q : A × B,
      (q.1 - p.1.1 ∈ (chartExceptional R t x)^(n+1) ∧
        q.2 - p.1.2 ∈ (chartExceptional R x t)^(n+1)) ∧ Inv (n+2) q := by
    intro n p
    obtain ⟨FA', FB', h1, h2, h3⟩ := glued_generators_succ R t x beta hreg d gA gB hA hB hregA
      hregBc hoverlap hregC (n+1) (by omega) p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2
    exact ⟨(FA', FB'), ⟨h1, h2⟩, h3⟩
  obtain ⟨FA1, FB1, h1⟩ := glued_generators_level_one R t x beta d (gA 1) (gB 1) hnorm
  choose next hnext using hstep
  let seq : ∀ n : ℕ, {p : A × B // Inv (n+1) p} := fun n =>
    Nat.rec ⟨(FA1, FB1), h1⟩ (fun n p => ⟨next n p, (hnext n p).2⟩) n
  let left : ℕ → A := fun j => match j with | 0 => gA 0 | n+1 => (seq n).1.1
  let right : ℕ → B := fun j => match j with | 0 => gB 0 | n+1 => (seq n).1.2
  refine ⟨⟨left, right, ?_, ?_, ?_⟩, ?_⟩ <;> rintro (_ | n)
  · simp
  · exact (hnext n (seq n)).1.1
  · simp
  · exact (hnext n (seq n)).1.2
  · simp
  · exact (seq n).2.2.2
  · exact ⟨rfl, rfl⟩
  · exact ⟨(seq n).2.1, (seq n).2.2.1⟩

/-! ### Transport of transversality and finite contact along completion isomorphisms -/

section TransportCompletion

variable {S T : Type} [CommRing S] [CommRing T]

private theorem injective_mk_mul_iff (g e : S) :
    Function.Injective (fun a : S ⧸ Ideal.span {g} => Ideal.Quotient.mk (Ideal.span {g}) e * a) ↔
      ∀ a, e * a ∈ Ideal.span {g} → a ∈ Ideal.span {g} := by
  constructor
  · intro h a ha
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply h
    simp only [mul_zero]
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  · intro h a b hab
    induction a using Quotient.inductionOn' with | h a => ?_
    induction b using Quotient.inductionOn' with | h b => ?_
    change Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b
    change Ideal.Quotient.mk _ e * Ideal.Quotient.mk _ a =
      Ideal.Quotient.mk _ e * Ideal.Quotient.mk _ b at hab
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq] at hab
    rw [Ideal.Quotient.eq]
    apply h
    rw [mul_sub]; exact hab

/-- Transversality transports along a ring isomorphism `Θ` sending the parameter `e` to a unit
multiple of `eT`: if multiplication by `e` is injective modulo `g`, then multiplication by `eT` is
injective modulo `Θ g`. -/
theorem mul_injective_quotient_transport (Θ : S ≃+* T) {g e : S} {eT u : T} (hu : IsUnit u)
    (he : Θ e * u = eT)
    (h : Function.Injective
      (fun a : S ⧸ Ideal.span {g} => Ideal.Quotient.mk (Ideal.span {g}) e * a)) :
    Function.Injective
      (fun a : T ⧸ Ideal.span {Θ g} => Ideal.Quotient.mk (Ideal.span {Θ g}) eT * a) := by
  rw [injective_mk_mul_iff] at h ⊢
  intro b hb
  rw [← he, mul_assoc, Ideal.mem_span_singleton] at hb
  have h1 := h (Θ.symm (u * b)) (Ideal.mem_span_singleton.mpr (by simpa using map_dvd Θ.symm hb))
  rw [Ideal.mem_span_singleton, ← hu.dvd_mul_left]
  simpa using map_dvd Θ (Ideal.mem_span_singleton.mp h1)

private theorem sup_pow_le (I J : Ideal S) (j : ℕ) : (I ⊔ J) ^ j ≤ I ⊔ J ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    calc (I ⊔ J) ^ (n+1) = (I ⊔ J) * (I ⊔ J) ^ n := pow_succ' _ _
      _ ≤ (I ⊔ J) * (I ⊔ J ^ n) := Ideal.mul_mono_right ih
      _ ≤ I ⊔ J ^ (n+1) := by
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, pow_succ']
        exact sup_le (sup_le (le_sup_of_le_left Ideal.mul_le_right)
          (le_sup_of_le_left Ideal.mul_le_left))
          (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)

private theorem exists_pow_le_span_pair {M : Ideal S} {g e : S}
    (h : ∃ L, M ^ L ≤ Ideal.span {g, e ^ 1}) (j : ℕ) : ∃ L, M ^ L ≤ Ideal.span {g, e ^ j} := by
  obtain ⟨L, hL⟩ := h
  refine ⟨L * j, ?_⟩
  rw [pow_mul]
  refine (Ideal.pow_right_mono hL j).trans ?_
  rw [Ideal.span_insert, Ideal.span_insert, pow_one, ← Ideal.span_singleton_pow]
  exact sup_pow_le _ _ j

/-- Finite contact transports along a ring isomorphism `Θ` sending the parameter `e` to a unit
multiple of `eT`: if a power of `MS` lies in `(g, e)` and `MT ⊆ Θ(MS)`, then for every `j` a power
of `MT` lies in `(Θ g, eT^j)`. -/
theorem exists_pow_le_span_pair_transport (Θ : S ≃+* T) {g e : S} {eT u : T} (hu : IsUnit u)
    (he : Θ e * u = eT) {MS : Ideal S} {MT : Ideal T} (hM : MT ≤ MS.map Θ)
    (h : ∃ L, MS ^ L ≤ Ideal.span {g, e ^ 1}) (j : ℕ) :
    ∃ L, MT ^ L ≤ Ideal.span {Θ g, eT ^ j} := by
  refine exists_pow_le_span_pair ?_ j
  obtain ⟨L, hL⟩ := h
  refine ⟨L, (Ideal.pow_right_mono hM L).trans ?_⟩
  rw [← Ideal.map_pow]
  refine (Ideal.map_mono hL).trans ?_
  rw [Ideal.map_span, Set.image_pair, Ideal.span_le]
  rintro _ (rfl | rfl)
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · obtain ⟨v, rfl⟩ := hu
    have : Θ e = eT * ↑v⁻¹ := by rw [← he, mul_assoc, Units.mul_inv, mul_one]
    simp only [this, pow_one]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

end TransportCompletion

/-- The maximal ideal of `A_P` generates in the completion `(A_P)^` the extension of `P`. -/
theorem map_maximalIdeal_localCompletion {A : Type} [CommRing A] (P : Ideal A) [P.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
        (localCompletionMap (Localization.AtPrime P)) =
      P.map (completedPointMap A P) := by
  calc _ = (P.map (algebraMap A (Localization.AtPrime P))).map
          (localCompletionMap (Localization.AtPrime P)) := by
        rw [Localization.AtPrime.map_eq_maximalIdeal]
    _ = _ := by rw [Ideal.map_map]; rfl

/-- A ring isomorphism `Θ : (B_Q)^ ≃ (A_P)^` compatible with `f : A → B` carries the extension of
`f(P)` to the maximal ideal of `(A_P)^`. -/
theorem map_maximalIdeal_localCompletion_transport {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (Θ : CompletedLocalAt B Q ≃+* CompletedLocalAt A P)
    (hΘ : ∀ a, Θ (completedPointMap B Q (f a)) = completedPointMap A P a) :
    ((P.map f).map (completedPointMap B Q)).map (Θ : _ →+* _) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map (localCompletionMap _) := by
  rw [map_maximalIdeal_localCompletion, Ideal.map_map, Ideal.map_map]
  exact congrArg (Ideal.map · P) (RingHom.ext hΘ)

/-- For a ring isomorphism `Θ : (B_Q)^ ≃ (A_{f⁻¹Q})^` compatible with `f : A → B`, the maximal ideal
of `(A_{f⁻¹Q})^` is contained in the image under `Θ` of the maximal ideal of `(B_Q)^`. -/
theorem map_maximalIdeal_localCompletion_comap_le {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (Q : Ideal B) [Q.IsPrime]
    (Θ : CompletedLocalAt B Q ≃+* CompletedLocalAt A (Q.comap f))
    (hΘ : ∀ a, Θ (completedPointMap B Q (f a)) = completedPointMap A (Q.comap f) a) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime (Q.comap f))).map (localCompletionMap _) ≤
      ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).map (localCompletionMap _)).map
        (Θ : _ →+* _) := by
  rw [← map_maximalIdeal_localCompletion_transport f _ Q Θ hΘ, map_maximalIdeal_localCompletion Q]
  exact Ideal.map_mono (Ideal.map_mono Ideal.map_comap_le)

/-- Chart-independent form of the strict-transform equation: let `P` be finitely many distinct
maximal ideals of a noetherian ring `A` containing `z`, with local equations `g` of finite contact
with `z`, and let `F` be generators of the level kernels, `(F j) + (z)^j = ⋂ (g, z^j)`. If
`y ≡ z^d F j mod z^j` for every `j` and `z`, `g` form a regular sequence in `(A_P)^`, then
`y = z^d · g · unit` in `(A_P)^`. -/
theorem strict_transform_equation_of_kernels {A ι : Type} [CommRing A] [IsNoetherianRing A]
    [Finite ι] (P : ι → Ideal A) [∀ s, (P s).IsMaximal] (hP : Function.Injective P) (z : A)
    (hz : ∀ s, z ∈ P s) (g : ∀ s, CompletedLocalAt A (P s))
    (hfin : ∀ j s, ∃ L, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P s))).map
      (localCompletionMap _)) ^ L ≤ finiteLocalCurveIdeal A (P s) z (g s) j)
    (F : ℕ → A) (hF : ∀ j, Ideal.span {F j} ⊔ Ideal.span {z} ^ j =
      finiteSupportKernel A ι P (fun s => finiteLocalCurveIdeal A (P s) z (g s) j))
    (d : ℕ) (y : A) (hy : ∀ j, y - z ^ d * F j ∈ Ideal.span {z} ^ j) (s : ι)
    [IsNoetherianRing (CompletedLocalAt A (P s))]
    (hereg : Function.Injective
      (fun a : CompletedLocalAt A (P s) => completedPointMap A (P s) z * a))
    (hgreg : Function.Injective (fun a : CompletedLocalAt A (P s) ⧸
      Ideal.span {completedPointMap A (P s) z} =>
      Ideal.Quotient.mk (Ideal.span {completedPointMap A (P s) z}) (g s) * a)) :
    ∃ v : (CompletedLocalAt A (P s))ˣ, completedPointMap A (P s) y =
      completedPointMap A (P s) z ^ d * g s * (v : CompletedLocalAt A (P s)) := by
  set φ := completedPointMap A (P s)
  have he : φ z ∈ IsLocalRing.maximalIdeal (CompletedLocalAt A (P s)) := by
    have h1 : algebraMap A (Localization.AtPrime (P s)) z ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime (P s)) := by
      rw [Localization.AtPrime.map_eq_maximalIdeal.symm]
      exact Ideal.mem_map_of_mem _ (hz s)
    have := AdicCompletion.algebraMap_isLocalHom_of_fg (R := Localization.AtPrime (P s))
      (IsNoetherian.noetherian _)
    have : IsLocalHom (localCompletionMap (Localization.AtPrime (P s))) := this
    exact map_nonunit (localCompletionMap (Localization.AtPrime (P s))) _ h1
  refine strict_transform_equation_from_levels _ (φ z) (g s) he hereg hgreg d (fun j => φ (F j))
    (fun j => ?_) _ (fun j => ?_)
  · have hrec := finite_support_completion_recovers A ι P hP (fun s => (hfin j s).choose) _
      (fun s => (hfin j s).choose_spec) s
    rw [← hF, Ideal.map_sup, Ideal.map_span, Ideal.map_pow, Ideal.map_span, Set.image_singleton,
      Set.image_singleton, Ideal.span_singleton_pow, finiteLocalCurveIdeal] at hrec
    rw [← hrec, Ideal.span_insert]
  · have := Ideal.mem_map_of_mem φ (hy j)
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow] at this
    simpa [map_sub, map_mul, map_pow] using this

/-! ### Two-chart curve data -/

/-- At every point of the first chart in two-chart curve data, the exceptional parameter is a
nonzerodivisor modulo the local equation, and some power of the maximal ideal of the completion lies
in the level-`j` local curve ideal. -/
theorem two_chart_left_data_transverse_finite (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta) (j : ℕ) :
    (∀ s, Function.Injective (fun a : CompletedLocalAt (BlowupChart R t x) (leftPoint D s) ⧸
      Ideal.span {leftData D s} => Ideal.Quotient.mk (Ideal.span {leftData D s})
      (completedPointMap (BlowupChart R t x) (leftPoint D s) (chartBase R t x t)) * a)) ∧ ∀ s, ∃ L :
      ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime (leftPoint D s))).map (localCompletionMap
      (Localization.AtPrime (leftPoint D s))))^L ≤ leftLevelIdeal D j s := by
  have he (i : D.ι) : D.leftIso i (completedPointMap _ (D.Q i) (overlapException R t x)) * 1 =
      completedPointMap _ (leftPoint D (.inl i)) (chartBase R t x t) :=
    (mul_one _).trans (D.leftIso_compat i _)
  constructor
  · rintro (i | k)
    · exact mul_injective_quotient_transport (D.leftIso i) isUnit_one (he i) (D.transverse i)
    · exact D.transverse0 k
  · rintro (i | k)
    · exact exists_pow_le_span_pair_transport (D.leftIso i) isUnit_one (he i)
        (map_maximalIdeal_localCompletion_comap_le _ _ _ (D.leftIso_compat i)) (D.finite i) j
    · exact exists_pow_le_span_pair (D.finite0 k) j

/-- The points of the first chart in two-chart curve data are distinct maximal ideals lying on the
exceptional divisor. -/
theorem two_chart_left_points_maximal (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] :
    (∀ s, (leftPoint D s).IsMaximal) ∧ Function.Injective (leftPoint D) ∧ ∀ s, chartBase R t x t ∈
      leftPoint D s := by
  have key : ∀ i, ((D.Q i).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))).IsMaximal ∧
      chartSlope R t x ∉ (D.Q i).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) ∧
      chartBase R t x t ∈ (D.Q i).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) :=
    fun i => overlap_exceptional_point_comap_maximal R t x (D.Q i) (D.onE i)
  refine ⟨?_, ?_, ?_⟩
  · rintro (i | k)
    · exact (key i).1
    · exact D.maximal0 k
  · rintro (i | i) (j | j) h
    · congr 1
      apply D.inj
      have h' : (D.Q i).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) =
          (D.Q j).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) := h
      have := congrArg (Ideal.map (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) h'
      rwa [IsLocalization.map_under (Submonoid.powers (chartSlope R t x)),
        IsLocalization.map_under (Submonoid.powers (chartSlope R t x))] at this
    · exfalso
      have h' : (D.Q i).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) = D.P0 j := h
      exact (key i).2.1 (h' ▸ D.slope0 j)
    · exfalso
      have h' : D.P0 i = (D.Q j).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) := h
      exact (key j).2.1 (h' ▸ D.slope0 i)
    · congr 1
      exact D.inj0 h
  · rintro (i | k)
    · exact (key i).2.2
    · exact D.onE0 k

/-- At a point of the first chart, the pullback of the surface function `f` factors in the completed
local ring as `tᵈ · (local equation) · unit`. -/
theorem strict_transform_left_point_equation (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x)
    (D : TwoChartCurveData R t x beta) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hG : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} =
      leftLevelKernel D j ∧ Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)}
      = rightLevelKernel D j)
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    (s : D.ι ⊕ D.ι0) [IsNoetherianRing (CompletedLocalAt (BlowupChart R t x) (leftPoint D s))]
    (hereg : Function.Injective (fun a : CompletedLocalAt (BlowupChart R t x) (leftPoint D s) =>
      completedPointMap (BlowupChart R t x) (leftPoint D s) (chartBase R t x t) * a))
    (hgreg : Function.Injective (fun a : CompletedLocalAt (BlowupChart R t x) (leftPoint D s) ⧸
      Ideal.span {completedPointMap (BlowupChart R t x) (leftPoint D s) (chartBase R t x t)} =>
      Ideal.Quotient.mk
      (Ideal.span {completedPointMap (BlowupChart R t x) (leftPoint D s) (chartBase R t x t)})
      (leftData D s) * a)) :
    ∃ v : (CompletedLocalAt (BlowupChart R t x) (leftPoint D s))ˣ, completedPointMap
      (BlowupChart R t x) (leftPoint D s) (algebraMap R (BlowupChart R t x) f) =
      (completedPointMap (BlowupChart R t x) (leftPoint D s) (chartBase R t x t))^d * leftData D s *
      (v : CompletedLocalAt (BlowupChart R t x) (leftPoint D s)) := by
  obtain ⟨hmax, hinj, hmem⟩ := two_chart_left_points_maximal R t x beta D
  have : ∀ s, (leftPoint D s).IsMaximal := hmax
  exact strict_transform_equation_of_kernels (leftPoint D) hinj _ hmem (leftData D)
    (fun j => (two_chart_left_data_transverse_finite R t x beta D j).2) G.left
    (fun j => (curve_ideal_lattice_eq_kernels R t x beta D d G hG j).1) d _
    (glued_function_left_chart R t x beta d G f hf) s hereg hgreg

/-- At every point of the second chart in two-chart curve data, the exceptional parameter is a
nonzerodivisor modulo the local equation, and some power of the maximal ideal of the completion lies
in the level-`j` local curve ideal. -/
theorem two_chart_right_data_transverse_finite (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta) (j : ℕ) :
    (∀ s, Function.Injective (fun a : CompletedLocalAt (BlowupChart R x t) (rightPoint D s) ⧸
      Ideal.span {rightData D s} => Ideal.Quotient.mk (Ideal.span {rightData D s})
      (completedPointMap (BlowupChart R x t) (rightPoint D s) (chartBase R x t x)) * a)) ∧ ∀ s, ∃ L
      : ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime (rightPoint D s))).map
      (localCompletionMap (Localization.AtPrime (rightPoint D s))))^L ≤ rightLevelIdeal D j s := by
  -- `x = t · (x/t)` on the overlap, and the slope `x/t` is a unit there
  have hu (i : D.ι) : IsUnit (D.rightIso i (completedPointMap _ (D.Q i) (overlapSlope R t x))) :=
    ((IsLocalization.Away.algebraMap_isUnit _).map _).map _
  have he (i : D.ι) : D.rightIso i (completedPointMap _ (D.Q i) (overlapException R t x)) *
      D.rightIso i (completedPointMap _ (D.Q i) (overlapSlope R t x)) =
      completedPointMap _ (rightPoint D (.inl i)) (chartBase R x t x) := by
    rw [← map_mul, ← map_mul, ← beta_right_chartBase_self]
    exact D.rightIso_compat i _
  constructor
  · rintro (i | l)
    · exact mul_injective_quotient_transport (D.rightIso i) (hu i) (he i) (D.transverse i)
    · exact D.transverseinf l
  · rintro (i | l)
    · exact exists_pow_le_span_pair_transport (D.rightIso i) (hu i) (he i)
        (map_maximalIdeal_localCompletion_comap_le _ _ _ (D.rightIso_compat i)) (D.finite i) j
    · exact exists_pow_le_span_pair (D.finiteinf l) j

end SurfaceBlowup
