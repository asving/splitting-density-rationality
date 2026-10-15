/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.ExceptionalLayers
import SurfaceBlowup.Surfaces.ChartCompletions

/-!
# Closed points on the blow-up of the concrete surface

We classify the closed points of the exceptional divisor of the blow-up of the concrete surface
and identify the completed local rings there: at points of the `t`-chart they are concrete
surfaces (over `O` or an unramified extension), and at the point at infinity of the `x`-chart
the strict transform of a curve meets the exceptional divisor transversally.

## Main results

* `concrete_chart_point_span_form`: classification of closed points of the `t`-chart.
* `concrete_left_point_completion_is_surface`, `concrete_left_point_completion_instances`,
  `concrete_left_point_exceptional_regular`.
* `concrete_infinity_point_completion`, `concrete_infinity_strict_transform_transverse_finite`.

Provenance: `concrete_chart_point_span_form`, `concrete_left_point_completion_{is_surface,
instances}`, `concrete_left_point_exceptional_regular`, `concrete_infinity_point_completion`,
`concrete_infinity_strict_transform_transverse_finite`.
-/


namespace SurfaceBlowup

/-! ### Notation

Local notations for the charts of the blow-up of `R = ConcreteSurface O pi u a b` at its
closed point, taking the surface data as explicit arguments. -/

/-- The `t`-chart `R[x/t]` of the blow-up of the concrete surface `R` at `(t, x)`. -/
local notation:max "tChart" O:max pi:max u:max a:max b:max =>
  BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)

/-- The structure map `R → R[x/t]` of the `t`-chart. -/
local notation:max "tBase" O:max pi:max u:max a:max b:max =>
  chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)

/-- The slope `x/t` in the `t`-chart. -/
local notation:max "tSlope" O:max pi:max u:max a:max b:max =>
  chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)

/-- The `x`-chart `R[t/x]` of the blow-up of the concrete surface `R` at `(t, x)`. -/
local notation:max "xChart" O:max pi:max u:max a:max b:max =>
  BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)

/-- The structure map `R → R[t/x]` of the `x`-chart. -/
local notation:max "xBase" O:max pi:max u:max a:max b:max =>
  chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)

/-- The slope `t/x` in the `x`-chart. -/
local notation:max "xSlope" O:max pi:max u:max a:max b:max =>
  chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)

/-- A closed point `P` of `R[x/t]` on the exceptional divisor, cut out on the exceptional line
by an irreducible `φ`, equals `(t, Φ₀(x/t))` for every lift `Φ₀` of `φ` along `O → R/(t, x)`. -/
private theorem chart_point_eq_span_of_lift (O : Type) [CommRing O] (R : Type) [CommRing R]
    [Algebra O R] (t x : R) [(Ideal.span ({t, x} : Set R)).IsMaximal]
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial
      (R ⧸ Ideal.span ({t,x} : Set R)))
    (he : ∀ r : R, e (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.span ({t,x} : Set R)) r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X)
    (P : Ideal (BlowupChart R t x)) [P.IsMaximal] (hP : chartBase R t x t ∈ P)
    (φ : Polynomial (R ⧸ Ideal.span ({t,x} : Set R))) (hirr : Irreducible φ)
    (hmap : (P.map (Ideal.Quotient.mk (chartExceptional R t x))).map e = Ideal.span {φ})
    (Φ₀ : Polynomial O)
    (hΦ₀ : Φ₀.map ((Ideal.Quotient.mk (Ideal.span ({t, x} : Set R))).comp (algebraMap O R)) = φ) :
    P = Ideal.span {chartBase R t x t,
      Polynomial.eval₂ ((chartBase R t x).comp (algebraMap O R)) (chartSlope R t x) Φ₀} := by
  set ρ : O →+* R ⧸ Ideal.span ({t, x} : Set R) :=
    (Ideal.Quotient.mk (Ideal.span ({t, x} : Set R))).comp (algebraMap O R) with hρdef
  set F := Polynomial.eval₂ ((chartBase R t x).comp (algebraMap O R)) (chartSlope R t x) Φ₀
  have hF : e (Ideal.Quotient.mk (chartExceptional R t x) F) = φ := by
    rw [← hΦ₀]
    have : ((e : _ →+* _).comp ((Ideal.Quotient.mk (chartExceptional R t x)).comp
        (Polynomial.eval₂RingHom ((chartBase R t x).comp (algebraMap O R)) (chartSlope R t x))))
        = Polynomial.mapRingHom ρ := by
      apply Polynomial.ringHom_ext
      · intro c; simp [he, ρ]
      · simp [heZ]
    exact congrArg (fun g => g Φ₀) this
  have hFP : F ∈ P := by
    have h1 : φ ∈ (P.map (Ideal.Quotient.mk (chartExceptional R t x))).map e := by
      rw [hmap]; exact Ideal.subset_span rfl
    rw [← hF] at h1
    rw [Ideal.mem_map_of_equiv] at h1
    obtain ⟨y, hy, hye⟩ := h1
    rw [e.injective hye] at hy
    rwa [Ideal.mem_quotient_iff_mem] at hy
    rw [chartExceptional, Ideal.span_le]
    simpa using hP
  have hirr' : Irreducible ((Φ₀.map (algebraMap O R)).map
      (Ideal.Quotient.mk (Ideal.span ({t, x} : Set R)))) := by
    rw [Polynomial.map_map, ← hρdef, hΦ₀]; exact hirr
  let _ : Field (BlowupChart R t x ⧸ P) := Ideal.Quotient.field P
  obtain ⟨-, hspan⟩ := chart_nonrational_point_span_eq_comap R t x (Φ₀.map (algebraMap O R)) hirr'
    (BlowupChart R t x ⧸ P) (Ideal.Quotient.mk P)
    (by rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
        exact hP)
    (by
      rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem,
        Polynomial.eval₂_map]; exact hFP)
  rw [Polynomial.eval₂_map] at hspan
  rw [hspan, IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- Classification of the closed points on the exceptional divisor of a chart `R[x/t]` with
residue field that of `O`: the origin, a rational point `x/t = α` with `α` a unit, or a
non-rational point cut out by an unramified lift `Φ` of degree at least `2`. -/
private theorem chart_point_trichotomy (O : Type) [CommRing O] [IsLocalRing O] (R : Type)
    [CommRing R] [Algebra O R] (t x : R) [(Ideal.span ({t, x} : Set R)).IsMaximal]
    (ψ : (R ⧸ Ideal.span ({t, x} : Set R)) ≃+* IsLocalRing.ResidueField O)
    (hψρ : ∀ c : O, ψ (Ideal.Quotient.mk _ (algebraMap O R c)) = IsLocalRing.residue O c)
    (P : Ideal (BlowupChart R t x)) [P.IsMaximal] (hP : chartBase R t x t ∈ P) :
    P = Ideal.span {chartBase R t x t, chartSlope R t x} ∨
    (∃ α : O, IsUnit α ∧ P = Ideal.span
        {chartBase R t x t, chartSlope R t x - chartBase R t x (algebraMap O R α)}) ∨
    (∃ Φ : Polynomial O, IsUnramifiedLift O Φ ∧ 2 ≤ Φ.natDegree ∧ P = Ideal.span {chartBase R t x t,
      Polynomial.eval₂ ((chartBase R t x).comp (algebraMap O R)) (chartSlope R t x) Φ}) := by
  obtain ⟨e, he, heZ⟩ := exceptional_line_equiv_chart_exceptional R t x
  obtain ⟨φ, hmon, hirr, hmap, -, -⟩ :=
    blowup_chart_exceptional_point_polynomial R t x e he heZ P hP
  set ρ : O →+* R ⧸ Ideal.span ({t, x} : Set R) :=
    (Ideal.Quotient.mk (Ideal.span ({t, x} : Set R))).comp (algebraMap O R) with hρdef
  have hρ : ∀ c : O, ρ c = ψ.symm (IsLocalRing.residue O c) := fun c => by
    rw [← hψρ, RingEquiv.symm_apply_apply]; rfl
  have hρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (ψ y)
    exact ⟨c, by rw [hρ, hc, RingEquiv.symm_apply_apply]⟩
  have key (Φ₀ : Polynomial O) (hΦ₀ : Φ₀.map ρ = φ) :=
    chart_point_eq_span_of_lift O R t x e he heZ P hP φ hirr hmap Φ₀ hΦ₀
  have hdeg : φ.natDegree ≠ 0 := by
    intro h
    rw [hmon.natDegree_eq_zero] at h
    exact hirr.not_isUnit (h ▸ isUnit_one)
  by_cases hX : φ = Polynomial.X
  · left
    simpa using key Polynomial.X (by simp [hX])
  by_cases h1 : φ.natDegree = 1
  · right; left
    have hφ := hmon.eq_X_add_C h1
    set c := φ.coeff 0
    have hc : c ≠ 0 := fun hc => hX (by rw [hφ, hc]; simp)
    obtain ⟨α, hα⟩ := hρsurj (-c)
    refine ⟨α, ?_, ?_⟩
    · by_contra hu
      have : IsLocalRing.residue O α = 0 := (IsLocalRing.residue_eq_zero_iff α).2
        ((IsLocalRing.mem_maximalIdeal α).2 hu)
      apply hc
      rw [← neg_eq_zero, ← hα, hρ, this, map_zero]
    · have := key (Polynomial.X - Polynomial.C α) (by rw [hφ]; simp [hα, sub_eq_add_neg])
      simpa using this
  · right; right
    obtain ⟨Φ₀, hmapΦ, hdegΦ, hmonΦ⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic (Polynomial.mem_lifts_of_surjective hρsurj φ) hmon
    refine ⟨Φ₀, ⟨hmonΦ, ?_⟩, by omega, key Φ₀ hmapΦ⟩
    have hres : residuePoly O Φ₀ = (Polynomial.mapEquiv ψ) φ := by
      rw [← hmapΦ]
      simp only [residuePoly, Polynomial.mapEquiv_apply, Polynomial.map_map]
      congr 1
      ext c
      simp [hρ]
    rw [hres]
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv ψ).toMulEquiv).2 hirr

/-- The closed points of the `t`-chart of the concrete surface lying over the closed point are the
origin, rational points `(t, x/t - α)` with `α` a unit, and non-rational points `(t, Φ(x/t))`. -/
theorem concrete_chart_point_span_form (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (P : Ideal (tChart O pi u a b)) [P.IsMaximal]
    (hP : tBase O pi u a b (surfaceT O pi u a b) ∈ P) :
    P = Ideal.span {tBase O pi u a b (surfaceT O pi u a b), tSlope O pi u a b} ∨
      (∃ α : O, IsUnit α ∧ P = Ideal.span {tBase O pi u a b (surfaceT O pi u a b),
        tSlope O pi u a b - tBase O pi u a b (algebraMap O (ConcreteSurface O pi u a b) α)}) ∨
      (∃ Φ : Polynomial O, IsUnramifiedLift O Φ ∧ 2 ≤ Φ.natDegree ∧
        P = Ideal.span {tBase O pi u a b (surfaceT O pi u a b),
          Polynomial.eval₂ ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b)))
            (tSlope O pi u a b) Φ}) := by
  obtain ⟨ψ, hψ⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  have : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} :
      Set (ConcreteSurface O pi u a b))).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  exact chart_point_trichotomy O (ConcreteSurface O pi u a b) _ _ ψ
    (fun c ↦ hψ (MvPowerSeries.C c)) P hP

/-- The completion of the `t`-chart at any closed point over the closed point of the concrete
surface is again a concrete surface over a complete discrete valuation ring, with `t ↦ t'`. -/
theorem concrete_left_point_completion_is_surface (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (P : Ideal (tChart O pi u a b)) [P.IsMaximal] [P.IsPrime]
    (hP : tBase O pi u a b (surfaceT O pi u a b) ∈ P) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O')
      (_ : Finite (IsLocalRing.ResidueField O')) (pi' : O') (u' : (TwoSeries O')ˣ) (a' b' : ℕ),
      Irreducible pi' ∧ 0 < a' ∧
      ∃ Eq : CompletedLocalAt (tChart O pi u a b) P ≃+* ConcreteSurface O' pi' u' a' b',
      Eq (completedPointMap (tChart O pi u a b) P (tBase O pi u a b (surfaceT O pi u a b))) =
          surfaceT O' pi' u' a' b' := by
  have hT : ∀ (R : Type) [CommRing R] (α : R), chartSubst R α (axisT R) = axisT R :=
    fun R _ α => (chartSubst_apply_generators R α).2.1
  rcases concrete_chart_point_span_form O pi hpi u a b ha P hP with h | ⟨α, hα, h⟩ | ⟨Φ, hΦ, h2, h⟩
  · obtain ⟨E, hE, -⟩ := t_chart_origin_completion_equiv O pi hpi u a b ha P h
    refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, pi,
          substUnit O 0 u, a + b, b, hpi, by omega, E, (hE _).trans (congrArg _ (hT O 0))⟩
  · obtain ⟨E, hE, -⟩ := t_chart_unit_point_completion_equiv O pi hpi u a b ha α hα P h
    refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, pi, _,
          a + b, 0, hpi, by omega, E, (hE _).trans (congrArg _ (hT O α))⟩
  · have hθ := unramified_root_isUnit_of_two_le_natDegree O Φ hΦ h2
    obtain ⟨E, hE, -⟩ := t_chart_nonrational_point_completion_equiv O pi hpi u a b ha Φ hΦ hθ P h
    obtain ⟨hd, hl, hdvr, -, hirr, hc, hf, -⟩ := unramified_is_dvr O Φ hΦ
    refine ⟨AdjoinRoot Φ, inferInstance, hd, hdvr, hc, hf, algebraMap O (AdjoinRoot Φ) pi, _, a + b,
          0, hirr pi hpi, by omega, E, ?_⟩
    have hm : MvPowerSeries.map (algebraMap O (AdjoinRoot Φ)) (axisT O) = axisT (AdjoinRoot Φ) := by
      simp [axisT, MvPowerSeries.map_X]
    exact (hE _).trans (congrArg _ (by rw [hm, hT]))

/-- The completion of the `t`-chart at a closed point over the closed point of the concrete
surface is a noetherian complete local domain. -/
theorem concrete_left_point_completion_instances (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (P : Ideal (tChart O pi u a b)) [P.IsMaximal] [P.IsPrime]
    (hP : tBase O pi u a b (surfaceT O pi u a b) ∈ P) :
    IsNoetherianRing (CompletedLocalAt (tChart O pi u a b) P) ∧
      IsDomain (CompletedLocalAt (tChart O pi u a b) P) ∧
      ∃ _ : IsLocalRing (CompletedLocalAt (tChart O pi u a b) P),
      IsAdicComplete (IsLocalRing.maximalIdeal (CompletedLocalAt (tChart O pi u a b) P))
      (CompletedLocalAt (tChart O pi u a b) P) := by
  obtain ⟨O', c1, c2, c3, c4, c5, pi', u', a', b', hpi', ha', Eq, -⟩ :=
    concrete_left_point_completion_is_surface O pi hpi u a b ha P hP
  exact concrete_surface_equiv_instances _ O' pi' hpi' u' a' b' ha' Eq

/-- The exceptional equation `t` is a non-zero-divisor in the completion of the `t`-chart at any
closed point over the closed point. -/
theorem concrete_left_point_exceptional_regular (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (P : Ideal (tChart O pi u a b)) [P.IsMaximal] [P.IsPrime]
    (hP : tBase O pi u a b (surfaceT O pi u a b) ∈ P) :
    Function.Injective
      (fun y : CompletedLocalAt (tChart O pi u a b) P => completedPointMap (tChart O pi u a b) P
        (tBase O pi u a b (surfaceT O pi u a b)) * y) := by
  obtain ⟨O', c1, c2, c3, c4, c5, pi', u', a', b', hpi', ha', Eq, hEq⟩ :=
    concrete_left_point_completion_is_surface O pi hpi u a b ha P hP
  have e : Eq.symm (surfaceT O' pi' u' a' b') = completedPointMap _ P
      (tBase O pi u a b (surfaceT O pi u a b)) := by
    rw [← hEq]; simp
  exact e ▸ (concrete_surface_equiv_regular_pair _ O' pi' hpi' u' a' b' ha' Eq).2.2

/-- The point at infinity `(x, t/x)` of the `x`-chart: its completion is a concrete surface, a
noetherian complete local ring in which `x` is a non-zero-divisor. -/
theorem concrete_infinity_point_completion (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (P : Ideal (xChart O pi u a b)) [P.IsMaximal] [P.IsPrime]
    (hx : xBase O pi u a b (surfaceX O pi u a b) ∈ P) (hW : xSlope O pi u a b ∈ P) :
    P = Ideal.span {xBase O pi u a b (surfaceX O pi u a b), xSlope O pi u a b} ∧
      (∃ Eq : CompletedLocalAt (xChart O pi u a b) P ≃+*
          ConcreteSurface O pi (xSubstUnit O u) (a + b) a,
        Eq (completedPointMap (xChart O pi u a b) P (xBase O pi u a b (surfaceX O pi u a b))) =
          surfaceT O pi (xSubstUnit O u) (a + b) a) ∧
      IsNoetherianRing (CompletedLocalAt (xChart O pi u a b) P) ∧
      (∃ _ : IsLocalRing (CompletedLocalAt (xChart O pi u a b) P),
        IsAdicComplete (IsLocalRing.maximalIdeal (CompletedLocalAt (xChart O pi u a b) P))
        (CompletedLocalAt (xChart O pi u a b) P)) ∧ Function.Injective
      (fun y : CompletedLocalAt (xChart O pi u a b) P => completedPointMap (xChart O pi u a b) P
        (xBase O pi u a b (surfaceX O pi u a b)) * y) := by
  obtain ⟨hd, hr, D, hpi', ht, hx', h5, h6, h7⟩ :=
      concrete_surface_data_exists_unconditional O pi hpi u a b ha
  have hmax := (infinity_point_maximal O (ConcreteSurface O pi u a b) D).1
  rw [ht, hx'] at hmax
  have hPeq : P = Ideal.span {xBase O pi u a b (surfaceX O pi u a b), xSlope O pi u a b} := by
    symm
    apply Ideal.IsMaximal.eq_of_le hmax (Ideal.IsPrime.ne_top inferInstance)
    unfold infinityPoint
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    exacts [hx, hW]
  obtain ⟨E, hE, hEs, hEc⟩ := x_chart_infinity_completion_equiv O pi hpi u a b ha P hPeq
  have hT : E (completedPointMap (xChart O pi u a b) P (xBase O pi u a b (surfaceX O pi u a b))) =
      surfaceT O pi (xSubstUnit O u) (a + b) a :=
    (hE _).trans (congrArg _ (chartSubst_apply_generators O 0).2.2.2.2.2.1)
  have hinst := concrete_surface_equiv_instances _ O pi hpi (xSubstUnit O u) (a+b) a (by omega) E
  refine ⟨hPeq, ⟨E, hT⟩, hinst.1, hinst.2.2, ?_⟩
  have hreg :=
      (concrete_surface_equiv_regular_pair _ O pi hpi (xSubstUnit O u) (a+b) a (by omega) E).2.2
  have : completedPointMap (xChart O pi u a b) P (xBase O pi u a b (surfaceX O pi u a b)) =
      E.symm (surfaceT O pi (xSubstUnit O u) (a + b) a) := by
    rw [← hT]; simp
  rw [this]; exact hreg

/-- `residueKillT` kills the `x`-chart substitution down to the residue of the constant term. -/
theorem residueKillT_xChartSubst (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (pi : O) (hpi : Irreducible pi) (s : TwoSeries O) :
    residueKillT O (xChartSubst O s) = PowerSeries.C
      (IsLocalRing.residue O (MvPowerSeries.constantCoeff s)) := by
  obtain ⟨-, -, -, hC, hT, hX, -⟩ := chartSubst_apply_generators O 0
  obtain ⟨kC, kT, kX, -, -⟩ := residueKillT_apply_ker O pi hpi
  let L : TwoSeries O →+* PowerSeries (IsLocalRing.ResidueField O) :=
    (residueKillT O).comp (xChartSubst O : TwoSeries O →+* TwoSeries O)
  let R : TwoSeries O →+* PowerSeries (IsLocalRing.ResidueField O) :=
    (PowerSeries.C).comp ((IsLocalRing.residue O).comp MvPowerSeries.constantCoeff)
  have LT : L (axisT O) = 0 := by
    change residueKillT O (xChartSubst O (axisT O)) = 0
    rw [hT, map_mul, kT, zero_mul]
  have LX : L (axisX O) = 0 := by
    change residueKillT O (xChartSubst O (axisX O)) = 0
    rw [hX, kT]
  have RT : R (axisT O) = 0 := by simp [R, axisT]
  have RX : R (axisX O) = 0 := by simp [R, axisX]
  have h : L = R := by
    apply twoSeries_ringHom_ext_of_isNilpotent O _ L R
    · intro c
      change residueKillT O (xChartSubst O (MvPowerSeries.C c)) = _
      simp [R, hC, kC]
    · rw [LT, RT]
    · rw [LX, RX]
    · exact LT ▸ IsNilpotent.zero
    · exact LX ▸ IsNilpotent.zero
  exact congrArg (fun f => f s) h

/-- A power series `∑ rᵢ X^(d - i)` with some `rᵢ ≠ 0` is nonzero. -/
private theorem sum_C_mul_X_pow_ne_zero {K : Type} [Field K] (d : ℕ) (r : Fin (d + 1) → K)
    (hne : ∃ i, r i ≠ 0) :
    (∑ i : Fin (d+1), PowerSeries.C (r i) * PowerSeries.X ^ (d - i.val) : PowerSeries K) ≠ 0 := by
  obtain ⟨i, hi⟩ := hne
  intro h
  apply hi
  have := congrArg (PowerSeries.coeff (d - i.val)) h
  rw [map_zero, map_sum, Finset.sum_eq_single i] at this
  · rwa [PowerSeries.coeff_C_mul_X_pow, if_pos rfl] at this
  · intro j _ hj
    rw [PowerSeries.coeff_C_mul_X_pow, if_neg]
    intro h'; apply hj; ext; have := j.isLt; have := i.isLt; omega
  · simp

/-- At the point at infinity of the `x`-chart, the strict transform `∑ cᵢ (t/x)^(d-i)` of a curve
`f = ∑ cᵢ t^(d-i) x^i` (some `cᵢ` a unit) and the exceptional equation `x` form a transverse pair,
and they cut out a finite-length quotient. -/
theorem concrete_infinity_strict_transform_transverse_finite (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (d : ℕ)
    (c : Fin (d + 1) → ConcreteSurface O pi u a b)
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {(surfaceT O pi u a b), (surfaceX O pi u a b)})
    (P : Ideal (xChart O pi u a b)) [P.IsMaximal] [P.IsPrime]
    (hx : xBase O pi u a b (surfaceX O pi u a b) ∈ P) (hW : xSlope O pi u a b ∈ P) :
    Function.Injective
      (fun w : CompletedLocalAt (xChart O pi u a b) P ⧸ Ideal.span
          {completedPointMap (xChart O pi u a b) P (∑ i : Fin (d+1),
            algebraMap (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) *
              xSlope O pi u a b ^ (d - i.val))} =>
        Ideal.Quotient.mk (Ideal.span {completedPointMap (xChart O pi u a b) P (∑ i : Fin (d+1),
            algebraMap (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) *
              xSlope O pi u a b ^ (d - i.val))})
          (completedPointMap (xChart O pi u a b) P (xBase O pi u a b (surfaceX O pi u a b))) * w) ∧
    Function.Injective
      (fun w : CompletedLocalAt (xChart O pi u a b) P ⧸ Ideal.span
          {completedPointMap (xChart O pi u a b) P (xBase O pi u a b (surfaceX O pi u a b))} =>
        Ideal.Quotient.mk (Ideal.span
            {completedPointMap (xChart O pi u a b) P (xBase O pi u a b (surfaceX O pi u a b))})
          (completedPointMap (xChart O pi u a b) P (∑ i : Fin (d+1),
            algebraMap (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) *
              xSlope O pi u a b ^ (d - i.val))) * w) ∧
    ∃ L : ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
        (localCompletionMap (Localization.AtPrime P)))^L ≤
      finiteLocalCurveIdeal (xChart O pi u a b) P (xBase O pi u a b (surfaceX O pi u a b))
        (completedPointMap (xChart O pi u a b) P (∑ i : Fin (d+1),
          algebraMap (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) *
            xSlope O pi u a b ^ (d - i.val))) 1 := by
  have : IsLocalRing (ConcreteSurface O pi u a b) :=
    concrete_surface_isLocalRing O pi u a b hpi.not_isUnit ha
  obtain ⟨hP, -, hN, ⟨hLoc, -⟩, hreg⟩ :=
      concrete_infinity_point_completion O pi hpi u a b ha P hx hW
  obtain ⟨Eq, hb, hs, -⟩ := x_chart_infinity_completion_equiv O pi hpi u a b ha P hP
  obtain ⟨q, hq⟩ := concrete_surface_quotient_T_equiv O pi hpi (xSubstUnit O u) (a + b) a (by omega)
  obtain ⟨e0, he0⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  have h461 := concrete_surface_maximalIdeal_eq O pi hpi u a b ha
  let κ : IsLocalRing.ResidueField (ConcreteSurface O pi u a b) ≃+* IsLocalRing.ResidueField O :=
    (Ideal.quotEquivOfEq h461).trans e0
  have hκ : ∀ s : TwoSeries O,
      κ (IsLocalRing.residue (ConcreteSurface O pi u a b) (surfaceMk O pi u a b s)) =
      IsLocalRing.residue O (MvPowerSeries.constantCoeff s) := fun s => by
    change e0 (Ideal.quotEquivOfEq h461 (Ideal.Quotient.mk _ (surfaceMk O pi u a b s))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact he0 s
  have hxT : Eq (completedPointMap _ P (xBase O pi u a b (surfaceX O pi u a b))) =
      surfaceT O pi (xSubstUnit O u) (a + b) a := by
    have h := hb (axisX O)
    rwa [(chartSubst_apply_generators O 0).2.2.2.2.2.1] at h
  let Ψ : xChart O pi u a b →+* PowerSeries (IsLocalRing.ResidueField O) :=
    q.toRingHom.comp ((Ideal.Quotient.mk _).comp (Eq.toRingHom.comp (completedPointMap _ P)))
  have hΨc : ∀ r, Ψ (algebraMap (ConcreteSurface O pi u a b) (xChart O pi u a b) r) =
      PowerSeries.C (κ (IsLocalRing.residue _ r)) := fun r => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    change q (Ideal.Quotient.mk _ (Eq (completedPointMap _ P (xBase O pi u a b
        (surfaceMk O pi u a b s))))) = _
    rw [hb, hq, residueKillT_xChartSubst O pi hpi]; exact congrArg _ (hκ s).symm
  have hΨW : Ψ (xSlope O pi u a b) = PowerSeries.X := by
    change q (Ideal.Quotient.mk _ (Eq (completedPointMap _ P _))) = _
    rw [hs, show surfaceX O pi (xSubstUnit O u) (a + b) a = surfaceMk _ _ _ _ _ (axisX O) from rfl,
      hq, (residueKillT_apply_ker O pi hpi).2.2.1]
  set S := CompletedLocalAt (xChart O pi u a b) P
  set e := completedPointMap (xChart O pi u a b) P (xBase O pi u a b (surfaceX O pi u a b))
  set g := completedPointMap (xChart O pi u a b) P
      (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) *
          xSlope O pi u a b ^ (d - i.val))
  have hmap : Ideal.map Eq (Ideal.span {e}) = Ideal.span
      {surfaceT O pi (xSubstUnit O u) (a + b) a} := by
    rw [Ideal.map_span, Set.image_singleton, hxT]
  let e1 : (S ⧸ Ideal.span {e}) ≃+*
      (ConcreteSurface O pi (xSubstUnit O u) (a + b) a ⧸ Ideal.span
        {surfaceT O pi (xSubstUnit O u) (a + b) a}) :=
    Ideal.quotientEquiv (Ideal.span {e})
        (Ideal.span {surfaceT O pi (xSubstUnit O u) (a + b) a}) Eq hmap.symm
  obtain ⟨k1, k2, L, hL'⟩ := transverse_of_reduction_ne_zero S e g hreg
    (IsLocalRing.ResidueField O) (e1.trans q) (by
      change Ψ (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) *
        xSlope O pi u a b ^ (d - i.val)) ≠ 0
      simp only [map_sum, map_mul, map_pow, hΨc, hΨW]
      obtain ⟨i, hi⟩ := hne
      refine sum_C_mul_X_pow_ne_zero d _ ⟨i, ?_⟩
      rwa [Ne, map_eq_zero_iff κ κ.injective, IsLocalRing.residue_eq_zero_iff, h461])
  refine ⟨k1, k2, L, ?_⟩
  unfold finiteLocalCurveIdeal
  rw [pow_one]
  convert hL' using 2
  all_goals exact (AdicCompletion.maximalIdeal_eq_map (R := Localization.AtPrime P)).symm

end SurfaceBlowup
