/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.TwoChartCurveData
import SurfaceBlowup.Measure.Atlas
import SurfaceBlowup.Surfaces.ConcreteAtlas

/-!
# Volumes and strict transforms on the concrete surface

We compute the measures of the crossing and single states of the concrete surface and verify
the local conditions on two-chart curve data on its blow-up: noetherian completions, regular
exceptional equations, transversality, and the identification of strict transforms.

## Main results

* `concrete_crossing_state_volume`, `concrete_single_state_volume`.
* `two_chart_datum_concrete_instances`, `two_chart_datum_concrete_transverse`.
* `concrete_strict_transforms_are_prescribed`.

Provenance: `coordinate_ideal_measurable_chart_sigma`, `concrete_{crossing,single}_state_volume`,
`two_chart_datum_concrete_{instances,transverse}`, `concrete_strict_transforms_are_prescribed`.
-/

open scoped ENNReal

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

/-- The overlap of the two charts of the blow-up of the concrete surface at `(t, x)`. -/
local notation:max "tOverlap" O:max pi:max u:max a:max b:max =>
  BlowupOverlap (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)

/-! ### Volumes of crossing and single states -/

/-- The coordinate-ideal map of a division chart is measurable for the ideal-chart σ-algebra. -/
theorem coordinate_ideal_measurable_chart_sigma (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (R : Type) [CommRing R] [Algebra O R] [IsDomain R]
    [IsLocalRing R] (pi : O) (hpi : Irreducible pi) (hp0 : algebraMap O R pi ≠ 0)
    (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (n : ℕ) (f : R) (b : Fin n → R)
    (hchart : IsDivisionChart O R pi f b) [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] :
    @Measurable (Fin n → O) (Ideal R) inferInstance (idealChartSigma O R pi)
      (coordinateIdeal pi f b) := by
  refine @measurable_generateFrom _ _ inferInstance _ _ ?_
  rintro T ⟨n', g, c, S, hc, hS, rfl⟩
  exact division_chart_preimage_image_measurable O htop R pi hpi hp0 hpm n n' f g b c hchart hc S hS

/-- The crossing state `(a, b, c, h)` of the concrete surface has measure
`(q - 1) q^(-(c + h))`, where `q` is the size of the residue field. -/
theorem concrete_crossing_state_volume (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hSpi : S.pi = pi)
    (hSt : S.t = surfaceT O pi u a b) (hSx : S.x = surfaceX O pi u a b) (hSa : S.a = a)
    (hSb : S.b = b)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b)
    (he : ∀ s : TwoSeries O,
      e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      (surfaceMk O pi u a b s)) = Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a b)
      (residueSeries O s)) (c h : ℕ) (hc : 0 < c) (hh : 0 < h) [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (htop : IsAdic (IsLocalRing.maximalIdeal O)) :
    (letI : MeasurableSpace (Ideal (ConcreteSurface O pi u a b)) := idealChartSigma O
        (ConcreteSurface O pi u a b) pi; ∃ A : IdealAtlas O (ConcreteSurface O pi u a b) pi
        (a*c+b*h) (surfaceStateSet O (ConcreteSurface O pi u a b) S (State.crossing a b c h)),
        stateMeasure O (ConcreteSurface O pi u a b) pi (a*c+b*h)
        (Nat.card (IsLocalRing.ResidueField O)) A Set.univ =
        ((Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞) - 1) *
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(c+h)) := by
  let : MeasurableSpace (Ideal (ConcreteSurface O pi u a b)) := idealChartSigma O
      (ConcreteSurface O pi u a b) pi
  change ∃ A : IdealAtlas _ _ _ _ _, _
  obtain ⟨A, hA⟩ :=
      concrete_crossing_state_atlas_exists O pi hpi u a b ha hb S hSt hSx hSa hSb e he c h hc
      hh
  refine ⟨A, ?_⟩
  obtain ⟨hp0, hpm⟩ := surface_vertical_parameter O (ConcreteSurface O pi u a b) S
  rw [hSpi] at hp0 hpm
  refine crossing_state_volume O
      (ConcreteSurface O pi u a b) htop pi _ a b c h ha hb hc hh A ?_ hA
  intro i
  have := division_coordinate_module_isAdicComplete O pi hpi u a b ha (a*c+b*h)
  exact coordinate_ideal_measurable_chart_sigma O htop
      (ConcreteSurface O pi u a b) pi hpi hp0 hpm _ _ _ (A.chart i).isDivisionChart

/-- The single state `(a, c)` of the concrete surface (with `b = 0`) has measure `q^(-c)`, where
`q` is the size of the residue field. -/
theorem concrete_single_state_volume (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a 0)]
    [IsRegularLocalRing (ConcreteSurface O pi u a 0)]
    (S : SurfaceData O (ConcreteSurface O pi u a 0)) (hSpi : S.pi = pi)
    (hSt : S.t = surfaceT O pi u a 0) (hSa : S.a = a) (hSb : S.b = 0)
    (e : (ConcreteSurface O pi u a 0 ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a 0)
    (he : ∀ s : TwoSeries O,
      e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi})
      (surfaceMk O pi u a 0 s)) = Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a 0)
      (residueSeries O s)) (c : ℕ) (hc : 0 < c) [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) :
    (letI : MeasurableSpace (Ideal (ConcreteSurface O pi u a 0)) := idealChartSigma O
        (ConcreteSurface O pi u a 0) pi; ∃ A : IdealAtlas O (ConcreteSurface O pi u a 0) pi (a*c)
        (surfaceStateSet O (ConcreteSurface O pi u a 0) S (State.single a c)),
        stateMeasure O (ConcreteSurface O pi u a 0) pi (a*c)
        (Nat.card (IsLocalRing.ResidueField O)) A Set.univ =
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^c) := by
  let : MeasurableSpace (Ideal (ConcreteSurface O pi u a 0)) := idealChartSigma O
      (ConcreteSurface O pi u a 0) pi
  obtain ⟨A, hA⟩ := concrete_single_state_atlas_exists O pi hpi u a ha S hSt hSa hSb e he c hc
  refine ⟨A, ?_⟩
  obtain ⟨hp0, hpm⟩ := surface_vertical_parameter O (ConcreteSurface O pi u a 0) S
  rw [hSpi] at hp0 hpm
  refine single_state_volume O (ConcreteSurface O pi u a 0) htop pi _ a c ha A ?_ hA
  intro i
  have := division_coordinate_module_isAdicComplete O pi hpi u a 0 ha (a*c)
  exact coordinate_ideal_measurable_chart_sigma O htop (ConcreteSurface O pi u a 0) pi hpi hp0 hpm
      _ _ _ (A.chart i).isDivisionChart

/-! ### Two-chart curve data on the concrete surface -/

/-- The completion at a prime `P` of a noetherian ring is a noetherian complete local ring whose
maximal ideal contains the image of any `e ∈ P`. -/
private theorem completion_isNoetherian_isDomain_of_equiv (A : Type) [CommRing A]
    [IsNoetherianRing A] (P : Ideal A) [P.IsPrime]
    (e : A) (he : e ∈ P) :
    ∃ _ : IsLocalRing (CompletedLocalAt A P), IsAdicComplete (IsLocalRing.maximalIdeal
      (CompletedLocalAt A P)) (CompletedLocalAt A P) ∧
      completedPointMap A P e ∈ IsLocalRing.maximalIdeal (CompletedLocalAt A P) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P e).2 he)

/-- Injectivity of multiplication by `x` follows from that of multiplication by `z` along a ring
isomorphism sending `x` to `z` times a unit. -/
private theorem injective_mul_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] (φ : A ≃+* B)
    {x : A} {z w : B} (h : φ x = z * w) (hw : IsUnit w)
    (hz : Function.Injective (fun y : B => z * y)) :
    Function.Injective (fun y : A => x * y) := by
  intro y y' hyy
  have h' := congrArg φ hyy
  simp only [map_mul, h, mul_assoc] at h'
  exact φ.injective (hw.mul_left_cancel (hz h'))

/-- At every point of two-chart curve data on the blow-up of the concrete surface, the completed
local ring is noetherian (complete local) and the exceptional equation is a non-zero-divisor. -/
theorem two_chart_datum_concrete_instances (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) beta) :
    (∀ s : D.ι ⊕ D.ι0,
        IsNoetherianRing (CompletedLocalAt (tChart O pi u a b) (leftPoint D s)) ∧
        Function.Injective (fun y : (CompletedLocalAt (tChart O pi u a b) (leftPoint D s)) =>
          (completedPointMap (tChart O pi u a b) (leftPoint D s))
            (tBase O pi u a b (surfaceT O pi u a b)) * y)) ∧
      (∀ s : D.ι ⊕ D.ιinf,
        IsNoetherianRing (CompletedLocalAt (xChart O pi u a b) (rightPoint D s)) ∧
        Function.Injective (fun y : (CompletedLocalAt (xChart O pi u a b) (rightPoint D s)) =>
          (completedPointMap (xChart O pi u a b) (rightPoint D s))
            (xBase O pi u a b (surfaceX O pi u a b)) * y)) ∧
      ∀ p : AllPoints D, IsNoetherianRing (localRing D p) ∧ ∃ _ : IsLocalRing (localRing D p),
      IsAdicComplete (IsLocalRing.maximalIdeal (localRing D p)) (localRing D p) ∧
      localException D p ∈ IsLocalRing.maximalIdeal (localRing D p) := by
  have : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} :
      Set (ConcreteSurface O pi u a b))).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  obtain ⟨hLmax, -, hLt⟩ := two_chart_left_points_maximal _ _ _ beta D
  have hL : ∀ s, IsNoetherianRing (CompletedLocalAt (tChart O pi u a b) (leftPoint D s)) ∧
      Function.Injective (fun y : CompletedLocalAt (tChart O pi u a b) (leftPoint D s) =>
        completedPointMap _ (leftPoint D s) (tBase O pi u a b (surfaceT O pi u a b)) * y) := by
    intro s
    have := hLmax s
    exact ⟨(concrete_left_point_completion_instances O pi hpi u a b ha (leftPoint D s) (hLt s)).1,
      concrete_left_point_exceptional_regular O pi hpi u a b ha (leftPoint D s) (hLt s)⟩
  have hInf : ∀ l, IsNoetherianRing
      (CompletedLocalAt (xChart O pi u a b) (rightPoint D (Sum.inr l))) ∧
      Function.Injective (fun y : CompletedLocalAt (xChart O pi u a b) (rightPoint D (Sum.inr l)) =>
        completedPointMap _ (rightPoint D (Sum.inr l))
          (xBase O pi u a b (surfaceX O pi u a b)) * y) := by
    intro l
    have : (rightPoint D (Sum.inr l)).IsMaximal := D.maximalinf l
    have h := concrete_infinity_point_completion O pi hpi u a b ha (rightPoint D (Sum.inr l))
      (D.onEinf l) (D.slopeinf l)
    exact ⟨h.2.2.1, h.2.2.2.2⟩
  -- at an overlap point, transport from the `t`-chart along `φ = rightIso⁻¹ ≫ leftIso`
  have hR : ∀ i : D.ι, IsNoetherianRing
      (CompletedLocalAt (xChart O pi u a b) (rightPoint D (Sum.inl i))) ∧
      Function.Injective (fun y : CompletedLocalAt (xChart O pi u a b) (rightPoint D (Sum.inl i)) =>
        completedPointMap _ (rightPoint D (Sum.inl i))
          (xBase O pi u a b (surfaceX O pi u a b)) * y) := by
    intro i
    let P := (D.Q i).comap (algebraMap (tChart O pi u a b) (tOverlap O pi u a b))
    obtain ⟨hLn, hLinj⟩ : IsNoetherianRing (CompletedLocalAt _ P) ∧
        Function.Injective (fun y : CompletedLocalAt _ P =>
          completedPointMap _ P (tBase O pi u a b (surfaceT O pi u a b)) * y) := hL (Sum.inl i)
    let φ := (D.rightIso i).symm.trans (D.leftIso i)
    have hbeta : beta.right (xBase O pi u a b (surfaceX O pi u a b)) =
        algebraMap (tChart O pi u a b) (tOverlap O pi u a b)
          (tBase O pi u a b (surfaceX O pi u a b)) :=
      beta.right.commutes (surfaceX O pi u a b)
    have hφ : φ (completedPointMap (xChart O pi u a b) ((D.Q i).comap beta.right.toRingHom)
        (xBase O pi u a b (surfaceX O pi u a b))) =
        completedPointMap _ P (tBase O pi u a b (surfaceT O pi u a b)) *
          completedPointMap _ P (tSlope O pi u a b) := by
      have h1 := D.rightIso_compat i (xBase O pi u a b (surfaceX O pi u a b))
      rw [hbeta] at h1
      rw [← map_mul, blowup_chart_relation, ← h1]
      change D.leftIso i ((D.rightIso i).symm _) = _
      rw [RingEquiv.symm_apply_apply]
      exact D.leftIso_compat i _
    have hWnot : tSlope O pi u a b ∉ P := fun hW => (D.maximal i).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hW (IsLocalization.Away.algebraMap_isUnit _))
    have hWunit : IsUnit (completedPointMap _ P (tSlope O pi u a b)) :=
      (IsLocalization.map_units (Localization.AtPrime P)
        (⟨_, hWnot⟩ : P.primeCompl)).map (localCompletionMap _)
    exact ⟨isNoetherianRing_of_ringEquiv _ φ.symm, injective_mul_of_ringEquiv φ hφ hWunit hLinj⟩
  have hNC : ∀ i : D.ι, IsNoetherianRing (CompletedLocalAt (tOverlap O pi u a b) (D.Q i)) :=
    fun i => by
      have : IsNoetherianRing (CompletedLocalAt (tChart O pi u a b)
        ((D.Q i).comap (algebraMap (tChart O pi u a b) (tOverlap O pi u a b)))) :=
        (hL (Sum.inl i)).1
      exact isNoetherianRing_of_ringEquiv _ (D.leftIso i).symm
  have : IsNoetherianRing (tChart O pi u a b) :=
    blowupChart_concrete_isNoetherianRing O pi u a b _ _
  have : IsNoetherianRing (xChart O pi u a b) :=
    blowupChart_concrete_isNoetherianRing O pi u a b _ _
  refine ⟨hL, fun s => s.casesOn hR hInf, ?_⟩
  rintro (i | k | l)
  · exact ⟨hNC i, completion_isNoetherian_isDomain_of_equiv _ (D.Q i) _ (D.onE i)⟩
  · exact ⟨(hL (Sum.inr k)).1,
      completion_isNoetherian_isDomain_of_equiv _ (leftPoint D (Sum.inr k)) _ (D.onE0 k)⟩
  · exact ⟨(hInf l).1,
      completion_isNoetherian_isDomain_of_equiv _ (rightPoint D (Sum.inr l)) _ (D.onEinf l)⟩

/-- Multiplication by `g` is injective modulo `e` iff `e ∣ g w` implies `e ∣ w`. -/
private theorem injective_mul_iff {S : Type} [CommRing S] (e g : S) :
    Function.Injective (fun w : S ⧸ Ideal.span {e} => Ideal.Quotient.mk (Ideal.span {e}) g * w) ↔
      ∀ w : S, e ∣ g * w → e ∣ w := by
  constructor
  · intro h w hw
    have h1 : Ideal.Quotient.mk (Ideal.span {e}) g * Ideal.Quotient.mk (Ideal.span {e}) w =
        Ideal.Quotient.mk (Ideal.span {e}) g * 0 := by
      rw [mul_zero, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hw
    have h2 := h h1
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2
  · intro h x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only at hxy
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton, ← mul_sub] at hxy
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h _ hxy

/-- At a point whose completion is a concrete surface with `e ↦ t`, a curve of finite colength
with `e` is transverse to `e`. -/
private theorem transverse_of_regular_local (A : Type) [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsMaximal]
    (e g : CompletedLocalAt A P)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O')
    (hpi' : Irreducible pi') (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a')
    (Eq : CompletedLocalAt A P ≃+* ConcreteSurface O' pi' u' a' b')
    (hE : Eq e = surfaceT O' pi' u' a' b') (L : ℕ)
    (hL : ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (localCompletionMap (Localization.AtPrime P))) ^ L ≤ Ideal.span {g, e ^ 1}) :
    ∀ w, e ∣ g * w → e ∣ w := by
  obtain ⟨q, -⟩ := concrete_surface_quotient_T_equiv O' pi' hpi' u' a' b' ha'
  have hsymm : Eq.symm (surfaceT O' pi' u' a' b') = e := by rw [← hE]; simp
  have hreg := (concrete_surface_equiv_curve_length_and_regular (CompletedLocalAt A P) O' pi'
    u' a' b' Eq q g).2
  rw [hsymm] at hreg
  rw [← injective_mul_iff]
  refine hreg.mpr ?_
  intro h0
  have hmk : Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (Eq g) = 0 := by
    simpa using h0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmk
  have hge : e ∣ g := by
    have := map_dvd Eq.symm hmk
    rwa [hsymm, RingEquiv.symm_apply_apply] at this
  have hL' : ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (localCompletionMap (Localization.AtPrime P)))^L ≤ Ideal.span {e} := by
    refine hL.trans (Ideal.span_le.mpr ?_)
    rintro z (rfl | rfl)
    · exact Ideal.mem_span_singleton.mpr hge
    · simp
  have hsurj := finite_completed_point_quotient_surjective A P L (Ideal.span {e}) hL'
  let θ : CompletedLocalAt A P ⧸ Ideal.span {e} →+* PowerSeries (IsLocalRing.ResidueField O') :=
    Ideal.Quotient.lift (Ideal.span {e})
      (q.toRingHom.comp
            ((Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'})).comp Eq.toRingHom))
      (fun z hz => by
        have := hE ▸ map_dvd Eq (Ideal.mem_span_singleton.mp hz)
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr this)])
  have hθ : Function.Surjective θ := by
    intro f
    obtain ⟨z, hz⟩ := q.surjective f
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨Ideal.Quotient.mk _ (Eq.symm z), ?_⟩
    simp [θ, hz]
  let ψ : A →+* PowerSeries (IsLocalRing.ResidueField O') :=
    θ.comp ((Ideal.Quotient.mk (Ideal.span {e})).comp (completedPointMap A P))
  have hψ : Function.Surjective ψ := hθ.comp hsurj
  have hP : ∀ p ∈ P, ψ p = 0 := by
    intro p hp
    have hm : completedPointMap A P p ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
        (localCompletionMap (Localization.AtPrime P)) := Ideal.mem_map_of_mem _
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P p).mpr hp)
    have hpow := hL' (Ideal.pow_mem_pow hm L)
    have : ψ p ^ L = 0 := by
      rw [← map_pow]
      simp only [ψ, RingHom.comp_apply]
      rw [map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hpow, map_zero]
    exact pow_eq_zero_iff'.mp this |>.1
  obtain ⟨c, hc⟩ := hψ PowerSeries.X
  have hcP : c ∉ P := fun hcP => PowerSeries.X_ne_zero (hc ▸ hP c hcP)
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv ‹P.IsMaximal› hcP
  have := congrArg ψ hyi
  rw [map_add, map_mul, hP i hi, hc, add_zero, map_one] at this
  have := congrArg PowerSeries.constantCoeff this
  simp at this

/-- Regularity of `g` modulo `e` transports along a ring isomorphism `Θ` to regularity of `Θ g`
modulo any unit multiple of `Θ e`. -/
private theorem dvd_transport {S T : Type} [CommRing S] [CommRing T] (Θ : S ≃+* T) {e g : S}
    {eT gT u : T} (hu : IsUnit u) (he : Θ e * u = eT) (hg : Θ g = gT)
    (h : ∀ w, e ∣ g * w → e ∣ w) : ∀ w, eT ∣ gT * w → eT ∣ w := by
  subst he hg
  intro w hw
  rw [hu.mul_right_dvd] at hw ⊢
  simpa using map_dvd Θ (h (Θ.symm w) (by simpa using map_dvd Θ.symm hw))

/-- The strict transforms in two-chart curve data on the blow-up of the concrete surface are
transverse to the exceptional divisor at every point. -/
theorem two_chart_datum_concrete_transverse (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) beta) :
    (∀ s : D.ι ⊕ D.ι0,
        Function.Injective
        (fun w : (CompletedLocalAt (tChart O pi u a b) (leftPoint D s)) ⧸ Ideal.span
          {(completedPointMap (tChart O pi u a b) (leftPoint D s))
            (tBase O pi u a b (surfaceT O pi u a b))} =>
          Ideal.Quotient.mk (Ideal.span {(completedPointMap (tChart O pi u a b) (leftPoint D s))
            (tBase O pi u a b (surfaceT O pi u a b))}) (leftData D s) * w)) ∧
      ∀ s : D.ι ⊕ D.ιinf,
      Function.Injective
      (fun w : (CompletedLocalAt (xChart O pi u a b) (rightPoint D s)) ⧸ Ideal.span
        {(completedPointMap (xChart O pi u a b) (rightPoint D s))
          (xBase O pi u a b (surfaceX O pi u a b))} =>
        Ideal.Quotient.mk (Ideal.span {(completedPointMap (xChart O pi u a b) (rightPoint D s))
          (xBase O pi u a b (surfaceX O pi u a b))}) (rightData D s) * w) := by
  have hmaxTX : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} :
      Set (ConcreteSurface O pi u a b))).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  have : IsNoetherianRing (ConcreteSurface O pi u a b) :=
    concrete_surface_isNoetherianRing O pi u a b
  obtain ⟨hLmax, -, hLmem⟩ := two_chart_left_points_maximal _ _ _ beta D
  obtain ⟨hRmax, -, hRmem⟩ := two_chart_right_points_maximal _ _ _ beta D
  obtain ⟨-, hLfin⟩ := two_chart_left_data_transverse_finite _ _ _ beta D 1
  obtain ⟨-, hRfin⟩ := two_chart_right_data_transverse_finite _ _ _ beta D 1
  have hleft : ∀ s : D.ι ⊕ D.ι0, ∀ w,
      completedPointMap _ (leftPoint D s) (tBase O pi u a b (surfaceT O pi u a b)) ∣
        leftData D s * w →
      completedPointMap _ (leftPoint D s) (tBase O pi u a b (surfaceT O pi u a b)) ∣ w := by
    intro s
    have := hLmax s
    obtain ⟨O', _, _, _, _, _, pi', u', a', b', hpi', ha', Eq, hEq⟩ :=
      concrete_left_point_completion_is_surface O pi hpi u a b ha (leftPoint D s) (hLmem s)
    obtain ⟨L, hL⟩ := hLfin s
    exact transverse_of_regular_local _ (leftPoint D s) _ _ O' pi' hpi' u' a' b' ha'
      Eq hEq L hL
  refine ⟨fun s => (injective_mul_iff _ _).mpr (hleft s), fun s => ?_⟩
  rw [injective_mul_iff]
  rcases s with i | l
  · refine dvd_transport ((D.leftIso i).symm.trans (D.rightIso i))
      (e := D.leftIso i (completedPointMap _ (D.Q i) (algebraMap _ _ (chartBase _ _ _ _))))
      (u := D.rightIso i (completedPointMap _ (D.Q i) (overlapSlope _ _ _)))
      (((IsLocalization.Away.algebraMap_isUnit _).map _).map _) ?_
      (congrArg (D.rightIso i) ((D.leftIso i).symm_apply_apply _))
      (by rw [D.leftIso_compat i]; exact hleft (Sum.inl i))
    rw [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, ← map_mul, ← map_mul]
    exact (congrArg (fun z => D.rightIso i (completedPointMap _ _ z))
      (beta_right_chartBase_self (beta := beta)).symm).trans (D.rightIso_compat i _)
  · have := hRmax (Sum.inr l)
    obtain ⟨-, ⟨Eq, hEq⟩, -⟩ := concrete_infinity_point_completion O pi hpi u a b ha
      (rightPoint D (Sum.inr l)) (hRmem (Sum.inr l)) (D.slopeinf l)
    obtain ⟨L, hL⟩ := hRfin (Sum.inr l)
    exact transverse_of_regular_local _ (rightPoint D (Sum.inr l)) _ _ O pi hpi
      (xSubstUnit O u) (a + b) a (by omega) Eq hEq L hL

/-- The strict transforms of a curve `(f)` at the points of two-chart curve data are the
prescribed local equations. -/
theorem concrete_strict_transforms_are_prescribed (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) beta) (f : ConcreteSurface O pi u a b)
    (G : GluedGenerators (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) beta (curveDataDegree D))
    (hf : ∀ j : ℕ,
      surfaceToCechInput (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) j f =
      (cechInputLattice (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) j).mkQ
      (gluedFunctionPair (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) G j))
    (hG : ∀ j : ℕ,
      Ideal.span
      {Ideal.Quotient.mk
      ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))^j) (G.left j)} = leftLevelKernel D j ∧ Ideal.span
      {Ideal.Quotient.mk
      ((chartExceptional (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
      (surfaceT O pi u a b))^j) (G.right j)} = rightLevelKernel D j) :
    (∀ s : D.ι ⊕ D.ι0,
        strictTransformAt (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
        (leftPoint D s) (curveDataDegree D) (Ideal.span {f}) = Ideal.span {leftData D s}) ∧
      ∀ s : D.ι ⊕ D.ιinf,
      strictTransformAt (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)
      (rightPoint D s) (curveDataDegree D) (Ideal.span {f}) = Ideal.span {rightData D s} := by
  have : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} :
      Set (ConcreteSurface O pi u a b))).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  have h1 := blowupChart_concrete_isNoetherianRing O pi u a b (surfaceT O pi u a b)
      (surfaceX O pi u a b)
  have h2 := blowupChart_concrete_isNoetherianRing O pi u a b (surfaceX O pi u a b)
      (surfaceT O pi u a b)
  obtain ⟨hI1, hI2, -⟩ := two_chart_datum_concrete_instances O pi hpi u a b ha beta D
  obtain ⟨hT1, hT2⟩ := two_chart_datum_concrete_transverse O pi hpi u a b ha beta D
  refine ⟨fun s => ?_, fun s => ?_⟩
  · obtain ⟨_, hereg⟩ := hI1 s
    obtain ⟨v, hv⟩ := strict_transform_left_point_equation _ _ _ beta D _ G hG f hf s hereg (hT1 s)
    unfold strictTransformAt
    rw [principal_ideal_image, RingHom.comp_apply, chartBase_apply_eq_algebraMap, hv,
      Ideal.span_singleton_mul_right_unit v.isUnit]
    exact span_pow_mul_colon_eq _ _ _ hereg
  · obtain ⟨_, hreg⟩ := hI2 s
    exact global_function_strict_transform_at_right_point _ _ _ beta D _ G hG f hf s hreg (hT2 s)

end SurfaceBlowup
