/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.NilpotentGluing
import SurfaceBlowup.Measure.StateVolumes

/-!
# Strict transforms and the strict normalizer

This file studies strict transforms of curves on the concrete surfaces
`O⟦t, x⟧ ⧸ (pi - u tᵃ xᵇ)` under the blow-up of the closed point. It computes the local
intersection data of a strict transform with the exceptional divisor, proves that functions of
finite contact on the special fiber are nonzerodivisors, and develops the *strict normalizer*:
the change of coordinates showing that, on a `pi`-adic coordinate box, strict transforms of a
perturbed generator `f + pi ^ (s + a) • ℓ(z)` are again perturbations of the strict transform
`g`, with an explicitly scaled coordinate map. It also computes the cokernel of the induced map
of quotient modules and transports strict transforms between the two blow-up charts.

## Main results

* `concrete_strict_transform_multiplicity`: intersection length with the exceptional divisor
  equals the multiplicity of the corresponding factor of the tangent form.
* `strict_transform_mapsTo_child_ideals`: strict transforms send a fixed tangent cell into the
  child ideal sets (Proposition 5.1, maps-to part).
* `special_fiber_crossing_contact_regular`, `special_fiber_single_contact_regular`.
* `strict_chart_coordinates_commute`, `strict_chart_preimage_set_identity`: the strict
  normalizer in chart coordinates.
* `strict_quotient_cokernel_length`: the cokernel length `s * N - tri d`.
* `cell_strict_transforms_agree_at_datum_points`,
  `strict_transforms_give_level_lattice_membership`.

Provenance: `Thm_SurfaceBlowupV2_*` nodes `concrete_strict_transform_{reduction_ne_zero,
transverse_finite, multiplicity}`, `prop_5_1_mapsTo`, `{scalar,power}_normalizer_*`,
`normalized_{coordinate_equation, quadratic_preserves_congruence}`, `scaled_{inverse_from_image_
containment, linear_image_index}`, `coordinate_scale_measure`, `special_fiber_{crossing,single}_
contact_regular`, `concrete_surface_single_curve_free`, `strict_{correction_raises_order,
normalizer_*, pullback_*, chart_*, quotient_*}`, `actual_strict_map_is_scaled_normalizer`,
`strict_transform_{common_point_transport, equation_from_levels}`,
`cell_strict_transforms_agree_at_datum_points`, `strict_transforms_give_level_lattice_membership`.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-! ### Strict transforms on concrete surfaces -/

/-- If the strict transform `FA` of `f` has nonzero reduction on the exceptional divisor, then
the completed local ring at an exceptional point is again a concrete surface in which the image
of `FA` has nonzero reduction modulo the new `t`. -/
private theorem concrete_strict_transform_reduction_ne_zero (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (FA : (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))) (hne : Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) FA ≠
    0) (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))) [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (surfaceT O pi u a b) ∈ P) : ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O')
    (_ : IsDiscreteValuationRing O') (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O')
    (_ : Finite (IsLocalRing.ResidueField O')) (pi' : O') (u' : (TwoSeries O')ˣ) (a' b' : ℕ),
    Irreducible pi' ∧ 0 < a' ∧ ∃ (Eq : CompletedLocalAt
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P ≃+*
    ConcreteSurface O' pi' u' a' b') (q : (ConcreteSurface O' pi' u' a' b' ⧸ Ideal.span
    {surfaceT O' pi' u' a' b'}) ≃+* PowerSeries (IsLocalRing.ResidueField O')), Eq
    (completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (surfaceT O pi u a b))) = surfaceT O' pi' u' a' b' ∧ q
    (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'})
    (Eq (completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P FA))) ≠ 0 := by
  have : IsLocalRing (ConcreteSurface O pi u a b) :=
    concrete_surface_isLocalRing O pi u a b hpi.not_isUnit ha
  have hm : IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b) =
      Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} : Set _) :=
    concrete_surface_maximalIdeal_eq O pi hpi u a b ha
  have : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} : Set _)).IsMaximal :=
    hm ▸ IsLocalRing.maximalIdeal.isMaximal _
  obtain ⟨e0, he0, he0Z⟩ := exceptional_line_equiv_chart_exceptional (ConcreteSurface O pi u a b)
      (surfaceT O pi u a b) (surfaceX O pi u a b)
  let iso : (ConcreteSurface O pi u a b ⧸ Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} :
      Set _)) ≃+* IsLocalRing.ResidueField (ConcreteSurface O pi u a b) :=
    Ideal.quotEquivOfEq hm.symm
  let e := e0.trans (Polynomial.mapEquiv iso)
  have he : ∀ r, e (Ideal.Quotient.mk _ (chartBase _ _ _ r)) =
      Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r) := fun r ↦ by
    simp only [e, RingEquiv.trans_apply, he0, Polynomial.mapEquiv_apply, Polynomial.map_C]
    rfl
  have heZ : e (Ideal.Quotient.mk _ (chartSlope _ _ _)) = Polynomial.X := by simp [e, he0Z]
  obtain ⟨φ, hmon, hirr, hPφ, -, -⟩ :=
    blowup_chart_exceptional_point_polynomial (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b) e0 he0 he0Z P hP
  have hφ' : (φ.map iso.toRingHom).Monic ∧ Irreducible (φ.map iso.toRingHom) :=
    ⟨hmon.map _, (MulEquiv.irreducible_iff (Polynomial.mapEquiv iso)).mpr hirr⟩
  have hPφ' : (P.map (Ideal.Quotient.mk _)).map e = Ideal.span {φ.map iso.toRingHom} := by
    have h1 : ∀ J : Ideal _, Ideal.map e J =
        Ideal.map (Polynomial.mapEquiv iso) (Ideal.map e0 J) := fun J ↦ by
      change Ideal.map e.toRingHom J =
        Ideal.map (Polynomial.mapEquiv iso).toRingHom (Ideal.map e0.toRingHom J)
      rw [Ideal.map_map]
      rfl
    rw [h1, hPφ, Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨O', i1, i2, i3, i4, i5, pi', u', a', b', hpi', ha', Eq, q, ι, alphaBar, hT, -, hF⟩ :=
    concrete_strict_transform_residue_series O pi hpi u a b ha P hP e he heZ _ hφ' hPφ'
  refine ⟨O', i1, i2, i3, i4, i5, pi', u', a', b', hpi', ha', Eq, q, hT, ?_⟩
  rw [hF FA, Ne, Polynomial.coe_eq_zero_iff, ← Polynomial.taylor_apply]
  simpa [Polynomial.map_eq_zero_iff ι.injective] using hne

/-- At an exceptional point of the blow-up chart, the strict transform `FA` and the exceptional
equation `t` are mutually regular in the completed local ring, and some power of the maximal
ideal lies in the local curve ideal they cut out. -/
theorem concrete_strict_transform_transverse_finite (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (FA : (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))) (hne : Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) FA ≠
    0) (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))) [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (surfaceT O pi u a b) ∈ P) : Function.Injective
    (fun w : CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ⧸ Ideal.span {completedPointMap
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P FA} =>
    Ideal.Quotient.mk (Ideal.span {completedPointMap
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P FA})
    (completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (surfaceT O pi u a b))) * w) ∧ Function.Injective
    (fun w : CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ⧸ Ideal.span {completedPointMap
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P
    ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (surfaceT O pi u a b))} => Ideal.Quotient.mk
    (Ideal.span {completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (surfaceT O pi u a b))})
    (completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P FA) * w) ∧ ∃ L : ℕ,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
    (localCompletionMap (Localization.AtPrime P)))^L ≤ finiteLocalCurveIdeal
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P
    ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (surfaceT O pi u a b)) (completedPointMap
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P FA)
    1 := by
  obtain ⟨hN, hD, hL, hC⟩ := concrete_left_point_completion_instances O pi hpi u a b ha P hP
  have hreg := concrete_left_point_exceptional_regular O pi hpi u a b ha P hP
  obtain ⟨O', c1, c2, c3, c4, c5, pi', u', a', b', hpi', ha', Eq, q, hEq, hq⟩ :=
    concrete_strict_transform_reduction_ne_zero O pi hpi u a b ha FA hne P hP
  let e1 := Ideal.quotientEquiv (Ideal.span {completedPointMap _ P
    (chartBase _ (surfaceT O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))})
    (Ideal.span {surfaceT O' pi' u' a' b'}) Eq (by
      rw [Ideal.map_span, Set.image_singleton]; exact congrArg (Ideal.span {·}) hEq.symm)
  obtain ⟨k1, k2, L, hL'⟩ := transverse_of_reduction_ne_zero _ _ _ hreg
    (IsLocalRing.ResidueField O') (e1.trans q) hq
  refine ⟨k1, k2, L, ?_⟩
  rw [finiteLocalCurveIdeal, pow_one]
  convert hL' using 2
  all_goals exact (AdicCompletion.maximalIdeal_eq_map (R := Localization.AtPrime P)).symm

/-- The order of a nonzero polynomial viewed as a power series is its trailing degree. -/
private theorem order_coe_polynomial {K : Type} [Field K] (H : Polynomial K) (hH : H ≠ 0) :
    (H : PowerSeries K).order = (H.natTrailingDegree : ℕ∞) := by
  rw [PowerSeries.order_eq_nat]
  refine ⟨?_, ?_⟩
  · rw [Polynomial.coeff_coe]
    exact mt Polynomial.trailingCoeff_eq_zero.mp hH
  · intro i hi
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi

open scoped Classical in
/-- The local intersection length of the strict transform with the exceptional divisor at the
point `P` equals the multiplicity of the irreducible factor `φ` (defining `P`) in the reduced
tangent form `∑ cᵢ Xⁱ`. -/
theorem concrete_strict_transform_multiplicity (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (d : ℕ) (c : Fin (d + 1) → ConcreteSurface O pi u a b)
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {(surfaceT O pi u a b), (surfaceX O pi u a b)})
    [IsLocalRing (ConcreteSurface O pi u a b)]
    (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))) [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (surfaceT O pi u a b) ∈ P) (e : ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) ⧸ chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) ≃+* Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (he : ∀ r : (ConcreteSurface O pi u a b), e
    (Ideal.Quotient.mk (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) r)) = Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))) = Polynomial.X) (φ : Polynomial
    (IsLocalRing.ResidueField (ConcreteSurface O pi u a b))) (hφ : φ.Monic ∧ Irreducible φ)
    (hPφ : (P.map (Ideal.Quotient.mk (chartExceptional (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b)))).map e = Ideal.span {φ}) : Module.length
    (CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P) (CompletedLocalAt
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P ⧸
    Ideal.span {completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (c i) *
    (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))^i.val),
    completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (surfaceT O pi u a b))}) =
    (Multiset.count φ (UniqueFactorizationMonoid.normalizedFactors
    (∑ i : Fin (d+1), Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) (c i)) *
    Polynomial.X^i.val : Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))) :
    ℕ∞) := by
  have h461 := concrete_surface_maximalIdeal_eq O pi hpi u a b ha
  obtain ⟨e0, -⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  let κ : IsLocalRing.ResidueField (ConcreteSurface O pi u a b) ≃+* IsLocalRing.ResidueField O :=
    (Ideal.quotEquivOfEq h461).trans e0
  have : Finite (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)) :=
    Finite.of_equiv _ κ.symm.toEquiv
  obtain ⟨O', i1, i2, i3, i4, i5, pi', u', a', b', hpi', ha', Eq, q, ι, alphaBar, hT, hroot, hF⟩ :=
    concrete_strict_transform_residue_series O pi hpi u a b ha P hP e he heZ φ hφ hPφ
  set FA := (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (c i) *
      (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))^i.val)
  set Fbar :=
      (∑ i : Fin (d+1), Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) (c i)) *
      Polynomial.X^i.val : Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
  have hred : e (Ideal.Quotient.mk _ FA) = Fbar := by
    simp only [FA, Fbar, map_sum, map_mul, map_pow, heZ]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← he (c i)]; rfl
  have hFne : Fbar ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro h0
    have hc := congrArg (fun p => Polynomial.coeff p i.val) h0
    simp only [Fbar, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single i (fun j _ hj => if_neg fun hji => hj (Fin.ext hji.symm))
      (by simp)] at hc
    exact hi (by rw [← h461, ← IsLocalRing.residue_eq_zero_iff]; simpa using hc :
      c i ∈ surfaceParameterIdeal O pi u a b)
  have hL := (concrete_surface_equiv_curve_length_and_regular _ O' pi' u' a' b' Eq q
    (completedPointMap _ P FA)).1
  rw [show Eq.symm (surfaceT O' pi' u' a' b') = completedPointMap _ P (chartBase _ _ _
    (surfaceT O pi u a b)) by rw [← hT, RingEquiv.symm_apply_apply]] at hL
  rw [hL, hF FA, hred]
  have hH : (Fbar.map ι).comp (Polynomial.X + Polynomial.C alphaBar) ≠ 0 := by
    rw [← Polynomial.taylor_apply]
    simpa [Polynomial.map_eq_zero_iff ι.injective] using hFne
  rw [order_coe_polynomial _ hH, ← Polynomial.rootMultiplicity_eq_natTrailingDegree,
    rootMultiplicity_map_eq_count_normalizedFactors _ _ ι Fbar hFne φ hφ alphaBar hroot]

/-- Proposition 5.1 (maps-to part): taking strict transforms at all exceptional points sends the
fixed tangent cell of state `s` and degree `d` into the product of the child ideal sets. -/
theorem strict_transform_mapsTo_child_ideals (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    [IsDomain (ConcreteSurface O pi u a b)] [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b))
    (hS : S.t = (surfaceT O pi u a b) ∧ S.x = (surfaceX O pi u a b) ∧ S.a = a ∧ S.b = b)
    (e : ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸
    chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ≃+*
    Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (he : ∀ r : (ConcreteSurface O pi u a b), e
    (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) r)) =
    Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) =
    Polynomial.X) (Dv : ExceptionalDivisor (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (hinf : (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)).IsPrime) (s : State) (d : ℕ) :
    Set.MapsTo (fun J Q => divisorStrictTransform (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) e Dv hinf d J Q)
      (fixedTangentCell O (ConcreteSurface O pi u a b) S s d Dv)
      (Set.pi Set.univ
      (childIdealSet (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b) e Dv
      hinf s d)) := by
  intro J hJ
  obtain ⟨f, c, H, hJf, hc, hH, hcH, hne⟩ :=
    fixed_tangent_cell_generator_coefficients O _ S s d Dv J hJ
  obtain ⟨hSt, hSx, -, hSb⟩ := hS
  rw [hSt, hSx] at hc hne
  have hstate := hJ.1
  subst hJf
  have hHBAR := reduced_form_eq_of_residue_coeff _ d c H hH.2.1 hcH
  have : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} : Set _)).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  have hinfmax := infinity_point_maximal O _ S
  rw [hSt, hSx] at hinfmax
  have : (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)).IsMaximal := hinfmax.1
  have key : ∀ (n : ℕ) (ℓ : ℕ∞), (n : ℕ∞) = d + ℓ → ℓ = ((n - d : ℕ) : ℕ∞) := by
    intro n ℓ h
    lift ℓ to ℕ using (by rintro rfl; simp at h)
    norm_cast at h ⊢
    omega
  have hT : Module.length (ConcreteSurface O pi u a b) (ConcreteSurface O pi u a b ⧸
      (Ideal.span {f} ⊔ Ideal.span {surfaceT O pi u a b})) = (stateContactT s : ℕ∞) := by
    obtain ⟨_, _, hm⟩ := hstate
    cases s with
    | single a' c' => rw [← hSt]; exact hm.2.2
    | crossing a' b' c' h' => rw [← hSt]; exact hm.2.2.1
  have hdir := directionPoint_properties _ _ _ e he heZ
  rw [Set.mem_univ_pi]
  rintro ⟨_ | φ, hQ⟩
  · have := (hdir.1 (zeroAffine _)).1
    have hmul := concrete_infinity_strict_transform_multiplicity O pi hpi u a b ha d c hne _
      hinfmax.2.1 hinfmax.2.2.1
    rw [hHBAR, Ideal.span_insert, ← hH.2.2.1] at hmul
    simp only [childIdealSet, divisorStrictTransform]
    rw [(concrete_strict_transform_generators O pi hpi u a b ha d f c hc _
      (hdir.1 (zeroAffine _)).2.1 _ hinfmax.2.1 hinfmax.2.2.1).2]
    exact ⟨⟨_, rfl⟩, hmul, fun _ ↦ key _ _ (hT.symm.trans (concrete_infinity_boundary_contact
      O pi hpi u a b ha d f c hc _ hinfmax.2.1 hinfmax.2.2.1)),
      fun h ↦ absurd h (by simp [zeroDirection])⟩
  · have := (hdir.1 φ).1
    have hmul := concrete_strict_transform_multiplicity O pi hpi u a b ha d c hne _
      (hdir.1 φ).2.1 e he heZ φ.val φ.property (hdir.1 φ).2.2.2
    rw [hHBAR, hH.2.2.2, (count_normalizedFactors_divisorAffinePolynomial _ Dv _
      (Polynomial.leadingCoeff_ne_zero.mpr hH.1) φ).1, Ideal.span_insert] at hmul
    simp only [childIdealSet, divisorStrictTransform]
    rw [(concrete_strict_transform_generators O pi hpi u a b ha d f c hc _ (hdir.1 φ).2.1 _
      hinfmax.2.1 hinfmax.2.2.1).1]
    refine ⟨⟨_, rfl⟩, hmul, fun h ↦ absurd h (by simp), fun hz h hsh ↦ ?_⟩
    obtain rfl : φ = zeroAffine _ := Option.some.inj hz
    obtain ⟨_, hv, hm⟩ := hstate
    cases s with
    | single a' c' => simp [stateContactX] at hsh
    | crossing a' b' c' h' =>
      simp only [stateContactX, Option.some.injEq] at hsh
      subst hsh
      have hb : 0 < b := by rw [← hSb, hm.2.1]; exact hv.2.1
      exact key _ _ ((hSx ▸ hm.2.2.2).symm.trans
        (concrete_zero_boundary_contact O pi hpi u a b ha hb d f c hc _ hdir.2.2))

/-! ### Normal forms of perturbed generators -/

/-- For `rho ∈ I`, the coordinate remainder map `coordinateRemainder rho b E` raises the
`I`-adic order of congruences by one. -/
private theorem scalar_normalizer_raises_order (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ)
    (I : Ideal O) (rho : O) (hrho : rho ∈ I) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R)) :
    RaisesAdicOrder I (coordinateRemainder rho b E) := by
  -- linear maps preserve I^j • ⊤
  have hlin : ∀ {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
      (L : M →ₗ[O] N) (j : ℕ) (m : M), m ∈ (I ^ j • ⊤ : Submodule O M) →
      L m ∈ (I ^ j • ⊤ : Submodule O N) := by
    intro M N _ _ _ _ L j m hm
    have : L m ∈ Submodule.map L (I ^ j • ⊤ : Submodule O M) := ⟨m, hm, rfl⟩
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  -- I^j • ⊤ in R is closed under multiplication by R
  have hmul : ∀ (j : ℕ) (c u : R), u ∈ (I ^ j • ⊤ : Submodule O R) →
      c * u ∈ (I ^ j • ⊤ : Submodule O R) := fun j c u hu => hlin (LinearMap.mulLeft O c) j u hu
  -- rho raises order
  have hsmul : ∀ {M : Type} [AddCommGroup M] [Module O M] (j : ℕ) (m : M),
      m ∈ (I ^ j • ⊤ : Submodule O M) → rho • m ∈ (I ^ (j+1) • ⊤ : Submodule O M) := by
    intro M _ _ j m hm
    rw [pow_succ', Submodule.mul_smul]
    exact Submodule.smul_mem_smul hrho hm
  let Lb : (Fin n → O) →ₗ[O] R := ∑ i, (LinearMap.proj i).smulRight (b i)
  have hLb : ∀ z, coordinateLift b z = Lb z := fun z => by simp [Lb, coordinateLift]
  intro j x y hxy
  unfold adicCongr at hxy ⊢
  have h1 : x.1 - y.1 ∈ (I ^ j • ⊤ : Submodule O (Fin n → O)) := by
    simpa using hlin (LinearMap.fst O (Fin n → O) R) j _ hxy
  have h2 : x.2 - y.2 ∈ (I ^ j • ⊤ : Submodule O R) := by
    simpa using hlin (LinearMap.snd O (Fin n → O) R) j _ hxy
  have h3 : coordinateLift b x.1 - coordinateLift b y.1 ∈ (I ^ j • ⊤ : Submodule O R) := by
    simpa [hLb] using hlin Lb j _ h1
  have h4 : x.2 * coordinateLift b x.1 - y.2 * coordinateLift b y.1
      ∈ (I ^ j • ⊤ : Submodule O R) := by
    have : x.2 * coordinateLift b x.1 - y.2 * coordinateLift b y.1
        = x.2 * (coordinateLift b x.1 - coordinateLift b y.1)
          + coordinateLift b y.1 * (x.2 - y.2) := by ring
    rw [this]
    exact Submodule.add_mem _ (hmul _ _ _ h3) (hmul _ _ _ h2)
  have h5 := hsmul j _ (hlin E.toLinearMap j _ h4)
  unfold coordinateRemainder
  rw [← smul_sub]
  simpa using h5

/-- The generator normal form is a right inverse of the adic perturbation by the coordinate
remainder of `pi ^ a`: perturbing `generatorNormalForm h` recovers `E h`. -/
private theorem power_normalizer_inverse_equation (O R : Type) [CommRing O] [CommRing R]
    [Algebra O R]
    (n : ℕ) (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (ha : 0 < a) (h : R) :
    adicPerturb (coordinateRemainder (pi^a) b E) (generatorNormalForm (pi^a) b E h) = E h := by
  have hmem : pi ^ a ∈ Ideal.span {pi} :=
    Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self pi) a ha
  have hr := scalar_normalizer_raises_order O R n (Ideal.span {pi}) (pi ^ a) hmem b E
  have hbij := adic_perturb_bijective O ((Fin n → O) × R) (Ideal.span {pi}) _ hr
  exact Function.rightInverse_invFun hbij.2 (E h)

/-- Coordinate equation satisfied by the normal form of `H z`: its first component plus
`pi ^ a` times the normalization quadratic equals the linear part
`normalizationLinearPart E H z`. -/
private theorem normalized_coordinate_equation (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ)
    (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (H : (Fin n → O) →ₗ[O] R) (ha : 0 < a)
    (z : Fin n → O) :
    (generatorNormalForm (pi^a) b E (H z)).1 + (pi^a) • normalizationQuadratic b E
      (generatorNormalForm (pi^a) b E (H z)) = normalizationLinearPart E H z := by
  have h := congrArg Prod.fst
    (power_normalizer_inverse_equation O R n pi a b E ha (H z))
  simpa [adicPerturb, coordinateRemainder, normalizationQuadratic,
    normalizationLinearPart] using h

/-- The generator normal form for `pi ^ a` (with `0 < a`) preserves `pi`-adic congruences. -/
private theorem power_normalizer_preserves_congruence (O R : Type) [CommRing O] [CommRing R]
    [Algebra O R]
    (n : ℕ) (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (ha : 0 < a) (j : ℕ) (h h2 : R)
    (hh : adicCongr (Ideal.span {pi}) j h h2) :
    adicCongr (Ideal.span {pi}) j (generatorNormalForm (pi^a) b E h)
      (generatorNormalForm (pi^a) b E h2) := by
  have h1 := linear_map_preserves_adic_congruence O R ((Fin n → O) × R)
    (Ideal.span {pi}) E.toLinearMap j h h2 hh
  have hmem : pi ^ a ∈ Ideal.span {pi} :=
    Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self pi) a ha
  have hr := scalar_normalizer_raises_order O R n (Ideal.span {pi}) (pi ^ a) hmem b E
  rwa [(adic_perturb_congruence_iff O ((Fin n → O) × R) (Ideal.span {pi}) _ hr j _ _).symm,
    power_normalizer_inverse_equation O R n pi a b E ha h,
    power_normalizer_inverse_equation O R n pi a b E ha h2]

/-- The normalization quadratic of the normal form of `H z` depends `pi`-adically continuously
on `z`: congruent inputs give congruent outputs. -/
private theorem normalized_quadratic_preserves_congruence (O R : Type) [CommRing O] [CommRing R]
    [Algebra O R] (n : ℕ) (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (H : (Fin n → O) →ₗ[O] R) (ha : 0 < a)
    (j : ℕ) (z w : Fin n → O) (hzw : adicCongr (Ideal.span {pi}) j z w) :
    adicCongr (Ideal.span {pi}) j
      (normalizationQuadratic b E (generatorNormalForm (pi^a) b E (H z)))
      (normalizationQuadratic b E (generatorNormalForm (pi^a) b E (H w))) := by
  have h1 := linear_map_preserves_adic_congruence O _ _ _ H j z w hzw
  have h2 := power_normalizer_preserves_congruence O R n pi a b E ha j _ _ h1
  set s := generatorNormalForm (pi^a) b E (H z)
  set t := generatorNormalForm (pi^a) b E (H w)
  have hs1 := linear_map_preserves_adic_congruence O _ _ _
    (LinearMap.fst O (Fin n → O) R) j s t h2
  have hs2 := linear_map_preserves_adic_congruence O _ _ _
    (LinearMap.snd O (Fin n → O) R) j s t h2
  let L : (Fin n → O) →ₗ[O] R :=
    { toFun := coordinateLift b
      map_add' := by
        intro x y; simp [coordinateLift, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x; simp [coordinateLift, Finset.smul_sum, smul_smul] }
  have hL := linear_map_preserves_adic_congruence O _ _ _ L j _ _ hs1
  have hp := algebra_product_congruence O R _ j _ _ _ _ hs2 hL
  exact linear_map_preserves_adic_congruence O _ _ _
    ((LinearMap.fst O (Fin n → O) R).comp E.toLinearMap) j _ _ hp

/-- If `D` is injective and `pi ^ k • W ⊆ range D`, then there is a linear map `Q` with
`D ∘ Q = pi ^ k • id` and `Q ∘ D = pi ^ k • id`. -/
theorem scaled_inverse_from_image_containment (O V W : Type) [CommRing O] [AddCommGroup V]
    [Module O V] [AddCommGroup W] [Module O W] (pi : O) (k : ℕ) (D : V →ₗ[O] W)
    (hD : Function.Injective D) (himage : ∀ w : W, (pi^k) • w ∈ D.range) :
    ∃ Q : W →ₗ[O] V, (∀ w, D (Q w) = (pi^k) • w) ∧ ∀ v, Q (D v) = (pi^k) • v := by
  have hc : ∀ w : W, ∃ v : V, D v = (pi^k) • w := fun w => LinearMap.mem_range.mp (himage w)
  let f : W → V := fun w => Classical.choose (hc w)
  have hf : ∀ w, D (f w) = (pi^k) • w := fun w => Classical.choose_spec (hc w)
  let Q : W →ₗ[O] V :=
    { toFun := f
      map_add' := fun a b => hD (by rw [map_add, hf, hf, hf, smul_add])
      map_smul' := fun c a => hD (by
        rw [map_smul, hf, hf, RingHom.id_apply, smul_comm]) }
  exact ⟨Q, hf, fun v => hD <| (hf (D v)).trans (map_smul D _ v).symm⟩

/-- Over a DVR with finite residue field of size `q`, if `D` is injective on `Oⁿ` with cokernel
of length `k`, then the image of `pi ^ a • D` has index `q ^ (a * n + k)`. -/
theorem scaled_linear_image_index (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (n a k : ℕ)
    (D : (Fin n → O) →ₗ[O] (Fin n → O))
    (hk : Module.length O ((Fin n → O) ⧸ LinearMap.range D) = k) :
    (LinearMap.range ((pi^a) • D)).toAddSubgroup.index =
      (Nat.card (IsLocalRing.ResidueField O))^(a*n + k) := by
  set q := Nat.card (IsLocalRing.ResidueField O)
  have hpi0 : pi ^ a ≠ 0 := pow_ne_zero _ hpi.ne_zero
  set g : (Fin n → O) →ₗ[O] (Fin n → O) := (pi ^ a) • LinearMap.id with hg_def
  have hcomp : (pi ^ a) • D = g.comp D := by
    ext x i; simp [g]
  have hg : Function.Injective g := by
    intro x y h
    funext i
    have := congrFun h i
    simp [g] at this
    exact this.resolve_right (fun h => hpi.ne_zero h.1)
  have hD' : (LinearMap.range D).toAddSubgroup.index = q ^ k :=
    finite_length_module_card O ((Fin n → O) ⧸ LinearMap.range D) k hk
  have hrange : LinearMap.range g = Submodule.pi Set.univ
      (fun _ : Fin n => (IsLocalRing.maximalIdeal O) ^ a) := by
    have hm : (IsLocalRing.maximalIdeal O) ^ a = Ideal.span {pi ^ a} := by
      rw [hpi.maximalIdeal_eq, Ideal.span_singleton_pow]
    rw [hm]
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies,
      Ideal.mem_span_singleton', g]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, by simp [mul_comm]⟩
    · intro h
      choose y hy using h
      exact ⟨y, by funext i; simp [← hy i, mul_comm]⟩
  have hg' : (LinearMap.range g).toAddSubgroup.index = q ^ (a * n) := by
    change Nat.card ((Fin n → O) ⧸ LinearMap.range g) = _
    rw [hrange, Nat.card_congr (Submodule.quotientPi _).toEquiv, Nat.card_pi]
    simp [residue_quotient_card, q, pow_mul]
  rw [hcomp, linear_composition_index _ _ _ _ D g hg, hD', hg', ← pow_add, add_comm]

/-- Scaling the coordinates by `pi ^ m` multiplies the Haar measure of a measurable subset of
`Oⁿ` by `q⁻¹ ^ (m * n)`. -/
theorem coordinate_scale_measure (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (pi : O) (hpi : Irreducible pi) (n m : ℕ)
    (S : Set (Fin n → O)) :
    coefficientMeasure O n (coordinateScale pi m '' S) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(m*n) * coefficientMeasure O n S := by
  obtain ⟨-, hHaar, hProb, -, -⟩ :=
    coefficient_space_strict_instances O htop pi hpi n
  let L : (Fin n → O) →ₗ[O] (Fin n → O) := (pi^m) • LinearMap.id
  have hidx := scaled_linear_image_index O pi hpi n m 0 LinearMap.id (by
      rw [Nat.cast_zero, Module.length_eq_zero_iff, LinearMap.range_id]
      infer_instance)
  have hpm : pi ^ m ≠ 0 := pow_ne_zero _ hpi.ne_zero
  have hinj : Function.Injective L.toAddMonoidHom := fun _ _ hxy => smul_right_injective _ hpm hxy
  have hcont : Continuous L.toAddMonoidHom :=
    finite_coordinate_linear_continuous O n n L
  have hrange : L.toAddMonoidHom.range = (LinearMap.range L).toAddSubgroup := rfl
  have hq : 0 < Nat.card (IsLocalRing.ResidueField O) := Nat.card_pos
  have hne : L.toAddMonoidHom.range.index ≠ 0 := by
    rw [hrange, hidx]; positivity
  have : L.toAddMonoidHom.range.FiniteIndex := ⟨hne⟩
  have key := compact_injective_image_measure (Fin n → O) (Fin n → O)
    L.toAddMonoidHom hcont hinj (coefficientMeasure O n) (coefficientMeasure O n) S
  have himg : coordinateScale pi m '' S = L.toAddMonoidHom '' S := rfl
  rw [himg, key, hrange, hidx]
  simp [ENNReal.inv_pow, Nat.cast_pow]

/-! ### Regularity on special fibers -/

/-- A function with finite contact `c` along the axis `X s` of a monomial special fiber is not
divisible by `X s` (otherwise the contact length would be infinite). -/
private theorem not_mem_axis_of_contact (k : Type) [Field k] (a b c : ℕ) (s t : Fin 2) (hst : s ≠ t)
    (F : TwoSeries k)
  (hle : monomialIdeal k a b ≤ Ideal.span {(MvPowerSeries.X s : TwoSeries k)})
  (hmem : F ∈ Ideal.span {(MvPowerSeries.X s : TwoSeries k)})
  (hf : contact (Ideal.Quotient.mk (monomialIdeal k a b) F)
    (Ideal.Quotient.mk (monomialIdeal k a b) (MvPowerSeries.X s)) = c) : False := by
  have hspan : Ideal.span {Ideal.Quotient.mk (monomialIdeal k a b) F,
      Ideal.Quotient.mk (monomialIdeal k a b) (MvPowerSeries.X s)}
      = (Ideal.span {(MvPowerSeries.X s : TwoSeries k)}).map
          (Ideal.Quotient.mkₐ (TwoSeries k) (monomialIdeal k a b)) := by
    rw [Ideal.map_span, Set.image_singleton]
    have h2 : Ideal.Quotient.mkₐ (TwoSeries k) (monomialIdeal k a b) (MvPowerSeries.X s)
      = Ideal.Quotient.mk (monomialIdeal k a b) (MvPowerSeries.X s) := rfl
    rw [h2]
    refine Submodule.span_insert_eq_span ?_
    rw [← h2]
    exact Ideal.mem_span_singleton.mpr
        (map_dvd (Ideal.Quotient.mkₐ (TwoSeries k) (monomialIdeal k a b))
        (Ideal.mem_span_singleton.mp hmem))
  have e := (DoubleQuot.quotQuotEquivQuotOfLEₐ (TwoSeries k) hle).toLinearEquiv
  have h1 := e.length_eq
  rw [axis_quotient_length_top k s t hst] at h1
  rw [contact, hspan] at hf
  rw [← Module.length_eq_of_surjective (S := TwoSeries k) Ideal.Quotient.mk_surjective] at hf
  exact ENat.top_ne_natCast c (h1.symm.trans hf)

/-- The axis variables of `k⟦t, x⟧` are nonzero. -/
private theorem axis_X_ne_zero (k : Type) [Field k] (s : Fin 2) :
    (MvPowerSeries.X s : TwoSeries k) ≠ 0 := fun h0 => by
  simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single s 1)) h0

/-- If `F` is not divisible by the axis variable `X s`, then `F * W ∈ (X s ^ n)` forces
`W ∈ (X s ^ n)`. -/
private theorem mem_axis_pow_of_mul_mem (k : Type) [Field k] (s : Fin 2) (F : TwoSeries k)
    (hF : F ∉ Ideal.span {(MvPowerSeries.X s : TwoSeries k)}) :
    ∀ n : ℕ, ∀ W : TwoSeries k, F * W ∈ Ideal.span {(MvPowerSeries.X s : TwoSeries k) ^ n} →
      W ∈ Ideal.span {(MvPowerSeries.X s : TwoSeries k) ^ n} := by
  have hprime := axis_span_isPrime k s
  have hT0 := axis_X_ne_zero k s
  intro n
  induction n with
  | zero => intro W _; simp
  | succ n ih =>
    intro W hW
    have hW1 : F * W ∈ Ideal.span {(MvPowerSeries.X s : TwoSeries k)} := by
      rw [Ideal.mem_span_singleton] at hW ⊢
      exact (dvd_pow_self _ n.succ_ne_zero).trans hW
    have hWT : W ∈ Ideal.span {(MvPowerSeries.X s : TwoSeries k)} :=
      (hprime.mem_or_mem hW1).resolve_left hF
    obtain ⟨W', rfl⟩ := Ideal.mem_span_singleton.mp hWT
    have h' : F * W' ∈ Ideal.span {(MvPowerSeries.X s : TwoSeries k) ^ n} := by
      rw [Ideal.mem_span_singleton] at hW ⊢
      obtain ⟨q, hq⟩ := hW
      refine ⟨q, mul_left_cancel₀ hT0 ?_⟩
      rw [pow_succ] at hq
      linear_combination hq
    have := ih W' h'
    rw [Ideal.mem_span_singleton] at this ⊢
    rw [pow_succ']
    exact mul_dvd_mul_left _ this

/-- On the crossing special fiber `k⟦t, x⟧ ⧸ (tᵃ xᵇ)` with `a, b > 0`, a function of finite
contact with both axes is a nonzerodivisor. -/
theorem special_fiber_crossing_contact_regular (k : Type) [Field k] (a b c h : ℕ) (ha : 0 < a)
    (hb : 0 < b) (f : SpecialFiber k a b) (ht : contact f (fiberT k a b) = c)
    (hx : contact f (fiberX k a b) = h) :
    Function.Injective (fun w : SpecialFiber k a b => f * w) := by
  have hI : monomialIdeal k a b = Ideal.span
      {(MvPowerSeries.X 0 : TwoSeries k) ^ a * (MvPowerSeries.X 1 : TwoSeries k) ^ b} := rfl
  have hle0 : monomialIdeal k a b ≤ Ideal.span {(MvPowerSeries.X 0 : TwoSeries k)} := by
    rw [hI, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr (Dvd.dvd.mul_right (dvd_pow_self _ ha.ne') _)
  have hle1 : monomialIdeal k a b ≤ Ideal.span {(MvPowerSeries.X 1 : TwoSeries k)} := by
    rw [hI, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr (Dvd.dvd.mul_left (dvd_pow_self _ hb.ne') _)
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
  have hF0 : F ∉ Ideal.span {(MvPowerSeries.X 0 : TwoSeries k)} := fun hmem =>
    not_mem_axis_of_contact k a b c 0 1 (by decide) F hle0 hmem ht
  have hF1 : F ∉ Ideal.span {(MvPowerSeries.X 1 : TwoSeries k)} := fun hmem =>
    not_mem_axis_of_contact k a b h 1 0 (by decide) F hle1 hmem hx
  have hTa : (MvPowerSeries.X 0 : TwoSeries k) ^ a ≠ 0 := pow_ne_zero _ (axis_X_ne_zero k 0)
  intro w₁ w₂ hw
  obtain ⟨W₁, rfl⟩ := Ideal.Quotient.mk_surjective w₁
  obtain ⟨W₂, rfl⟩ := Ideal.Quotient.mk_surjective w₂
  simp only [← map_mul] at hw
  rw [Ideal.Quotient.eq] at hw ⊢
  rw [hI] at hw ⊢
  rw [← mul_sub] at hw
  generalize W₁ - W₂ = W at hw ⊢
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hw
  have hWa : F * W ∈ Ideal.span {(MvPowerSeries.X 0 : TwoSeries k) ^ a} :=
    Ideal.mem_span_singleton.mpr ⟨(MvPowerSeries.X 1 : TwoSeries k) ^ b * q, by rw [hq]; ring⟩
  obtain ⟨W', rfl⟩ := Ideal.mem_span_singleton.mp (mem_axis_pow_of_mul_mem k 0 F hF0 a W hWa)
  have hW'b : F * W' ∈ Ideal.span {(MvPowerSeries.X 1 : TwoSeries k) ^ b} :=
    Ideal.mem_span_singleton.mpr ⟨q, mul_left_cancel₀ hTa (by linear_combination hq)⟩
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp (mem_axis_pow_of_mul_mem k 1 F hF1 b W' hW'b)
  exact Ideal.mem_span_singleton.mpr ⟨r, by ring⟩

/-- On the single special fiber `k⟦t, x⟧ ⧸ (tᵃ)` with `a > 0`, a function of finite contact with
the axis `t = 0` is a nonzerodivisor. -/
theorem special_fiber_single_contact_regular (k : Type) [Field k] (a c : ℕ) (ha : 0 < a)
    (f : SpecialFiber k a 0) (hf : contact f (fiberT k a 0) = c) :
    Function.Injective (fun w : SpecialFiber k a 0 => f * w) := by
  have hI : monomialIdeal k a 0 = Ideal.span {(MvPowerSeries.X 0 : TwoSeries k) ^ a} := by
    simp [monomialIdeal, axisT]
  have hle : monomialIdeal k a 0 ≤ Ideal.span {(MvPowerSeries.X 0 : TwoSeries k)} := by
    rw [hI, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr (dvd_pow_self _ ha.ne')
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
  have hF : F ∉ Ideal.span {(MvPowerSeries.X 0 : TwoSeries k)} := fun hmem =>
    not_mem_axis_of_contact k a 0 c 0 1 (by decide) F hle hmem hf
  intro w₁ w₂ h
  obtain ⟨W₁, rfl⟩ := Ideal.Quotient.mk_surjective w₁
  obtain ⟨W₂, rfl⟩ := Ideal.Quotient.mk_surjective w₂
  simp only [← map_mul] at h
  rw [Ideal.Quotient.eq] at h ⊢
  rw [hI] at h ⊢
  exact mem_axis_pow_of_mul_mem k 0 F hF a _ (by rwa [mul_sub])

/-- On the concrete surface with `b = 0`, if `f` reduces to a function of positive finite contact
`c` with the special fiber axis, then `O[f]` is free of rank `a * c` over `O`. -/
theorem concrete_surface_single_curve_free (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a : ℕ) (ha : 0 < a)
    (f : ConcreteSurface O pi u a 0)
    (e : (ConcreteSurface O pi u a 0 ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi})
    ≃+* SpecialFiber (IsLocalRing.ResidueField O) a 0) (c : ℕ) (hc : 0 < c)
    (hcontact : contact
    (e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi}) f))
    (fiberT (IsLocalRing.ResidueField O) a 0) = c) :
    Module.Free O (ConcreteSurface O pi u a 0 ⧸ Ideal.span {f}) ∧ Module.Finite O
      (ConcreteSurface O pi u a 0 ⧸ Ideal.span {f}) ∧ Module.finrank O
      (ConcreteSurface O pi u a 0 ⧸ Ideal.span {f}) = a*c := by
  have hreg := special_fiber_single_contact_regular _ a c ha _ hcontact
  have hreg' := concrete_surface_residue_regular_of_special_fiber O pi u a 0 f e hreg
  have hlen := single_special_fiber_length _ a c ha _ hcontact
  have hN := (concrete_surface_special_fiber_length_transport O pi u a 0 f e).trans hlen
  have hfu : ¬ IsUnit f := by
    intro hu
    have hu' :=
        (hu.map (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi}))).map
        e
    have htop : Ideal.span
      {e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi}) f), fiberT
      (IsLocalRing.ResidueField O) a 0} = ⊤ := by
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hu'
    rw [contact, htop] at hcontact
    have : Subsingleton
        (SpecialFiber (IsLocalRing.ResidueField O) a 0 ⧸
        (⊤ : Ideal (SpecialFiber (IsLocalRing.ResidueField O) a 0))) :=
        Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero] at hcontact
    exact absurd hcontact.symm (by exact_mod_cast hc.ne')
  exact concrete_surface_curve_free_of_length O pi hpi u a 0 ha f hreg' (a*c)
      (by exact_mod_cast hN)

/-! ### The strict normalizer -/

/-- For `k < a`, the normalization correction map raises the `pi`-adic order of congruences. -/
theorem strict_correction_raises_order (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (H : (Fin n → O) →ₗ[O] R) (k : ℕ)
    (ha : k < a) (Q : (Fin n → O) →ₗ[O] (Fin n → O)) :
    RaisesAdicOrder (Ideal.span {pi}) (normalizationCorrection pi a k b E H Q) := by
  intro j x y hxy
  have h1 := normalized_quadratic_preserves_congruence O R n pi a b E H
    (by omega) j x y hxy
  have h2 := linear_map_preserves_adic_congruence O _ _ _ Q j _ _ h1
  unfold adicCongr at h2 ⊢
  unfold normalizationCorrection
  rw [← smul_sub]
  have hmem : -(pi ^ (a - k)) ∈ Ideal.span {pi} := (Submodule.neg_mem_iff _).mpr
    (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self pi) _ (by omega))
  have := Submodule.smul_mem_smul hmem h2
  rwa [← Submodule.smul_assoc, smul_eq_mul, ← pow_succ'] at this

/-- The scaled strict map factors as `pi ^ a` times the normalization linear part composed with
the adic perturbation by the normalization correction. -/
theorem strict_normalizer_factors_through_linear (O R : Type) [CommRing O] [CommRing R]
    [Algebra O R] (n : ℕ) (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (H : (Fin n → O) →ₗ[O] R) (k : ℕ)
    (ha : k < a) (Q : (Fin n → O) →ₗ[O] (Fin n → O))
    (hQ : ∀ w, normalizationLinearPart E H (Q w) = (pi ^ k) • w) (z : Fin n → O) :
    scaledStrictMap pi a b E H z = (pi^a) • normalizationLinearPart E H
      (adicPerturb (normalizationCorrection pi a k b E H Q) z) := by
  have h := normalized_coordinate_equation O R n pi a b E H (by omega) z
  have hpow : pi ^ (a - k) * pi ^ k = pi ^ a := by
    rw [← pow_add, Nat.sub_add_cancel ha.le]
  unfold scaledStrictMap adicPerturb normalizationCorrection
  rw [map_add, neg_smul, map_neg, map_smul, hQ, smul_smul, hpow, ← h]
  congr 1
  abel

/-- When `pi` lies in the Jacobson radical, the perturbed principal ideal `(g + pi ^ a • H z)`
equals the normalized ideal at the scaled strict map of `z`. -/
private theorem strict_normalizer_ideal_jacobson (O R : Type) [CommRing O] [CommRing R]
    [Algebra O R]
    (n : ℕ) (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (H : (Fin n → O) →ₗ[O] R) (ha : 0 < a)
    (hpi : algebraMap O R pi ∈ Ideal.jacobson (⊥ : Ideal R)) (g : R)
    (hE : ∀ w, E.symm w = divisionMap g b w) (z : Fin n → O) :
    Ideal.span {g + (pi^a) • H z} = normalizedIdeal g b (scaledStrictMap pi a b E H z) := by
  set s := generatorNormalForm (pi^a) b E (H z) with hs
  have h1 := scaled_normalization_identity O R n (pi^a) g b E hE s
  rw [power_normalizer_inverse_equation O R n pi a b E ha (H z),
    LinearEquiv.symm_apply_apply] at h1
  have hu : IsUnit (1 + pi^a • s.2) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    rw [add_sub_cancel_left, Algebra.smul_def, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hpi a ha)
  rw [← h1, ← hu.unit_spec, principal_ideal_unit_invariance]
  unfold normalizedIdeal normalizedGenerator scaledStrictMap coordinateLift
  congr 3
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_assoc]

/-- The scaled strict map has the same image as the linear map `z ↦ pi ^ a • L z`, where `L` is
the normalization linear part. -/
theorem strict_normalizer_lattice_image (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (H : (Fin n → O) →ₗ[O] R) (k : ℕ)
    (ha : k < a) (Q : (Fin n → O) →ₗ[O] (Fin n → O))
    (hQ : ∀ w, normalizationLinearPart E H (Q w) = (pi ^ k) • w)
    [IsAdicComplete (Ideal.span {pi}) (Fin n → O)] :
    Set.range (scaledStrictMap pi a b E H) = Set.range
      (fun z : Fin n → O => (pi^a) • normalizationLinearPart E H z) := by
  have hbij := adic_perturb_bijective O (Fin n → O) (Ideal.span {pi}) _
    (strict_correction_raises_order O R n pi a b E H k ha Q)
  have hf := strict_normalizer_factors_through_linear O R n pi a b E H k ha Q hQ
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, (hf z).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := hbij.2 w
    exact ⟨z, by rw [hf z, hz]⟩

/-- Pullback identity: if `alpha f = e ^ d * g` and `pi ^ s = e ^ d * c` in `C`, then `alpha`
sends the perturbation `f + pi ^ (s + a) • ℓ(z)` to `e ^ d` times the pulled perturbation of `g`. -/
private theorem strict_pullback_perturbation_identity (O R C : Type) [CommRing O] [CommRing R]
    [CommRing C]
    [Algebra O R] [Algebra O C] (n : ℕ) (pi : O) (s a d : ℕ) (alpha : R →ₐ[O] C) (f : R) (g e c : C)
    (b : Fin n → R) (hf : alpha f = e ^ d * g) (hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (z : Fin n → O) :
    alpha (f + (pi^(s+a)) • coordinateLift b z) = e^d *
      (g + (pi^a) • pulledVariation alpha c b z) := by
  have hL : coordinateLinear (O := O) b z = coordinateLift b z := by
    simp [coordinateLinear, coordinateLift, LinearMap.sum_apply]
  have hP : pulledVariation alpha c b z = c * alpha (coordinateLift b z) := by
    simp [pulledVariation, hL]
  rw [hP, map_add, map_smul, hf, Algebra.smul_def, Algebra.smul_def, map_pow, map_pow, pow_add, hpi]
  ring

/-- The strict transform (colon by `e ^ d`) of the pulled-back perturbed principal ideal is the
principal ideal of the pulled perturbation of `g`. -/
private theorem strict_pullback_colon_perturbation (O R C : Type) [CommRing O] [CommRing R]
    [CommRing C]
    [Algebra O R] [Algebra O C] (n : ℕ) (pi : O) (s a d : ℕ) (alpha : R →ₐ[O] C) (f : R) (g e c : C)
    (b : Fin n → R) (hf : alpha f = e ^ d * g) (hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (he : Function.Injective (fun z : C => e*z)) (z : Fin n → O) :
    ((Ideal.span {f + (pi^(s+a)) • coordinateLift b z}).map alpha.toRingHom).colon {e^d} =
      Ideal.span {g + (pi^a) • pulledVariation alpha c b z} := by
  have hid := strict_pullback_perturbation_identity O R C n pi s a d alpha f g e c b hf hpi z
  rw [Ideal.map_span, Set.image_singleton]
  change (Ideal.span {alpha (f + (pi^(s+a)) • coordinateLift b z)}).colon {e^d} = _
  rw [hid]
  have hinj : IsLeftRegular (e ^ d) := IsLeftRegular.pow d he
  ext u
  rw [Submodule.mem_colon_singleton, Ideal.mem_span_singleton', Ideal.mem_span_singleton']
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, hinj ?_⟩
    rw [smul_eq_mul] at hv
    linear_combination hv
  · rintro ⟨v, rfl⟩
    exact ⟨v, by rw [smul_eq_mul]; ring⟩

/-- The strict transform of a perturbed principal ideal is the normalized ideal at the scaled
strict map of the pulled variation. -/
private theorem actual_strict_map_is_scaled_normalizer (O R C : Type) [CommRing O] [CommRing R]
    [CommRing C]
    [Algebra O R] [Algebra O C] (n : ℕ) (pi : O) (s a d : ℕ) (alpha : R →ₐ[O] C) (f : R) (g e c : C)
    (b : Fin n → R) (hf : alpha f = e ^ d * g) (hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (he : Function.Injective (fun z : C => e*z)) (ha : 0 < a)
    (hjac : algebraMap O C pi ∈ Ideal.jacobson (⊥ : Ideal C)) (bc : Fin n → C)
    (E : C ≃ₗ[O] ((Fin n → O) × C)) (hE : ∀ w, E.symm w = divisionMap g bc w)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × C)] (z : Fin n → O) :
    ((Ideal.span {f + (pi^(s+a)) • coordinateLift b z}).map alpha.toRingHom).colon {e^d} =
      normalizedIdeal g bc (scaledStrictMap pi a bc E (pulledVariation alpha c b) z) := by
  rw [strict_pullback_colon_perturbation O R C n pi s a d alpha f g e c b hf hpi he z]
  exact strict_normalizer_ideal_jacobson O C n pi a bc E (pulledVariation alpha c b) ha hjac g hE z

/-- Chart coordinates commute with strict transforms: the strict transform of the coordinate
ideal at `pi ^ (s + a - 1) • z` is the coordinate ideal at the child coordinate map of `z`. -/
theorem strict_chart_coordinates_commute (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (n : ℕ) (pi : O) (s a d : ℕ) (alpha : R →ₐ[O] C) (f : R) (g e c : C)
    (b : Fin n → R) (hf : alpha f = e ^ d * g) (hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (he : Function.Injective (fun z : C => e*z)) (ha : 0 < a)
    (hjac : algebraMap O C pi ∈ Ideal.jacobson (⊥ : Ideal C)) (bc : Fin n → C)
    (E : C ≃ₗ[O] ((Fin n → O) × C)) (hE : ∀ w, E.symm w = divisionMap g bc w)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × C)] (z : Fin n → O) :
    strictTransformIdeal alpha e d (coordinateIdeal pi f b (coordinateScale pi (s+a-1) z)) =
      coordinateIdeal pi g bc (childCoordinateMap pi a bc E (pulledVariation alpha c b) z) := by
  have h1 : coordinateIdeal pi f b (coordinateScale pi (s+a-1) z)
      = Ideal.span {f + (pi^(s+a)) • coordinateLift b z} := by
    have h2 : pi * pi^(s+a-1) = pi^(s+a) := by
      rw [← pow_succ' pi]; congr 1; omega
    have : coordinateLift b (pi • coordinateScale pi (s+a-1) z) = (pi^(s+a)) • coordinateLift b
      z := by
      simp only [coordinateLift, coordinateScale, Finset.smul_sum, Pi.smul_apply, smul_eq_mul,
          smul_smul, ← mul_assoc, h2]
    simp only [coordinateIdeal, normalizedIdeal, normalizedGenerator, this]
  have h3 : pi • childCoordinateMap pi a bc E (pulledVariation alpha c b) z
      = scaledStrictMap pi a bc E (pulledVariation alpha c b) z := by
    have h2 : pi * pi^(a-1) = pi^a := by
      rw [← pow_succ' pi]; congr 1; omega
    simp only [childCoordinateMap, scaledStrictMap, smul_smul, h2]
  rw [h1, strictTransformIdeal,
    actual_strict_map_is_scaled_normalizer O R C n pi s a d alpha f g e c b hf hpi he ha hjac bc E
        hE z,
    coordinateIdeal, ← h3]

/-- Preimage form of `strict_chart_coordinates_commute`: on the scaled coordinate lattice, the
preimage of a set of child coordinate ideals is the scaled preimage under the child map. -/
theorem strict_chart_preimage_set_identity (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (n : ℕ) (pi : O) (s a d : ℕ) (alpha : R →ₐ[O] C) (f : R) (g e c : C)
    (b : Fin n → R) (hf : alpha f = e ^ d * g) (hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (he : Function.Injective (fun z : C => e*z)) (ha : 0 < a)
    (hjac : algebraMap O C pi ∈ Ideal.jacobson (⊥ : Ideal C)) (bc : Fin n → C)
    (E : C ≃ₗ[O] ((Fin n → O) × C)) (hE : ∀ w, E.symm w = divisionMap g bc w)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × C)]
    (hΨ : Function.Injective (coordinateIdeal pi g bc)) (T : Set (Fin n → O)) :
    coordinateIdeal pi f b ⁻¹' (strictTransformIdeal alpha e d ⁻¹' (coordinateIdeal pi g bc '' T)) ∩
      Set.range (coordinateScale pi (s+a-1)) = coordinateScale pi (s+a-1) ''
      (childCoordinateMap pi a bc E (pulledVariation alpha c b) ⁻¹' T) := by
  have key := fun z => strict_chart_coordinates_commute O R C n pi s a d alpha f g e c b hf hpi he
      ha hjac bc E hE z
  ext x
  constructor
  · rintro ⟨hx, z, rfl⟩
    refine ⟨z, ?_, rfl⟩
    obtain ⟨w, hw, hw2⟩ := hx
    rw [key] at hw2
    change _ ∈ T; rwa [← hΨ hw2]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, z, rfl⟩
    simp only [Set.mem_preimage]
    rw [key]
    exact ⟨_, hz, rfl⟩

/-! ### Strict quotient maps -/

/-- Additivity of cokernel lengths along a composition with injective second factor. -/
private theorem length_coker_comp (O : Type) [CommRing O] {M N P : Type} [AddCommGroup M]
    [Module O M]
    [AddCommGroup N] [Module O N] [AddCommGroup P] [Module O P]
    (u : M →ₗ[O] N) (v : N →ₗ[O] P) (hv : Function.Injective v) :
    Module.length O (P ⧸ LinearMap.range (v.comp u)) =
      Module.length O (N ⧸ LinearMap.range u) + Module.length O (P ⧸ LinearMap.range v) := by
  have h1 : LinearMap.range u ≤ (LinearMap.range (v.comp u)).comap v := by
    rintro _ ⟨m, rfl⟩
    exact ⟨m, rfl⟩
  have h2 : LinearMap.range (v.comp u) ≤ (LinearMap.range v).comap LinearMap.id := by
    rintro _ ⟨m, rfl⟩
    exact ⟨u m, rfl⟩
  refine Module.length_eq_add_of_exact (Submodule.mapQ _ _ v h1)
    (Submodule.mapQ _ _ LinearMap.id h2) ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨m, hm⟩ := hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, hv hm⟩
  · intro y
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk p, rfl⟩
  · intro y
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨Submodule.Quotient.mk n, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
      obtain ⟨m, hm⟩ := hx
      refine ⟨n - u m, ?_⟩
      simp only [LinearMap.comp_apply] at hm
      rw [map_sub, hm]; abel

/-- Cokernel length of `w ^ k` for an injective endomorphism `w`. -/
private theorem length_coker_pow (O : Type) [CommRing O] {P : Type} [AddCommGroup P] [Module O P]
    (w : Module.End O P) (hw : Function.Injective w) (k : ℕ) :
    Module.length O (P ⧸ LinearMap.range (w ^ k)) = k * Module.length O
      (P ⧸ LinearMap.range w) := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_mul, Module.length_eq_zero_iff, pow_zero, Module.End.one_eq_id,
      LinearMap.range_id]
    infer_instance
  | succ k ih =>
    rw [pow_succ', Module.End.mul_eq_comp, length_coker_comp O _ _ hw, ih]
    push_cast; ring

/-- `tri d = chooseTwo d + d`. -/
private theorem tri_eq_chooseTwo_add (d : ℕ) : tri d = chooseTwo d + d := by
  unfold tri chooseTwo
  cases d with
  | zero => rfl
  | succ n =>
    have : (n+1)*(n+1+1) = (n+1)*(n+1-1) + (n+1)*2 := by
      simp only [Nat.add_sub_cancel]; ring
    rw [this, Nat.add_mul_div_right _ _ (by norm_num)]

/-- Length of the cokernel of the strict quotient map `phi`: it equals `s * N - tri d`, computed
from the relation `e ^ d * phi = pi ^ s • iota` and the cokernel lengths of `iota`, `e`, `pi`. -/
theorem strict_quotient_cokernel_length (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (alpha : R →ₐ[O] C) (f : R) (g e c : C) (d : ℕ)
    (pi : O) (s : ℕ) (hpi : (algebraMap O C pi) ^ s = e ^ d * c) (N : ℕ)
    (phi iota : (R ⧸ Ideal.span {f}) →ₗ[O] (C ⧸ Ideal.span {g}))
    (hphi : ∀ h : R, phi (Ideal.Quotient.mk (Ideal.span {f}) h) = Ideal.Quotient.mk (Ideal.span {g})
    (c * alpha h))
    (hiota : ∀ h : R, iota (Ideal.Quotient.mk (Ideal.span {f}) h) = Ideal.Quotient.mk
    (Ideal.span {g}) (alpha h))
    (hindex : Module.length O ((C ⧸ Ideal.span {g}) ⧸ LinearMap.range iota) = (chooseTwo d : ℕ∞))
    (hereg : Function.Injective
    (fun y : C ⧸ Ideal.span {g} => Ideal.Quotient.mk (Ideal.span {g}) e * y))
    (hechild : Module.length O
    ((C ⧸ Ideal.span {g}) ⧸ LinearMap.range
    (LinearMap.mulLeft O (Ideal.Quotient.mk (Ideal.span {g}) e))) = (d : ℕ∞))
    (hpireg : Function.Injective (fun y : C ⧸ Ideal.span {g} => (pi : O) • y))
    (hpiquot : Module.length O
    ((C ⧸ Ideal.span {g}) ⧸ LinearMap.range
    ((pi : O) • (LinearMap.id : (C ⧸ Ideal.span {g}) →ₗ[O] (C ⧸ Ideal.span {g})))) = (N : ℕ∞))
    (hsmall : tri d ≤ s*N) :
    Module.length O ((C ⧸ Ideal.span {g}) ⧸ LinearMap.range phi) = ((s*N - tri d : ℕ) : ℕ∞) := by
  set me : Module.End O (C ⧸ Ideal.span {g}) := LinearMap.mulLeft O
      (Ideal.Quotient.mk (Ideal.span {g}) e)
  set mp : Module.End O (C ⧸ Ideal.span {g}) := (pi : O) •
      (LinearMap.id : (C ⧸ Ideal.span {g}) →ₗ[O] (C ⧸ Ideal.span {g}))
  have hrel : (me ^ d).comp phi = (mp ^ s).comp iota := by
    apply LinearMap.ext
    intro u
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective u
    have hme' : ∀ k y, (me ^ k) y = Ideal.Quotient.mk (Ideal.span {g}) (e ^ k) * y := fun k y ↦ by
      simp [me]
    have hmp' : ∀ k y, (mp ^ k) y = (pi ^ k) • y := fun k ↦ by
      induction k with
      | zero => simp
      | succ k ih => intro y; simp [pow_succ', Module.End.mul_apply, ih, mp, mul_smul]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hme', hmp', hphi, hiota,
      Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, ← map_mul, map_pow, hpi,
      mul_assoc]
  have hme : Function.Injective me := hereg
  have hmp : Function.Injective mp := hpireg
  have key := congrArg (fun F => Module.length O ((C ⧸ Ideal.span {g}) ⧸ LinearMap.range F)) hrel
  rw [length_coker_comp O _ _ (hme.iterate d |> fun h => by simpa [Module.End.coe_pow] using h),
    length_coker_comp O _ _ (hmp.iterate s |> fun h => by simpa [Module.End.coe_pow] using h),
    length_coker_pow O _ hme, length_coker_pow O _ hmp, hindex, hechild, hpiquot] at key
  have ht := tri_eq_chooseTwo_add d
  have h2 : 2 * tri d = d * d + d := by
    unfold tri
    rw [Nat.mul_div_cancel' (Nat.even_mul_succ_self d).two_dvd]; ring
  have hdd : d * d = chooseTwo d + tri d := by omega
  have hL : Module.length O ((C ⧸ Ideal.span {g}) ⧸ LinearMap.range phi) ≠ ⊤ := fun h ↦ by
    rw [h, top_add] at key
    exact ENat.natCast_ne_top (chooseTwo d + s * N) (by rw [key]; push_cast; rfl)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hL
  rw [← hn] at key ⊢
  norm_cast at key ⊢
  omega

/-- If `alpha f = e ^ d * g`, then `alpha` descends to an `O`-linear map
`R ⧸ (f) → C ⧸ (g)`. -/
theorem strict_quotient_inclusion_exists (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (alpha : R →ₐ[O] C) (f : R) (g e : C) (d : ℕ)
    (hf : alpha f = e ^ d * g) :
    ∃ iota : (R ⧸ Ideal.span {f}) →ₗ[O] (C ⧸ Ideal.span {g}), ∀ h : R, iota
      (Ideal.Quotient.mk (Ideal.span {f}) h) = Ideal.Quotient.mk (Ideal.span {g}) (alpha h) := by
  have hle : Ideal.span {f} ≤ (Ideal.span {g}).comap alpha :=
    (Ideal.span_singleton_le_iff_mem _).mpr <| by
      rw [Ideal.mem_comap, hf]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)
  exact ⟨(Ideal.quotientMapₐ (Ideal.span {g}) alpha hle).toLinearMap, fun h => rfl⟩

/-- If `alpha f = e ^ d * g`, then `h ↦ c * alpha h` descends to an `O`-linear map
`R ⧸ (f) → C ⧸ (g)`. -/
theorem strict_quotient_map_exists (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (alpha : R →ₐ[O] C) (f : R) (g e c : C) (d : ℕ)
    (hf : alpha f = e ^ d * g) :
    ∃ phi : (R ⧸ Ideal.span {f}) →ₗ[O] (C ⧸ Ideal.span {g}), ∀ h : R, phi
      (Ideal.Quotient.mk (Ideal.span {f}) h) = Ideal.Quotient.mk (Ideal.span {g})
          (c * alpha h) := by
  let L : R →ₗ[O] (C ⧸ Ideal.span {g}) :=
    (Ideal.Quotient.mkₐ O (Ideal.span {g})).toLinearMap ∘ₗ (LinearMap.mulLeft O c) ∘ₗ
        alpha.toLinearMap
  have hL : (Ideal.span {f}).restrictScalars O ≤ LinearMap.ker L := by
    intro x hx
    rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨r, rfl⟩ := hx
    simp only [LinearMap.mem_ker, L, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply, map_mul, hf,
      Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g)]
    simp
  exact ⟨((Ideal.span {f}).restrictScalars O).liftQ L hL, fun h => rfl⟩

/-- The strict quotient map `phi` and the inclusion `iota` satisfy `e ^ d * phi = pi ^ s • iota`. -/
private theorem strict_quotient_maps_relation (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (alpha : R →ₐ[O] C) (f : R) (g e c : C) (d : ℕ)
    (pi : O) (s : ℕ) (hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (phi iota : (R ⧸ Ideal.span {f}) →ₗ[O] (C ⧸ Ideal.span {g}))
    (hphi : ∀ h : R, phi (Ideal.Quotient.mk (Ideal.span {f}) h) = Ideal.Quotient.mk (Ideal.span {g})
    (c * alpha h))
    (hiota : ∀ h : R, iota (Ideal.Quotient.mk (Ideal.span {f}) h) = Ideal.Quotient.mk
    (Ideal.span {g}) (alpha h)) (u : R ⧸ Ideal.span {f}) :
    Ideal.Quotient.mk (Ideal.span {g}) (e^d) * phi u = (pi^s) • iota u := by
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [hphi, hiota, Algebra.smul_def, ← map_mul, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
    map_pow, hpi, mul_assoc]

/-- If `iota` is injective and `pi` is a nonzerodivisor on `C ⧸ (g)`, then the strict quotient
map `phi` is injective. -/
theorem strict_quotient_map_injective (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (alpha : R →ₐ[O] C) (f : R) (g e c : C) (d : ℕ)
    (pi : O) (s : ℕ) (hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (phi iota : (R ⧸ Ideal.span {f}) →ₗ[O] (C ⧸ Ideal.span {g}))
    (hphi : ∀ h : R, phi (Ideal.Quotient.mk (Ideal.span {f}) h) = Ideal.Quotient.mk (Ideal.span {g})
    (c * alpha h))
    (hiota : ∀ h : R, iota (Ideal.Quotient.mk (Ideal.span {f}) h) = Ideal.Quotient.mk
    (Ideal.span {g}) (alpha h)) (hiota_inj : Function.Injective iota)
    (hpireg : Function.Injective (fun y : C ⧸ Ideal.span {g} => (pi : O) • y)) :
    Function.Injective phi := by
  have key : ∀ x : C ⧸ Ideal.span {g}, (pi ^ s) • x = 0 → x = 0 := fun x h =>
    IsSMulRegular.pow s hpireg (h.trans (smul_zero _).symm)
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h := strict_quotient_maps_relation O R C alpha f g e c d pi s hpi phi iota hphi hiota u
  rw [hu, mul_zero] at h
  apply hiota_inj
  rw [map_zero]
  exact key _ h.symm

/-! ### Strict transforms across the two charts -/

/-- Ring isomorphisms commute with colon ideals. -/
private theorem colon_map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (I : Ideal A) (y : A) :
    (I.colon {y}).map (e : A →+* B) = (I.map (e : A →+* B)).colon {e y} := by
  ext z
  rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv, Ideal.mem_comap,
    Submodule.mem_colon_singleton, Submodule.mem_colon_singleton, Ideal.mem_comap]
  simp only [smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]

/-- Colon by `y * v` equals colon by `y` for a unit `v`. -/
private theorem colon_singleton_mul_unit {B : Type*} [CommRing B] (K : Ideal B) (y v : B)
    (hv : IsUnit v) :
    K.colon {y * v} = K.colon {y} := by
  ext z
  rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, Ideal.mul_unit_mem_iff_mem _ hv]

/-- Transport of strict transforms along an isomorphism of completed local rings compatible
with the base maps and with `x = t * unit`. -/
private theorem strictTransformAt_map_of_compat (R : Type) [CommRing R] (t x : R)
    (PA : Ideal (BlowupChart R t x)) [PA.IsPrime]
    (PB : Ideal (BlowupChart R x t)) [PB.IsPrime]
    (Ψ : CompletedLocalAt (BlowupChart R t x) PA ≃+* CompletedLocalAt (BlowupChart R x t) PB)
    (u : CompletedLocalAt (BlowupChart R x t) PB) (hu : IsUnit u)
    (hbase : ∀ r : R, Ψ (completedPointMap _ PA (chartBase R t x r)) = completedPointMap _ PB
        (chartBase R x t r))
    (hx : completedPointMap _ PB (chartBase R x t x) = Ψ
        (completedPointMap _ PA (chartBase R t x t)) * u)
    (d : ℕ) (J : Ideal R) :
    (strictTransformAt R t x PA d J).map Ψ.toRingHom = strictTransformAt R x t PB d J := by
  have hJ : (J.map ((completedPointMap (BlowupChart R t x) PA).comp (chartBase R t x))).map
      (Ψ : _ →+* _) =
      J.map ((completedPointMap (BlowupChart R x t) PB).comp (chartBase R x t)) := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext hbase
  unfold strictTransformAt
  have := colon_map_ringEquiv Ψ
      (J.map ((completedPointMap (BlowupChart R t x) PA).comp (chartBase R t x)))
    ((completedPointMap (BlowupChart R t x) PA (chartBase R t x t))^d)
  refine this.trans ?_
  rw [hJ, map_pow, hx, mul_pow, colon_singleton_mul_unit _ _ _ (hu.pow d)]

/-- At a common point of the two charts, the gluing isomorphism of completed local rings carries
the left-chart strict transform of `J` to the right-chart strict transform. -/
theorem strict_transform_common_point_transport (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta) (i : D.ι) (d : ℕ)
    (J : Ideal R) :
    (strictTransformAt R t x (leftPoint D (Sum.inl i)) d J).map
      ((D.rightIso i).toRingHom.comp (D.leftIso i).symm.toRingHom) = strictTransformAt R x t
      (rightPoint D (Sum.inl i)) d J := by
  have key : ∀ a : BlowupChart R t x, ((D.leftIso i).symm.trans (D.rightIso i))
      (completedPointMap _ ((D.Q i).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) a)
          =
      D.rightIso i
          (completedPointMap _ (D.Q i)
              (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) a)) := by
    intro a
    rw [RingEquiv.trans_apply, ← D.leftIso_compat i a, RingEquiv.symm_apply_apply]
  have hR : ∀ r : R, algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x r) =
      beta.right (chartBase R x t r) := by
    intro r
    have h1 : chartBase R x t r = algebraMap R (BlowupChart R x t) r := rfl
    have h2 : chartBase R t x r = algebraMap R (BlowupChart R t x) r := rfl
    rw [h1, h2, beta.right.commutes, ← IsScalarTower.algebraMap_apply]
  have hbase : ∀ r : R, ((D.leftIso i).symm.trans (D.rightIso i))
      (completedPointMap _ ((D.Q i).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)))
          (chartBase R t x r)) =
      completedPointMap _ ((D.Q i).comap beta.right.toRingHom) (chartBase R x t r) := by
    intro r
    rw [key, hR]
    exact D.rightIso_compat i _
  have hrel : chartBase R t x t * chartSlope R t x = chartBase R t x x := by
    unfold chartBase chartSlope
    rw [RingHom.comp_apply, RingHom.comp_apply, ← map_mul, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hx : completedPointMap _ ((D.Q i).comap beta.right.toRingHom) (chartBase R x t x) =
      ((D.leftIso i).symm.trans (D.rightIso i))
        (completedPointMap _ ((D.Q i).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)))
            (chartBase R t x t)) *
      D.rightIso i
          (completedPointMap _ (D.Q i)
          (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x))) := by
    rw [← hbase, ← hrel, key, key, map_mul, map_mul, map_mul]
  have hunit : IsUnit
      (D.rightIso i
      (completedPointMap _ (D.Q i)
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x)))) := by
    exact ((IsLocalization.Away.algebraMap_isUnit (chartSlope R t x)).map _).map _
  exact strictTransformAt_map_of_compat R t x _ _ ((D.leftIso i).symm.trans (D.rightIso i)) _ hunit
      hbase hx d J

/-- If the local intersection length of `F` with `y ∈ P` vanishes, then `F` is a unit. -/
private theorem span_eq_top_of_length_eq_zero {A : Type} [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] (y : A) (hy : y ∈ P) (F : CompletedLocalAt A P)
    (h : Module.length (CompletedLocalAt A P)
        (CompletedLocalAt A P ⧸ Ideal.span {F, completedPointMap A P y}) = 0) :
    Ideal.span {F} = ⊤ := by
  have : IsNoetherianRing (Localization.AtPrime P) := IsLocalization.isNoetherianRing P.primeCompl _
      inferInstance
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff] at h
  have hy' : completedPointMap A P y ∈ IsLocalRing.maximalIdeal (CompletedLocalAt A P) := by
    have h1 : algebraMap A (Localization.AtPrime P) y ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime P) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hy
    rw [IsLocalRing.mem_maximalIdeal] at h1 ⊢
    exact fun hu ↦ h1 ((isUnit_map_iff (algebraMap (Localization.AtPrime P) _) _).mp hu)
  by_contra hF
  have hF' : F ∈ IsLocalRing.maximalIdeal (CompletedLocalAt A P) :=
    fun hu ↦ hF (Ideal.span_singleton_eq_top.mpr hu)
  have : Ideal.span {F, completedPointMap A P y} ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.span_le.mpr (Set.pair_subset hF' hy')
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ this))

/-- For an ideal `J` of a fixed tangent cell, the strict transform of `J` at a point of the
exceptional divisor where the tangent divisor `Dv` has multiplicity zero is the unit ideal. -/
private theorem cell_strictTransformAt_eq_top (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b))
    (hS : S.t = surfaceT O pi u a b ∧ S.x = surfaceX O pi u a b)
    (e : ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸
    chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ≃+*
    Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (he : ∀ r : (ConcreteSurface O pi u a b), e
    (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) r)) =
    Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) =
    Polynomial.X)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (hinf : (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)).IsPrime) (s : State) (d : ℕ) (J : Ideal (ConcreteSurface O pi u a b))
    (hJ : J ∈ fixedTangentCell O _ S s d Dv) :
    (∀ φ, Dv (some φ) = 0 → strictTransformAt _ _ _
      (directionPoint _ (surfaceT O pi u a b) (surfaceX O pi u a b) e φ) d J = ⊤) ∧
    (Dv none = 0 → strictTransformAt _ (surfaceX O pi u a b) (surfaceT O pi u a b)
      (infinityPoint _ (surfaceT O pi u a b) (surfaceX O pi u a b)) d J = ⊤) := by
  rcases S with ⟨pi', hpi', t', x', v', a', b', ha', hpar, hdim, hcomp, hinj, hres, hrc, hvert⟩
  simp only at hS
  obtain ⟨rfl, rfl⟩ := hS
  have : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} : Set _)).IsMaximal := by
    rw [hpar]; infer_instance
  have hdp := directionPoint_properties (ConcreteSurface O pi u a b) _ _ e he heZ
  have hinfP := infinity_point_maximal O _ ⟨pi', hpi', surfaceT O pi u a b,
    surfaceX O pi u a b, v', a', b', ha', hpar, hdim, hcomp, hinj, hres, hrc, hvert⟩
  have : (infinityPoint _ (surfaceT O pi u a b) (surfaceX O pi u a b)).IsMaximal := hinfP.1
  have := blowupChart_concrete_isNoetherianRing O pi u a b (surfaceT O pi u a b)
      (surfaceX O pi u a b)
  have := blowupChart_concrete_isNoetherianRing O pi u a b (surfaceX O pi u a b)
      (surfaceT O pi u a b)
  obtain ⟨f, c, H, rfl, hf, hH, hc, hne⟩ :=
    fixed_tangent_cell_generator_coefficients O _ _ s d Dv J hJ
  have hred := reduced_form_eq_of_residue_coeff _ d c H hH.2.1 hc
  refine ⟨fun φ hz ↦ ?_, fun hz ↦ ?_⟩
  · have : (directionPoint _ (surfaceT O pi u a b) (surfaceX O pi u a b) e φ).IsMaximal :=
      (hdp.1 φ).1
    have hP := (hdp.1 φ).2.1
    rw [(concrete_strict_transform_generators O pi hpi u a b ha d f c hf _ hP _ hinfP.2.1
      hinfP.2.2.1).1]
    refine span_eq_top_of_length_eq_zero _ _ hP _ ?_
    rw [concrete_strict_transform_multiplicity O pi hpi u a b ha d c hne _ hP e he heZ φ.val
      φ.property (hdp.1 φ).2.2.2, hred, hH.2.2.2, (count_normalizedFactors_divisorAffinePolynomial
      _ Dv _ (Polynomial.leadingCoeff_ne_zero.mpr hH.1) φ).1, hz]
    rfl
  · have : (directionPoint _ (surfaceT O pi u a b) (surfaceX O pi u a b) e
        (zeroAffine _)).IsMaximal := (hdp.1 _).1
    rw [(concrete_strict_transform_generators O pi hpi u a b ha d f c hf _
      (hdp.1 (zeroAffine _)).2.1 _ hinfP.2.1 hinfP.2.2.1).2]
    refine span_eq_top_of_length_eq_zero _ _ hinfP.2.1 _ ?_
    rw [concrete_infinity_strict_transform_multiplicity O pi hpi u a b ha d c hne _ hinfP.2.1
      hinfP.2.2.1, hred, ← hH.2.2.1, hz]
    rfl

/-- If two ideals of the same fixed tangent cell have equal strict transforms at the points of
positive divisor multiplicity, and the first has the prescribed strict transforms at all datum
points, then so does the second. -/
theorem cell_strict_transforms_agree_at_datum_points (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b))
    (hS : S.t = (surfaceT O pi u a b) ∧ S.x = (surfaceX O pi u a b) ∧ S.a = a ∧ S.b = b)
    (e : ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸
    chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ≃+*
    Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (he : ∀ r : (ConcreteSurface O pi u a b), e
    (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) r)) =
    Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) =
    Polynomial.X) (Dv : ExceptionalDivisor (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (hinf : (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)).IsPrime) (s : State) (d : ℕ) (J₁ J₂ : Ideal (ConcreteSurface O pi u a b))
    (h₁ : J₁ ∈ (fixedTangentCell O (ConcreteSurface O pi u a b) S s d Dv))
    (h₂ : J₂ ∈ (fixedTangentCell O (ConcreteSurface O pi u a b) S s d Dv))
    (heq : ∀ Q : divisorSupport Dv, divisorStrictTransform (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b) e Dv hinf d J₁ Q = divisorStrictTransform
    (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b) e Dv hinf d J₂ Q)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
    beta) (hm : MatchesDivisor e D Dv)
    (hst₁ : ∀ s : D.ι ⊕ D.ι0, strictTransformAt (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b) (leftPoint D s) d J₁ = Ideal.span {leftData D s})
    (hst₁r : ∀ s : D.ι ⊕ D.ιinf, strictTransformAt (ConcreteSurface O pi u a b)
    (surfaceX O pi u a b) (surfaceT O pi u a b) (rightPoint D s) d J₁ = Ideal.span {rightData D s})
    :
    (∀ s : D.ι ⊕ D.ι0, strictTransformAt (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) (leftPoint D s) d J₂ = Ideal.span {leftData D s}) ∧ ∀ s : D.ι ⊕ D.ιinf,
      strictTransformAt (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)
      (rightPoint D s) d J₂ = Ideal.span {rightData D s} := by
  rcases S with ⟨pi', hpi', t', x', v', a', b', ha', hpar, hdim, hcomp, hinj, hres, hrc, hvert⟩
  simp only at hS
  obtain ⟨rfl, rfl, -, -⟩ := hS
  set S₀ : SurfaceData O (ConcreteSurface O pi u a b) := ⟨pi', hpi', surfaceT O pi u a b,
    surfaceX O pi u a b, v', a', b', ha', hpar, hdim, hcomp, hinj, hres, hrc, hvert⟩
  have htop := fun J (hJ : J ∈ fixedTangentCell O _ S₀ s d Dv) ↦
    cell_strictTransformAt_eq_top O pi hpi u a b ha S₀ ⟨rfl, rfl⟩ e he heZ Dv hinf s d J hJ
  have left_eq : ∀ φ, strictTransformAt _ _ _
      (directionPoint _ (surfaceT O pi u a b) (surfaceX O pi u a b) e φ) d J₂ =
      strictTransformAt _ _ _ (directionPoint _ (surfaceT O pi u a b) (surfaceX O pi u a b) e φ) d
        J₁ := fun φ ↦ by
    by_cases hpos : 0 < Dv (some φ)
    · exact (heq ⟨some φ, hpos⟩).symm
    · rw [(htop J₂ h₂).1 φ (by omega), (htop J₁ h₁).1 φ (by omega)]
  have right_eq : strictTransformAt _ (surfaceX O pi u a b) (surfaceT O pi u a b)
      (infinityPoint _ (surfaceT O pi u a b) (surfaceX O pi u a b)) d J₂ =
      strictTransformAt _ (surfaceX O pi u a b) (surfaceT O pi u a b)
        (infinityPoint _ (surfaceT O pi u a b) (surfaceX O pi u a b)) d J₁ := by
    by_cases hpos : 0 < Dv none
    · exact (heq ⟨none, hpos⟩).symm
    · rw [(htop J₂ h₂).2 (by omega), (htop J₁ h₁).2 (by omega)]
  -- Transport along an equality of points (the `IsPrime` instances block a plain `rw`).
  have key : ∀ {T X : ConcreteSurface O pi u a b} (P P' : Ideal (BlowupChart _ T X)) [P.IsPrime]
      [P'.IsPrime], P = P' → strictTransformAt _ T X P' d J₂ = strictTransformAt _ T X P' d J₁ →
      strictTransformAt _ T X P d J₂ = strictTransformAt _ T X P d J₁ := by
    intro T X P P' _ _ h; subst h; exact id
  have hleft : ∀ s, strictTransformAt _ _ _ (leftPoint D s) d J₂ = strictTransformAt _ _ _
      (leftPoint D s) d J₁ := by
    rintro (i | k)
    · obtain ⟨φ, hφ, hQ, -⟩ := hm.common i
      refine key _ (directionPoint _ _ _ e φ) ?_ (left_eq φ)
      change (D.Q i).comap _ = _
      rw [hQ]
      exact (direction_point_overlap_maximal O _ S₀ e he heZ φ hφ).2.2
    · exact key _ _ (hm.zero k).1 (left_eq _)
  refine ⟨fun s ↦ (hleft s).trans (hst₁ s), ?_⟩
  rintro (i | l)
  · rw [← strict_transform_common_point_transport, hleft, strict_transform_common_point_transport]
    exact hst₁r _
  · rw [key (rightPoint D (Sum.inr l)) _ (hm.inf l).1 right_eq]
    exact hst₁r _

/-- Recovering a strict transform equation from its truncations: if `φ ≡ e ^ d * F j` modulo
`e ^ j` and `(F j, e ^ j) = (g, e ^ j)` for all `j`, then `φ = e ^ d * g * v` for a unit `v`. -/
theorem strict_transform_equation_from_levels (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (e g : S) (he : e ∈ IsLocalRing.maximalIdeal S)
    (hereg : Function.Injective (fun a : S => e * a))
    (hg : Function.Injective
    (fun a : S ⧸ Ideal.span {e} => Ideal.Quotient.mk (Ideal.span {e}) g * a)) (d : ℕ) (F : ℕ → S)
    (hFideal : ∀ j : ℕ, Ideal.span {F j, e^j} = Ideal.span {g, e^j}) (φ : S)
    (hφ : ∀ j : ℕ, φ - e^d * F j ∈ Ideal.span {e^j}) :
    ∃ v : Sˣ, φ = e^d * g * (v : S) := by
  -- injectivity of multiplication by e^n
  have hpow : ∀ n : ℕ, ∀ a b : S, e ^ n * a = e ^ n * b → a = b := fun n _ _ h =>
    IsLeftRegular.pow n hereg h
  -- Step A: φ = e^d ψ
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hφ d)
  set ψ := F d + t with hψ
  have hφψ : φ = e ^ d * ψ := by rw [hψ]; linear_combination -ht
  -- Step B: ψ = F (d+k) + e^k s
  have hB : ∀ k : ℕ, ∃ s : S, ψ = F (d + k) + e ^ k * s := by
    intro k
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (hφ (d + k))
    refine ⟨s, hpow d _ _ ?_⟩
    rw [← hφψ]
    linear_combination -hs
  -- Step C: ψ ∈ span {g}
  have hC : ψ ∈ Ideal.span {g} := by
    have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := Ideal.span {e})
      (M := S ⧸ Ideal.span {g})
      (by rw [Ne, Ideal.span_singleton_eq_top]; exact (IsLocalRing.mem_maximalIdeal e).mp he)
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : (Ideal.Quotient.mk (Ideal.span {g}) ψ) ∈
        (⨅ i : ℕ, (Ideal.span {e}) ^ i • ⊤ : Submodule S (S ⧸ Ideal.span {g})) := by
      rw [Submodule.mem_iInf]
      intro k
      obtain ⟨s, hs⟩ := hB k
      have hF : F (d + k) ∈ Ideal.span {g, e ^ (d + k)} := by
        rw [← hFideal]; exact Ideal.subset_span (by simp)
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hF
      have : Ideal.Quotient.mk (Ideal.span {g}) ψ =
          e ^ k • Ideal.Quotient.mk (Ideal.span {g}) (b * e ^ d + s) := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
          Ideal.Quotient.eq, Ideal.mem_span_singleton']
        refine ⟨a, ?_⟩
        rw [hs, ← hab]; ring
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self e) k)
        Submodule.mem_top
    rw [key] at this
    simpa using this
  obtain ⟨v₀, hv₀⟩ := Ideal.mem_span_singleton'.mp hC
  -- Step D: v₀ is a unit
  obtain ⟨s, hs⟩ := hB 1
  have hg1 : g ∈ Ideal.span {F (d + 1), e ^ (d + 1)} := by
    rw [hFideal]; exact Ideal.subset_span (by simp)
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hg1
  have hmem : 1 - a * v₀ ∈ Ideal.span {e} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hg
    simp only [mul_zero]
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨b * e ^ d - a * s, ?_⟩
    have : F (d + 1) = v₀ * g - e * s := by rw [hv₀]; linear_combination -hs
    rw [this] at hab
    linear_combination hab
  have hv : IsUnit v₀ := isUnit_of_mul_isUnit_right <|
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (a * v₀)).resolve_right
      ((IsLocalRing.mem_maximalIdeal _).1 ((Ideal.span_singleton_le_iff_mem _).2 he hmem))
  refine ⟨hv.unit, ?_⟩
  rw [IsUnit.unit_spec, hφψ, ← hv₀]; ring

/-- If `f' ∈ (t, x) ^ d` and its strict transform at `P` is `(g)`, then `f' ∈ (g)` locally. -/
private theorem mem_strictTransform_of_mem_pow (R : Type) [CommRing R] (t x : R)
    (P : Ideal (BlowupChart R t x)) [P.IsPrime]
    (d : ℕ) (f' : R) (hd : f' ∈ (Ideal.span {t,x}) ^ d)
    (g : CompletedLocalAt (BlowupChart R t x) P)
    (h : strictTransformAt R t x P d (Ideal.span {f'}) = Ideal.span {g}) :
    completedPointMap (BlowupChart R t x) P (algebraMap R (BlowupChart R t x) f') ∈ Ideal.span
      {g} := by
  have hmap : (Ideal.span ({t,x} : Set R)).map (chartBase R t x) ≤ Ideal.span
      {chartBase R t x t} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · exact Ideal.subset_span rfl
    · rw [← blowup_chart_relation]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have h1 : chartBase R t x f' ∈ Ideal.span {chartBase R t x t ^ d} := by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hmap d
        (Ideal.map_pow (chartBase R t x) _ d ▸ Ideal.mem_map_of_mem _ hd)
  obtain ⟨F, hF⟩ := Ideal.mem_span_singleton'.mp h1
  have halg : algebraMap R (BlowupChart R t x) f' = chartBase R t x f' := rfl
  set ψ := completedPointMap (BlowupChart R t x) P
  have hcol : ψ F ∈ strictTransformAt R t x P d (Ideal.span {f'}) := by
    unfold strictTransformAt
    rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.map_span, Set.image_singleton]
    refine Ideal.mem_span_singleton'.mpr ⟨1, ?_⟩
    simp only [RingHom.comp_apply, one_mul]
    rw [← hF, map_mul, map_pow]
  rw [h] at hcol
  rw [halg, ← hF, map_mul]
  exact Ideal.mul_mem_right _ _ hcol

/-- If `f' ∈ (t, x) ^ d` has the given strict transforms at all datum points, then its image in
the chart pair lies in the curve ideal lattice of every level `j`. -/
theorem strict_transforms_give_level_lattice_membership (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x)
    (D : TwoChartCurveData R t x beta) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hG : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} =
    leftLevelKernel D j ∧ Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} =
    rightLevelKernel D j) (f' : R) (hd : f' ∈ (Ideal.span {t,x})^d)
    (hleft : ∀ s : D.ι ⊕ D.ι0, strictTransformAt R t x (leftPoint D s) d (Ideal.span {f'}) =
    Ideal.span {leftData D s})
    (hright : ∀ s : D.ι ⊕ D.ιinf, strictTransformAt R x t (rightPoint D s) d (Ideal.span {f'}) =
    Ideal.span {rightData D s}) (j : ℕ) :
    surfaceToChartPair R t x f' ∈ curveIdealLattice R t x beta G j := by
  obtain ⟨hl, hr⟩ := curve_ideal_lattice_eq_kernels R t x beta D d G hG j
  have hd' : f' ∈ (Ideal.span {x,t})^d := by rwa [Set.pair_comm]
  unfold curveIdealLattice
  rw [Submodule.mem_prod]
  refine ⟨?_, ?_⟩
  · change algebraMap R (BlowupChart R t x) f' ∈ leftCurveIdeal R t x beta G j
    rw [hl, leftKernel, finiteSupportKernel, Ideal.mem_iInf]
    intro s
    rw [Ideal.mem_comap, leftLevelIdeal, finiteLocalCurveIdeal]
    exact Ideal.span_mono (by simp) (mem_strictTransform_of_mem_pow R t x _ d f' hd _ (hleft s))
  · change algebraMap R (BlowupChart R x t) f' ∈ rightCurveIdeal R t x beta G j
    rw [hr, rightKernel, finiteSupportKernel, Ideal.mem_iInf]
    intro s
    rw [Ideal.mem_comap, rightLevelIdeal, finiteLocalCurveIdeal]
    exact Ideal.span_mono (by simp) (mem_strictTransform_of_mem_pow R x t _ d f' hd' _ (hright s))

end SurfaceBlowup
