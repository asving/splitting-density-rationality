/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.CurveOrders
import SurfaceBlowup.Surfaces.Regularity

/-!
# Completions of the blow-up charts of the concrete surface

Let `R = O[[T,X]]/(π - u T^a X^b)` be the concrete surface and `R[x/t]`, `R[t/x]` the two charts
of its blow-up at the closed point. We show that the completed local rings of these charts at
the closed points of the exceptional divisor are again concrete surfaces (over `O` at rational
points, over the unramified extension `O[θ]` at non-rational points).

## Main results

* `chart_child_completion_equiv`: the general completion isomorphism for a chart map.
* `t_chart_nonrational_point_completion_equiv`, `t_chart_origin_completion_equiv`,
  `t_chart_unit_point_completion_equiv`, `x_chart_infinity_completion_equiv`.
* `concrete_residue_ideal_chart_exists`: lifting curves of the special fiber.

Provenance: `chart_child_{completion_equiv, map_exists}`, `concrete_residue_ideal_chart_exists`,
`chart_point_quotient_adjoinRoot_equiv`, `chart_{nonrational,rational}_point_span_eq_comap`,
`nonrational_point_{derivative_isUnit_mod, hensel_root}`,
`t_chart_{nonrational_point, origin, unit_point}_completion_equiv`,
`x_chart_infinity_completion_equiv`.
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

/-- The chart `R[f/e]` of the concrete surface `R`, where `e, f` are the images of `E, F`. -/
local notation:max "efChart" O:max pi:max u:max a:max b:max E:max F:max =>
  BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)

/-- The structure map `R → R[f/e]`. -/
local notation:max "efBase" O:max pi:max u:max a:max b:max E:max F:max =>
  chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)

/-- The slope `f/e` in the chart `R[f/e]`. -/
local notation:max "efSlope" O:max pi:max u:max a:max b:max E:max F:max =>
  chartSlope (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)

/-- The child surface over `O[θ] = O[X]/(Φ)` at a non-rational point of the exceptional divisor. -/
local notation:max "childSurface" O:max pi:max u:max a:max b:max Φ:max hθ:max =>
  ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
        (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0

/-- The unit of the child surface over `O[θ] = O[X]/(Φ)` at a non-rational point. -/
local notation:max "childUnit" O:max u:max b:max Φ:max hθ:max =>
  substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
      (AdjoinRoot.root Φ) hθ ^ b

/-! ### Completions of charts at closed points -/

/-- An endomorphism of the completed local ring of a noetherian ring `A` at a maximal ideal `P`
that fixes the image of `A` and preserves the maximal ideal is the identity. -/
private theorem completedLocalAt_ringHom_eq_id (A : Type) [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsMaximal] (φ : CompletedLocalAt A P →+* CompletedLocalAt A P)
    (hφ : φ.comp (completedPointMap A P) = completedPointMap A P)
    (hle : IsLocalRing.maximalIdeal (CompletedLocalAt A P) ≤
      (IsLocalRing.maximalIdeal (CompletedLocalAt A P)).comap φ) :
    φ = RingHom.id _ := by
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  set M := IsLocalRing.maximalIdeal (CompletedLocalAt A P)
  have hmhat : M = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (localCompletionMap (Localization.AtPrime P)) := AdicCompletion.maximalIdeal_eq_map
  refine RingHom.ext <| congrFun <| IsHausdorff.funext' M (f := fun y => φ y)
    (g := fun y => y) fun n y => ?_
  obtain ⟨x, hx⟩ := finite_completed_point_quotient_surjective A P n (M ^ n) (by rw [hmhat])
    (Ideal.Quotient.mk _ y)
  rw [RingHom.comp_apply] at hx
  have h : φ (completedPointMap A P x - y) ∈ M ^ n :=
    (Ideal.pow_right_mono hle n).trans (Ideal.le_comap_pow φ n) (Ideal.Quotient.eq.mp hx)
  rw [map_sub, ← RingHom.comp_apply φ, hφ] at h
  exact (Ideal.Quotient.eq.mpr h).symm.trans hx

/-- Let `Λ : R[f/e] → R'` be a chart map to a concrete surface `R'` over `O'`, compatible with a
substitution `s : O[[T,X]] → O'[[T,X]]` (`E ↦ T`, `F ↦ T (X + α)`), and surjective modulo the
parameter ideal. Then the completion of `R[f/e]` at `P = Λ⁻¹(t', x')` is isomorphic to `R'`. -/
theorem chart_child_completion_equiv (O O' : Type) [CommRing O] [IsNoetherianRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) (pi' : O')
    (hpi' : Irreducible pi') (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a') (E F : TwoSeries O)
    (hEF : (E = axisT O ∧ F = axisX O) ∨ (E = axisX O ∧ F = axisT O)) (ρ : O →+* O') (α : O')
    (s : TwoSeries O →+* TwoSeries O')
    (hsC : ∀ c : O, s (MvPowerSeries.C c) = MvPowerSeries.C (ρ c)) (hsE : s E = axisT O')
    (hsF : s F = axisT O' * (axisX O' + MvPowerSeries.C α))
    (hs : s (surfaceRelation O pi u a b) = surfaceRelation O' pi' u' a' b')
    (Λ : efChart O pi u a b E F →+* ConcreteSurface O' pi' u' a' b')
    (hΛ : ∀ g : TwoSeries O, Λ (efBase O pi u a b E F (surfaceMk O pi u a b g)) =
        surfaceMk O' pi' u' a' b' (s g))
    (hΛZ : Λ (efSlope O pi u a b E F) = surfaceX O' pi' u' a' b' + algebraMap O'
        (ConcreteSurface O' pi' u' a' b') α)
    (P : Ideal (efChart O pi u a b E F)) [P.IsPrime] (hP : ∀ x, x ∈ P ↔ Λ x ∈ surfaceParameterIdeal
        O' pi' u' a' b')
    (hsurj : ∀ y : ConcreteSurface O' pi' u' a' b', ∃ x : efChart O pi u a b E F,
      Λ x - y ∈ surfaceParameterIdeal O' pi' u' a' b')
    (Λ' : CompletedLocalAt (efChart O pi u a b E F) P →+* ConcreteSurface O' pi' u' a' b')
    (hΛ' : ∀ x, Λ' (completedPointMap (efChart O pi u a b E F) P x) = Λ x)
        (κ : O' →+* CompletedLocalAt (efChart O pi u a b E F) P)
    (hκ : ∀ c : O', Λ' (κ c) = algebraMap O' (ConcreteSurface O' pi' u' a' b') c)
    (hκρ : ∀ c : O,
      κ (ρ c) = completedPointMap (efChart O pi u a b E F) P
      (efBase O pi u a b E F (algebraMap O (ConcreteSurface O pi u a b) c))) :
    ∃ Eq : CompletedLocalAt (efChart O pi u a b E F) P ≃+* ConcreteSurface O' pi' u' a' b',
      (∀ y, Eq y = Λ' y) ∧ ∀ c : O',
      Eq.symm (algebraMap O' (ConcreteSurface O' pi' u' a' b') c) = κ c := by
  have : IsNoetherianRing (efChart O pi u a b E F) :=
    blowupChart_concrete_isNoetherianRing O pi u a b _ _
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have : IsLocalRing (ConcreteSurface O' pi' u' a' b') :=
    concrete_surface_isLocalRing O' pi' u' a' b' hpi'.not_isUnit ha'
  have hm := concrete_surface_maximalIdeal_eq O' pi' hpi' u' a' b' ha'
  have := concrete_surface_isAdicComplete_maximalIdeal O' pi' hpi' u' a' b' ha'
  set M := IsLocalRing.maximalIdeal (CompletedLocalAt (efChart O pi u a b E F) P) with hM
  have hmhat : M = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (localCompletionMap (Localization.AtPrime P)) := AdicCompletion.maximalIdeal_eq_map
  have hmem : ∀ y, y ∈ M ↔ Λ' y ∈ surfaceParameterIdeal O' pi' u' a' b' := by
    rw [hmhat]; exact chart_child_completion_map_local _ O' pi' hpi' u' a' b' ha' Λ P hP Λ' hΛ'
  have hTmem : surfaceT O' pi' u' a' b' ∈ surfaceParameterIdeal O' pi' u' a' b' :=
    Ideal.subset_span (by simp)
  have hXmem : surfaceX O' pi' u' a' b' ∈ surfaceParameterIdeal O' pi' u' a' b' :=
    Ideal.subset_span (by simp)
  -- The images `e` of `E` and `z = f/e - α` in the completion lie in its maximal ideal `M`.
  set e := completedPointMap _ P (efBase O pi u a b E F (surfaceMk O pi u a b E)) with he_def
  set z := completedPointMap _ P (efSlope O pi u a b E F) - κ α with hz_def
  have hΛE : Λ (efBase O pi u a b E F (surfaceMk O pi u a b E)) = surfaceT O' pi' u' a' b' := by
    rw [hΛ, hsE]; rfl
  have hΛ'e : Λ' e = surfaceT O' pi' u' a' b' := by rw [hΛ', hΛE]
  have hΛ'z : Λ' z = surfaceX O' pi' u' a' b' := by rw [map_sub, hΛ', hΛZ, hκ]; ring
  have he : e ∈ M := by rw [hmem, hΛ'e]; exact hTmem
  have hz : z ∈ M := by rw [hmem, hΛ'z]; exact hXmem
  -- Evaluating `T ↦ e`, `X ↦ z` gives an inverse candidate `Θ : R' → completion`.
  obtain ⟨Θt, hΘC, hΘT, hΘX⟩ := twoSeries_eval_exists_of_isAdicComplete _ M O' κ _ _ he hz
  have hcomp : ∀ g,
      Θt (s g) = completedPointMap _ P (efBase O pi u a b E F (surfaceMk O pi u a b g)) :=
    congrFun <| congrArg DFunLike.coe <| child_series_eval_comp_chart_subst O O' pi u a b E F hEF
      P (by rw [hP, hΛE]; exact hTmem)
      (by rw [hP, hΛ, hsF, map_mul]; exact Ideal.mul_mem_right _ _ hTmem) ρ α s hsC hsE hsF κ hκρ
      Θt hΘC hΘT hΘX
  have hrel : Θt (surfaceRelation O' pi' u' a' b') = 0 := by
    have : surfaceMk O pi u a b (surfaceRelation O pi u a b) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [← hs, hcomp, this, map_zero, map_zero]
  let Θ : ConcreteSurface O' pi' u' a' b' →+* CompletedLocalAt (efChart O pi u a b E F) P :=
    Ideal.Quotient.lift (surfaceIdeal O' pi' u' a' b') Θt fun r hr => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [map_mul, hrel, mul_zero]
  have hΘmk : ∀ g, Θ (surfaceMk O' pi' u' a' b' g) = Θt g := fun g => Ideal.Quotient.lift_mk _ _ _
  have hΘalg : ∀ c : O', Θ (algebraMap O' (ConcreteSurface O' pi' u' a' b') c) = κ c :=
    fun c => (hΘmk _).trans (hΘC c)
  have hΘT' : Θ (surfaceT O' pi' u' a' b') = e := (hΘmk _).trans hΘT
  have hΘX' : Θ (surfaceX O' pi' u' a' b') = z := (hΘmk _).trans hΘX
  -- `Λ' ∘ Θ = id`, checked modulo each power of the maximal ideal of `R'`.
  have h5 : Λ'.comp Θ = RingHom.id _ := by
    refine RingHom.ext <| congrFun <| IsHausdorff.funext' (IsLocalRing.maximalIdeal _)
      (f := fun r => Λ' (Θ r)) (g := fun r => r) fun n r => ?_
    let Q := IsLocalRing.maximalIdeal (ConcreteSurface O' pi' u' a' b') ^ n
    refine DFunLike.congr_fun (concrete_surface_ringHom_ext_of_isNilpotent O'
      (ConcreteSurface O' pi' u' a' b' ⧸ Q) pi' u' a' b' ((Ideal.Quotient.mk Q).comp (Λ'.comp Θ))
      (Ideal.Quotient.mk Q) ?_ ?_ ?_ ?_ ?_) r
    all_goals simp only [RingHom.comp_apply, hΘalg, hκ, hΘT', hΘX', hΛ'e, hΛ'z, implies_true]
    all_goals refine ⟨n, ?_⟩
    all_goals rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exacts [Ideal.pow_mem_pow (hm ▸ hTmem) n, Ideal.pow_mem_pow (hm ▸ hXmem) n]
  -- `Θ ∘ Λ' = id`, checked modulo each power of `M`, using that `P` is maximal.
  have hPe : (IsLocalRing.maximalIdeal _).comap Λ = P := by ext x; rw [Ideal.mem_comap, hm, hP]
  have : P.IsMaximal := by
    rw [← hPe]; exact chart_point_isMaximal_of_residue_surjective _ _ Λ (hm ▸ hsurj)
  have hfix : Θ.comp Λ = completedPointMap _ P := by
    apply blowup_chart_ringHom_ext
    · intro r
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Θ (Λ (chartBase _ _ _ (surfaceMk O pi u a b g))) = _
      rw [hΛ, hΘmk, hcomp]; rfl
    · change Θ (Λ _) = _
      rw [hΛZ, map_add, hΘalg, hΘX', hz_def]; ring
  have hle : M ≤ M.comap (Θ.comp Λ') := fun y hy => by
    refine (Ideal.span_le (I := M.comap Θ)).2 ?_ ((hmem y).1 hy)
    rintro w (rfl | rfl) <;> simp only [SetLike.mem_coe, Ideal.mem_comap, hΘT', hΘX', he, hz]
  have h6 : Θ.comp Λ' = RingHom.id _ :=
    completedLocalAt_ringHom_eq_id _ P _ (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, hΛ' x]; exact DFunLike.congr_fun hfix x) hle
  exact ⟨RingEquiv.ofRingHom Λ' Θ h5 h6, fun y => rfl, hΘalg⟩

/-- A substitution `s : O[[T,X]] → O'[[T,X]]` with `E ↦ T`, `F ↦ T (X + α)` that maps the
relation of `R` into the relation ideal of `R'` induces a chart map `R[f/e] → R'` with
`f/e ↦ x' + α`. -/
private theorem chart_child_map_exists (O O' : Type) [CommRing O] [CommRing O'] (pi : O)
    (u : (TwoSeries O)ˣ) (a b : ℕ) (pi' : O') (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (E F : TwoSeries O)
    (s : TwoSeries O →+* TwoSeries O')
    (hs : s (surfaceRelation O pi u a b) ∈ surfaceIdeal O' pi' u' a' b') (α : O')
    (hE : s E = axisT O') (hF : s F = axisT O' * (axisX O' + MvPowerSeries.C α)) :
    ∃ Λ : efChart O pi u a b E F →+* ConcreteSurface O' pi' u' a' b',
      (∀ g : TwoSeries O, Λ (efBase O pi u a b E F (surfaceMk O pi u a b g)) =
          surfaceMk O' pi' u' a' b' (s g)) ∧
      Λ (efSlope O pi u a b E F) = surfaceX O' pi' u' a' b' + algebraMap O'
          (ConcreteSurface O' pi' u' a' b') α := by
  have hk : ∀ x ∈ surfaceIdeal O pi u a b, (surfaceMk O' pi' u' a' b') (s x) = 0 := by
    intro x hx
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul, map_mul]
    have : (surfaceMk O' pi' u' a' b') (s (surfaceRelation O pi u a b)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hs
    rw [this, zero_mul]
  let σ : ConcreteSurface O pi u a b →+* ConcreteSurface O' pi' u' a' b' :=
    Ideal.Quotient.lift _ ((surfaceMk O' pi' u' a' b').comp s) hk
  have hσ : ∀ g, σ (surfaceMk O pi u a b g) = surfaceMk O' pi' u' a' b' (s g) := fun g =>
    Ideal.Quotient.lift_mk _ _ _
  have hC : surfaceMk O' pi' u' a' b' (MvPowerSeries.C α) = algebraMap O'
      (ConcreteSurface O' pi' u' a' b') α := rfl
  obtain ⟨psi, h1, h2⟩ := blowup_chart_universal (ConcreteSurface O pi u a b)
      (ConcreteSurface O' pi' u' a' b')
    (surfaceMk O pi u a b E) (surfaceMk O pi u a b F) σ
    (surfaceX O' pi' u' a' b' + algebraMap O' (ConcreteSurface O' pi' u' a' b') α) (by
      rw [hσ, hσ, hE, hF, map_mul, map_add, hC]; rfl)
  exact ⟨psi, fun g => by rw [h1, hσ], h2⟩

/-- Every non-unit, non-zero-divisor `f̄` of the special fiber lifts to an ideal chart of the
concrete surface whose reduction generates the same ideal as `f̄`. -/
theorem concrete_residue_ideal_chart_exists (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b)
    (fbar : SpecialFiber (IsLocalRing.ResidueField O) a b) (hunit : ¬ IsUnit fbar)
    (hreg : Function.Injective (fun w : SpecialFiber (IsLocalRing.ResidueField O) a b => fbar * w))
    (N : ℕ) (hN : Module.length (SpecialFiber (IsLocalRing.ResidueField O) a b)
      (SpecialFiber (IsLocalRing.ResidueField O) a b ⧸ Ideal.span {fbar}) = N) :
    ∃ ch : IdealChart O (ConcreteSurface O pi u a b) pi N,
      Ideal.span
      {e ((Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})) ch.f)} =
      Ideal.span {fbar} := by
  obtain ⟨q, hq⟩ := e.surjective fbar
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hfu : ¬ IsUnit f := fun h => hunit
      (hq ▸ (h.map
        (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}))).map e)
  have hreg' : Function.Injective (fun w : SpecialFiber (IsLocalRing.ResidueField O) a b =>
      e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}) f) * w) := by
          rw [hq]; exact hreg
  have hregR := concrete_surface_residue_regular_of_special_fiber O pi u a b f e hreg'
  have hlen := concrete_surface_special_fiber_length_transport O pi u a b f e
  rw [hq, hN] at hlen
  obtain ⟨hfree, hfin, hrank⟩ :=
    concrete_surface_curve_free_of_length O pi hpi u a b ha f hregR N hlen
  have := concrete_surface_isDomain O pi hpi u a b ha
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : Subsingleton (SpecialFiber (IsLocalRing.ResidueField O) a b) :=
      ⟨fun x y => hreg (by simp only [← hq, map_zero, zero_mul])⟩
    exact hunit (Subsingleton.elim 1 fbar ▸ isUnit_one)
  let B0 := Module.Free.chooseBasis O (ConcreteSurface O pi u a b ⧸ Ideal.span {f})
  have hcard : Fintype.card
      (Module.Free.ChooseBasisIndex O (ConcreteSurface O pi u a b ⧸ Ideal.span {f})) = N := by
    rw [← hrank, Module.finrank_eq_card_chooseBasisIndex]
  let B : Module.Basis (Fin N) O (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) :=
    B0.reindex ((Fintype.equivFin _).trans (finCongr hcard))
  choose bb hbb using fun i => Ideal.Quotient.mk_surjective (B i)
  obtain ⟨E, hE⟩ := division_linear_equivalence O (ConcreteSurface O pi u a b) N f B bb hbb hf0
  refine ⟨⟨f, bb, E, hE, ?_⟩, ?_⟩
  · intro x y hxy
    apply hregR
    simp only at hxy ⊢
    exact (mul_comm _ _).trans (hxy.trans (mul_comm _ _))
  · exact congrArg (fun z => Ideal.span {z}) hq

/-! ### Closed points of the exceptional divisor -/

/-- For a polynomial `Φ` over `R`, the quotient of the chart `R[f/e]` by `(e, Φ(f/e))` is
`(R/(e, f))[X]/(Φ̄)`. -/
private theorem chart_point_quotient_adjoinRoot_equiv (R : Type) [CommRing R] (e f : R)
    (Φ : Polynomial R) :
    ∃ q : (BlowupChart R e f ⧸ Ideal.span
        {chartBase R e f e, Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) Φ}) ≃+* AdjoinRoot
      (Φ.map (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R)))),
      (∀ r : R, q (Ideal.Quotient.mk _ (chartBase R e f r)) = AdjoinRoot.of _
        (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R)) r)) ∧ q
      (Ideal.Quotient.mk _ (chartSlope R e f)) = AdjoinRoot.root _ := by
  obtain ⟨ε, hεb, hεs⟩ := exceptional_chart_is_affine_line R e f
  set P := Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) Φ with hP
  set J := exceptionalLevelIdeal R e f 1 with hJ
  have hsup : Ideal.span {chartBase R e f e, P} = J ⊔ Ideal.span {P} := by
    rw [hJ, exceptionalLevelIdeal, pow_one, ← Ideal.span_insert]
  have hεP : ε (Ideal.Quotient.mk J P) =
      Φ.map (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R))) := by
    rw [hP, Polynomial.hom_eval₂]
    change (ε.toRingHom) _ = _
    rw [Polynomial.hom_eval₂]
    have h1 : ε.toRingHom.comp ((Ideal.Quotient.mk J).comp (chartBase R e f)) =
        Polynomial.C.comp (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R))) := by
      exact RingHom.ext hεb
    have h2 : ε.toRingHom (Ideal.Quotient.mk J (chartSlope R e f)) = Polynomial.X := hεs
    rw [h1, h2]
    rfl
  have hK : Ideal.span {Φ.map (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R)))} =
      (Ideal.map (Ideal.Quotient.mk J) (Ideal.span {P})).map ε.toRingHom := by
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    simp [hεP]
  let E1 := Ideal.quotEquivOfEq hsup
  let E2 := (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {P})).symm
  let E3 : ((BlowupChart R e f ⧸ J) ⧸ (Ideal.map (Ideal.Quotient.mk J) (Ideal.span {P}))) ≃+*
      AdjoinRoot (Φ.map (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R)))) :=
    Ideal.quotientEquiv _ _ ε hK
  refine ⟨(E1.trans E2).trans E3, ?_, ?_⟩
  · intro r
    change Ideal.Quotient.mk _ (ε (Ideal.Quotient.mk J (chartBase R e f r))) = _
    rw [show Ideal.Quotient.mk J (chartBase R e f r) = levelBase R e f 1 r from rfl, hεb]
    rfl
  · change Ideal.Quotient.mk _ (ε (Ideal.Quotient.mk J (chartSlope R e f))) = _
    rw [show Ideal.Quotient.mk J (chartSlope R e f) = levelSlope R e f 1 from rfl, hεs]
    rfl

/-- If `Φ̄` is irreducible over the field `R/(e, f)`, then `(e, Φ(f/e))` is a maximal ideal of the
chart, equal to the preimage of the maximal ideal under any local map `Λ` killing it. -/
theorem chart_nonrational_point_span_eq_comap (R : Type) [CommRing R] (e f : R)
    [(Ideal.span ({e, f} : Set R)).IsMaximal] (Φ : Polynomial R)
    (hΦ : Irreducible (Φ.map (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R))))) (S : Type)
    [CommRing S] [IsLocalRing S] (Λ : BlowupChart R e f →+* S)
    (he : Λ (chartBase R e f e) ∈ IsLocalRing.maximalIdeal S)
    (hΦZ : Λ (Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) Φ)
      ∈ IsLocalRing.maximalIdeal S) :
    (Ideal.span
        {chartBase R e f e, Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) Φ}).IsMaximal ∧
      Ideal.span {chartBase R e f e, Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) Φ} =
      (IsLocalRing.maximalIdeal S).comap Λ := by
  obtain ⟨q, -, -⟩ := chart_point_quotient_adjoinRoot_equiv R e f Φ
  let _ := Ideal.Quotient.field (Ideal.span ({e, f} : Set R))
  have : Fact (Irreducible (Φ.map (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R))))) := ⟨hΦ⟩
  have hF : IsField (AdjoinRoot (Φ.map (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R))))) :=
    Field.toIsField _
  have hmax :
      (Ideal.span
        {chartBase R e f e, Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) Φ}).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField hF q.toMulEquiv)
  refine ⟨hmax,
        hmax.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal S).ne_top) ?_⟩
  rw [Ideal.span_le]
  rintro x (rfl | rfl)
  exacts [he, hΦZ]

/-- `(e, f/e - r)` is a maximal ideal of the chart `R[f/e]`, equal to the preimage of the maximal
ideal under any local map `Λ` killing it. -/
private theorem chart_rational_point_span_eq_comap (R : Type) [CommRing R] (e f : R)
    [(Ideal.span ({e, f} : Set R)).IsMaximal] (S : Type) [CommRing S] [IsLocalRing S]
    (Λ : BlowupChart R e f →+* S) (r : R) (he : Λ (chartBase R e f e) ∈ IsLocalRing.maximalIdeal S)
    (hr : Λ (chartSlope R e f) - Λ (chartBase R e f r) ∈ IsLocalRing.maximalIdeal S) :
    (Ideal.span {chartBase R e f e, chartSlope R e f - chartBase R e f r}).IsMaximal ∧ Ideal.span
      {chartBase R e f e, chartSlope R e f - chartBase R e f r} =
      (IsLocalRing.maximalIdeal S).comap Λ := by
  have hmax : (Ideal.span {chartBase R e f e, chartSlope R e f - chartBase R e f r}).IsMaximal := by
    obtain ⟨q, -, -⟩ := chart_point_quotient_adjoinRoot_equiv R e f
      (Polynomial.X - Polynomial.C r)
    have hev : Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) (Polynomial.X - Polynomial.C r)
        = chartSlope R e f - chartBase R e f r := by
      simp [Polynomial.eval₂_sub]
    rw [hev] at q
    have hmap : (Polynomial.X - Polynomial.C r).map
        (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R)))
        = Polynomial.X - Polynomial.C (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R)) r) := by
      simp
    rw [hmap] at q
    let : Field (R ⧸ Ideal.span ({e, f} : Set R)) := Ideal.Quotient.field _
    let q2 := (Polynomial.quotientSpanXSubCAlgEquiv
      (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R)) r)).toRingEquiv
    apply Ideal.Quotient.maximal_of_isField
    exact MulEquiv.isField (Field.toIsField (R ⧸ Ideal.span ({e, f} : Set R)))
      (q.trans q2).toMulEquiv
  refine ⟨hmax,
        hmax.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal S).ne_top) ?_⟩
  rw [Ideal.span_le]
  rintro x (rfl | rfl)
  exacts [he, by simpa [map_sub] using hr]

/-- For an unramified lift `Φ`, the derivative `Φ'(x/t)` is invertible modulo the non-rational
point `(t, Φ(x/t))` of the `t`-chart. -/
private theorem nonrational_point_derivative_isUnit_mod (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O)
    (hΦ : IsUnramifiedLift O Φ) :
    ∃ w : tChart O pi u a b,
      Polynomial.eval₂ ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b)))
          (tSlope O pi u a b)
      (Polynomial.derivative Φ) * w - 1 ∈ Ideal.span
      {tBase O pi u a b (surfaceT O pi u a b),
        Polynomial.eval₂ ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b)))
            (tSlope O pi u a b) Φ} := by
  set R := ConcreteSurface O pi u a b
  set t := surfaceT O pi u a b
  set x := surfaceX O pi u a b
  set I : Ideal R := Ideal.span ({t, x} : Set R) with hI
  have hmax : I.IsMaximal := concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  let _ : Field (R ⧸ I) := Ideal.Quotient.field I
  obtain ⟨e, -⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  have : Finite (R ⧸ I) := Finite.of_equiv _ e.toEquiv.symm
  set ψ : Polynomial (R ⧸ I) := (Φ.map (algebraMap O R)).map (Ideal.Quotient.mk I) with hψ
  have hirr : Irreducible ψ := by
    rw [hψ, Polynomial.map_map]
    exact unramified_lift_map_parameter_quotient_irreducible O pi hpi u a b ha Φ hΦ
  have : Fact (Irreducible ψ) := ⟨hirr⟩
  have hder : Polynomial.derivative ψ ≠ 0 :=
    (Polynomial.separable_iff_derivative_ne_zero hirr).1
        (PerfectField.separable_of_irreducible hirr)
  rw [← Polynomial.eval₂_map, ← Polynomial.eval₂_map, ← Polynomial.derivative_map]
  set J := Ideal.span
      {chartBase R t x t,
        Polynomial.eval₂ (chartBase R t x) (chartSlope R t x) (Φ.map (algebraMap O R))} with hJ
  obtain ⟨q, hqb, hqs⟩ := chart_point_quotient_adjoinRoot_equiv R t x (Φ.map (algebraMap O R))
  have hcomp : ((q : _ →+* AdjoinRoot ψ).comp (Ideal.Quotient.mk J)).comp (chartBase R t x)
      = (AdjoinRoot.of ψ).comp (Ideal.Quotient.mk I) := RingHom.ext hqb
  have heval : ∀ P : Polynomial R,
      q (Ideal.Quotient.mk J (Polynomial.eval₂ (chartBase R t x) (chartSlope R t x) P))
      = AdjoinRoot.mk ψ (P.map (Ideal.Quotient.mk I)) := by
    intro P
    change ((q : _ →+* AdjoinRoot ψ).comp (Ideal.Quotient.mk J))
        (Polynomial.eval₂ (chartBase R t x) (chartSlope R t x) P) = _
    rw [Polynomial.hom_eval₂, hcomp, RingHom.comp_apply]
    erw [hqs]
    rw [← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
    rfl
  set D := Polynomial.eval₂ (chartBase R t x) (chartSlope R t x)
      (Polynomial.derivative (Φ.map (algebraMap O R)))
  have hD : q (Ideal.Quotient.mk J D) = AdjoinRoot.mk ψ (Polynomial.derivative ψ) := by
    rw [heval]
    simp only [hψ, Polynomial.derivative_map]
  have hne : AdjoinRoot.mk ψ (Polynomial.derivative ψ) ≠ 0 := by
    rw [Ne, AdjoinRoot.mk_eq_zero]
    exact fun hdvd => hder
      (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd (Polynomial.degree_derivative_lt hirr.ne_zero))
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
      (q.symm (AdjoinRoot.mk ψ (Polynomial.derivative ψ))⁻¹)
  refine ⟨w, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hsplit : Ideal.Quotient.mk J (D * w - 1) =
      Ideal.Quotient.mk J D * Ideal.Quotient.mk J w - 1 := rfl
  apply q.injective
  rw [hsplit, RingEquiv.map_zero]
  erw [map_sub q, map_mul q, map_one q, hD, hw, RingEquiv.apply_symm_apply, mul_inv_cancel₀ hne,
        sub_self]

/-- Hensel's lemma at a non-rational point `P = (t, Φ(x/t))` of the `t`-chart: `Φ` has a root in
the completion at `P` congruent to `x/t` modulo the maximal ideal. -/
private theorem nonrational_point_hensel_root (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O)
    (hΦ : IsUnramifiedLift O Φ) (P : Ideal (tChart O pi u a b)) [P.IsPrime]
    (hP : P = Ideal.span
      {tBase O pi u a b (surfaceT O pi u a b),
      Polynomial.eval₂ ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b)))
          (tSlope O pi u a b) Φ}) :
    ∃ θ' : CompletedLocalAt (tChart O pi u a b) P,
      Polynomial.eval₂
      ((completedPointMap (tChart O pi u a b) P).comp ((tBase O pi u a b).comp
          (algebraMap O (ConcreteSurface O pi u a b))))
      θ' Φ = 0 ∧ θ' - completedPointMap (tChart O pi u a b) P (tSlope O pi u a b) ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (localCompletionMap (Localization.AtPrime P)) := by
  set A := tChart O pi u a b
  set φ := (tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b)) with hφ
  set Z := tSlope O pi u a b
  obtain ⟨w, hw⟩ := nonrational_point_derivative_isUnit_mod O pi hpi u a b ha Φ hΦ
  rw [← hP] at hw
  have : IsNoetherianRing A := blowupChart_concrete_isNoetherianRing O pi u a b _ _
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  set L := Localization.AtPrime P
  set c := completedPointMap A P
  have hmap : (IsLocalRing.maximalIdeal L).map (localCompletionMap L)
      = IsLocalRing.maximalIdeal (CompletedLocalAt A P) :=
    (AdicCompletion.maximalIdeal_eq_map (R := L)).symm
  have hPm : ∀ x ∈ P, c x ∈ IsLocalRing.maximalIdeal (CompletedLocalAt A P) := by
    intro x hx
    rw [← hmap]
    apply Ideal.mem_map_of_mem
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P L]
    exact Ideal.mem_map_of_mem _ hx
  have hmem : Polynomial.eval₂ φ Z Φ ∈ P := by
    rw [hP]; exact Ideal.subset_span (by simp)
  have key : ∀ q : Polynomial O, (q.map (c.comp φ)).eval (c Z) = c (q.eval₂ φ Z) := fun q => by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂]
  obtain ⟨θ, hθ, hθZ⟩ := HenselianRing.is_henselian
      (I := IsLocalRing.maximalIdeal (CompletedLocalAt A P))
    (Φ.map (c.comp φ)) (hΦ.1.map _) (c Z) (by rw [key]; exact hPm _ hmem) (by
      rw [Polynomial.derivative_map, key]
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ (c w)) ?_
      rw [← map_mul, ← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, ← map_one c,
        ← map_sub]
      exact hPm _ hw)
  refine ⟨θ, by rwa [Polynomial.IsRoot, Polynomial.eval_map] at hθ, ?_⟩
  rw [hmap]; exact hθZ

/-- Let `Λ' : Â_P → R'` map the completion at a non-rational point `P` to the child surface
over `O[θ]`, compatibly with `O`, with `Λ'(x/t) = x' + θ`. Then `Λ'` sends a Hensel root `θ'` of
`Φ` near `x/t` to `θ`, so the lift `κ : O[θ] → Â_P`, `θ ↦ θ'`, is a section of `Λ'` on `O[θ]`. -/
private theorem nonrational_point_root_lift (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O)
    (hΦ : IsUnramifiedLift O Φ) (hθ : IsUnit (AdjoinRoot.root Φ))
    (P : Ideal (tChart O pi u a b)) [P.IsPrime]
    (Λ' : CompletedLocalAt (tChart O pi u a b) P →+* childSurface O pi u a b Φ hθ)
    (hΛ'O : Λ'.comp ((completedPointMap (tChart O pi u a b) P).comp
        ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b)))) =
      (algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ)).comp
        (algebraMap O (AdjoinRoot Φ)))
    (hΛ'Z : Λ' (completedPointMap (tChart O pi u a b) P (tSlope O pi u a b)) =
      surfaceX (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) (childUnit O u b Φ hθ) (a + b) 0 +
        algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ) (AdjoinRoot.root Φ))
    (θ' : CompletedLocalAt (tChart O pi u a b) P)
    (hroot : Polynomial.eval₂ ((completedPointMap (tChart O pi u a b) P).comp
      ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b)))) θ' Φ = 0)
    (hcong : Λ' (θ' - completedPointMap (tChart O pi u a b) P (tSlope O pi u a b)) ∈
      surfaceParameterIdeal (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
        (childUnit O u b Φ hθ) (a + b) 0) (c : AdjoinRoot Φ) :
    Λ' (AdjoinRoot.lift ((completedPointMap (tChart O pi u a b) P).comp
      ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b)))) θ' hroot c) =
      algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ) c := by
  obtain ⟨_, _, hdvr, -, hirr, -, -, -⟩ := unramified_is_dvr O Φ hΦ
  have := hdvr
  have hpiδ : Irreducible (algebraMap O (AdjoinRoot Φ) pi) := hirr pi hpi
  have hab : 0 < a + b := by omega
  have : IsLocalRing (childSurface O pi u a b Φ hθ) :=
    concrete_surface_isLocalRing _ _ _ _ _ hpiδ.not_isUnit hab
  have hmax := concrete_surface_maximalIdeal_eq _ _ hpiδ (childUnit O u b Φ hθ) (a + b) 0 hab
  have hρθ : Φ.eval₂ (algebraMap O (AdjoinRoot Φ)) (AdjoinRoot.root Φ) = 0 :=
    AdjoinRoot.eval₂_root Φ
  -- `Λ' θ'` and `θ` are roots of `Φ` congruent modulo the maximal ideal, and `θ` is simple.
  have hθ' : Λ' θ' = algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ)
      (AdjoinRoot.root Φ) := by
    refine polynomial_root_unique_of_derivative_isUnit _ (Φ.map ((algebraMap (AdjoinRoot Φ)
      (childSurface O pi u a b Φ hθ)).comp (algebraMap O (AdjoinRoot Φ)))) _ (Λ' θ') ?_ ?_ ?_ ?_
    · rw [Polynomial.eval_map, ← Polynomial.hom_eval₂, hρθ, map_zero]
    · rw [Polynomial.eval_map, ← hΛ'O, ← Polynomial.hom_eval₂, hroot, map_zero]
    · rw [hmax, ← sub_add_cancel (Λ' θ') (Λ' (completedPointMap _ P (tSlope O pi u a b))),
        ← map_sub, hΛ'Z, add_sub_assoc, add_sub_cancel_right]
      exact Ideal.add_mem _ hcong (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    · have hu := (simple_root_derivative_unit O Φ hΦ (AdjoinRoot.root Φ) (by
        rw [Polynomial.eval_map]; exact (congrArg _ hρθ).trans (map_zero _))).2
      have h2 : Polynomial.eval (algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ)
          (AdjoinRoot.root Φ)) (Polynomial.derivative (Φ.map ((algebraMap (AdjoinRoot Φ)
            (childSurface O pi u a b Φ hθ)).comp (algebraMap O (AdjoinRoot Φ))))) =
          algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ)
            ((Φ.map (AdjoinRoot.of Φ)).derivative.eval (AdjoinRoot.root Φ)) := by
        rw [Polynomial.derivative_map, Polynomial.derivative_map, Polynomial.eval_map,
          Polynomial.eval_map, Polynomial.hom_eval₂]
        rfl
      rw [h2]; exact hu.map _
  induction c using AdjoinRoot.induction_on with
  | ih p =>
    rw [AdjoinRoot.lift_mk, Polynomial.hom_eval₂, hΛ'O, hθ', ← Polynomial.hom_eval₂,
      ← AdjoinRoot.aeval_eq, Polynomial.aeval_def]

/-- A chart map `Λ : R[x/t] → R'` to the child surface over `O[θ]`, compatible with `O`, with
`Λ(t) = t'` and `Λ(x/t) = x' + θ`, contracts the maximal ideal of `R'` to the non-rational point
`P = (t, Φ(x/t))`. -/
private theorem nonrational_point_mem_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (hθ : IsUnit (AdjoinRoot.root Φ)) (P : Ideal (tChart O pi u a b))
    (hP : P = Ideal.span
      {tBase O pi u a b (surfaceT O pi u a b),
      Polynomial.eval₂ ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b)))
          (tSlope O pi u a b) Φ})
    (Λ : tChart O pi u a b →+* childSurface O pi u a b Φ hθ)
    (hΛT : Λ (tBase O pi u a b (surfaceT O pi u a b)) =
      surfaceT (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) (childUnit O u b Φ hθ) (a + b) 0)
    (hΛO : Λ.comp ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b))) =
      (algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ)).comp
        (algebraMap O (AdjoinRoot Φ)))
    (hΛZ : Λ (tSlope O pi u a b) =
      surfaceX (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) (childUnit O u b Φ hθ) (a + b) 0 +
        algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ) (AdjoinRoot.root Φ))
    (x : tChart O pi u a b) :
    x ∈ P ↔ Λ x ∈ surfaceParameterIdeal (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (childUnit O u b Φ hθ) (a + b) 0 := by
  obtain ⟨_, _, hdvr, -, hirr, -, -, -⟩ := unramified_is_dvr O Φ hΦ
  have := hdvr
  have hpiδ : Irreducible (algebraMap O (AdjoinRoot Φ) pi) := hirr pi hpi
  have hab : 0 < a + b := by omega
  have : IsLocalRing (childSurface O pi u a b Φ hθ) :=
    concrete_surface_isLocalRing _ _ _ _ _ hpiδ.not_isUnit hab
  have hmax := concrete_surface_maximalIdeal_eq _ _ hpiδ (childUnit O u b Φ hθ) (a + b) 0 hab
  have : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} :
      Set (ConcreteSurface O pi u a b))).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  have hirrR := unramified_lift_map_parameter_quotient_irreducible O pi hpi u a b ha Φ hΦ
  rw [← Polynomial.map_map] at hirrR
  obtain ⟨-, hspan⟩ := chart_nonrational_point_span_eq_comap _ _ _
    (Φ.map (algebraMap O (ConcreteSurface O pi u a b))) hirrR _ Λ
    (by rw [hΛT, hmax]; exact Ideal.subset_span (Set.mem_insert _ _)) (by
      -- `Φ(x' + θ) ≡ Φ(θ) = 0` modulo `x'`
      rw [Polynomial.eval₂_map, Polynomial.hom_eval₂, hΛO, hΛZ, hmax]
      obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub (surfaceX (AdjoinRoot Φ)
        (algebraMap O (AdjoinRoot Φ) pi) (childUnit O u b Φ hθ) (a + b) 0 + algebraMap
          (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ) (AdjoinRoot.root Φ))
        (algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ) (AdjoinRoot.root Φ))
        (Φ.map ((algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ)).comp
          (algebraMap O (AdjoinRoot Φ))))
      have hF0 : Φ.eval₂ ((algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ)).comp
          (algebraMap O (AdjoinRoot Φ))) (algebraMap (AdjoinRoot Φ)
            (childSurface O pi u a b Φ hθ) (AdjoinRoot.root Φ)) = 0 := by
        rw [← Polynomial.hom_eval₂, show Φ.eval₂ (algebraMap O (AdjoinRoot Φ))
          (AdjoinRoot.root Φ) = 0 from AdjoinRoot.eval₂_root Φ, map_zero]
      rw [Polynomial.eval_map, Polynomial.eval_map, hF0, sub_zero, add_sub_cancel_right] at hk
      rw [hk]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  rw [← hmax, ← Ideal.mem_comap, ← hspan, hP, Polynomial.eval₂_map]

/-! ### The completion isomorphisms -/

/-- The completion of the `t`-chart at a non-rational point `(t, Φ(x/t))` is isomorphic to the
child surface over `O[θ] = O[X]/(Φ)`, compatibly with the chart substitution, and the image of
`θ` is the Hensel root of `Φ`. -/
theorem t_chart_nonrational_point_completion_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (hθ : IsUnit (AdjoinRoot.root Φ)) (P : Ideal (tChart O pi u a b)) [P.IsPrime]
    (hP : P = Ideal.span
      {tBase O pi u a b (surfaceT O pi u a b),
      Polynomial.eval₂ ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b)))
          (tSlope O pi u a b) Φ}) :
    ∃ Eq : CompletedLocalAt (tChart O pi u a b) P ≃+* childSurface O pi u a b Φ hθ,
      (∀ s : TwoSeries O,
        Eq (completedPointMap (tChart O pi u a b) P (tBase O pi u a b (surfaceMk O pi u a b s))) =
          surfaceMk (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) (childUnit O u b Φ hθ) (a + b) 0
            (chartSubst (AdjoinRoot Φ) (AdjoinRoot.root Φ)
              (MvPowerSeries.map (algebraMap O (AdjoinRoot Φ)) s))) ∧
      Eq (completedPointMap (tChart O pi u a b) P (tSlope O pi u a b)) =
        surfaceX (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) (childUnit O u b Φ hθ) (a + b) 0 +
          algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ) (AdjoinRoot.root Φ) ∧
      (∀ c : O,
        Eq (completedPointMap (tChart O pi u a b) P
            (tBase O pi u a b (algebraMap O (ConcreteSurface O pi u a b) c))) =
          algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ)
            (algebraMap O (AdjoinRoot Φ) c)) ∧
      Polynomial.eval₂ ((completedPointMap (tChart O pi u a b) P).comp
          ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b))))
        (Eq.symm (algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ) (AdjoinRoot.root Φ)))
        Φ = 0 ∧
      Eq.symm (algebraMap (AdjoinRoot Φ) (childSurface O pi u a b Φ hθ) (AdjoinRoot.root Φ)) -
          completedPointMap (tChart O pi u a b) P (tSlope O pi u a b) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
          (localCompletionMap (Localization.AtPrime P)) := by
  obtain ⟨_, _, hdvr, -, hirr, -, -, -⟩ := unramified_is_dvr O Φ hΦ
  have := hdvr
  set θ := AdjoinRoot.root Φ
  set ρ := algebraMap O (AdjoinRoot Φ)
  set uδ := substUnit (AdjoinRoot Φ) θ (baseChangeUnit O ρ u) * shiftUnit (AdjoinRoot Φ) θ hθ ^ b
  set R := ConcreteSurface O pi u a b
  set Rδ := ConcreteSurface (AdjoinRoot Φ) (ρ pi) uδ (a + b) 0
  set A := BlowupChart R (surfaceT O pi u a b) (surfaceX O pi u a b)
  set cb := chartBase R (surfaceT O pi u a b) (surfaceX O pi u a b)
  set Z := chartSlope R (surfaceT O pi u a b) (surfaceX O pi u a b)
  set cpm := completedPointMap A P
  set aδ := algebraMap (AdjoinRoot Φ) Rδ
  set Xδ := surfaceX (AdjoinRoot Φ) (ρ pi) uδ (a + b) 0
  have hpiδ : Irreducible (ρ pi) := hirr pi hpi
  have hab : 0 < a + b := by omega
  have : IsLocalRing Rδ := concrete_surface_isLocalRing _ _ _ _ _ hpiδ.not_isUnit hab
  have : IsNoetherianRing A := blowupChart_concrete_isNoetherianRing O pi u a b _ _
  -- The chart substitution `s = chartSubst θ ∘ map ρ` and the chart map `Λ : A → Rδ` it induces.
  obtain ⟨hsC0, hsT0, hsX0, -⟩ := chartSubst_apply_generators (AdjoinRoot Φ) θ
  set s := (chartSubst (AdjoinRoot Φ) θ).toRingHom.comp (MvPowerSeries.map ρ)
  have hsC : ∀ c : O, s (MvPowerSeries.C c) = MvPowerSeries.C (ρ c) := fun c =>
    (congrArg (chartSubst (AdjoinRoot Φ) θ) (MvPowerSeries.map_C _ _)).trans (hsC0 _)
  have hsE : s (axisT O) = axisT (AdjoinRoot Φ) :=
    (congrArg (chartSubst (AdjoinRoot Φ) θ) (MvPowerSeries.map_X _ _)).trans hsT0
  have hsF : s (axisX O) = axisT (AdjoinRoot Φ) * (axisX (AdjoinRoot Φ) + MvPowerSeries.C θ) :=
    (congrArg (chartSubst (AdjoinRoot Φ) θ) (MvPowerSeries.map_X _ _)).trans hsX0
  have hs : s (surfaceRelation O pi u a b) = surfaceRelation (AdjoinRoot Φ) (ρ pi) uδ (a + b) 0 :=
    (chartSubst_surfaceRelation_base_change_and_x_chart O (AdjoinRoot Φ) ρ pi u a b).1 θ hθ
  obtain ⟨Λ, hΛ, hΛZ⟩ : ∃ Λ : A →+* Rδ, (∀ g : TwoSeries O,
      Λ (cb (surfaceMk O pi u a b g)) = surfaceMk (AdjoinRoot Φ) (ρ pi) uδ (a + b) 0 (s g)) ∧
      Λ Z = Xδ + aδ θ := chart_child_map_exists O (AdjoinRoot Φ) pi u a b (ρ pi) uδ (a + b) 0
    (axisT O) (axisX O) s (hs ▸ Ideal.mem_span_singleton_self _) θ hsE hsF
  have hΛC : ∀ c : O, Λ (cb (algebraMap O R c)) = aδ (ρ c) :=
    fun c ↦ (hΛ (MvPowerSeries.C c)).trans (congrArg _ (hsC c))
  have hΛCc : Λ.comp (cb.comp (algebraMap O R)) = aδ.comp ρ := RingHom.ext hΛC
  -- `P` is the preimage of the maximal ideal of `Rδ`; pass to the completion.
  have hP' := nonrational_point_mem_iff O pi hpi u a b ha Φ hΦ hθ P hP Λ
    (by have := hΛ (axisT O); rw [hsE] at this; exact this) hΛCc hΛZ
  obtain ⟨Λ', hΛ'⟩ := chart_child_completion_map_exists A (AdjoinRoot Φ) (ρ pi) hpiδ uδ
    (a + b) 0 hab Λ P hP'
  have hloc' := chart_child_completion_map_local A (AdjoinRoot Φ) (ρ pi) hpiδ uδ
    (a + b) 0 hab Λ P hP' Λ' hΛ'
  -- The Hensel root `θ'` of `Φ` maps to `θ`, so `θ ↦ θ'` extends `O → completion` to `κ`.
  obtain ⟨θ', hroot, hcong⟩ := nonrational_point_hensel_root O pi hpi u a b ha Φ hΦ P hP
  set κO := cpm.comp (cb.comp (algebraMap O R))
  have hΛ'κO : Λ'.comp κO = aδ.comp ρ := by rw [← hΛCc]; ext c; exact hΛ' _
  set κ := AdjoinRoot.lift κO θ' hroot with hκdef
  have hκ := nonrational_point_root_lift O pi hpi u a b ha Φ hΦ hθ P Λ' hΛ'κO
    ((hΛ' _).trans hΛZ) θ' hroot ((hloc' _).1 hcong)
  obtain ⟨E, hE, hEs⟩ : ∃ E : CompletedLocalAt A P ≃+* Rδ,
      (∀ y, E y = Λ' y) ∧ ∀ c, E.symm (aδ c) = κ c :=
    @chart_child_completion_equiv O (AdjoinRoot Φ) _ _ _ _ _ pi u a b (ρ pi)
    hpiδ uδ (a + b) 0 hab (axisT O) (axisX O) (Or.inl ⟨rfl, rfl⟩) ρ θ s hsC hsE hsF hs Λ hΛ hΛZ P
    ‹_› hP'
    (nonrational_point_residue_surjective O pi u a b Φ hθ Λ hΛ hΛZ) Λ' hΛ' κ hκ
    fun c => AdjoinRoot.lift_of (h := hroot)
  have hEθ : E.symm (aδ (AdjoinRoot.root Φ)) = θ' := by
    rw [hEs]; exact AdjoinRoot.lift_root (h := hroot)
  refine ⟨E, fun g => ((hE _).trans (hΛ' _)).trans (hΛ g), ((hE _).trans (hΛ' _)).trans hΛZ,
    fun c => ((hE _).trans (hΛ' _)).trans (hΛC c), ?_, ?_⟩
  · rw [hEθ]; exact hroot
  · rw [hEθ]; exact hcong

/-- Common form of the completion isomorphisms at the rational points of the exceptional
divisor: if `s : O[[T,X]] → O[[T,X]]` fixes constants, sends `E ↦ T`, `F ↦ T (X + α)` and the
relation to a child relation, then the completed local ring of `R[f/e]` at
`P = (e, f/e - α)` is isomorphic to the child surface, compatibly with `s`. -/
private theorem rational_point_completion_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (u' : (TwoSeries O)ˣ) (a' b' : ℕ) (ha' : 0 < a') (E F : TwoSeries O)
    (hEF : (E = axisT O ∧ F = axisX O) ∨ (E = axisX O ∧ F = axisT O))
    (hEFmax : (Ideal.span ({surfaceMk O pi u a b E, surfaceMk O pi u a b F} :
      Set (ConcreteSurface O pi u a b))).IsMaximal)
    (α : O) (s : TwoSeries O →+* TwoSeries O)
    (hsC : ∀ c : O, s (MvPowerSeries.C c) = MvPowerSeries.C c) (hsE : s E = axisT O)
    (hsF : s F = axisT O * (axisX O + MvPowerSeries.C α))
    (hrel : s (surfaceRelation O pi u a b) = surfaceRelation O pi u' a' b')
    (P : Ideal (efChart O pi u a b E F)) (hPp : P.IsPrime)
    (hP : P = Ideal.span {efBase O pi u a b E F (surfaceMk O pi u a b E),
      efSlope O pi u a b E F - efBase O pi u a b E F (algebraMap O (ConcreteSurface O pi u a b)
          α)}) :
    ∃ Eq : CompletedLocalAt (efChart O pi u a b E F) P ≃+* ConcreteSurface O pi u' a' b',
      (∀ g : TwoSeries O, Eq (completedPointMap (efChart O pi u a b E F) P
          (efBase O pi u a b E F (surfaceMk O pi u a b g))) =
        surfaceMk O pi u' a' b' (s g)) ∧
      Eq (completedPointMap (efChart O pi u a b E F) P (efSlope O pi u a b E F)) =
        surfaceX O pi u' a' b' + algebraMap O (ConcreteSurface O pi u' a' b') α ∧
      ∀ c : O, Eq
        (completedPointMap (efChart O pi u a b E F) P (efBase O pi u a b E F
            (algebraMap O (ConcreteSurface O pi u a b) c))) =
        algebraMap O (ConcreteSurface O pi u' a' b') c := by
  have : IsLocalRing (ConcreteSurface O pi u' a' b') :=
    concrete_surface_isLocalRing O pi _ _ _ hpi.not_isUnit ha'
  have : IsNoetherianRing (efChart O pi u a b E F) := blowupChart_concrete_isNoetherianRing O pi u a
      b _ _
  have hmax := concrete_surface_maximalIdeal_eq O pi hpi u' a' b' ha'
  obtain ⟨Λ, hΛ, hΛZ⟩ := chart_child_map_exists O O pi u a b pi u' a' b' E F s
    (hrel ▸ Ideal.mem_span_singleton_self _) α hsE hsF
  set R0 := ConcreteSurface O pi u' a' b'
  have hT : surfaceMk O pi u' a' b' (axisT O) ∈ IsLocalRing.maximalIdeal R0 := by
    rw [hmax]; exact Ideal.subset_span (Set.mem_insert _ _)
  have hXm : surfaceX O pi u' a' b' ∈ IsLocalRing.maximalIdeal R0 := by
    rw [hmax]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hΛC : ∀ c : O,
      Λ (efBase O pi u a b E F (algebraMap O (ConcreteSurface O pi u a b) c)) = algebraMap O R0 c :=
    fun c ↦ (hΛ (MvPowerSeries.C c)).trans (congrArg _ (hsC c))
  have := hEFmax
  have := hPp
  obtain ⟨-, hspan⟩ := chart_rational_point_span_eq_comap (ConcreteSurface O pi u a b)
    (surfaceMk O pi u a b E) (surfaceMk O pi u a b F) R0 Λ (algebraMap O _ α)
    (by rw [hΛ, hsE]; exact hT) (by rw [hΛZ, hΛC, add_sub_cancel_right]; exact hXm)
  have hP' : ∀ x, x ∈ P ↔ Λ x ∈ surfaceParameterIdeal O pi u' a' b' := fun x ↦ by
    rw [← hmax, ← Ideal.mem_comap, ← hspan, hP]
  have hsurj : ∀ y : R0, ∃ x, Λ x - y ∈ surfaceParameterIdeal O pi u' a' b' := by
    intro y
    obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨efBase O pi u a b E F (algebraMap O (ConcreteSurface O pi u a b)
        (MvPowerSeries.constantCoeff s')), ?_⟩
    rw [hΛC, ← neg_sub]
    exact (Ideal.neg_mem_iff _).mpr
      (concrete_surface_sub_constantCoeff_mem_parameterIdeal O pi u' a' b' s')
  obtain ⟨Λ', hΛ'⟩ := chart_child_completion_map_exists _ O pi hpi u' a' b' ha' Λ P hP'
  obtain ⟨e, he, -⟩ := chart_child_completion_equiv O O pi u a b pi hpi u' a' b' ha' E F hEF
    (RingHom.id O) α s hsC hsE hsF hrel Λ hΛ hΛZ P hP' hsurj Λ' hΛ'
    ((completedPointMap (efChart O pi u a b E F) P).comp ((efBase O pi u a b E F).comp
        (algebraMap O _)))
    (fun c ↦ by
      change Λ' (completedPointMap _ P (efBase O pi u a b E F (algebraMap O _ c))) = _
      rw [hΛ', hΛC]) fun c ↦ rfl
  exact ⟨e, fun g ↦ ((he _).trans (hΛ' _)).trans (hΛ g), ((he _).trans (hΛ' _)).trans hΛZ,
    fun c ↦ ((he _).trans (hΛ' _)).trans (hΛC c)⟩

/-- The completion of the `t`-chart at its origin `(t, x/t)` is the concrete surface
with unit `substUnit O 0 u` and exponents `(a + b, b)`, compatibly with the chart substitution. -/
theorem t_chart_origin_completion_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) (P : Ideal (tChart O pi u a b)) [P.IsPrime]
    (hP : P = Ideal.span {tBase O pi u a b (surfaceT O pi u a b), tSlope O pi u a b}) :
    ∃ Eq : CompletedLocalAt (tChart O pi u a b) P ≃+* ConcreteSurface O pi (substUnit O 0 u) (a + b)
        b,
      (∀ s : TwoSeries O,
        Eq (completedPointMap (tChart O pi u a b) P (tBase O pi u a b (surfaceMk O pi u a b s))) =
            surfaceMk O pi
        (substUnit O 0 u) (a + b) b (chartSubst O 0 s)) ∧ Eq (completedPointMap (tChart O pi u a b)
            P (tSlope O pi u a b)) =
      surfaceX O pi (substUnit O 0 u) (a + b) b ∧ ∀ c : O,
      Eq (completedPointMap (tChart O pi u a b) P (tBase O pi u a b
          (algebraMap O (ConcreteSurface O pi u a b) c))) =
      algebraMap O (ConcreteSurface O pi (substUnit O 0 u) (a + b) b) c := by
  obtain ⟨hsC, hsT, hsX, -⟩ := chartSubst_apply_generators O 0
  obtain ⟨e, h1, h2, h3⟩ := rational_point_completion_equiv O pi hpi u a b (substUnit O 0 u)
    (a + b) b (by omega) (axisT O) (axisX O) (Or.inl ⟨rfl, rfl⟩)
    (concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha) 0 (chartSubst O 0).toRingHom
    hsC hsT hsX (chartSubst_surfaceRelation_origin_and_unit_point O pi u a b).1 P ‹_›
    (by rw [hP]; simp only [map_zero, sub_zero]; rfl)
  rw [map_zero, add_zero] at h2
  exact ⟨e, h1, h2, h3⟩

/-- The completion of the `t`-chart at a rational point `(t, x/t - α)` with `α` a unit is the
child concrete surface with exponents `(a + b, 0)`, compatibly with the chart substitution. -/
theorem t_chart_unit_point_completion_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) (α : O) (hα : IsUnit α) (P : Ideal (tChart O pi u a b)) [P.IsPrime]
    (hP : P = Ideal.span
      {tBase O pi u a b (surfaceT O pi u a b), tSlope O pi u a b - tBase O pi u a b
          (algebraMap O (ConcreteSurface O pi u a b) α)}) :
    ∃ Eq : CompletedLocalAt (tChart O pi u a b) P ≃+* ConcreteSurface O pi
      (substUnit O α u * shiftUnit O α hα ^ b) (a + b) 0,
      (∀ s : TwoSeries O,
        Eq (completedPointMap (tChart O pi u a b) P (tBase O pi u a b (surfaceMk O pi u a b s))) =
            surfaceMk O pi
        (substUnit O α u * shiftUnit O α hα ^ b) (a + b) 0 (chartSubst O α s)) ∧ Eq
      (completedPointMap (tChart O pi u a b) P (tSlope O pi u a b)) =
          surfaceX O pi (substUnit O α u * shiftUnit O α hα ^ b)
      (a + b) 0 + algebraMap O
      (ConcreteSurface O pi (substUnit O α u * shiftUnit O α hα ^ b) (a + b) 0) α ∧ ∀ c : O,
      Eq (completedPointMap (tChart O pi u a b) P (tBase O pi u a b
          (algebraMap O (ConcreteSurface O pi u a b) c))) =
      algebraMap O (ConcreteSurface O pi (substUnit O α u * shiftUnit O α hα ^ b) (a + b) 0) c := by
  obtain ⟨hsC, hsT, hsX, -⟩ := chartSubst_apply_generators O α
  exact rational_point_completion_equiv O pi hpi u a b _ (a + b) 0 (by omega) (axisT O) (axisX O)
    (Or.inl ⟨rfl, rfl⟩) (concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha) α
    (chartSubst O α).toRingHom hsC hsT hsX
    ((chartSubst_surfaceRelation_origin_and_unit_point O pi u a b).2 α hα) P ‹_› hP

/-- The completion of the `x`-chart at its origin `(x, t/x)` is the child concrete surface with
exponents `(a + b, a)`, compatibly with the `x`-chart substitution. -/
theorem x_chart_infinity_completion_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) (P : Ideal (xChart O pi u a b)) [P.IsPrime]
    (hP : P = Ideal.span {xBase O pi u a b (surfaceX O pi u a b), xSlope O pi u a b}) :
    ∃ Eq : CompletedLocalAt (xChart O pi u a b) P ≃+* ConcreteSurface O pi (xSubstUnit O u) (a + b)
        a,
      (∀ s : TwoSeries O,
        Eq (completedPointMap (xChart O pi u a b) P (xBase O pi u a b (surfaceMk O pi u a b s))) =
            surfaceMk O pi
        (xSubstUnit O u) (a + b) a (xChartSubst O s)) ∧ Eq (completedPointMap (xChart O pi u a b) P
            (xSlope O pi u a b)) =
      surfaceX O pi (xSubstUnit O u) (a + b) a ∧ ∀ c : O,
      Eq (completedPointMap (xChart O pi u a b) P (xBase O pi u a b
          (algebraMap O (ConcreteSurface O pi u a b) c))) =
      algebraMap O (ConcreteSurface O pi (xSubstUnit O u) (a + b) a) c := by
  obtain ⟨-, -, -, hsC, hsT, hsX, -⟩ := chartSubst_apply_generators O 0
  obtain ⟨e, h1, h2, h3⟩ := rational_point_completion_equiv O pi hpi u a b (xSubstUnit O u)
    (a + b) a (by omega) (axisX O) (axisT O) (Or.inr ⟨rfl, rfl⟩)
    (by rw [Ideal.span_pair_comm]; exact concrete_surface_parameterIdeal_isMaximal O pi hpi u a b
          ha)
    0 (xChartSubst O).toRingHom hsC hsX (by rw [map_zero, add_zero]; exact hsT)
    (chartSubst_surfaceRelation_base_change_and_x_chart O O (RingHom.id O) pi u a b).2 P ‹_›
    (by rw [hP]; simp only [map_zero, sub_zero]; rfl)
  rw [map_zero, add_zero] at h2
  exact ⟨e, h1, h2, h3⟩

end SurfaceBlowup
