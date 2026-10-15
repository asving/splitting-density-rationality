/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.Charts
import SurfaceBlowup.Surfaces.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Regularity of the concrete surface

The concrete surface `R = O[[T,X]] / (π - u T^a X^b)` is a two-dimensional regular local
domain, `(t, x)` and `(x, t)` are regular parameter pairs, and quotients `R/(f)` by suitable
non-units are free `O`-modules of rank `length R/(π, f)`. We also construct the maps from
completed local rings of blow-up charts to child surfaces.

## Main results

* `concrete_surface_isDomain`, `concrete_surface_isRegularLocalRing`,
  `concrete_surface_ringKrullDim_eq_two`, `concrete_surface_data_exists_unconditional`.
* `concrete_surface_regular_pair_tx`, `concrete_surface_equiv_regular_pair`.
* `concrete_surface_curve_free_of_length`.
* `chart_child_completion_map_exists`, `chart_child_completion_map_local`,
  `child_series_eval_comp_chart_subst`.

Provenance: `blowupChart_concrete_isNoetherianRing`, `nonrational_point_residue_surjective`,
`chart_child_completion_map_{exists,local}`, `concrete_surface_{regular_pair_tx, regular_pair_xt,
isDomain, equiv_instances, equiv_regular_pair, two_le_ringKrullDim, isRegularLocalRing,
ringKrullDim_eq_two, data_exists, data_exists_unconditional, pi_regular_mod_curve, curve_basis,
curve_free_finrank, curve_free_of_length}`, `regular_pair_first_regular_mod_second`,
`child_series_eval_comp_chart_subst`.
-/

namespace SurfaceBlowup

/-! ### Blow-up charts and their completions -/

/-- Every blow-up chart of the concrete surface is noetherian. -/
theorem blowupChart_concrete_isNoetherianRing (O : Type) [CommRing O] [IsNoetherianRing O] (pi : O)
    (u : (TwoSeries O)ˣ) (a b : ℕ) (e f : ConcreteSurface O pi u a b) :
    IsNoetherianRing (BlowupChart (ConcreteSurface O pi u a b) e f) := by
  have := concrete_surface_isNoetherianRing O pi u a b
  unfold BlowupChart
  infer_instance

/-- For the chart map `Λ` to the concrete surface over `O[θ] = O[X]/(Φ)` attached to a
non-rational point, every element of the target is congruent modulo the parameter ideal to an
element in the image of `Λ`. -/
theorem nonrational_point_residue_surjective (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O)
    (hθ : IsUnit (AdjoinRoot.root Φ))
    (Λ : BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) →+* ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
      (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0)
    (hΛ : ∀ g : TwoSeries O,
      Λ (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
      (surfaceMk O pi u a b g)) = surfaceMk (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
      (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0
      (chartSubst (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (MvPowerSeries.map (algebraMap O (AdjoinRoot Φ)) g)))
    (hΛZ : Λ (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) =
      surfaceX (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
      (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0 + algebraMap (AdjoinRoot Φ)
      (ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
      (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0) (AdjoinRoot.root Φ)) :
    ∀ y : ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
        (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0,
      ∃ x : BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b),
      Λ x - y ∈ surfaceParameterIdeal (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
        (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0 := by
  intro y
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective y
  set B := chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
  set I := surfaceParameterIdeal (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
    (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
      (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0
  have hXI : surfaceX _ _ _ _ _ ∈ I := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  obtain ⟨p, hp⟩ : ∃ p, AdjoinRoot.mk Φ p = MvPowerSeries.constantCoeff s' :=
    Ideal.Quotient.mk_surjective _
  refine ⟨p.eval₂ (B.comp (algebraMap O _)) (chartSlope _ _ _), ?_⟩
  -- `Λ (p(θ)) ≡ p(θ) ≡ s'(0, 0) ≡ s'` modulo the parameter ideal
  have key : Λ (p.eval₂ (B.comp (algebraMap O _)) (chartSlope _ _ _)) -
      algebraMap (AdjoinRoot Φ) _ (MvPowerSeries.constantCoeff s') ∈ I := by
    rw [← Ideal.Quotient.eq, Polynomial.hom_eval₂, hΛZ, ← hp, ← AdjoinRoot.aeval_eq,
      Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.hom_eval₂, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr hXI, zero_add, Polynomial.hom_eval₂]
    congr 1
    refine RingHom.ext fun c₀ ↦ ?_
    change Ideal.Quotient.mk I (Λ (B (surfaceMk O pi u a b (MvPowerSeries.C c₀)))) = _
    rw [hΛ, MvPowerSeries.map_C,
      (chartSubst_apply_generators (AdjoinRoot Φ) (AdjoinRoot.root Φ)).1]
    rfl
  have := I.sub_mem key (concrete_surface_sub_constantCoeff_mem_parameterIdeal _ _ _ _ _ s')
  rwa [sub_sub_sub_cancel_right] at this

/-- A ring map `Λ : A → R'` to a concrete surface, under which `P` is the preimage of the
parameter ideal, extends to the completed local ring of `A` at `P`. -/
theorem chart_child_completion_map_exists (A : Type) [CommRing A] [IsNoetherianRing A] (O' : Type)
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi')
    (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a') (Λ : A →+* ConcreteSurface O' pi' u' a' b')
    (P : Ideal A) [P.IsPrime] (hP : ∀ x : A, x ∈ P ↔ Λ x ∈ surfaceParameterIdeal O' pi' u' a' b') :
    ∃ Λ' : CompletedLocalAt A P →+* ConcreteSurface O' pi' u' a' b', ∀ x : A,
      Λ' (completedPointMap A P x) = Λ x := by
  have hloc : IsLocalRing (ConcreteSurface O' pi' u' a' b') :=
    concrete_surface_isLocalRing O' pi' u' a' b' hpi'.not_isUnit ha'
  set R := ConcreteSurface O' pi' u' a' b'
  have hmax : IsLocalRing.maximalIdeal R = surfaceParameterIdeal O' pi' u' a' b' :=
    concrete_surface_maximalIdeal_eq O' pi' hpi' u' a' b' ha'
  have hcomp : IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
    concrete_surface_isAdicComplete_maximalIdeal O' pi' hpi' u' a' b' ha'
  set m' := IsLocalRing.maximalIdeal R
  -- Step 1: localize
  have hunit (y : P.primeCompl) : IsUnit (Λ y) := by
    by_contra h
    exact y.2 ((hP y).2 (hmax ▸ (IsLocalRing.mem_maximalIdeal _).2 h))
  let ΛP : (Localization.AtPrime P) →+* R := IsLocalization.lift (M := P.primeCompl) hunit
  have hΛP : ∀ x : A,
      ΛP (algebraMap A (Localization.AtPrime P) x) = Λ x := fun x ↦ IsLocalization.lift_eq _ _
  -- Step 2
  have hle : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map ΛP ≤ m' := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P), Ideal.map_map,
          Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply]
    rw [hΛP, hmax]; exact (hP x).1 hx
  have hlen (n : ℕ) :
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n ≤ (m' ^ n).comap ΛP := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hle n
  -- Step 3
  let f : (n : ℕ) → CompletedLocalAt A P →+* R ⧸ m' ^ n := fun n ↦
    (Ideal.quotientMap (m' ^ n) ΛP (hlen n)).comp
        (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n).toRingHom
  have hf : ∀ {m n : ℕ} (hmn : m ≤ n), (Ideal.Quotient.factorPow m' hmn).comp (f n) = f m := by
    intro m n hmn
    ext y
    induction y using AdicCompletion.induction_on with
    | h s =>
      simp only [f, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk,
        Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
      rw [Ideal.Quotient.eq, ← map_sub]
      apply Ideal.mem_comap.mp (hlen m _)
      have := (s.property hmn)
      rw [SModEq.comm, SModEq.sub_mem] at this
      simpa [smul_eq_mul, Ideal.mul_top] using this
  refine ⟨IsAdicComplete.liftRingHom m' f hf, fun x ↦ ?_⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.haus hcomp.toIsHausdorff
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem,
    map_sub, IsAdicComplete.mk_liftRingHom, sub_eq_zero]
  simp only [f, completedPointMap, localCompletionMap, RingHom.coe_comp, Function.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk,
        Algebra.algebraMap_self, RingHom.id_apply, hΛP]

/-- The extension `Λ'` of `chart_child_completion_map_exists` is local: the maximal ideal of
the completion is exactly the preimage of the parameter ideal. -/
theorem chart_child_completion_map_local (A : Type) [CommRing A] [IsNoetherianRing A] (O' : Type)
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi')
    (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a') (Λ : A →+* ConcreteSurface O' pi' u' a' b')
    (P : Ideal A) [P.IsPrime] (hP : ∀ x : A, x ∈ P ↔ Λ x ∈ surfaceParameterIdeal O' pi' u' a' b')
    (Λ' : CompletedLocalAt A P →+* ConcreteSurface O' pi' u' a' b')
    (hΛ' : ∀ x : A, Λ' (completedPointMap A P x) = Λ x) :
    ∀ y : CompletedLocalAt A P,
      y ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (localCompletionMap (Localization.AtPrime P)) ↔
      Λ' y ∈ surfaceParameterIdeal O' pi' u' a' b' := by
  have : IsLocalRing (ConcreteSurface O' pi' u' a' b') :=
    concrete_surface_isLocalRing O' pi' u' a' b' hpi'.not_isUnit ha'
  have e2 : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (localCompletionMap (Localization.AtPrime P)) = P.map (completedPointMap A P) :=
    (congrArg (Ideal.map (localCompletionMap (Localization.AtPrime P)))
      (IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)).symm).trans
      (Ideal.map_map _ _)
  intro y
  rw [e2]
  constructor
  · refine fun hy ↦ (Ideal.map_le_iff_le_comap.2 fun x hx ↦ ?_ :
      P.map (completedPointMap A P) ≤ (surfaceParameterIdeal O' pi' u' a' b').comap Λ') hy
    change Λ' (completedPointMap A P x) ∈ surfaceParameterIdeal O' pi' u' a' b'
    rw [hΛ']
    exact (hP x).1 hx
  · refine fun hy ↦ by_contra fun hn ↦ ?_
    have : IsNoetherianRing (Localization.AtPrime P) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    have hu : IsUnit y := by_contra fun hnu ↦ hn <|
      AdicCompletion.maximalIdeal_eq_map.trans e2 ▸ (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [← concrete_surface_maximalIdeal_eq O' pi' hpi' u' a' b' ha'] at hy
    exact (IsLocalRing.mem_maximalIdeal _).1 hy (hu.map Λ')

/-! ### Regularity and dimension -/

/-- `(t, x)` is a regular parameter pair of the concrete surface. -/
theorem concrete_surface_regular_pair_tx (O : Type) [CommRing O] [IsDomain O] (pi : O)
    (hpi : pi ≠ 0) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a) :
    RegularParameterPair (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b) :=
      by
  have hP : MvPowerSeries.constantCoeff (surfaceRelation O pi u a b) ≠ 0 := by
    rw [surfaceRelation_constantCoeff O pi u a b ha]; exact hpi
  exact ⟨mvPowerSeries_quotient_var_regular (Fin 2) O 0 _ hP,
    mvPowerSeries_fin_two_quotient_var_regular_mod_var O 0 1 (by decide) _ hP⟩

/-- The concrete surface over a discrete valuation ring is a domain. -/
theorem concrete_surface_isDomain (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a) :
    IsDomain (ConcreteSurface O pi u a b) := by
  have : Nontrivial (ConcreteSurface O pi u a b) :=
    Ideal.Quotient.nontrivial_iff.mpr (surfaceIdeal_ne_top O pi u a b hpi.not_isUnit ha)
  have := concrete_surface_isNoetherianRing O pi u a b
  have := concrete_surface_isLocalRing O pi u a b hpi.not_isUnit ha
  have hp := concrete_surface_span_T_isPrime O pi hpi u a b ha
  exact isDomain_of_regular_prime_element _ (surfaceT O pi u a b)
    (concrete_surface_regular_pair_tx O pi hpi.ne_zero u a b ha).1 hp
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ hp.ne_top)

/-- A ring isomorphic to a concrete surface is a noetherian complete local domain. -/
theorem concrete_surface_equiv_instances (S : Type) [CommRing S] (O' : Type) [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi')
    (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a') (Eq : S ≃+* ConcreteSurface O' pi' u' a' b') :
    IsNoetherianRing S ∧ IsDomain S ∧ ∃ _ : IsLocalRing S,
      IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  have := concrete_surface_isNoetherianRing O' pi' u' a' b'
  have := concrete_surface_isDomain O' pi' hpi' u' a' b' ha'
  have := concrete_surface_isLocalRing O' pi' u' a' b' hpi'.not_isUnit ha'
  have hC := concrete_surface_isAdicComplete_maximalIdeal O' pi' hpi' u' a' b' ha'
  refine ⟨isNoetherianRing_of_ringEquiv _ Eq.symm, Eq.toMulEquiv.isDomain, ?_⟩
  have : Nontrivial S := Eq.toEquiv.nontrivial
  have hLS : IsLocalRing S :=
    IsLocalRing.of_surjective' (Eq.symm : ConcreteSurface O' pi' u' a' b' →+* S) Eq.symm.surjective
  refine ⟨hLS, ?_⟩
  have : ((IsLocalRing.maximalIdeal (ConcreteSurface O' pi' u' a' b')).comap
      (Eq : S →+* _)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ Eq.surjective
  have hm : (IsLocalRing.maximalIdeal (ConcreteSurface O' pi' u' a' b')).map Eq.symm =
      IsLocalRing.maximalIdeal S := by
    rw [← IsLocalRing.eq_maximalIdeal this]; exact Ideal.map_symm Eq
  rw [← hm]
  exact (IsAdicComplete.congr_ringEquiv
    (I := IsLocalRing.maximalIdeal (ConcreteSurface O' pi' u' a' b')) Eq.symm).mpr hC

/-- `(x, t)` is a regular parameter pair of the concrete surface. -/
theorem concrete_surface_regular_pair_xt (O : Type) [CommRing O] [IsDomain O] (pi : O)
    (hpi : pi ≠ 0) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a) :
    RegularParameterPair (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b) :=
      by
  have hP : MvPowerSeries.constantCoeff (surfaceRelation O pi u a b) ≠ 0 := by
    rw [surfaceRelation_constantCoeff O pi u a b ha]; exact hpi
  exact ⟨mvPowerSeries_quotient_var_regular (Fin 2) O 1 _ hP,
    mvPowerSeries_fin_two_quotient_var_regular_mod_var O 1 0 (by decide) _ hP⟩

/-- Regular parameter pairs transport along ring isomorphisms. -/
private theorem regularParameterPair_transport {S R : Type} [CommRing S] [CommRing R] (e : S ≃+* R)
    (t x : R)
    (h : RegularParameterPair R t x) :
    RegularParameterPair S (e.symm t) (e.symm x) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a b hab ↦ ?_, ?_⟩
  · apply e.injective
    apply h1
    simpa using congrArg e hab
  · have hJ : Ideal.span {t} = (Ideal.span {e.symm t}).map e := by
      rw [Ideal.map_span]; simp
    let Q := Ideal.quotientEquiv (Ideal.span {e.symm t}) (Ideal.span {t}) e hJ
    intro a b hab
    apply Q.injective
    apply h2
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    have hx : Q (Ideal.Quotient.mk (Ideal.span {e.symm t}) (e.symm x)) =
        Ideal.Quotient.mk (Ideal.span {t}) x := by
      change Ideal.Quotient.mk _ (e (e.symm x)) = _
      simp
    have hab' : Ideal.Quotient.mk (Ideal.span {e.symm t}) (e.symm x * a') =
        Ideal.Quotient.mk (Ideal.span {e.symm t}) (e.symm x * b') := by
      simpa only [map_mul] using hab
    change _ * Q _ = _ * Q _
    rw [← hx, ← map_mul, ← map_mul, hab']
    simp only [map_mul]

/-- In a ring isomorphic to a concrete surface, the images of `(t, x)` and `(x, t)` are regular
parameter pairs; in particular `t` is a non-zero-divisor. -/
theorem concrete_surface_equiv_regular_pair (S : Type) [CommRing S] (O' : Type) [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi')
    (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a') (Eq : S ≃+* ConcreteSurface O' pi' u' a' b') :
    RegularParameterPair S (Eq.symm (surfaceT O' pi' u' a' b'))
      (Eq.symm (surfaceX O' pi' u' a' b')) ∧ RegularParameterPair S
      (Eq.symm (surfaceX O' pi' u' a' b')) (Eq.symm (surfaceT O' pi' u' a' b')) ∧ Function.Injective
      (fun y : S ↦ Eq.symm (surfaceT O' pi' u' a' b') * y) := by
  have h1 := regularParameterPair_transport Eq _ _
    (concrete_surface_regular_pair_tx O' pi' hpi'.ne_zero u' a' b' ha')
  exact ⟨h1, regularParameterPair_transport Eq _ _
    (concrete_surface_regular_pair_xt O' pi' hpi'.ne_zero u' a' b' ha'), h1.1⟩

/-- A regular sequence `t, x` with `R/(t, x)` nontrivial forces `2 ≤ dim R`. -/
private theorem two_le_ringKrullDim_of_regular_pair {R : Type} [CommRing R] (t x : R)
    (h1 : Function.Injective (fun a : R ↦ t*a))
    (h2 : Function.Injective
        (fun a : R ⧸ Ideal.span {t} ↦ Ideal.Quotient.mk (Ideal.span {t}) x * a))
    (hP : Nontrivial (R ⧸ Ideal.span {t, x})) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim R := by
  have ht : t ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_right.2 fun z hz ↦
    h1 (by simp only [mul_zero]; rw [mul_comm]; exact hz)
  have hx : Ideal.Quotient.mk (Ideal.span {t}) x ∈ nonZeroDivisors (R ⧸ Ideal.span {t}) :=
    mem_nonZeroDivisors_iff_right.2 fun z hz ↦
      h2 (by simp only [mul_zero]; rw [mul_comm]; exact hz)
  let f1 : R ⧸ Ideal.span {t} →+* R ⧸ Ideal.span {t, x} :=
    Ideal.Quotient.factor (Ideal.span_mono (by simp))
  let f2 : (R ⧸ Ideal.span {t}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) x} →+*
      R ⧸ Ideal.span {t, x} :=
    Ideal.Quotient.lift _ f1 fun z hz ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      rw [map_mul, show f1 (Ideal.Quotient.mk (Ideal.span {t}) x) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp)), mul_zero]
  have := f2.domain_nontrivial
  have k1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor ht
  have k2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
  have k0 := ringKrullDim_nonneg_of_nontrivial
    (R := (R ⧸ Ideal.span {t}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) x})
  calc (2 : WithBot ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ ringKrullDim ((R ⧸ Ideal.span {t}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) x})
        + 1 + 1 := by gcongr
    _ ≤ ringKrullDim (R ⧸ Ideal.span {t}) + 1 := by gcongr
    _ ≤ _ := k1

/-- The concrete surface has Krull dimension at least `2`. -/
private theorem concrete_surface_two_le_ringKrullDim (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim (ConcreteSurface O pi u a b) := by
  obtain ⟨h1, h2⟩ := concrete_surface_regular_pair_tx O pi hpi.ne_zero u a b ha
  obtain ⟨e, -⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  exact two_le_ringKrullDim_of_regular_pair _ _ h1 h2 e.toRingHom.domain_nontrivial

/-- The concrete surface is a regular local ring. -/
theorem concrete_surface_isRegularLocalRing (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    IsRegularLocalRing (ConcreteSurface O pi u a b) := by
  have : IsLocalRing (ConcreteSurface O pi u a b) :=
    concrete_surface_isLocalRing O pi u a b hpi.not_isUnit ha
  have := concrete_surface_isNoetherianRing O pi u a b
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  exact le_trans (by exact_mod_cast concrete_surface_spanFinrank_le_two O pi hpi u a b ha)
    (concrete_surface_two_le_ringKrullDim O pi hpi u a b ha)

/-- The concrete surface has Krull dimension `2`. -/
theorem concrete_surface_ringKrullDim_eq_two (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    ringKrullDim (ConcreteSurface O pi u a b) = 2 := by
  have : IsLocalRing (ConcreteSurface O pi u a b) :=
    concrete_surface_isLocalRing O pi u a b hpi.not_isUnit ha
  refine le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_)
    (concrete_surface_two_le_ringKrullDim O pi hpi u a b ha)
  exact_mod_cast concrete_surface_spanFinrank_le_two O pi hpi u a b ha

/-- The concrete surface carries `SurfaceData` with uniformizer `π`, parameters `t, x`, unit
`u` and exponents `a, b`. -/
private theorem concrete_surface_data_exists (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    [IsDomain (ConcreteSurface O pi u a b)] [IsRegularLocalRing (ConcreteSurface O pi u a b)] :
    ∃ S : SurfaceData O (ConcreteSurface O pi u a b),
      S.pi = pi ∧ S.t = surfaceT O pi u a b ∧ S.x = surfaceX O pi u a b ∧ S.unit =
      surfaceUnit O pi u a b ∧ S.a = a ∧ S.b = b := by
  obtain ⟨e, he⟩ := concrete_surface_residueField_equiv O pi hpi u a b ha
  exact ⟨{
    pi := pi
    pi_irreducible := hpi
    t := surfaceT O pi u a b
    x := surfaceX O pi u a b
    unit := surfaceUnit O pi u a b
    a := a
    b := b
    a_pos := ha
    parameters := (concrete_surface_maximalIdeal_eq O pi hpi u a b ha).symm
    dimension := concrete_surface_ringKrullDim_eq_two O pi hpi u a b ha
    complete := concrete_surface_isAdicComplete_maximalIdeal O pi hpi u a b ha
    base_injective := concrete_surface_base_injective O pi hpi u a b ha
    residueEquiv := e
    residue_compat := he
    vertical := concrete_surface_vertical O pi u a b }, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The concrete surface is a regular local domain carrying `SurfaceData` with uniformizer `π`,
parameters `t, x`, unit `u` and exponents `a, b`. -/
theorem concrete_surface_data_exists_unconditional (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a) :
    ∃ (_ : IsDomain (ConcreteSurface O pi u a b))
      (_ : IsRegularLocalRing (ConcreteSurface O pi u a b)),
      ∃ D : SurfaceData O (ConcreteSurface O pi u a b),
      D.pi = pi ∧ D.t = surfaceT O pi u a b ∧ D.x = surfaceX O pi u a b ∧ D.unit =
      surfaceUnit O pi u a b ∧ D.a = a ∧ D.b = b := by
  have := concrete_surface_isDomain O pi hpi u a b ha
  have := concrete_surface_isRegularLocalRing O pi hpi u a b ha
  exact ⟨‹_›, ‹_›, concrete_surface_data_exists O pi hpi u a b ha⟩

/-! ### Curves on the concrete surface -/

/-- If `(p, f)` is a regular parameter pair, then `p` is a non-zero-divisor modulo `f`. -/
private theorem regular_pair_first_regular_mod_second (A : Type) [CommRing A] (p f : A)
    (h : RegularParameterPair A p f) :
    Function.Injective (fun v : A ⧸ Ideal.span {f} ↦ Ideal.Quotient.mk (Ideal.span {f}) p * v) :=
      by
  obtain ⟨h1, h2⟩ := h
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only at hab
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub, Ideal.mem_span_singleton] at hab
  obtain ⟨w, hw⟩ := hab
  have hw0 : Ideal.Quotient.mk (Ideal.span {p}) f * Ideal.Quotient.mk (Ideal.span {p}) w
      = Ideal.Quotient.mk (Ideal.span {p}) f * 0 := by
    rw [mul_zero, ← map_mul, ← hw, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  have := h2 hw0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨w1, rfl⟩ := this
  have : a' - b' = f * w1 := h1 (by simp only; rw [hw]; ring)
  rw [Ideal.Quotient.eq, this, Ideal.mem_span_singleton]
  exact dvd_mul_right _ _

/-- If `f` is a non-zero-divisor modulo `π` on the concrete surface, then `π` is a
non-zero-divisor modulo `f`. -/
private theorem concrete_surface_pi_regular_mod_curve (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (f : ConcreteSurface O pi u a b)
    (hf : Function.Injective
      (fun w : ConcreteSurface O pi u a b ⧸ Ideal.span
      {algebraMap O (ConcreteSurface O pi u a b) pi} => Ideal.Quotient.mk
      (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}) f * w)) :
    Function.Injective
      (fun v : ConcreteSurface O pi u a b ⧸ Ideal.span {f} ↦ Ideal.Quotient.mk (Ideal.span {f})
        (algebraMap O (ConcreteSurface O pi u a b) pi) * v) :=
  regular_pair_first_regular_mod_second _ _ _
    ⟨concrete_surface_pi_regular O pi hpi u a b, hf⟩

/-- For `f` regular modulo `π`, a family that is a basis modulo `π` lifts to an
`O`-basis of the curve ring `R/(f)`. -/
theorem concrete_surface_curve_basis (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (f : ConcreteSurface O pi u a b)
    (hf : Function.Injective
      (fun w : ConcreteSurface O pi u a b ⧸ Ideal.span
      {algebraMap O (ConcreteSurface O pi u a b) pi} => Ideal.Quotient.mk
      (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}) f * w)) {N : ℕ}
    (β : Fin N → ConcreteSurface O pi u a b)
    (hβ : ResidueBasisFamily pi (fun i ↦ Ideal.Quotient.mk (Ideal.span {f}) (β i))) :
    ∃ B : Module.Basis (Fin N) O (ConcreteSurface O pi u a b ⧸ Ideal.span {f}), ∀ i,
      B i = Ideal.Quotient.mk (Ideal.span {f}) (β i) := by
  have := dvr_isAdicComplete_span_uniformizer O pi hpi
  have := concrete_surface_curve_isAdicComplete O pi hpi u a b ha f
  have hinj := concrete_surface_pi_regular_mod_curve O pi hpi u a b f hf
  refine residue_basis_family_basis O _ pi (fun m hm ↦ ?_) _ hβ
  have h2 : (Ideal.Quotient.mk (Ideal.span {f}))
      ((algebraMap O (ConcreteSurface O pi u a b)) pi) * m = 0 :=
    (Algebra.smul_def pi m).symm.trans hm
  exact hinj (h2.trans (mul_zero (M₀ := ConcreteSurface O pi u a b ⧸ Ideal.span {f}) _).symm)

/-- For `f` regular modulo `π`, a residue basis family of size `N` shows that
`R/(f)` is free of rank `N` over `O`. -/
private theorem concrete_surface_curve_free_finrank (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (f : ConcreteSurface O pi u a b)
    (hf : Function.Injective
      (fun w : ConcreteSurface O pi u a b ⧸ Ideal.span
      {algebraMap O (ConcreteSurface O pi u a b) pi} => Ideal.Quotient.mk
      (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}) f * w)) {N : ℕ}
    (β : Fin N → ConcreteSurface O pi u a b)
    (hβ : ResidueBasisFamily pi (fun i ↦ Ideal.Quotient.mk (Ideal.span {f}) (β i))) :
    Module.Free O (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) ∧ Module.Finite O
      (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) ∧ Module.finrank O
      (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) = N := by
  obtain ⟨B, _⟩ := concrete_surface_curve_basis O pi hpi u a b ha f hf β hβ
  exact ⟨Module.Free.of_basis B, Module.Finite.of_basis B, by simp [Module.finrank_eq_card_basis B]⟩

/-- Over an `O`-algebra `R`, the kernel of the reduction `R/(f) → R/(π, f)` consists of the
multiples of `π`. -/
private theorem factor_span_pair_eq_zero_iff {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (pi : O) (f : R) (hle : Ideal.span {f} ≤ Ideal.span {algebraMap O R pi, f})
    (m : R ⧸ Ideal.span {f}) :
    Ideal.Quotient.factorₐ O hle m = 0 ↔ ∃ w, m = pi • w := by
  have hsm (I : Ideal R) (r : R) : pi • Ideal.Quotient.mk I r =
      Ideal.Quotient.mk I (algebraMap O _ pi * r) :=
    congrArg (Ideal.Quotient.mk I) (Algebra.smul_def pi r)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  change Ideal.Quotient.mk _ r = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_pair]
  constructor
  · rintro ⟨α, g, hr⟩
    refine ⟨Ideal.Quotient.mk _ α, ?_⟩
    rw [hsm, Ideal.Quotient.eq, ← hr]
    exact Ideal.mem_span_singleton.mpr ⟨g, by ring⟩
  · rintro ⟨w, hw⟩
    obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [hsm, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hw
    obtain ⟨g, hg⟩ := hw
    exact ⟨α, g, by rw [hg]; ring⟩

/-- For `f` regular modulo `π`, the curve ring `R/(f)` is free over `O` of rank
equal to the length of `R/(π, f)`. -/
theorem concrete_surface_curve_free_of_length (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (f : ConcreteSurface O pi u a b)
    (hf : Function.Injective
      (fun w : ConcreteSurface O pi u a b ⧸ Ideal.span
      {algebraMap O (ConcreteSurface O pi u a b) pi} => Ideal.Quotient.mk
      (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}) f * w)) (N : ℕ)
    (hN : Module.length (ConcreteSurface O pi u a b)
      (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi, f}) =
      N) :
    Module.Free O (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) ∧ Module.Finite O
      (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) ∧ Module.finrank O
      (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) = N := by
  have : IsLocalRing (ConcreteSurface O pi u a b) :=
      concrete_surface_isLocalRing O pi u a b hpi.not_isUnit ha
  obtain ⟨e, he⟩ := concrete_surface_residueField_equiv O pi hpi u a b ha
  have hsurj : ∀ r : (ConcreteSurface O pi u a b), ∃ c : O,
      r - algebraMap O (ConcreteSurface O pi u a b) c ∈ IsLocalRing.maximalIdeal
      (ConcreteSurface O pi u a b) := by
    intro r
    obtain ⟨k, hk⟩ := e.surjective (IsLocalRing.residue (ConcreteSurface O pi u a b) r)
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective k
    exact ⟨c, by rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← he, hk, sub_self]⟩
  have hker : ∀ c : O,
      algebraMap O (ConcreteSurface O pi u a b) c ∈ IsLocalRing.maximalIdeal
      (ConcreteSurface O pi u a b) → pi ∣ c := by
    intro c hc
    rwa [← IsLocalRing.residue_eq_zero_iff, ← he, map_eq_zero_iff e e.injective,
      IsLocalRing.residue_eq_zero_iff, hpi.maximalIdeal_eq, Ideal.mem_span_singleton] at hc
  have hsm : ∀ (I : Ideal (ConcreteSurface O pi u a b)) (r : ConcreteSurface O pi u a b),
      pi • Ideal.Quotient.mk I r = Ideal.Quotient.mk I (algebraMap O _ pi * r) :=
    fun I r ↦ congrArg (Ideal.Quotient.mk I) (Algebra.smul_def pi r)
  have hpiM : ∀ m :
      (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi, f}),
      pi • m = 0 := by
    intro m
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [hsm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  obtain ⟨γ, hγ⟩ := residue_basis_family_of_length O (ConcreteSurface O pi u a b)
      ((ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi, f}))
      pi hsurj hker hpiM N hN
  have hle : Ideal.span {f} ≤ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi, f} :=
      Ideal.span_mono (by simp)
  let q : ((ConcreteSurface O pi u a b) ⧸ Ideal.span {f}) →ₗ[O]
      ((ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi, f}))
      := (Ideal.Quotient.factorₐ O hle).toLinearMap
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective hle
  obtain ⟨β₀, -, hβ₀⟩ :=
    residue_basis_family_lift_along_reduction O ((ConcreteSurface O pi u a b) ⧸ Ideal.span {f})
        ((ConcreteSurface O pi u a b ⧸ Ideal.span
          {algebraMap O (ConcreteSurface O pi u a b) pi, f})) pi q hq
          (factor_span_pair_eq_zero_iff pi f hle) γ hγ
  choose β hβ using fun i ↦ Ideal.Quotient.mk_surjective (β₀ i)
  have hfun : (fun i ↦ Ideal.Quotient.mk (Ideal.span {f}) (β i)) = β₀ := funext hβ
  exact concrete_surface_curve_free_finrank O pi hpi u a b ha f hf β (hfun ▸ hβ₀)

/-! ### Evaluation on completed charts -/

/-- Elements of `P` map into the maximal ideal of the completion at `P`. -/
private theorem completedPointMap_mem_maximalIdeal (A : Type) [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] (x : A) (hx : x ∈ P) :
    completedPointMap A P x ∈ IsLocalRing.maximalIdeal (CompletedLocalAt A P) := by
  have h1 : algebraMap A (Localization.AtPrime P) x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)]
    exact Ideal.mem_map_of_mem _ hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
  intro hu
  exact h1 ((isUnit_map_iff (algebraMap (Localization.AtPrime P)
    (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P))) _).mp hu)

/-- Elements of `I` are nilpotent modulo `I ^ n`. -/
private theorem isNilpotent_mk_pow_of_mem (S : Type) [CommRing S] (I : Ideal S) (n : ℕ) (y : S)
    (hy : y ∈ I) : IsNilpotent (Ideal.Quotient.mk (I ^ n) y) :=
  ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hy n⟩

/-- General form of `child_series_eval_comp_chart_subst` for an arbitrary quotient map
`sm : O[[T,X]] → R`. -/
private theorem eval_comp_chart_eq (O O' R : Type) [CommRing O] [CommRing O'] [CommRing R]
    (sm : TwoSeries O →+* R) (E F : TwoSeries O)
    (hEF : (E = axisT O ∧ F = axisX O) ∨ (E = axisX O ∧ F = axisT O))
    (P : Ideal (BlowupChart R (sm E) (sm F))) [P.IsPrime]
    [IsNoetherianRing (BlowupChart R (sm E) (sm F))]
    (hE : chartBase R (sm E) (sm F) (sm E) ∈ P) (hF : chartBase R (sm E) (sm F) (sm F) ∈ P)
    (ρ : O →+* O') (α : O') (s : TwoSeries O →+* TwoSeries O')
    (hsC : ∀ c : O, s (MvPowerSeries.C c) = MvPowerSeries.C (ρ c)) (hsE : s E = axisT O')
    (hsF : s F = axisT O' * (axisX O' + MvPowerSeries.C α))
    (κ : O' →+* CompletedLocalAt (BlowupChart R (sm E) (sm F)) P)
    (hκ : ∀ c : O, κ (ρ c) = completedPointMap (BlowupChart R (sm E) (sm F)) P
      (chartBase R (sm E) (sm F) (sm (MvPowerSeries.C c))))
    (Θ : TwoSeries O' →+* CompletedLocalAt (BlowupChart R (sm E) (sm F)) P)
    (hΘC : ∀ c : O', Θ (MvPowerSeries.C c) = κ c)
    (hΘT : Θ (axisT O') = completedPointMap (BlowupChart R (sm E) (sm F)) P
      (chartBase R (sm E) (sm F) (sm E)))
    (hΘX : Θ (axisX O') = completedPointMap (BlowupChart R (sm E) (sm F)) P
      (chartSlope R (sm E) (sm F)) - κ α) :
    Θ.comp s = (completedPointMap (BlowupChart R (sm E) (sm F)) P).comp
      ((chartBase R (sm E) (sm F)).comp sm) := by
  set A := BlowupChart R (sm E) (sm F)
  set cb := chartBase R (sm E) (sm F)
  set cp := completedPointMap A P
  set m := IsLocalRing.maximalIdeal (CompletedLocalAt A P)
  have gC (c : O) : Θ (s (.C c)) = cp (cb (sm (.C c))) := by rw [hsC, hΘC, hκ]
  have gE : Θ (s E) = cp (cb (sm E)) := by rw [hsE, hΘT]
  have gF : Θ (s F) = cp (cb (sm F)) := by
    rw [hsF, map_mul, map_add, hΘT, hΘX, hΘC, sub_add_cancel, ← map_mul, blowup_chart_relation]
  -- the variables `T, X` are `E, F` in some order
  have hG (G : TwoSeries O) (hG : G = E ∨ G = F) :
      Θ (s G) = cp (cb (sm G)) ∧ cp (cb (sm G)) ∈ m := by
    rcases hG with rfl | rfl
    exacts [⟨gE, completedPointMap_mem_maximalIdeal A P _ hE⟩,
      ⟨gF, completedPointMap_mem_maximalIdeal A P _ hF⟩]
  obtain ⟨gT, nT⟩ := hG (axisT O) (by rcases hEF with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2])
  obtain ⟨gX, nX⟩ := hG (axisX O) (by rcases hEF with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2])
  refine DFunLike.coe_injective (IsHausdorff.funext' m fun n r ↦ ?_)
  have key := twoSeries_ringHom_ext_of_isNilpotent O _
    ((Ideal.Quotient.mk (m ^ n)).comp (Θ.comp s))
    ((Ideal.Quotient.mk (m ^ n)).comp (cp.comp (cb.comp sm))) (fun c ↦ congrArg _ (gC c))
    (congrArg _ gT) (congrArg _ gX)
    (by simpa only [RingHom.comp_apply, gT] using isNilpotent_mk_pow_of_mem _ m n _ nT)
    (by simpa only [RingHom.comp_apply, gX] using isNilpotent_mk_pow_of_mem _ m n _ nX)
  exact congrArg (· r) key

/-- The evaluation `Θ` of the child power series, composed with the chart substitution `s`,
agrees with the canonical map from `O[[T,X]]` through the chart to its completion at `P`. -/
theorem child_series_eval_comp_chart_subst (O O' : Type) [CommRing O] [IsNoetherianRing O]
    [CommRing O'] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) (E F : TwoSeries O)
    (hEF : (E = axisT O ∧ F = axisX O) ∨ (E = axisX O ∧ F = axisT O))
    (P : Ideal
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)))
    [P.IsPrime]
    (hE : chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)
      (surfaceMk O pi u a b E) ∈ P)
    (hF : chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)
      (surfaceMk O pi u a b F) ∈ P) (ρ : O →+* O') (α : O') (s : TwoSeries O →+* TwoSeries O')
    (hsC : ∀ c : O, s (MvPowerSeries.C c) = MvPowerSeries.C (ρ c)) (hsE : s E = axisT O')
    (hsF : s F = axisT O' * (axisX O' + MvPowerSeries.C α))
    (κ : O' →+* CompletedLocalAt
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))
      P) (hκ : ∀ c : O,
      κ (ρ c) = completedPointMap
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) P
      (chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)
      (algebraMap O (ConcreteSurface O pi u a b) c)))
    (Θ : TwoSeries O' →+* CompletedLocalAt
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))
      P) (hΘC : ∀ c : O', Θ (MvPowerSeries.C c) = κ c)
    (hΘT : Θ (axisT O') = completedPointMap
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) P
      (chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)
      (surfaceMk O pi u a b E)))
    (hΘX : Θ (axisX O') = completedPointMap
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) P
      (chartSlope (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))
      - κ α) :
    Θ.comp s =
      (completedPointMap
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))
        P).comp ((chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E)
        (surfaceMk O pi u a b F)).comp (surfaceMk O pi u a b)) := by
  have : IsNoetherianRing (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E)
      (surfaceMk O pi u a b F)) :=
    blowupChart_concrete_isNoetherianRing O pi u a b _ _
  exact eval_comp_chart_eq O O' _ (surfaceMk O pi u a b) E F hEF P hE hF ρ α s hsC hsE hsF κ
    (fun c ↦ (hκ c).trans rfl) Θ hΘC hΘT hΘX

end SurfaceBlowup
