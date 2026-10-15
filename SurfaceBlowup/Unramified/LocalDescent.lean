/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.Charts
import SurfaceBlowup.Surfaces.PowerSeries
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Local lengths and finite quotients of completions

Assorted local results: the length of a principal quotient of the model special fibre
`k[[T,X]]/(T^a X^b)` in terms of contact numbers; finite quotients `Â/m̂^L ≃ A/m^L` of the
completion of a Noetherian local ring and the resulting descent of finite-colength ideals.

## Main results

* `SurfaceBlowup.crossing_special_fiber_length`, `SurfaceBlowup.single_special_fiber_length`
* `SurfaceBlowup.local_completion_finite_quotient`,
  `SurfaceBlowup.finite_colength_completion_ideal_descent`,
  `SurfaceBlowup.finite_completed_point_quotient_surjective`

Provenance: Thm_SurfaceBlowupV2_{crossing_special_fiber_length, single_special_fiber_length,
local_completion_finite_quotient, completion_to_finite_quotient_surjective,
finite_colength_completion_ideal_descent,
finite_completed_point_quotient_surjective}.
-/

namespace SurfaceBlowup


/-! ### Lengths in the special fibre -/

/-- Let `Xₛ` be a variable dividing `T^a X^b`. If the images of `F` and `Xₛ` in the special fibre
`k[[T,X]]/(T^a X^b)` have finite contact `c`, then `Xₛ` is a nonzerodivisor modulo `F` and
`k[[T,X]]/(F, Xₛⁿ)` has length `n c`. -/
private theorem axis_contact (k : Type) [Field k] (a b : ℕ) (F : TwoSeries k) (s t : Fin 2)
    (hst : s ≠ t) (c : ℕ)
    (hdvd : (MvPowerSeries.X s : TwoSeries k) ∣ MvPowerSeries.X 0 ^ a * MvPowerSeries.X 1 ^ b)
    (hc : contact (Ideal.Quotient.mk (monomialIdeal k a b) F)
      (Ideal.Quotient.mk _ (MvPowerSeries.X s)) = c) :
    (∀ n x, (MvPowerSeries.X s : TwoSeries k) ^ n * x ∈ Ideal.span {F} → x ∈ Ideal.span {F}) ∧
    ∀ n : ℕ, Module.length (TwoSeries k) (TwoSeries k ⧸
      (Ideal.span {F} ⊔ Ideal.span {(MvPowerSeries.X s : TwoSeries k) ^ n})) = n * c := by
  have hc' : Module.length (TwoSeries k)
      (TwoSeries k ⧸ (Ideal.span {F} ⊔ Ideal.span {(MvPowerSeries.X s : TwoSeries k)})) = c := by
    have hJ : monomialIdeal k a b ≤ Ideal.span {F, MvPowerSeries.X s} :=
      (Ideal.span_singleton_le_span_singleton.2 hdvd).trans
        (Ideal.span_mono (Set.subset_insert F _))
    have h1 := length_double_quotient_eq (TwoSeries k) (monomialIdeal k a b)
      (Ideal.span {F, MvPowerSeries.X s})
    rw [Ideal.map_span, Set.image_pair, sup_eq_right.mpr hJ] at h1
    rw [← Ideal.span_insert, ← h1]
    exact hc
  have hF : F ∉ Ideal.span {(MvPowerSeries.X s : TwoSeries k)} := fun hmem ↦ by
    rw [sup_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem),
      axis_quotient_length_top k s t hst] at hc'
    exact ENat.top_ne_natCast c hc'
  have hcan := axis_pow_mul_mem_span_cancel k s F hF
  refine ⟨hcan, fun n ↦ ?_⟩
  rw [length_quotient_sup_pow_eq_mul _ _ _ (fun x hx ↦ hcan 1 x (by simpa using hx)) n, hc']

/-- A principal quotient of `k[[T,X]]/(T^a X^b)` (with `a, b > 0`) by `f` has length `a c + b h`,
where `c` and `h` are the contacts of `f` with `T` and with `X`. -/
theorem crossing_special_fiber_length (k : Type) [Field k] (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b)
    (f : SpecialFiber k a b) (ht : contact f (fiberT k a b) = c)
    (hx : contact f (fiberX k a b) = h) :
    Module.length (SpecialFiber k a b) ((SpecialFiber k a b) ⧸ Ideal.span {f}) = a * c + b * h := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨-, hT⟩ := axis_contact k a b F 0 1 (by decide) c
    (dvd_mul_of_dvd_left (dvd_pow_self _ ha.ne') _) ht
  obtain ⟨hX, hX'⟩ := axis_contact k a b F 1 0 (by decide) h
    (dvd_mul_of_dvd_right (dvd_pow_self _ hb.ne') _) hx
  have h5 := length_double_quotient_eq (TwoSeries k) (monomialIdeal k a b) (Ideal.span {F})
  rw [Ideal.map_span, Set.image_singleton] at h5
  rw [h5, monomialIdeal, axisT, axisX, sup_comm, length_quotient_sup_mul_eq_add _ _ _ _ (hX b), hT,
    hX']

/-- A principal quotient of `k[[T,X]]/(T^a)` (with `a > 0`) by `f` has length `a c`, where `c` is
the contact of `f` with `T`. -/
theorem single_special_fiber_length (k : Type) [Field k] (a c : ℕ) (ha : 0 < a)
    (f : SpecialFiber k a 0) (hf : contact f (fiberT k a 0) = c) :
    Module.length (SpecialFiber k a 0) ((SpecialFiber k a 0) ⧸ Ideal.span {f}) = a * c := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨-, hT⟩ := axis_contact k a 0 F 0 1 (by decide) c
    (dvd_mul_of_dvd_left (dvd_pow_self _ ha.ne') _) hf
  have h5 := length_double_quotient_eq (TwoSeries k) (monomialIdeal k a 0) (Ideal.span {F})
  rw [Ideal.map_span, Set.image_singleton] at h5
  rw [h5, monomialIdeal, pow_zero, mul_one, sup_comm, axisT, hT]

/-! ### Finite quotients of completions -/

/-- For a Noetherian local ring `(A, m)` with completion `Â`, the quotient `Â/(m Â)^L` is
`A`-isomorphic to `A/m^L`, compatibly with the maps from `A`. -/
theorem local_completion_finite_quotient (A : Type) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (L : ℕ) :
    ∃ E : (LocalCompletion A ⧸ ((IsLocalRing.maximalIdeal A).map (localCompletionMap A))^L) ≃ₐ[A]
      (A ⧸ (IsLocalRing.maximalIdeal A)^L), ∀ a : A,
      E (Ideal.Quotient.mk (((IsLocalRing.maximalIdeal A).map (localCompletionMap A))^L)
        (localCompletionMap A a)) = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A)^L) a := by
  set I := IsLocalRing.maximalIdeal A
  have fg : I.FG := (IsNoetherian.noetherian I)
  have hker : RingHom.ker (AdicCompletion.evalₐ I L) = (I.map (localCompletionMap A))^L := by
    ext x
    trans x ∈ (AdicCompletion.eval I A L).ker
    · have eq : I ^ L • (⊤ : Ideal A) = I ^ L := by simp
      have : Function.Injective (Ideal.Quotient.factor ((le_of_eq eq))) := by
        simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
          using Ideal.map_mk_eq_bot_of_le (le_of_eq eq.symm)
      rw [RingHom.mem_ker, ← AdicCompletion.factor_eval_eq_evalₐ I x (le_of_eq eq)]
      exact (map_eq_zero_iff _ this).trans LinearMap.mem_ker.symm
    · rw [← AdicCompletion.pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map, ← Ideal.map_pow]
      rfl
  refine ⟨(Ideal.quotientEquivAlgOfEq A hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.surjective_evalₐ I L)), fun a ↦ ?_⟩
  simp only [AlgEquiv.trans_apply]
  exact AdicCompletion.evalₐ_of I L a

/-- For an ideal `J` of the completion `Â` containing `(m Â)^L`, the composite `A → Â → Â/J` is
surjective. -/
private theorem completion_to_finite_quotient_surjective (A : Type) [CommRing A]
    [IsNoetherianRing A]
    [IsLocalRing A] (L : ℕ) (J : Ideal (LocalCompletion A))
    (hJ : ((IsLocalRing.maximalIdeal A).map (localCompletionMap A)) ^ L ≤ J) :
    Function.Surjective ((Ideal.Quotient.mk J).comp (localCompletionMap A)) := by
  obtain ⟨E, hE⟩ := local_completion_finite_quotient A L
  intro q
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (E (Ideal.Quotient.mk _ b))
  refine ⟨a, Ideal.Quotient.eq.2 (hJ (Ideal.Quotient.eq.1 (E.injective ?_)))⟩
  rw [hE, ha]

/-- An ideal `J` of the completion `Â` containing `(m Â)^L` is extended from its contraction to
`A`. -/
theorem finite_colength_completion_ideal_descent (A : Type) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (L : ℕ) (J : Ideal (LocalCompletion A))
    (hJ : ((IsLocalRing.maximalIdeal A).map (localCompletionMap A)) ^ L ≤ J) :
    (J.comap (localCompletionMap A)).map (localCompletionMap A) = J := by
  refine le_antisymm Ideal.map_comap_le fun b hb ↦ ?_
  set M := (IsLocalRing.maximalIdeal A).map (localCompletionMap A)
  obtain ⟨E, hE⟩ := local_completion_finite_quotient A L
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (E (Ideal.Quotient.mk (M ^ L) b))
  have hdiff : b - localCompletionMap A a ∈ M ^ L :=
    Ideal.Quotient.eq.mp (E.injective (by rw [hE a, ha]))
  set I := J.comap (localCompletionMap A)
  have hML : M ^ L ≤ I.map (localCompletionMap A) := by
    rw [← Ideal.map_pow]
    exact Ideal.map_mono fun x hx ↦
      hJ ((Ideal.map_pow (localCompletionMap A) _ L).le (Ideal.mem_map_of_mem _ hx))
  simpa using (I.map (localCompletionMap A)).add_mem (hML hdiff)
    (Ideal.mem_map_of_mem (localCompletionMap A)
      (show a ∈ I from (by simpa using J.sub_mem hb (hJ hdiff) : localCompletionMap A a ∈ J)))

/-- At a maximal ideal `P` of a Noetherian ring `A`, an ideal `J` of the completed local ring
containing a power of its maximal ideal makes `A → Â_P → Â_P/J` surjective. -/
theorem finite_completed_point_quotient_surjective (A : Type) [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsMaximal] (L : ℕ) (J : Ideal (CompletedLocalAt A P))
    (hJ : ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (localCompletionMap (Localization.AtPrime P))) ^ L ≤ J) :
    Function.Surjective ((Ideal.Quotient.mk J).comp (completedPointMap A P)) := by
  intro y
  obtain ⟨x, rfl⟩ := completion_to_finite_quotient_surjective (Localization.AtPrime P) L J hJ y
  set φ := (Ideal.Quotient.mk J).comp (localCompletionMap (Localization.AtPrime P)) with hφ
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
  obtain ⟨b, u, hu, hbu⟩ := (inferInstance : P.IsMaximal).exists_inv s.2
  have hu' : u = 1 - b * s := by rw [← hbu]; ring
  have hgeom : (b * ∑ i ∈ Finset.range L, u ^ i) * s = 1 - u ^ L := by
    rw [← mul_neg_geom_sum, hu']; ring
  have huL : φ (algebraMap A _ (u ^ L)) = 0 := by
    simp only [hφ, RingHom.comp_apply, map_pow]
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hJ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P u).2 hu)) _)
  have hone : φ (algebraMap A _ ((b * ∑ i ∈ Finset.range L, u ^ i) * s)) = 1 := by
    rw [hgeom, map_sub, map_sub, huL, map_one, map_one, sub_zero]
  refine ⟨a * (b * ∑ i ∈ Finset.range L, u ^ i), ?_⟩
  have hmk : IsLocalization.mk' (Localization.AtPrime P) a s * algebraMap A _ (s : A)
      = algebraMap A _ a := IsLocalization.mk'_spec _ _ _
  change φ (algebraMap A _ _) = φ _
  calc φ (algebraMap A _ (a * (b * ∑ i ∈ Finset.range L, u ^ i)))
      = φ (IsLocalization.mk' (Localization.AtPrime P) a s * algebraMap A _ (s : A))
          * φ (algebraMap A _ (b * ∑ i ∈ Finset.range L, u ^ i)) := by
        rw [hmk, map_mul, map_mul]
    _ = φ (IsLocalization.mk' (Localization.AtPrime P) a s)
          * φ (algebraMap A _ ((b * ∑ i ∈ Finset.range L, u ^ i) * s)) := by
        simp only [map_mul]; ring
    _ = _ := by rw [hone, mul_one]

end SurfaceBlowup
