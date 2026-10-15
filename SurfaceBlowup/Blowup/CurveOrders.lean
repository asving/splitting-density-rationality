/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Formula.FiniteFieldCounts
import SurfaceBlowup.Formula.RationalEval
import SurfaceBlowup.Measure.AdicTransport
import SurfaceBlowup.Unramified.LocalDescent
import SurfaceBlowup.Unramified.PolynomialTypes

/-!
# Curve orders, the exceptional line, and finitely supported local data

Results about the blow-up charts of `Charts.lean`: curve ideals and curve sections on the two
charts and their inverse limit; glued function pairs; the exceptional line as `k[Z]` and the
overlap level as `k[Z, Z⁻¹]`; and the Chinese-remainder description of finitely supported local
data at finitely many maximal ideals.

The adic-perturbation and cylinder-measure API now lives in `Measure/AdicTransport.lean`, the
finite-field counts in `Formula/FiniteFieldCounts.lean`, and the rational evaluation of the
universal expressions in `Formula/RationalEval.lean`; this file imports them so that its
downstream modules see them unchanged.

## Main results

* `curve_ideal_lattice_eq_kernels`: curve ideals are the kernels of the finitely supported data.
* `curve_quotient_complete_equiv_threads`: `S/(g) ≅ lim S/(g, e^j)` for complete local `S`.
* `exceptional_line_equiv_residue_field`, `exceptional_overlap_is_laurent_line`: the exceptional
  line and its overlap.
* `homogeneous_form_not_mem_pow_succ`: forms with a unit coefficient have exact order `d`.
* `finite_support_quotient_equiv`, `finite_curve_support_kernel_saturated`: finitely supported
  local data.
* `division_equiv_child_coordinates`, `ideal_contact_generator`: miscellaneous.

Provenance: `Thm_SurfaceBlowupV2_{curve_ideal_lattice_eq_kernels, curve_ideal_lattice_le_sections,
curve_lattices_antitone, curve_limit_level_map_exists, curve_quotient_complete_equiv_threads,
curve_sections_quot_reduction_exists, directionPoint_properties, distinct_maximal_powers_coprime,
division_equiv_child_coordinates, exceptional_chart_is_affine_line,
exceptional_line_equiv_chart_exceptional, exceptional_line_equiv_residue_field,
exceptional_overlap_is_laurent_line, finite_curve_exceptional_annihilator,
finite_support_localization_recovers, finite_support_completion_recovers,
finite_support_quotient_surjective, finite_support_kernels_compatible,
finite_support_level_kernels_compatible, finite_support_generators_compatible,
finite_support_quotient_equiv, glued_function_left_chart, glued_function_pair_closed,
glued_function_pair_compatible, glued_function_right_chart, glued_generators_level_one,
homogeneous_form_not_mem_pow_succ, ideal_contact_generator,
kernel_saturation_from_top_layer_annihilators, finite_curve_support_kernel_saturated,
laurent_isUnit_iff_monomial}`.
-/

namespace SurfaceBlowup

/-! ### Curve orders on the two charts -/

/-- If `(g) + I` and `K ⊇ I` have the same image modulo `I`, then `(g) + I = K`. -/
private theorem span_sup_eq_of_map_eq {A : Type} [CommRing A] (I K : Ideal A) (g : A)
    (h : Ideal.span {Ideal.Quotient.mk I g} = K.map (Ideal.Quotient.mk I)) (hIK : I ≤ K) :
    Ideal.span {g} ⊔ I = K := by
  have h1 : Ideal.span {Ideal.Quotient.mk I g} = (Ideal.span {g}).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, Set.image_singleton]
  have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h
  rw [h1, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at h2
  have hk : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := Ideal.mk_ker
  rwa [hk, sup_eq_left.mpr hIK] at h2

/-- If the glued generators generate the level kernels of the curve data, then the curve ideals
on the two charts are the kernels of the finitely supported local data. -/
theorem curve_ideal_lattice_eq_kernels (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x)
    (D : TwoChartCurveData R t x beta) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hG : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} =
    leftLevelKernel D j ∧ Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} =
    rightLevelKernel D j) (j : ℕ) :
    leftCurveIdeal R t x beta G j = leftKernel D j ∧ rightCurveIdeal R t x beta G j = rightKernel D
        j := by
  have key : ∀ (A : Type) [CommRing A] (ι : Type) (P : ι → Ideal A) [∀ i, (P i).IsPrime]
      (J : ∀ i, Ideal (CompletedLocalAt A (P i))) (e : A) (g : ∀ i, CompletedLocalAt A (P i)),
      (∀ i, J i = finiteLocalCurveIdeal A (P i) e (g i) j) →
      e ^ j ∈ finiteSupportKernel A ι P J := by
    intro A _ ι P _ J e g hJ
    unfold finiteSupportKernel
    rw [Submodule.mem_iInf]
    intro i
    rw [Ideal.mem_comap, hJ i, map_pow]
    exact Ideal.subset_span (by simp)
  have hl : (chartExceptional R t x) ^ j ≤ leftKernel D j := by
    rw [chartExceptional, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact key _ _ _ _ _ (fun s => leftData D s) (fun _ => rfl)
  have hr : (chartExceptional R x t) ^ j ≤ rightKernel D j := by
    rw [chartExceptional, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact key _ _ _ _ _ (fun s => rightData D s) (fun _ => rfl)
  exact ⟨span_sup_eq_of_map_eq _ _ _ (by rw [(hG j).1]; rfl) hl,
    span_sup_eq_of_map_eq _ _ _ (by rw [(hG j).2]; rfl) hr⟩

/-- Every pair in the curve ideal lattice is a curve section. -/
theorem curve_ideal_lattice_le_sections (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ) :
    curveIdealLattice R t x beta G j ≤ curveSections R t x beta G j := by
  have hrel := blowup_chart_relation R t x
  set I := overlapCurveIdeal R t x beta G j
  set alg := algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
  have hE : (Ideal.span {overlapException R t x})^j ≤ I := le_sup_right
  have hL : Ideal.map alg (leftCurveIdeal R t x beta G j) ≤ I := by
    rw [leftCurveIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, chartExceptional,
      Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    exact sup_le le_sup_left hE
  have hbx : beta.right (chartBase R x t x) = overlapException R t x * overlapSlope R t x := by
    have h1 : beta.right (chartBase R x t x) = algebraMap R (BlowupOverlap R t x) x :=
      beta.right.commutes x
    rw [h1, overlapException, overlapSlope, ← map_mul, hrel, IsScalarTower.algebraMap_apply R
      (BlowupChart R t x) (BlowupOverlap R t x)]
    rfl
  have hR : Ideal.map beta.right.toRingHom (rightCurveIdeal R t x beta G j) ≤ I := by
    rw [rightCurveIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, chartExceptional,
      Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hu : IsUnit ((overlapSlope R t x)^d) :=
        (IsLocalization.Away.algebraMap_isUnit (chartSlope R t x)).pow d
      have h2 : (overlapSlope R t x)^d * beta.right (G.right j) ∈ I := by
        have h3 := hE (G.overlap j)
        have h4 : alg (G.left j) ∈ I :=
          (le_sup_left : Ideal.span _ ≤ I) (Ideal.subset_span rfl)
        simpa [alg] using I.sub_mem h4 h3
      obtain ⟨u, hu⟩ := hu
      have := I.mul_mem_left (↑u⁻¹) h2
      rwa [← hu, ← mul_assoc, Units.inv_mul, one_mul] at this
    · refine le_trans (Ideal.pow_right_mono ?_ j) hE
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change beta.right (chartBase R x t x) ∈ _
      rw [hbx]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  change alg a - (IsLocalization.Away.invSelf (chartSlope R t x))^0 * beta.right b ∈ I
  rw [pow_zero, one_mul]
  exact I.sub_mem (hL (Ideal.mem_map_of_mem _ ha)) (hR (Ideal.mem_map_of_mem _ hb))

/-- The curve ideal lattices and the curve sections decrease with the level. -/
theorem curve_lattices_antitone (R : Type) [CommRing R] (t x : R) (beta : BlowupRestriction R t x)
    (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ) :
    curveIdealLattice R t x beta G (j+1) ≤ curveIdealLattice R t x beta G j ∧ curveSections R t x
        beta G (j+1) ≤ curveSections R t x beta G j := by
  have key : ∀ (S : Type) [CommRing S] (s : S) (a b : S) (k : ℕ),
      a - b ∈ (Ideal.span {s})^k →
      Ideal.span {a} ⊔ (Ideal.span {s})^(k+1) ≤ Ideal.span {b} ⊔ (Ideal.span {s})^k := by
    intro S _ s a b k h
    refine sup_le ?_ (le_sup_of_le_right (Ideal.pow_le_pow_right (Nat.le_succ k)))
    rw [Ideal.span_singleton_le_iff_mem]
    rw [← add_sub_cancel b a]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.subset_span rfl)) (Ideal.mem_sup_right h)
  have hL : leftCurveIdeal R t x beta G (j+1) ≤ leftCurveIdeal R t x beta G j :=
    key _ _ _ _ _ (G.left_compat j)
  have hR : rightCurveIdeal R t x beta G (j+1) ≤ rightCurveIdeal R t x beta G j :=
    key _ _ _ _ _ (G.right_compat j)
  refine ⟨Submodule.prod_mono hL hR, ?_⟩
  have hO : overlapCurveIdeal R t x beta G (j+1) ≤ overlapCurveIdeal R t x beta G j := by
    apply key
    have h := G.left_compat j
    unfold chartExceptional at h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨c, hc⟩ := h
    rw [← map_sub, ← hc, map_mul, map_pow]
    have hm : (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t) ∈
        Ideal.span {overlapException R t x} := Ideal.subset_span rfl
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hm j)
  exact Submodule.comap_mono hO

/-- The curve order limit maps to each level of the curve sections, compatibly with threads. -/
theorem curve_limit_level_map_exists (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ) :
    ∃ π : CurveOrderLimit R t x beta G →ₗ[R] curveSectionsQuot R t x beta G j, ∀ p : curveThreads R
        t x beta G, ((π (curveLimitMk R t x beta G p) : curveSectionsQuot R t x beta G j) :
        (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G j) =
        (curveIdealLattice R t x beta G j).mkQ (p.val j) := by
  let g : curveThreads R t x beta G →ₗ[R] (BlowupChart R t x × BlowupChart R x t) ⧸
      curveIdealLattice R t x beta G j :=
    (curveIdealLattice R t x beta G j).mkQ ∘ₗ (LinearMap.proj j) ∘ₗ
        (curveThreads R t x beta G).subtype
  have hg : ∀ p, g p ∈ curveSectionsQuot R t x beta G j := by
    intro p
    have h := (Submodule.mem_inf.mp p.2).1
    exact ⟨p.val j, (Submodule.mem_pi.mp h) j (Set.mem_univ _), rfl⟩
  let g' := LinearMap.codRestrict (curveSectionsQuot R t x beta G j) g hg
  have hk : curveNullThreads R t x beta G ≤ LinearMap.ker g' := by
    intro p hp
    have : p.val j ∈ curveIdealLattice R t x beta G j := (Submodule.mem_pi.mp hp) j (Set.mem_univ _)
    rw [LinearMap.mem_ker]
    exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr this)
  exact ⟨(curveNullThreads R t x beta G).liftQ g' hk, fun _ => rfl⟩

/-- Reduction maps between consecutive levels of the curve sections modulo the curve lattices. -/
theorem curve_sections_quot_reduction_exists (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ) :
    ∃ ρ : curveSectionsQuot R t x beta G (j+1) →ₗ[R] curveSectionsQuot R t x beta G j, ∀ q :
        curveSectionsQuot R t x beta G (j+1), ∀ p : BlowupChart R t x × BlowupChart R x t,
        (q : (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G (j+1)) =
        (curveIdealLattice R t x beta G (j+1)).mkQ p → ((ρ q : curveSectionsQuot R t x beta G j) :
        (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G j) =
        (curveIdealLattice R t x beta G j).mkQ p := by
  obtain ⟨h1, h2⟩ := curve_lattices_antitone R t x beta d G j
  let m := Submodule.mapQ (curveIdealLattice R t x beta G (j+1)) (curveIdealLattice R t x beta G j)
      LinearMap.id
    (by simpa using h1)
  have hm : ∀ p, m ((curveIdealLattice R t x beta G (j+1)).mkQ p) =
      (curveIdealLattice R t x beta G j).mkQ p :=
    fun p => by simp [m]
  have hmap : ∀ q ∈ curveSectionsQuot R t x beta G (j+1), m q ∈ curveSectionsQuot R t x beta G j :=
      by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [show (curveIdealLattice R t x beta G (j+1)).mkQ p = _ from rfl, hm]
    exact ⟨p, h2 hp, rfl⟩
  refine ⟨m.restrict hmap, fun q p hp => ?_⟩
  change m (q : _) = _
  rw [hp, hm]

/-- For a complete Noetherian local ring `S` and `e` in its maximal ideal, `S/(g)` is the
inverse limit of the quotients `S/(g, e^j)`. -/
theorem curve_quotient_complete_equiv_threads (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [IsAdicComplete (IsLocalRing.maximalIdeal S) S] (e g : S)
    (he : e ∈ IsLocalRing.maximalIdeal S) :
    ∃ E : (S ⧸ Ideal.span {g}) ≃ {u : ∀ j : ℕ, S ⧸ Ideal.span {g, e^j} // ∀ j, levelReduction e g j
        (u (j+1)) = u j}, ∀ s : S, ∀ j : ℕ, (E (Ideal.Quotient.mk (Ideal.span {g}) s)).val j =
        Ideal.Quotient.mk (Ideal.span {g, e^j}) s := by
  have hle : ∀ j : ℕ, Ideal.span {g} ≤ Ideal.span {g, e^j} := fun j =>
    Ideal.span_mono (by simp)
  have hIne : Ideal.span {e} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal e).mp he
  have hpow : ∀ j : ℕ, ((Ideal.span {e}) ^ j • (⊤ : Submodule S S)) = Ideal.span {e ^ j} :=
    fun j ↦ by rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have hpair : ∀ j : ℕ, Ideal.span {g, e^j} = Ideal.span {g} ⊔ Ideal.span {e} ^ j :=
    fun j ↦ by rw [Ideal.span_singleton_pow, Ideal.span_insert]
  let F : S ⧸ Ideal.span {g} → {u : ∀ j : ℕ, S ⧸ Ideal.span {g, e^j} // ∀ j, levelReduction e g j
      (u (j+1)) = u j} :=
    fun q => ⟨fun j => Ideal.Quotient.factor (hle j) q, by
      intro j
      induction q using Quotient.inductionOn' with
      | h s => rfl⟩
  have hF : ∀ s j, (F (Ideal.Quotient.mk _ s)).val j = Ideal.Quotient.mk (Ideal.span {g, e^j}) s :=
    fun s j => rfl
  have hbij : Function.Bijective F := by
    constructor
    · intro q₁ q₂ h
      obtain ⟨s₁, rfl⟩ := Ideal.Quotient.mk_surjective q₁
      obtain ⟨s₂, rfl⟩ := Ideal.Quotient.mk_surjective q₂
      rw [Ideal.Quotient.eq, ← iInf_sup_pow_eq_of_isLocalRing S (Ideal.span {e}) (Ideal.span {g})
        hIne, Ideal.mem_iInf]
      exact fun j ↦ hpair j ▸ Ideal.Quotient.eq.mp (congrArg (fun u ↦ u.val j) h)
    · intro u
      choose s hs using fun j => Ideal.Quotient.mk_surjective (u.val j)
      have hdiff : ∀ j, s (j+1) - s j ∈ Ideal.span {g, e^j} := by
        intro j
        rw [← Ideal.Quotient.eq]
        have := u.property j
        rwa [← hs (j+1), ← hs j] at this
      choose a b hab using fun j => Ideal.mem_span_pair.mp (hdiff j)
      let t : ℕ → S := fun j => s j - ∑ i ∈ Finset.range j, a i * g
      have ht : ∀ j, t j ≡ t (j+1) [SMOD ((Ideal.span {e}) ^ j • (⊤ : Submodule S S))] := by
        intro j
        rw [SModEq.sub_mem, hpow]
        have : t j - t (j+1) = -(b j) * e ^ j := by
          simp only [t, Finset.sum_range_succ]
          linear_combination hab j
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      obtain ⟨L, hL⟩ := IsPrecomplete.prec
        (isAdicComplete_of_isAdicComplete_maximalIdeal S _ hIne).toIsPrecomplete
        ((AdicCompletion.isAdicCauchy_iff (Ideal.span {e}) S t).mpr ht)
      refine ⟨Ideal.Quotient.mk _ L, Subtype.ext <| funext fun j ↦ ?_⟩
      rw [hF, ← hs j, Ideal.Quotient.eq]
      have h1 : L - t j ∈ Ideal.span {e ^ j} := by
        rw [← hpow]; exact (SModEq.sub_mem.mp (hL j).symm)
      have h2 : L - s j = (L - t j) + (-(∑ i ∈ Finset.range j, a i) * g) := by
        simp only [t]; rw [neg_mul, Finset.sum_mul]; ring
      rw [h2]
      exact Ideal.add_mem _ (Ideal.span_mono (by simp) h1)
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  exact ⟨Equiv.ofBijective F hbij, fun s j => rfl⟩

/-! ### Glued functions -/

/-- A surface function lifting the glued pair agrees with it on the `t`-chart modulo `(t)^j`. -/
theorem glued_function_left_chart (R : Type) [CommRing R] (t x : R) (beta : BlowupRestriction R t x)
    (d : ℕ) (G : GluedGenerators R t x beta d) (f : R) (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
    (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j)) (j : ℕ) :
    algebraMap R (BlowupChart R t x) f - (chartBase R t x t)^d * G.left j ∈
        (chartExceptional R t x)^j := by
  have h := hf j
  simp only [surfaceToCechInput, LinearMap.comp_apply, Submodule.mkQ_apply] at h
  exact (Submodule.Quotient.eq _).mp h |>.1

/-- A surface function lifting the glued pair agrees with it on the `x`-chart modulo `(x)^j`. -/
theorem glued_function_right_chart (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d) (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f = (cechInputLattice R t x j).mkQ
    (gluedFunctionPair R t x G j)) (j : ℕ) :
    algebraMap R (BlowupChart R x t) f - (chartBase R x t x)^d * G.right j ∈
        (chartExceptional R x t)^j := by
  have h := hf j
  simp only [surfaceToCechInput, LinearMap.comp_apply, Submodule.mkQ_apply] at h
  exact (Submodule.Quotient.eq _).mp h |>.2

/-- The glued function pair is closed under the untwisted level Čech differential. -/
theorem glued_function_pair_closed (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta 0)) :
    finiteCechDifferential R t x beta 0 j h ((cechInputLattice R t x j).mkQ
        (gluedFunctionPair R t x G j)) = 0 := by
  unfold finiteCechDifferential
  rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  have hx : beta.right (chartBase R x t x) = overlapException R t x * overlapSlope R t x := by
    have h1 : chartBase R x t x = algebraMap R (BlowupChart R x t) x := rfl
    rw [h1, AlgHom.commutes, IsScalarTower.algebraMap_apply R (BlowupChart R t x),
      overlapException, overlapSlope, ← map_mul, blowup_chart_relation]
    rfl
  have key : fullCechDifferential R t x beta 0 (gluedFunctionPair R t x G j) =
      overlapException R t x ^ d *
        (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (G.left j) -
          (overlapSlope R t x)^d * beta.right (G.right j)) := by
    simp only [fullCechDifferential, ringCechDifferential, gluedFunctionPair, LinearMap.coe_mk,
      AddHom.coe_mk, pow_zero, one_mul, map_mul, map_pow, hx, IsScalarTower.coe_toAlgHom']
    simp only [overlapException]
    ring
  rw [key]
  change _ ∈ (Ideal.span {overlapException R t x})^j
  exact Ideal.mul_mem_left _ _ (G.overlap j)

/-- The glued function pairs form a compatible thread. -/
theorem glued_function_pair_compatible (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ) :
    cechInputReduction R t x j ((cechInputLattice R t x (j+1)).mkQ
        (gluedFunctionPair R t x G (j+1))) = (cechInputLattice R t x j).mkQ
        (gluedFunctionPair R t x G j) := by
  change Submodule.Quotient.mk (gluedFunctionPair R t x G (j+1)) =
    Submodule.Quotient.mk (p := cechInputLattice R t x j) (gluedFunctionPair R t x G j)
  rw [Submodule.Quotient.eq]
  constructor
  · change (chartBase R t x t)^d * G.left (j+1) - (chartBase R t x t)^d * G.left j ∈
      (chartExceptional R t x)^j
    rw [← mul_sub]
    exact Ideal.mul_mem_left _ _ (G.left_compat j)
  · change (chartBase R x t x)^d * G.right (j+1) - (chartBase R x t x)^d * G.right j ∈
      (chartExceptional R x t)^j
    rw [← mul_sub]
    exact Ideal.mul_mem_left _ _ (G.right_compat j)

/-- Level-one generators glued up to a unit can be renormalized to glue exactly. -/
theorem glued_generators_level_one (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (gA1 : BlowupChart R t x) (gB1 : BlowupChart R x t)
    (hnorm : ∃ u : Rˣ, (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) gA1 - algebraMap R
    (BlowupOverlap R t x) (u : R) * ((overlapSlope R t x) ^ d * beta.right gB1) ∈
    (Ideal.span {overlapException R t x})) :
    ∃ (FA1 : BlowupChart R t x) (FB1 : BlowupChart R x t), Ideal.span
        {Ideal.Quotient.mk ((chartExceptional R t x)^1) FA1} = Ideal.span
        {Ideal.Quotient.mk ((chartExceptional R t x)^1) gA1} ∧ Ideal.span
        {Ideal.Quotient.mk ((chartExceptional R x t)^1) FB1} = Ideal.span
        {Ideal.Quotient.mk ((chartExceptional R x t)^1) gB1} ∧
        (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) FA1 - (overlapSlope R t x)^d *
        beta.right FB1 ∈ (Ideal.span {overlapException R t x})^1 := by
  obtain ⟨u, hu⟩ := hnorm
  refine ⟨gA1, algebraMap R (BlowupChart R x t) (u : R) * gB1, rfl, ?_, ?_⟩
  · have hU : IsUnit (Ideal.Quotient.mk ((chartExceptional R x t)^1)
      (algebraMap R (BlowupChart R x t) (u : R))) :=
      (u.isUnit.map (algebraMap R (BlowupChart R x t))).map _
    obtain ⟨v, hv⟩ := hU
    rw [map_mul, ← hv]
    exact Ideal.span_singleton_mul_left_unit v.isUnit _
  · rw [pow_one]
    have : beta.right (algebraMap R (BlowupChart R x t) (u : R) * gB1) = algebraMap R
        (BlowupOverlap R t x) (u : R) * beta.right gB1 := by
      rw [map_mul]; congr 1; exact AlgHom.commutes _ _
    rwa [this, mul_left_comm]

/-! ### The exceptional line -/

/-- The first level `A/(t)` of the `t`-chart is the polynomial ring `(R/(t, x))[Z]`. -/
theorem exceptional_chart_is_affine_line (R : Type) [CommRing R] (t x : R) :
    ∃ e : ExceptionalChartLevel R t x 1 ≃+* Polynomial (R ⧸ Ideal.span {t,x}),
        (∀ r : R, e (levelBase R t x 1 r) = Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r)) ∧
        e (levelSlope R t x 1) = Polynomial.X := by
  set I : Ideal R := Ideal.span {t, x}
  have ht : Ideal.Quotient.mk I t = 0 := Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.subset_span (by simp))
  have hx : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.subset_span (by simp))
  let f0 : Polynomial R →+* Polynomial (R ⧸ I) := Polynomial.mapRingHom (Ideal.Quotient.mk I)
  have hf0 : ∀ a ∈ Ideal.span {blowupRelation R t x}, f0 a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [f0, blowupRelation, ht, hx]
  let f1 : BlowupChart R t x →+* Polynomial (R ⧸ I) := Ideal.Quotient.lift _ f0 hf0
  have hf1 : ∀ a ∈ exceptionalLevelIdeal R t x 1, f1 a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [f1, f0, chartBase, ht]
  let F : ExceptionalChartLevel R t x 1 →+* Polynomial (R ⧸ I) := Ideal.Quotient.lift _ f1 hf1
  have hbt : levelBase R t x 1 t = 0 := by
    simp only [levelBase, RingHom.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
  have hbx : levelBase R t x 1 x = 0 := by
    simp only [levelBase, RingHom.comp_apply, ← blowup_chart_relation R t x, map_mul]
    have h := hbt
    simp only [levelBase, RingHom.comp_apply] at h
    rw [h]; exact zero_mul (M₀ := ExceptionalChartLevel R t x 1) _
  have hb : ∀ a ∈ I, levelBase R t x 1 a = 0 := fun a ha ↦
    (show I ≤ RingHom.ker (levelBase R t x 1) from
      Ideal.span_le.2 (by rintro y (rfl | rfl); exacts [hbt, hbx])) ha
  let g0 : R ⧸ I →+* ExceptionalChartLevel R t x 1 := Ideal.Quotient.lift I (levelBase R t x 1) hb
  let G : Polynomial (R ⧸ I) →+* ExceptionalChartLevel R t x 1 := Polynomial.eval₂RingHom g0
      (levelSlope R t x 1)
  have hFb : ∀ r : R, F (levelBase R t x 1 r) = Polynomial.C (Ideal.Quotient.mk I r) := by
    intro r; simp [F, f1, f0, levelBase, chartBase]
  have hFs : F (levelSlope R t x 1) = Polynomial.X := by
    simp [F, f1, f0, levelSlope, chartSlope]
  have hGF : G.comp F = RingHom.id _ := by
    refine Ideal.Quotient.ringHom_ext <| Ideal.Quotient.ringHom_ext <| Polynomial.ringHom_ext ?_ ?_
    · intro r
      change G (F (levelBase R t x 1 r)) = levelBase R t x 1 r
      rw [hFb]; simp [G, g0]
    · change G (F (levelSlope R t x 1)) = levelSlope R t x 1
      rw [hFs]; simp [G]
  have hFG : F.comp G = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp [G, g0, hFb]
    · simp [G, hFs]
  exact ⟨RingEquiv.ofRingHom F G hFG hGF, hFb, hFs⟩

/-- The `t`-chart modulo its exceptional ideal is `(R/(t, x))[Z]`. -/
theorem exceptional_line_equiv_chart_exceptional (R : Type) [CommRing R] (t x : R) :
    ∃ e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial
        (R ⧸ Ideal.span ({t,x} : Set R)), (∀ r : R, e (Ideal.Quotient.mk (chartExceptional R t x)
        (chartBase R t x r)) = Polynomial.C (Ideal.Quotient.mk (Ideal.span ({t,x} : Set R)) r)) ∧ e
        (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X := by
  obtain ⟨e₀, h1, h2⟩ := exceptional_chart_is_affine_line R t x
  have hI : chartExceptional R t x = exceptionalLevelIdeal R t x 1 := by
    simp [chartExceptional, exceptionalLevelIdeal]
  exact ⟨(Ideal.quotEquivOfEq hI).trans e₀, fun r => h1 r, h2⟩

/-- For a surface, the `t`-chart modulo its exceptional ideal is `k[Z]`, `k` the residue
field. -/
theorem exceptional_line_equiv_residue_field (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) :
    ∃ e : (BlowupChart R S.t S.x ⧸ chartExceptional R S.t S.x) ≃+* Polynomial
        (IsLocalRing.ResidueField R), (∀ r : R, e (Ideal.Quotient.mk (chartExceptional R S.t S.x)
        (chartBase R S.t S.x r)) = Polynomial.C (IsLocalRing.residue R r)) ∧ e
        (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartSlope R S.t S.x)) = Polynomial.X := by
  obtain ⟨e₀, h1, h2⟩ := exceptional_line_equiv_chart_exceptional R S.t S.x
  let κ : (R ⧸ Ideal.span ({S.t, S.x} : Set R)) ≃+* IsLocalRing.ResidueField R :=
    Ideal.quotEquivOfEq S.parameters
  refine ⟨e₀.trans (Polynomial.mapEquiv κ), ?_, ?_⟩
  · intro r
    simp only [RingEquiv.trans_apply, h1]
    change Polynomial.map (κ.toRingHom) (Polynomial.C _) = _
    rw [Polynomial.map_C]
    rfl
  · simp [h2]

/-- The first level of the overlap is the Laurent polynomial ring `(R/(t, x))[Z, Z⁻¹]`. -/
theorem exceptional_overlap_is_laurent_line (R : Type) [CommRing R] (t x : R) :
    ∃ e : ExceptionalOverlapLevel R t x 1 ≃+* LaurentPolynomial (R ⧸ Ideal.span {t,x}),
        (∀ r : R, e (levelOverlapMap R t x 1 (levelBase R t x 1 r)) = LaurentPolynomial.C
        (Ideal.Quotient.mk (Ideal.span {t,x}) r)) ∧ e (levelOverlapMap R t x 1 (levelSlope R t x 1))
        = LaurentPolynomial.T 1 := by
  obtain ⟨e0, hC, hX⟩ := exceptional_chart_is_affine_line R t x
  have hL : IsLocalization (Submonoid.powers (Polynomial.X : Polynomial (R ⧸ Ideal.span {t,x})))
      (LaurentPolynomial (R ⧸ Ideal.span {t,x})) := LaurentPolynomial.isLocalization
  let E := IsLocalization.ringEquivOfRingEquiv (ExceptionalOverlapLevel R t x 1)
    (LaurentPolynomial (R ⧸ Ideal.span {t,x})) (M := Submonoid.powers (levelSlope R t x 1))
    (T := Submonoid.powers (Polynomial.X : Polynomial (R ⧸ Ideal.span {t,x}))) e0
    (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hX)
  have hE (a) : E (algebraMap _ _ a) = algebraMap _ _ (e0 a) :=
    IsLocalization.ringEquivOfRingEquiv_eq _ a
  refine ⟨E, fun r => ?_, ?_⟩
  · simp only [levelOverlapMap]
    rw [hE, hC, LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C]
  · simp only [levelOverlapMap]
    rw [hE, hX, LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X]

/-- The units of a Laurent polynomial ring over a field are the nonzero monomials. -/
theorem laurent_isUnit_iff_monomial (k : Type) [Field k] (f : LaurentPolynomial k) :
    IsUnit f ↔ ∃ c : k, c ≠ 0 ∧ ∃ m : ℤ, f = LaurentPolynomial.C c * LaurentPolynomial.T m := by
  constructor
  · rintro ⟨u, rfl⟩
    set f : LaurentPolynomial k := u.val
    set g : LaurentPolynomial k := u.inv
    have hfg : f * g = 1 := u.val_inv
    have hf : f ≠ 0 := fun h => by simp [h] at hfg
    have hg : g ≠ 0 := fun h => by simp [h] at hfg
    have hfn : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.2 fun h ↦
      hf (AddMonoidAlgebra.coeff_injective (by simpa using h))
    have hgn : g.coeff.support.Nonempty := Finsupp.support_nonempty_iff.2 fun h ↦
      hg (AddMonoidAlgebra.coeff_injective (by simpa using h))
    set a := f.coeff.support.max' hfn
    set a' := g.coeff.support.max' hgn
    set b := f.coeff.support.min' hfn
    set b' := g.coeff.support.min' hgn
    have hsupp1 : ∀ n : ℤ, (1 : LaurentPolynomial k).coeff n ≠ 0 → n = 0 := fun n hn ↦ by
      rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single] at hn
      exact not_imp_comm.1 Finsupp.single_eq_of_ne hn
    have e1 : a + a' = 0 := by
      apply hsupp1
      rw [← hfg, AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd]
      · exact mul_ne_zero (Finsupp.mem_support_iff.1 (Finset.max'_mem _ _))
          (Finsupp.mem_support_iff.1 (Finset.max'_mem _ _))
      · intro x y hx hy hxy
        have := Finset.le_max' _ x hx; have := Finset.le_max' _ y hy
        constructor <;> omega
    have e2 : b + b' = 0 := by
      apply hsupp1
      rw [← hfg, AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd]
      · exact mul_ne_zero (Finsupp.mem_support_iff.1 (Finset.min'_mem _ _))
          (Finsupp.mem_support_iff.1 (Finset.min'_mem _ _))
      · intro x y hx hy hxy
        have := Finset.min'_le _ x hx; have := Finset.min'_le _ y hy
        constructor <;> omega
    have hb' : b' ≤ a' := Finset.min'_le_max' _ hgn
    have hsub : f.coeff.support ⊆ {a} := fun c hc => by
      have := Finset.le_max' _ c hc; have := Finset.min'_le _ c hc
      rw [Finset.mem_singleton]; omega
    refine ⟨f.coeff a, Finsupp.mem_support_iff.1 (Finset.max'_mem _ _), a, ?_⟩
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    apply AddMonoidAlgebra.coeff_injective
    rw [AddMonoidAlgebra.coeff_single]
    exact Finsupp.support_subset_singleton.1 hsub
  · rintro ⟨c, hc, m, rfl⟩
    exact ((isUnit_iff_ne_zero.2 hc).map LaurentPolynomial.C).mul (LaurentPolynomial.isUnit_T m)

/-- The points above affine directions of the exceptional line are maximal, contain `t`,
contain the slope exactly for the direction `Z`, map to `(φ)` on the exceptional line, depend
injectively on `φ`, and the point above `Z` is `(t, Z)`. -/
theorem directionPoint_properties (R : Type) [CommRing R] [IsLocalRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+*
    Polynomial (IsLocalRing.ResidueField R)) (he : ∀ r : R, e
    (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) = Polynomial.C
    (IsLocalRing.residue R r)) (heZ : e (Ideal.Quotient.mk (chartExceptional R t x)
    (chartSlope R t x)) = Polynomial.X) :
    (∀ φ : AffineDirection (IsLocalRing.ResidueField R), (directionPoint R t x e φ).IsMaximal ∧
        chartBase R t x t ∈ directionPoint R t x e φ ∧ (chartSlope R t x ∈ directionPoint R t x e φ
        ↔ φ = zeroAffine (IsLocalRing.ResidueField R)) ∧
        ((directionPoint R t x e φ).map (Ideal.Quotient.mk (chartExceptional R t x))).map e =
        Ideal.span {φ.val}) ∧ Function.Injective (directionPoint R t x e) ∧ directionPoint R t x e
        (zeroAffine (IsLocalRing.ResidueField R)) = Ideal.span {chartBase R t x t, chartSlope R t x}
        := by
  set ψ : BlowupChart R t x →+* Polynomial (IsLocalRing.ResidueField R) :=
    e.toRingHom.comp (Ideal.Quotient.mk (chartExceptional R t x)) with hψ
  have hsurj : Function.Surjective ψ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker ψ = chartExceptional R t x := by
    ext a
    simp [hψ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hDP : ∀ φ : AffineDirection (IsLocalRing.ResidueField R),
      directionPoint R t x e φ = (Ideal.span {φ.val}).comap ψ := fun _ => rfl
  have ht0 : ψ (chartBase R t x t) = 0 := by
    have hm : Ideal.span ({t,x} : Set R) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal inferInstance
    have : t ∈ IsLocalRing.maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
    change e _ = 0
    rw [he, (IsLocalRing.residue_eq_zero_iff t).2 this, map_zero]
  have hZ : ψ (chartSlope R t x) = Polynomial.X := heZ
  have himg : ∀ φ : AffineDirection (IsLocalRing.ResidueField R),
      ((directionPoint R t x e φ).map (Ideal.Quotient.mk (chartExceptional R t x))).map e
        = Ideal.span {φ.val} := by
    intro φ
    rw [show Ideal.map e (Ideal.map (Ideal.Quotient.mk (chartExceptional R t x))
        (directionPoint R t x e φ)) = Ideal.map e.toRingHom (Ideal.map
        (Ideal.Quotient.mk (chartExceptional R t x)) (directionPoint R t x e φ)) from rfl,
      Ideal.map_map, hDP]
    exact Ideal.map_comap_of_surjective ψ hsurj _
  refine ⟨fun φ => ⟨?_, ?_, ?_, himg φ⟩, ?_, ?_⟩
  · have := PrincipalIdealRing.isMaximal_of_irreducible φ.2.2
    exact Ideal.comap_isMaximal_of_surjective ψ hsurj
  · rw [hDP, Ideal.mem_comap, ht0]; exact zero_mem _
  · rw [hDP, Ideal.mem_comap, hZ, Ideal.mem_span_singleton]
    exact ⟨fun h ↦ Subtype.ext <| Polynomial.eq_of_monic_of_associated φ.2.1 Polynomial.monic_X
      (φ.2.2.associated_of_dvd Polynomial.irreducible_X h), by rintro rfl; exact dvd_rfl⟩
  · intro φ φ' h
    have h2 := himg φ
    rw [h, himg φ', Ideal.span_singleton_eq_span_singleton] at h2
    exact Subtype.ext (Polynomial.eq_of_monic_of_associated φ.2.1 φ'.2.1 h2.symm)
  · have key : ∀ I J : Ideal (BlowupChart R t x), RingHom.ker ψ ≤ I → RingHom.ker ψ ≤ J →
        I.map ψ = J.map ψ → I = J := by
      intro I J hI hJ hIJ
      rw [RingHom.ker_eq_comap_bot] at hI hJ
      rw [← sup_eq_left.2 hI, ← sup_eq_left.2 hJ, ← Ideal.comap_map_of_surjective ψ hsurj,
        ← Ideal.comap_map_of_surjective ψ hsurj, hIJ]
    apply key
    · rw [hker, chartExceptional, Ideal.span_le, Set.singleton_subset_iff, hDP, SetLike.mem_coe,
        Ideal.mem_comap, ht0]; exact zero_mem _
    · rw [hker, chartExceptional, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    · rw [hDP, Ideal.map_comap_of_surjective ψ hsurj, Ideal.map_span, Set.image_pair, ht0, hZ,
        Ideal.span_insert_zero]
      rfl

/-- A degree-`d` form in a regular pair `(t, x)` with a coefficient outside `(t, x)` does not
lie in `(t, x)^(d+1)`. -/
theorem homogeneous_form_not_mem_pow_succ (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (hreg : RegularParameterPair R t x) (d : ℕ)
    (c : Fin (d + 1) → R) (i₀ : Fin (d + 1)) (hi₀ : c i₀ ∉ Ideal.span {t,x}) :
    (∑ i : Fin (d+1), c i * t^(d - i.val) * x^i.val) ∉ (Ideal.span {t,x})^(d+1) := by
  intro hF
  set φ := chartBase R t x with hφ
  set Z := chartSlope R t x with hZ
  have hrel : φ t * Z = φ x := blowup_chart_relation R t x
  have hinjd : IsLeftRegular (φ t ^ d) :=
    IsLeftRegular.pow d (blowup_exceptional_parameter_regular R t x hreg)
  set P : BlowupChart R t x := ∑ i : Fin (d+1), φ (c i) * Z ^ i.val with hP
  have hFP : φ (∑ i : Fin (d+1), c i * t^(d - i.val) * x^i.val) = φ t ^ d * P := by
    rw [map_sum, hP, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.val ≤ d := Nat.lt_succ_iff.mp i.2
    simp only [map_mul, map_pow]
    rw [← hrel, mul_pow]
    have : φ t ^ d = φ t ^ (d - i.val) * φ t ^ i.val := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    rw [this]; ring
  have hmem : φ (∑ i : Fin (d+1), c i * t^(d - i.val) * x^i.val) ∈ (Ideal.span {φ t})^(d+1) := by
    have h1 : φ (∑ i : Fin (d+1), c i * t^(d - i.val) * x^i.val) ∈ Ideal.map φ
        ((Ideal.span {t,x})^(d+1)) :=
      Ideal.mem_map_of_mem _ hF
    rw [Ideal.map_pow] at h1
    refine Ideal.pow_right_mono ?_ _ h1
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | hy
    · exact Ideal.subset_span rfl
    · have : y = x := by simpa using hy
      subst this
      rw [SetLike.mem_coe, ← hrel]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨w, hw⟩ := hmem
  rw [hFP] at hw
  have hPw : P = φ t * w := hinjd <| show φ t ^ d * P = φ t ^ d * (φ t * w) by
    rw [← mul_assoc, ← pow_succ, ← hw]; ring
  obtain ⟨e, he1, he2⟩ := exceptional_chart_is_affine_line R t x
  have hQ : (∑ i : Fin (d+1), levelBase R t x 1 (c i) * levelSlope R t x 1 ^ i.val)
      = Ideal.Quotient.mk (exceptionalLevelIdeal R t x 1) P := by
    rw [hP, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [levelBase, levelSlope, hφ, hZ]
  have hzero : Ideal.Quotient.mk (exceptionalLevelIdeal R t x 1) P = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, hPw, exceptionalLevelIdeal, pow_one]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have h0 := congrArg e (hQ.trans hzero)
  rw [map_sum, map_zero] at h0
  have h1 := congrArg (fun p => Polynomial.coeff p i₀.val) h0
  simp only [map_mul, map_pow, he1, he2, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at h1
  rw [Finset.sum_eq_single i₀] at h1
  · exact hi₀ (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h1))
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have : i₀.val ≠ b.val := fun h => hb (Fin.ext h).symm
    simp [this]
  · simp

/-! ### Finitely supported local data -/

/-- Powers of distinct maximal ideals are coprime. -/
private theorem distinct_maximal_powers_coprime (A : Type) [CommRing A] (P Q : Ideal A)
    [P.IsMaximal]
    [Q.IsMaximal] (hPQ : P ≠ Q) (L M : ℕ) :
    IsCoprime (P^L) (Q^M) :=
  (Ideal.isCoprime_of_isMaximal hPQ).pow

/-- Localizing the finitely supported kernel at `P i` recovers the contraction of `J i`. -/
private theorem finite_support_localization_recovers (A : Type) [CommRing A] [IsNoetherianRing A]
    (ι : Type)
    [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hP : Function.Injective P) (L : ι → ℕ)
    (J : ∀ i, Ideal (CompletedLocalAt A (P i))) (hJ : ∀ i,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ J i) (i : ι) :
    (finiteSupportKernel A ι P J).map (algebraMap A (Localization.AtPrime (P i))) = (J i).comap
        (localCompletionMap (Localization.AtPrime (P i))) := by
  classical
  have := Fintype.ofFinite ι
  set R := Localization.AtPrime (P i)
  set K : Ideal R := (J i).comap (localCompletionMap R) with hKdef
  have hIi : (J i).comap (completedPointMap A (P i)) = K.comap (algebraMap A R) := rfl
  apply le_antisymm
  · have h1 : finiteSupportKernel A ι P J ≤ (J i).comap (completedPointMap A (P i)) :=
      iInf_le _ i
    calc _ ≤ ((J i).comap (completedPointMap A (P i))).map (algebraMap A R) := Ideal.map_mono h1
      _ = K := by rw [hIi]; exact IsLocalization.map_under (P i).primeCompl R K
  · have hs : ∀ j, j ≠ i → ∃ s ∈ P j, s ∉ P i := fun j hj ↦ SetLike.not_le_iff_exists.1 fun h ↦
      hj (hP (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsMaximal.ne_top inferInstance) h))
    choose! s hs using hs
    set t := ∏ j ∈ Finset.univ.erase i, s j ^ L j
    have ht : t ∈ (P i).primeCompl := Submonoid.prod_mem _ fun j hj ↦
      Submonoid.pow_mem _ (hs j (Finset.ne_of_mem_erase hj)).2 _
    have htj : ∀ j, j ≠ i → t ∈ (J j).comap (completedPointMap A (P j)) := fun j hj ↦ by
      apply completed_point_power_contraction A (P j) (L j) (J j) (hJ j)
      obtain ⟨c, hc⟩ : s j ^ L j ∣ t :=
        Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
      rw [hc]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hs j hj).1 _)
    intro x hx
    obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (P i).primeCompl x
    have ha : a ∈ (J i).comap (completedPointMap A (P i)) := by
      rw [hIi, Ideal.mem_comap]
      have : algebraMap A R a = IsLocalization.mk' R a u * algebraMap A R u := by
        rw [IsLocalization.mk'_spec]
      rw [this]
      exact Ideal.mul_mem_right _ _ hx
    have hta : t * a ∈ finiteSupportKernel A ι P J := by
      refine Ideal.mem_iInf.2 fun j => ?_
      by_cases hj : j = i
      · subst hj; exact Ideal.mul_mem_left _ _ ha
      · exact Ideal.mul_mem_right _ _ (htj j hj)
    have : IsLocalization.mk' R a u = algebraMap A R (t * a) * IsLocalization.mk' R (1 : A)
        (u * ⟨t, ht⟩) := by
      rw [← IsLocalization.mk'_eq_mul_mk'_one, ← IsLocalization.mk'_cancel a u ⟨t, ht⟩, mul_comm a
          t]
    change IsLocalization.mk' R a u ∈ _
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hta)

/-- Extending the finitely supported kernel to the completion at `P i` recovers `J i`. -/
theorem finite_support_completion_recovers (A : Type) [CommRing A] [IsNoetherianRing A] (ι : Type)
    [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hP : Function.Injective P) (L : ι → ℕ)
    (J : ∀ i, Ideal (CompletedLocalAt A (P i))) (hJ : ∀ i,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ J i) (i : ι) :
    (finiteSupportKernel A ι P J).map (completedPointMap A (P i)) = J i := by
  have h1 := finite_support_localization_recovers A ι P hP L J hJ i
  have h2 := finite_colength_completion_ideal_descent
    (Localization.AtPrime (P i)) (L i) (J i) (hJ i)
  rw [completedPointMap, ← Ideal.map_map, h1, h2]

/-! The finitely supported results below are proved first for an arbitrary family of prime ideals
carrying a separate maximality hypothesis `hmax`, and then specialised to the
`[∀ i, (P i).IsMaximal]` statements. This keeps the instance arguments of the families
`finiteSupportQuotientMap`, `finiteSupportKernel` syntactically uniform (a local variable rather
than `fun i ↦ Ideal.IsMaximal.isPrime' (P i)`), which makes the kernel check far cheaper. -/

/-- `finite_support_quotient_surjective` for a family of primes that are maximal (the
maximality is a separate hypothesis, keeping the instance arguments uniform). -/
theorem finite_support_quotient_surjective_of_isPrime (A : Type) [CommRing A]
    [IsNoetherianRing A] (ι : Type) [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsPrime]
    (hmax : ∀ i, (P i).IsMaximal) (hP : Function.Injective P) (L : ι → ℕ)
    (J : ∀ i, Ideal (CompletedLocalAt A (P i))) (hJ : ∀ i,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ J i) :
    Function.Surjective (finiteSupportQuotientMap A ι P J) := by
  intro b
  have hrep : ∀ i, ∃ a : A, (Ideal.Quotient.mk (J i)) (completedPointMap A (P i) a) = b i :=
    fun i => @finite_completed_point_quotient_surjective A _ _ (P i) (hmax i) (L i) (J i) (hJ i)
      (b i)
  choose a ha using hrep
  have hcop : Pairwise fun i j => IsCoprime (P i ^ L i) (P j ^ L j) := fun i j hij =>
    @distinct_maximal_powers_coprime A _ (P i) (P j) (hmax i) (hmax j) (hP.ne hij) (L i) (L j)
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hcop a
  refine ⟨r, funext fun i => ?_⟩
  have hmem := @completed_point_power_contraction A _ (P i) (hmax i) (L i) (J i) (hJ i) _ (hr i)
  rw [Ideal.mem_comap, map_sub] at hmem
  change (Ideal.Quotient.mk (J i)) (completedPointMap A (P i) r) = b i
  rw [← ha i]
  exact Ideal.Quotient.eq.mpr hmem

/-- The map from `A` to the product of finite-colength completed local quotients is surjective. -/
theorem finite_support_quotient_surjective (A : Type) [CommRing A] [IsNoetherianRing A] (ι : Type)
    [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hP : Function.Injective P) (L : ι → ℕ)
    (J : ∀ i, Ideal (CompletedLocalAt A (P i))) (hJ : ∀ i,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ J i) :
    Function.Surjective (finiteSupportQuotientMap A ι P J) :=
  finite_support_quotient_surjective_of_isPrime A ι P (fun _ ↦ inferInstance) hP L J hJ

/-- Kernel at level `j` = kernel at level `j + 1` plus `(e)^j`. -/
private theorem finite_support_kernels_compatible (A : Type) [CommRing A] [IsNoetherianRing A]
    (ι : Type) [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsPrime] (hmax : ∀ i, (P i).IsMaximal)
    (hP : Function.Injective P) (e : A)
    (g : ∀ i, CompletedLocalAt A (P i)) (L : ι → ℕ) (hfin : ∀ i,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤
      finiteLocalCurveIdeal A (P i) e (g i) 1) (j : ℕ) :
    finiteSupportKernel A ι P (fun i => finiteLocalCurveIdeal A (P i) e (g i) j) =
        finiteSupportKernel A ι P (fun i => finiteLocalCurveIdeal A (P i) e (g i) (j+1)) ⊔
        (Ideal.span {e})^j := by
  apply le_antisymm
  · intro a ha
    simp only [finiteSupportKernel, Ideal.mem_iInf, Ideal.mem_comap, finiteLocalCurveIdeal,
      Ideal.mem_span_pair] at ha
    choose u v huv using ha
    obtain ⟨c, hc⟩ := finite_support_quotient_surjective_of_isPrime A ι P hmax hP L
      (fun i => finiteLocalCurveIdeal A (P i) e (g i) 1) hfin
      (fun i => Ideal.Quotient.mk _ (v i))
    have hc' : ∀ i, v i - completedPointMap A (P i) c ∈
        finiteLocalCurveIdeal A (P i) e (g i) 1 := fun i ↦
      Ideal.Quotient.eq.mp (congrFun hc i).symm
    have hmem : a - e ^ j * c ∈ finiteSupportKernel A ι P
        (fun i => finiteLocalCurveIdeal A (P i) e (g i) (j+1)) := by
      simp only [finiteSupportKernel, Ideal.mem_iInf, Ideal.mem_comap]
      intro i
      obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp (hc' i)
      simp only [finiteLocalCurveIdeal, Ideal.mem_span_pair]
      refine ⟨u i + (completedPointMap A (P i) e) ^ j * x, y, ?_⟩
      rw [map_sub, map_mul, map_pow, ← huv i]
      have : v i =
          x * g i + y * (completedPointMap A (P i) e) ^ 1 + completedPointMap A (P i) c := by
        rw [hxy]; ring
      rw [this]; ring
    rw [← sub_add_cancel a (e ^ j * c)]
    refine Submodule.add_mem_sup hmem ?_
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · refine sup_le ?_ ?_
    · refine iInf_mono fun i => Ideal.comap_mono ?_
      refine Ideal.span_le.mpr ?_
      rintro x (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [pow_succ]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · rw [Ideal.span_singleton_pow, Ideal.span_le]
      rintro x rfl
      simp only [finiteSupportKernel, SetLike.mem_coe, Ideal.mem_iInf, Ideal.mem_comap]
      intro i
      rw [map_pow]
      exact Ideal.subset_span (by simp)

/-- The level kernels are compatible with the reduction maps `A/(e)^{j+1} → A/(e)^j`. -/
private theorem finite_support_level_kernels_compatible (A : Type) [CommRing A] [IsNoetherianRing A]
    (ι : Type) [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsPrime] (hmax : ∀ i, (P i).IsMaximal)
    (hP : Function.Injective P)
    (e : A) (g : ∀ i, CompletedLocalAt A (P i)) (L : ι → ℕ)
    (hfin : ∀ i, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤
      finiteLocalCurveIdeal A (P i) e (g i) 1) (j : ℕ) :
    (finiteSupportLevelKernel A ι P (fun i => finiteLocalCurveIdeal A (P i) e (g i) (j+1)) e
        (j+1)).map (principalPowerReduction A e j).toRingHom = finiteSupportLevelKernel A ι P
        (fun i => finiteLocalCurveIdeal A (P i) e (g i) j) e j := by
  unfold finiteSupportLevelKernel
  rw [Ideal.map_map,
    finite_support_kernels_compatible A ι P hmax hP e g L hfin j, Ideal.map_sup,
    Ideal.map_quotient_self, sup_bot_eq]
  congr 1

/-- Generators of consecutive level kernels generate the same ideal modulo `(e)^j`. -/
theorem finite_support_generators_compatible (A : Type) [CommRing A] [IsNoetherianRing A] (ι : Type)
    [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hP : Function.Injective P) (e : A)
    (g : ∀ i, CompletedLocalAt A (P i)) (L : ι → ℕ) (hfin : ∀ i,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤
      finiteLocalCurveIdeal A (P i) e (g i) 1) (F : ℕ → A)
    (hF : ∀ j : ℕ, finiteSupportLevelKernel A ι P
    (fun i => finiteLocalCurveIdeal A (P i) e (g i) j) e j = Ideal.span
    {Ideal.Quotient.mk ((Ideal.span {e})^j) (F j)}) (j : ℕ) :
    Ideal.span {Ideal.Quotient.mk ((Ideal.span {e})^j) (F (j+1))} = Ideal.span
        {Ideal.Quotient.mk ((Ideal.span {e})^j) (F j)} := by
  have h := finite_support_level_kernels_compatible A ι P (fun _ ↦ inferInstance) hP e g L hfin j
  rwa [hF (j+1), hF j, Ideal.map_span, Set.image_singleton] at h

private theorem finite_support_quotient_equiv_aux (A : Type) [CommRing A] (ι : Type)
    (P : ι → Ideal A) [∀ i, (P i).IsPrime] (J : ∀ i, Ideal (CompletedLocalAt A (P i)))
    (hs : Function.Surjective (finiteSupportQuotientMap A ι P J)) :
    ∃ E : (A ⧸ finiteSupportKernel A ι P J) ≃+* (∀ i, CompletedLocalAt A (P i) ⧸ J i), ∀ a : A, E
        (Ideal.Quotient.mk (finiteSupportKernel A ι P J) a) = finiteSupportQuotientMap A ι P J a :=
        by
  have hker : RingHom.ker (finiteSupportQuotientMap A ι P J) = finiteSupportKernel A ι P J := by
    ext a
    simp only [RingHom.mem_ker, finiteSupportKernel, finiteSupportQuotientMap, Ideal.mem_iInf,
      Ideal.mem_comap, funext_iff, RingHom.pi_apply, RingHom.comp_apply, Pi.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hs),
    fun a => rfl⟩

/-- Chinese remainder theorem: `A` modulo the finitely supported kernel is the product of the
completed local quotients. -/
theorem finite_support_quotient_equiv (A : Type) [CommRing A] [IsNoetherianRing A] (ι : Type)
    [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hP : Function.Injective P) (L : ι → ℕ)
    (J : ∀ i, Ideal (CompletedLocalAt A (P i))) (hJ : ∀ i,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ J i) :
    ∃ E : (A ⧸ finiteSupportKernel A ι P J) ≃+* (∀ i, CompletedLocalAt A (P i) ⧸ J i), ∀ a : A, E
        (Ideal.Quotient.mk (finiteSupportKernel A ι P J) a) = finiteSupportQuotientMap A ι P J a :=
  finite_support_quotient_equiv_aux A ι P J (finite_support_quotient_surjective A ι P hP L J hJ)

/-- If `e` is a nonzerodivisor modulo `g`, then the annihilator of `e` in `C/(g, e^j)` is
generated by `e^(j−1)`. -/
private theorem finite_curve_exceptional_annihilator (C : Type) [CommRing C] (e g : C)
    (he : Function.Injective (fun a : C ⧸ Ideal.span {g} => Ideal.Quotient.mk (Ideal.span {g}) e *
    a)) (j : ℕ) (hj : 0 < j) (b : C ⧸ Ideal.span {g, e^j})
    (hb : Ideal.Quotient.mk (Ideal.span {g, e^j}) e * b = 0) :
    ∃ c : C ⧸ Ideal.span {g, e^j}, b = (Ideal.Quotient.mk (Ideal.span {g, e^j}) e)^(j-1)*c := by
  obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_pair] at hb
  obtain ⟨a, c0, hac⟩ := hb
  have hej : e ^ j = e * e ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  have key : Ideal.Quotient.mk (Ideal.span {g}) b0
      = Ideal.Quotient.mk (Ideal.span {g}) (e ^ (j - 1) * c0) := by
    apply he
    have hg : Ideal.Quotient.mk (Ideal.span {g}) g = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    simp only [← map_mul]
    rw [← hac, hej]
    simp only [map_add, map_mul, hg, mul_zero, zero_add]
    ring
  refine ⟨Ideal.Quotient.mk _ c0, ?_⟩
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq]
  rw [Ideal.Quotient.eq] at key
  exact Ideal.span_mono (by simp) key

/-- If `e^j = 0` and annihilators of `φ e` lie in `(φ e)^(j−1)`, then
`ker φ ∩ (e) ⊆ (e) · ker φ`. -/
private theorem kernel_saturation_from_top_layer_annihilators (A B : Type) [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ) (e : A) (j : ℕ) (hj : 0 < j) (he : e ^ j = 0)
    (hann : ∀ b : B, φ e * b = 0 → ∃ c : B, b = (φ e)^(j-1)*c) :
    RingHom.ker φ ⊓ Ideal.span {e} ≤ Ideal.span {e} * RingHom.ker φ := by
  intro x hxx
  obtain ⟨hx, hxe⟩ := Ideal.mem_inf.mp hxx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hxe
  rw [RingHom.mem_ker, map_mul, mul_comm] at hx
  obtain ⟨b, hb⟩ := hann (φ a) hx
  obtain ⟨c, rfl⟩ := hφ b
  have hy : a - e^(j-1) * c ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_pow, hb, sub_self]
  have hj' : e * e^(j-1) = e^j := by
    rw [← pow_succ']; congr 1; omega
  have : a * e = e * (a - e^(j-1) * c) := by
    rw [mul_sub, ← mul_assoc, hj', he, zero_mul, sub_zero, mul_comm]
  rw [this]
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self e) hy

private theorem finite_curve_support_kernel_saturated_aux (A : Type) [CommRing A]
    [IsNoetherianRing A] (ι : Type) [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsPrime]
    (hmax : ∀ i, (P i).IsMaximal) (hP : Function.Injective P)
    (e : A) (j : ℕ) (hj : 0 < j) (g : ∀ i, CompletedLocalAt A (P i)) (L : ι → ℕ)
    (hfinite : ∀ i, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤
      finiteLocalCurveIdeal A (P i) e (g i) j)
    (htransverse : ∀ i, Function.Injective (fun a : CompletedLocalAt A (P i) ⧸ Ideal.span {g i}
    => Ideal.Quotient.mk (Ideal.span {g i}) (completedPointMap A (P i) e) * a)) :
    (finiteSupportLevelKernel A ι P (fun i => finiteLocalCurveIdeal A (P i) e (g i) j) e j) ⊓
        Ideal.span {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)} ≤ Ideal.span
        {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)} * (finiteSupportLevelKernel A ι P
        (fun i => finiteLocalCurveIdeal A (P i) e (g i) j) e j) := by
  set J : ∀ i, Ideal (CompletedLocalAt A (P i)) := fun i => finiteLocalCurveIdeal A (P i) e (g i) j
      with hJdef
  set Φ := finiteSupportQuotientMap A ι P J with hΦ
  have hker : RingHom.ker Φ = finiteSupportKernel A ι P J := by
    ext a
    simp only [RingHom.mem_ker, finiteSupportKernel, Ideal.mem_iInf, Ideal.mem_comap, hΦ,
      finiteSupportQuotientMap, funext_iff, RingHom.pi_apply, RingHom.comp_apply, Pi.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  have hle : (Ideal.span {e})^j ≤ RingHom.ker Φ := by
    rw [Ideal.span_singleton_pow, Ideal.span_le]
    rintro x rfl
    rw [SetLike.mem_coe, RingHom.mem_ker]
    funext i
    change Ideal.Quotient.mk (J i) (completedPointMap A (P i) (e ^ j)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, map_pow]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  set φ := Ideal.Quotient.lift ((Ideal.span {e})^j) Φ hle with hφ
  have hsurj : Function.Surjective φ := fun y ↦ by
    obtain ⟨a, rfl⟩ := finite_support_quotient_surjective_of_isPrime A ι P hmax hP L J hfinite y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hkerφ : RingHom.ker φ = finiteSupportLevelKernel A ι P J e j := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, finiteSupportLevelKernel, Ideal.mem_quotient_iff_mem (hker ▸ hle), ← hker,
      RingHom.mem_ker]
    rfl
  have key := kernel_saturation_from_top_layer_annihilators _ _ φ hsurj
    (Ideal.Quotient.mk ((Ideal.span {e})^j) e) j hj (by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _) fun b hb ↦ by
      choose c hc using fun i ↦ finite_curve_exceptional_annihilator _
        (completedPointMap A (P i) e) (g i) (htransverse i) j hj (b i) (congrFun hb i)
      exact ⟨c, funext hc⟩
  rwa [hkerφ] at key

/-- The level kernel of transverse finite curve data is saturated with respect to `e`. -/
theorem finite_curve_support_kernel_saturated (A : Type) [CommRing A] [IsNoetherianRing A]
    (ι : Type) [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hP : Function.Injective P)
    (e : A) (j : ℕ) (hj : 0 < j) (g : ∀ i, CompletedLocalAt A (P i)) (L : ι → ℕ)
    (hfinite : ∀ i, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
    (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤
      finiteLocalCurveIdeal A (P i) e (g i) j)
    (htransverse : ∀ i, Function.Injective (fun a : CompletedLocalAt A (P i) ⧸ Ideal.span {g i}
    => Ideal.Quotient.mk (Ideal.span {g i}) (completedPointMap A (P i) e) * a)) :
    (finiteSupportLevelKernel A ι P (fun i => finiteLocalCurveIdeal A (P i) e (g i) j) e j) ⊓
        Ideal.span {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)} ≤ Ideal.span
        {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)} * (finiteSupportLevelKernel A ι P
        (fun i => finiteLocalCurveIdeal A (P i) e (g i) j) e j) :=
  finite_curve_support_kernel_saturated_aux A ι P (fun _ ↦ inferInstance) hP e j hj g L hfinite
    htransverse

/-! ### Miscellaneous -/

/-- A division-chart decomposition `C ≃ O^n × C` with second factor multiplied by `g`
induces `C/(g) ≃ O^n`. -/
theorem division_equiv_child_coordinates (O C : Type) [CommRing O] [CommRing C] [Algebra O C]
    (n : ℕ) (g : C) (bc : Fin n → C) (E : C ≃ₗ[O] ((Fin n → O) × C))
    (hE : ∀ w, E.symm w = divisionMap g bc w) :
    ∃ EC : (C ⧸ Ideal.span {g}) ≃ₗ[O] (Fin n → O), ∀ w : C, EC
        (Ideal.Quotient.mk (Ideal.span {g}) w) = (E w).1 := by
  have hlift0 : coordinateLift (O := O) bc 0 = 0 := by
    simp [coordinateLift]
  have hker : ∀ v : C, (E (g * v)).1 = 0 := by
    intro v
    have h : E.symm (0, v) = g * v := by rw [hE]; simp [divisionMap, hlift0]
    have : E (g * v) = (0, v) := by rw [← h]; simp
    rw [this]
  let P : Submodule O C := (Ideal.span {g}).restrictScalars O
  have hP : P ≤ LinearMap.ker ((LinearMap.fst O (Fin n → O) C) ∘ₗ E.toLinearMap) := by
    intro w hw
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    simpa [mul_comm] using hker v
  let f : (C ⧸ P) →ₗ[O] (Fin n → O) := P.liftQ _ hP
  have hf : ∀ w : C, f (Submodule.Quotient.mk w) = (E w).1 := fun w => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | _ w =>
      rw [hf] at hq
      have h1 : E.symm ((E w).1, (E w).2) = w := by simp
      rw [hq, hE] at h1
      have : w = g * (E w).2 := by
        have h2 : divisionMap g bc ((0 : Fin n → O), (E w).2) = g * (E w).2 := by simp
            [divisionMap, hlift0]
        rw [← h2]; exact h1.symm
      rw [Submodule.Quotient.mk_eq_zero, this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)
  have hsurj : Function.Surjective f := by
    intro z
    refine ⟨Submodule.Quotient.mk (coordinateLift bc z), ?_⟩
    rw [hf]
    have h : E.symm (z, 0) = coordinateLift bc z := by rw [hE]; simp [divisionMap]
    rw [← h]; simp
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun w => hf w⟩

/-- The length of `R/((f) + (y))` is the contact of `f` and `y`. -/
theorem ideal_contact_generator (R : Type) [CommRing R] (f y : R) :
    Module.length R (R ⧸ (Ideal.span {f} ⊔ Ideal.span {y})) = contact f y := by
  have h : Ideal.span {f} ⊔ Ideal.span {y} = Ideal.span ({f, y} : Set R) := by
    rw [Set.insert_eq, Ideal.span_union]
  rw [contact, h]

end SurfaceBlowup
