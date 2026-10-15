/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.CurveSections
import SurfaceBlowup.Blowup.StrictNormalizer
import SurfaceBlowup.Measure.Normalizer

/-!
# Ideal atlases and curve data on the concrete surface

We build ideal atlases of the crossing and single states of the concrete surface from residue
ideals of the special fiber, and we turn a form `∑ cᵢ t^(d-i) x^i` into two-chart curve data on
the blow-up.

## Main results

* `concrete_crossing_state_atlas_exists`, `concrete_single_state_atlas_exists`.
* `curve_datum_of_parent_function`.

Provenance: `concrete_{crossing,single}_state_atlas_exists`, `curve_datum_of_parent_function`.
-/


namespace SurfaceBlowup

/-- A unit of the special fiber has contact `0` with `t`. -/
private theorem contact_fiberT_eq_zero_of_isUnit (k : Type) [Field k] (a b : ℕ)
    {fb : SpecialFiber k a b} (hu : IsUnit fb) : contact fb (fiberT k a b) = 0 := by
  unfold contact
  rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hu]
  have : Subsingleton (SpecialFiber k a b ⧸ (⊤ : Ideal (SpecialFiber k a b))) :=
    Ideal.Quotient.subsingleton_iff.2 rfl
  exact Module.length_eq_zero

/-! ### Ideal atlases for crossing and single states -/

/-- The crossing state `(a, b, c, h)` of the concrete surface admits an ideal atlas indexed by the
crossing residue ideals of the special fiber. -/
theorem concrete_crossing_state_atlas_exists (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b))
    (hSt : S.t = surfaceT O pi u a b) (hSx : S.x = surfaceX O pi u a b) (hSa : S.a = a)
    (hSb : S.b = b)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b)
    (he : ∀ s : TwoSeries O,
      e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      (surfaceMk O pi u a b s)) = Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a b)
      (residueSeries O s)) (c h : ℕ) (hc : 0 < c) (hh : 0 < h) :
    ∃ A : IdealAtlas O (ConcreteSurface O pi u a b) pi (a*c+b*h)
      (surfaceStateSet O (ConcreteSurface O pi u a b) S (State.crossing a b c h)),
      Nonempty (A.ι ≃ crossingResidueIdeals (IsLocalRing.ResidueField O) a b c h) := by
  set k := IsLocalRing.ResidueField O
  have hcard := crossing_residue_ideal_count k a b c h ha hb hc hh
  have hfin : Finite (crossingResidueIdeals k a b c h) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    have : 1 < Nat.card k := Finite.one_lt_card
    have h2 : Nat.card k - 1 ≠ 0 := by omega
    have h3 : 0 < Nat.card k := by omega
    positivity
  let : Fintype (crossingResidueIdeals k a b c h) := Fintype.ofFinite _
  have key : ∀ I : crossingResidueIdeals k a b c h,
      ∃ ch : IdealChart O (ConcreteSurface O pi u a b) pi (a*c+b*h),
      Ideal.span
          {e ((Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})) ch.f)}
          = I.val := by
    intro I
    obtain ⟨fb, hI, hct, hcx⟩ := I.2
    have hnu : ¬ IsUnit fb := fun hu ↦
      hc.ne' (by exact_mod_cast hct.symm.trans (contact_fiberT_eq_zero_of_isUnit k _ _ hu))
    have hreg := special_fiber_crossing_contact_regular k a b c h ha hb fb hct hcx
    have hlen := crossing_special_fiber_length k a b c h ha hb fb hct hcx
    obtain ⟨ch, hch⟩ := concrete_residue_ideal_chart_exists O pi hpi u a b ha e fb hnu hreg
        (a*c+b*h) hlen
    exact ⟨ch, by rw [hch, hI]⟩
  choose ch hch using key
  have hcov :=
      concrete_crossing_state_eq_union_cells O pi u a b ha hb S hSt hSx hSa hSb e he c h hc
      hh (fun I => (ch I).f) hch
  exact ⟨{ ι := crossingResidueIdeals k a b c h, chart := ch, cover := hcov.1, disjoint := hcov.2 },
        ⟨Equiv.refl _⟩⟩

/-- The single state `(a, c)` of the concrete surface (with `b = 0`) admits an ideal atlas indexed
by the single residue ideals of the special fiber. -/
theorem concrete_single_state_atlas_exists (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a 0)]
    [IsRegularLocalRing (ConcreteSurface O pi u a 0)]
    (S : SurfaceData O (ConcreteSurface O pi u a 0))
    (hSt : S.t = surfaceT O pi u a 0) (hSa : S.a = a) (hSb : S.b = 0)
    (e : (ConcreteSurface O pi u a 0 ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a 0)
    (he : ∀ s : TwoSeries O,
      e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi})
      (surfaceMk O pi u a 0 s)) = Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a 0)
      (residueSeries O s)) (c : ℕ) (hc : 0 < c) :
    ∃ A : IdealAtlas O (ConcreteSurface O pi u a 0) pi (a*c)
      (surfaceStateSet O (ConcreteSurface O pi u a 0) S (State.single a c)),
      Nonempty (A.ι ≃ singleResidueIdeals (IsLocalRing.ResidueField O) a c) := by
  set k := IsLocalRing.ResidueField O
  have hcard := single_residue_ideal_count k a c ha
  have hfin : Finite (singleResidueIdeals k a c) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    have : 0 < Nat.card k := Nat.card_pos
    positivity
  let : Fintype (singleResidueIdeals k a c) := Fintype.ofFinite _
  have key : ∀ I : singleResidueIdeals k a c,
      ∃ ch : IdealChart O (ConcreteSurface O pi u a 0) pi (a*c),
      Ideal.span
          {e ((Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi})) ch.f)}
          = I.val := by
    intro I
    obtain ⟨fb, hI, hct⟩ := I.2
    have hnu : ¬ IsUnit fb := fun hu ↦
      hc.ne' (by exact_mod_cast hct.symm.trans (contact_fiberT_eq_zero_of_isUnit k _ _ hu))
    have hreg := special_fiber_single_contact_regular k a c ha fb hct
    have hlen := single_special_fiber_length k a c ha fb hct
    obtain ⟨ch, hch⟩ := concrete_residue_ideal_chart_exists O pi hpi u a 0 ha e fb hnu hreg
        (a*c) hlen
    exact ⟨ch, by rw [hch, hI]⟩
  choose ch hch using key
  have hcov := concrete_single_state_eq_union_cells O pi u a ha S hSt hSa hSb e he c hc
      (fun I => (ch I).f) hch
  exact ⟨{ ι := singleResidueIdeals k a c, chart := ch, cover := hcov.1, disjoint := hcov.2 },
        ⟨Equiv.refl _⟩⟩

section General
variable {R : Type} [CommRing R] (t x : R)

/-! ### Curve data from a parent function -/

/-- The chart structure map is the algebra map. -/
theorem chartBase_apply_eq_algebraMap (r : R) : chartBase R t x r = algebraMap R
    (BlowupChart R t x) r := rfl

/-- In `R[x/t]`, a form `∑ cᵢ t^(d-i) x^i` factors as `t^d ∑ cᵢ (x/t)^i`. -/
private theorem algebraMap_sum_eq_left (d : ℕ) (c : Fin (d + 1) → R) :
    algebraMap R (BlowupChart R t x) (∑ i : Fin (d+1), c i * t^(d - i.val) * x^i.val) =
      (chartBase R t x t)^d * ∑ i : Fin (d+1), algebraMap R (BlowupChart R t x) (c i) *
        (chartSlope R t x)^i.val := by
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : algebraMap R (BlowupChart R t x) x = chartBase R t x t * chartSlope R t x :=
    (blowup_chart_relation R t x).symm
  have hd : (chartBase R t x t)^d = (chartBase R t x t)^(d - i.val) *
      (chartBase R t x t)^i.val := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp i.isLt)]
  rw [map_mul, map_mul, map_pow, map_pow, hx, hd]; simp only [← chartBase_apply_eq_algebraMap]
  ring

/-- In `R[t/x]`, a form `∑ cᵢ t^(d-i) x^i` factors as `x^d ∑ cᵢ (t/x)^(d-i)`. -/
private theorem algebraMap_sum_eq_right (d : ℕ) (c : Fin (d + 1) → R) :
    algebraMap R (BlowupChart R x t) (∑ i : Fin (d+1), c i * t^(d - i.val) * x^i.val) =
      (chartBase R x t x)^d * ∑ i : Fin (d+1), algebraMap R (BlowupChart R x t) (c i) *
        (chartSlope R x t)^(d - i.val) := by
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ht : algebraMap R (BlowupChart R x t) t = chartBase R x t x * chartSlope R x t :=
    (blowup_chart_relation R x t).symm
  have hd : (chartBase R x t x)^d = (chartBase R x t x)^(d - i.val) *
      (chartBase R x t x)^i.val := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp i.isLt)]
  rw [map_mul, map_mul, map_pow, map_pow, ht, hd]; simp only [← chartBase_apply_eq_algebraMap]
  ring

/-- For a non-zero-divisor `e`, `(e^d g) : e^d = (g)`. -/
theorem span_pow_mul_colon_eq {S : Type} [CommRing S] (e g : S) (d : ℕ)
    (he : Function.Injective (fun y : S => e * y)) :
    (Ideal.span {e^d * g}).colon {e^d} = Ideal.span {g} := by
  have hed : IsLeftRegular (e^d) := IsLeftRegular.pow d (show IsLeftRegular e from he)
  ext y
  rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton,
        Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, hed ?_⟩
    simp only
    rw [mul_comm (e^d) y, hz]; ring
  · rintro ⟨z, rfl⟩
    exact ⟨z, by ring⟩

/-- If `f = t^d F` in the chart and `t` is regular at `P`, the strict transform of `(f)` is
`(F)`. -/
private theorem strictTransformAt_span_eq (P : Ideal (BlowupChart R t x)) [P.IsPrime] (d : ℕ)
    (f : R) (F : BlowupChart R t x)
    (hF : algebraMap R (BlowupChart R t x) f = (chartBase R t x t) ^ d * F)
    (he : Function.Injective (fun y : CompletedLocalAt (BlowupChart R t x) P =>
      completedPointMap (BlowupChart R t x) P (chartBase R t x t) * y)) :
    strictTransformAt R t x P d (Ideal.span {f}) =
      Ideal.span {completedPointMap (BlowupChart R t x) P F} := by
  unfold strictTransformAt
  rw [Ideal.map_span, Set.image_singleton, RingHom.comp_apply, chartBase_apply_eq_algebraMap, hF,
        map_mul, map_pow]
  exact span_pow_mul_colon_eq _ _ d he

/-- Ideals containing `I` are determined by their images in `S ⧸ I`. -/
private theorem quot_ext_eq {S : Type} [CommRing S] (I P1 P2 : Ideal S) (h1 : I ≤ P1) (h2 : I ≤ P2)
    (h : P1.map (Ideal.Quotient.mk I) = P2.map (Ideal.Quotient.mk I)) : P1 = P2 := by
  have k : ∀ P : Ideal S,
      I ≤ P → (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P := by
    intro P hP
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr hP
  rw [← k P1 h1, ← k P2 h2, h]

/-- A maximal ideal avoiding `z` stays maximal in the localization away from `z`. -/
private theorem localization_map_maximal {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (z : A)
    [IsLocalization.Away z S] (P : Ideal A) [hP : P.IsMaximal]
    (hz : z ∉ P) : (P.map (algebraMap A S)).IsMaximal ∧ (P.map (algebraMap A S)).comap
      (algebraMap A S) = P := by
  have hdisj : Disjoint ((Submonoid.powers z : Submonoid A) : Set A) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hz (hP.isPrime.mem_of_pow_mem n hn)
  have hu := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers z) S hP.isPrime hdisj
  refine ⟨?_, hu⟩
  rw [Ideal.isMaximal_def]
  refine ⟨fun htop => hP.ne_top ?_, fun J hJ => ?_⟩
  · rw [← hu, htop]; exact Ideal.comap_top
  · have hlt : P < J.under A := by
      rw [← hu]
      exact (IsLocalization.orderEmbedding (Submonoid.powers z) S).strictMono hJ
    have htop : J.under A = ⊤ := hP.out.2 _ hlt
    rw [← IsLocalization.map_under (Submonoid.powers z) S J, htop, Ideal.map_top]

/-- The reduction of the strict transform `∑ cᵢ (x/t)^i` to the exceptional line is nonzero. -/
private theorem reduction_ne_zero [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial
        (R ⧸ Ideal.span ({t,x} : Set R)))
    (he : ∀ r : R, e (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.span ({t,x} : Set R)) r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X)
    (d : ℕ) (c : Fin (d+1) → R) (hne : ∃ i : Fin (d+1), c i ∉ Ideal.span {t, x}) :
    e (Ideal.Quotient.mk (chartExceptional R t x)
        (∑ i : Fin (d+1), algebraMap R (BlowupChart R t x) (c i) *
        (chartSlope R t x)^i.val)) ≠ 0 := by
  obtain ⟨i0, hi0⟩ := hne
  intro h
  apply hi0
  have h2 := congrArg (fun p => Polynomial.coeff p i0.val) h
  simp only [← chartBase_apply_eq_algebraMap, map_sum, map_mul, map_pow, he, heZ,
        Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h2
  rw [Finset.sum_eq_single i0] at h2
  · simpa [Ideal.Quotient.eq_zero_iff_mem] using h2
  · intro j _ hj
    rw [if_neg]
    intro hv; exact hj (Fin.ext hv.symm)
  · simp

/-- Finite contact transports along `Φ : (A_z)^_Q ≃ A^_P`, `P` the contraction of `Q`. -/
private theorem transport_finite {A : Type} [CommRing A] (z : A) (Q : Ideal (Localization.Away z))
    [Q.IsPrime] (Φ : CompletedLocalAt (Localization.Away z) Q ≃+*
      CompletedLocalAt A (Q.comap (algebraMap A (Localization.Away z))))
    (hΦ : ∀ a, Φ (completedPointMap _ Q (algebraMap A _ a)) = completedPointMap A _ a) (e : A)
    (g : CompletedLocalAt A (Q.comap (algebraMap A _)))
    (h : ∃ L, ((IsLocalRing.maximalIdeal (Localization.AtPrime (Q.comap (algebraMap A _)))).map
      (localCompletionMap _)) ^ L ≤ finiteLocalCurveIdeal A _ e g 1) :
    ∃ L, ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).map (localCompletionMap _)) ^ L ≤
      finiteLocalCurveIdeal _ Q (algebraMap A _ e) (Φ.symm g) 1 := by
  refine exists_pow_le_span_pair_transport _ isUnit_one ?_ ?_ h 1
  · rw [mul_one, RingEquiv.symm_apply_eq]; exact (hΦ e).symm
  rw [Ideal.map_symm, ← Ideal.map_le_iff_le_comap, map_maximalIdeal_localCompletion Q,
    ← map_maximalIdeal_localCompletion_transport _ _ Q Φ hΦ]
  exact Ideal.map_mono (Ideal.map_mono (IsLocalization.map_under (.powers z) _ Q).ge)

/-- A prime of the chart containing `t` contains the exceptional ideal. -/
private theorem chartExceptional_le (P : Ideal (BlowupChart R t x))
    (hP : chartBase R t x t ∈ P) : chartExceptional R t x ≤ P := by
  unfold chartExceptional
  rw [Ideal.span_le, Set.singleton_subset_iff]; exact hP

/-- A curve with nonzero reduction meets the exceptional line in finitely many overlap points. -/
private theorem points_finite [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial
        (R ⧸ Ideal.span ({t,x} : Set R)))
    (he : ∀ r : R, e (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.span ({t,x} : Set R)) r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X)
    (F : BlowupChart R t x) (hF : e (Ideal.Quotient.mk (chartExceptional R t x) F) ≠ 0) :
    Finite {Q : Ideal (BlowupOverlap R t x) // Q.IsMaximal ∧
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ∈ Q ∧
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) F ∈ Q} := by
  classical
  let := Ideal.Quotient.field (Ideal.span ({t,x} : Set R))
  set g := e (Ideal.Quotient.mk (chartExceptional R t x) F) with hg
  have key : ∀ Q : {Q : Ideal (BlowupOverlap R t x) // Q.IsMaximal ∧
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ∈ Q ∧
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) F ∈ Q},
      ∃ φ ∈ UniqueFactorizationMonoid.normalizedFactors g,
        ((Q.1.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))).map
          (Ideal.Quotient.mk (chartExceptional R t x))).map e = Ideal.span {φ} := by
    rintro ⟨Q, hQm, hQt, hQF⟩
    have := hQm
    obtain ⟨hPm, -, hPt⟩ := overlap_exceptional_point_comap_maximal R t x Q hQt
    have := hPm
    obtain ⟨ψ, -, hirr, hmap, -, -⟩ := blowup_chart_exceptional_point_polynomial R t x e he heZ
      (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) hPt
    have hmem : g ∈ Ideal.span {ψ} := by
      rw [← hmap]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hQF)
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨q, hq, hassoc⟩ :=
        UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hF hirr hmem
    refine ⟨q, hq, ?_⟩
    rw [hmap]
    exact Ideal.span_singleton_eq_span_singleton.mpr hassoc
  choose φ hφ hφeq using key
  refine Finite.of_injective (β := (UniqueFactorizationMonoid.normalizedFactors g).toFinset)
    (fun Q => ⟨φ Q, Multiset.mem_toFinset.mpr (hφ Q)⟩) ?_
  intro Q1 Q2 h12
  have h12' : φ Q1 = φ Q2 := congrArg Subtype.val h12
  have hmaps := (hφeq Q1).trans (h12' ▸ (hφeq Q2).symm)
  rw [← Ideal.comap_symm, ← Ideal.comap_symm] at hmaps
  have hmaps' := Ideal.comap_injective_of_surjective _ e.symm.surjective hmaps
  have ht : ∀ Q : {Q : Ideal (BlowupOverlap R t x) // Q.IsMaximal ∧
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ∈ Q ∧
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) F ∈ Q},
      chartExceptional R t x ≤ Q.1.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) :=
    fun Q => chartExceptional_le t x _ Q.2.2.1
  have hc := quot_ext_eq _ _ _ (ht Q1) (ht Q2) hmaps'
  apply Subtype.ext
  rw [← IsLocalization.map_under (Submonoid.powers (chartSlope R t x)) (BlowupOverlap R t x) Q1.1,
    ← IsLocalization.map_under (Submonoid.powers (chartSlope R t x)) (BlowupOverlap R t x) Q2.1]
  exact congrArg _ hc

/-- There is at most one maximal ideal of the chart containing `t`, `x/t` and a given `F`. -/
private theorem zero_points_subsingleton [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial
        (R ⧸ Ideal.span ({t,x} : Set R)))
    (he : ∀ r : R, e (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.span ({t,x} : Set R)) r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X)
    (F : BlowupChart R t x) :
    Subsingleton {P : Ideal (BlowupChart R t x) // P.IsMaximal ∧ chartBase R t x t ∈ P ∧
      chartSlope R t x ∈ P ∧ F ∈ P} := by
  constructor
  have key : ∀ P : {P : Ideal (BlowupChart R t x) // P.IsMaximal ∧ chartBase R t x t ∈ P ∧
      chartSlope R t x ∈ P ∧ F ∈ P},
      (P.1.map (Ideal.Quotient.mk (chartExceptional R t x))).map e = Ideal.span {Polynomial.X} := by
    rintro ⟨P, hPm, hPt, hPZ, -⟩
    have := hPm
    obtain ⟨ψ, -, -, hmap, hZ, -⟩ := blowup_chart_exceptional_point_polynomial R t x e he heZ P hPt
    rw [hmap, hZ.mp hPZ]
  intro P1 P2
  have hmaps := (key P1).trans (key P2).symm
  rw [← Ideal.comap_symm, ← Ideal.comap_symm] at hmaps
  have hmaps' := Ideal.comap_injective_of_surjective _ e.symm.surjective hmaps
  exact Subtype.ext
      (quot_ext_eq _ _ _ (chartExceptional_le t x _ P1.2.2.1)
        (chartExceptional_le t x _ P2.2.2.1) hmaps')

section Overlap
variable (beta : BlowupRestriction R t x)

/-- If `f = t^d F_A` on the `t`-chart and `f = x^d F_B` on the `x`-chart, then `F_A = Z^d F_B`
on the overlap, where `Z = x/t`. -/
private theorem overlap_relation (d : ℕ) (f : R) (FA : BlowupChart R t x) (FB : BlowupChart R x t)
    (hFA : algebraMap R (BlowupChart R t x) f = (chartBase R t x t) ^ d * FA)
    (hFB : algebraMap R (BlowupChart R x t) f = (chartBase R x t x) ^ d * FB)
    (hreg : Function.Injective (fun y : BlowupOverlap R t x =>
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) * y)) :
    algebraMap (BlowupChart R t x) (BlowupOverlap R t x) FA =
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x)) ^ d *
        beta.right FB := by
  apply IsLeftRegular.pow d (show IsLeftRegular _ from hreg)
  have h1 : algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
      (algebraMap R (BlowupChart R t x) f) = beta.right (algebraMap R (BlowupChart R x t) f) := by
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have hx : beta.right (chartBase R x t x) =
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) *
        algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x) := by
    rw [← map_mul, blowup_chart_relation, chartBase_apply_eq_algebraMap,
      chartBase_apply_eq_algebraMap, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  simp only
  rw [hFA, hFB, map_mul, map_mul, map_pow, map_pow, hx] at h1
  rw [h1]; ring

variable {beta} in
/-- At a maximal ideal `Q` of the overlap containing `F_A = Z^d F_B`, the transported local
equation of `F_A` generates the same ideal as `F_B` on the `x`-chart, and `F_B ∈ Q`. -/
private theorem right_common_point_span (d : ℕ) (FA : BlowupChart R t x)
    (FB : BlowupChart R x t)
    (hrel : algebraMap (BlowupChart R t x) (BlowupOverlap R t x) FA =
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x)) ^ d *
        beta.right FB)
    (Q : Ideal (BlowupOverlap R t x)) [hQ : Q.IsMaximal]
    (hQF : algebraMap (BlowupChart R t x) (BlowupOverlap R t x) FA ∈ Q)
    (Ψ : CompletedLocalAt (BlowupOverlap R t x) Q ≃+*
      CompletedLocalAt (BlowupChart R x t) (Q.comap beta.right.toRingHom))
    (hΨ : ∀ b : BlowupChart R x t, Ψ (completedPointMap (BlowupOverlap R t x) Q (beta.right b)) =
      completedPointMap (BlowupChart R x t) (Q.comap beta.right.toRingHom) b) :
    Ideal.span {Ψ (completedPointMap (BlowupOverlap R t x) Q
        (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) FA))} =
      Ideal.span {completedPointMap (BlowupChart R x t) (Q.comap beta.right.toRingHom) FB} ∧
      beta.right FB ∈ Q := by
  have hZu : IsUnit ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
      (chartSlope R t x)) ^ d) := (IsLocalization.Away.algebraMap_isUnit _).pow d
  rw [hrel] at hQF ⊢
  refine ⟨?_, (hQ.isPrime.mem_or_mem hQF).resolve_left
    fun h => hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hZu)⟩
  rw [map_mul, map_mul, hΨ]
  exact Ideal.span_singleton_mul_left_unit ((hZu.map _).map Ψ) _

variable {beta} in
/-- A maximal ideal of the `x`-chart containing `x` and `F_B` but not the slope `t/x` is the
contraction of a maximal ideal of the overlap containing `t` and `F_A = Z^d F_B`. -/
private theorem right_point_of_overlap (d : ℕ) (FA : BlowupChart R t x) (FB : BlowupChart R x t)
    (hrel : algebraMap (BlowupChart R t x) (BlowupOverlap R t x) FA =
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x)) ^ d *
        beta.right FB)
    (P : Ideal (BlowupChart R x t)) [P.IsMaximal] (hPx : chartBase R x t x ∈ P) (hPF : FB ∈ P)
    (hW : chartSlope R x t ∉ P) :
    ∃ Q : Ideal (BlowupOverlap R t x), (Q.IsMaximal ∧
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ∈ Q ∧
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) FA ∈ Q) ∧
      Q.comap beta.right.toRingHom = P := by
  let : Algebra (BlowupChart R x t) (BlowupOverlap R t x) := beta.right.toRingHom.toAlgebra
  have := blowup_overlap_isLocalization_right R t x beta
  obtain ⟨hQm, hQc⟩ := localization_map_maximal (S := BlowupOverlap R t x) (chartSlope R x t) P hW
  have ht : algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) =
      beta.right (chartBase R x t t) := by
    rw [chartBase_apply_eq_algebraMap, chartBase_apply_eq_algebraMap, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  refine ⟨_, ⟨hQm, ?_, ?_⟩, hQc⟩
  · rw [ht, ← blowup_chart_relation]
    exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_right _ _ hPx)
  · rw [hrel]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap _ _) hPF)

end Overlap

end General

section Concrete
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
  (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)

local notation "RR" => ConcreteSurface O pi u a b
local notation "TT" => surfaceT O pi u a b
local notation "XX" => surfaceX O pi u a b
local notation "AA" =>
  BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
local notation "BB" =>
  BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)
local notation "CC" =>
  BlowupOverlap (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)

section Form
variable (d : ℕ) (c : Fin (d + 1) → ConcreteSurface O pi u a b)

/-- The strict transform `F_A = ∑ cᵢ Z^i` of `∑ cᵢ t^(d-i) x^i` on the `t`-chart, `Z = x/t`. -/
private noncomputable abbrev leftForm : AA :=
  ∑ i : Fin (d+1), algebraMap RR AA (c i) * (chartSlope RR TT XX)^i.val

/-- The strict transform `F_B = ∑ cᵢ W^(d-i)` of `∑ cᵢ t^(d-i) x^i` on the `x`-chart,
`W = t/x`. -/
private noncomputable abbrev rightForm : BB :=
  ∑ i : Fin (d+1), algebraMap RR BB (c i) * (chartSlope RR XX TT)^(d - i.val)

local notation "FA" => leftForm O pi u a b d c
local notation "FB" => rightForm O pi u a b d c

/-- The local data of the curve `∑ cᵢ t^(d-i) x^i = 0` on the blow-up: its points on the
exceptional divisor (on the overlap, at `Z = 0` and at infinity), all of them listed, with local
equations `F_A = ∑ cᵢ Z^i` and `F_B = ∑ cᵢ W^(d-i)`. -/
private theorem exists_curve_datum_points (hpi : Irreducible pi) (ha : 0 < a)
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {TT, XX}) (beta : BlowupRestriction RR TT XX) :
    ∃ D : TwoChartCurveData RR TT XX beta,
      (∀ i, D.g i = completedPointMap CC (D.Q i) (algebraMap AA CC FA) ∧
        algebraMap AA CC FA ∈ D.Q i) ∧
      (∀ Q : Ideal CC, Q.IsMaximal → algebraMap AA CC (chartBase RR TT XX TT) ∈ Q →
        algebraMap AA CC FA ∈ Q → ∃ i, D.Q i = Q) ∧
      (∀ k, D.g0 k = completedPointMap AA (D.P0 k) FA ∧ FA ∈ D.P0 k) ∧
      (∀ P : Ideal AA, P.IsMaximal → chartBase RR TT XX TT ∈ P → chartSlope RR TT XX ∈ P →
        FA ∈ P → ∃ k, D.P0 k = P) ∧
      (∀ l, D.ginf l = completedPointMap BB (D.Pinf l) FB ∧ FB ∈ D.Pinf l) ∧
      ∀ P : Ideal BB, P.IsMaximal → chartBase RR XX TT XX ∈ P → chartSlope RR XX TT ∈ P →
        FB ∈ P → ∃ l, D.Pinf l = P := by
  have : (Ideal.span ({TT, XX} : Set RR)).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  have : IsNoetherianRing AA := blowupChart_concrete_isNoetherianRing O pi u a b TT XX
  have : IsNoetherianRing BB := blowupChart_concrete_isNoetherianRing O pi u a b XX TT
  obtain ⟨e, he, heZ⟩ := exceptional_line_equiv_chart_exceptional RR TT XX
  have hgne := reduction_ne_zero TT XX e he heZ d c hne
  -- transversality and finiteness at the points of the `t`-chart on the exceptional divisor
  have hL : ∀ (P : Ideal AA) [P.IsMaximal], chartBase RR TT XX TT ∈ P → _ := fun P _ hP =>
    concrete_strict_transform_transverse_finite O pi hpi u a b ha FA
      (fun h => hgne (by rw [h, map_zero])) P hP
  -- common points on the overlap
  let ι := {Q : Ideal CC // Q.IsMaximal ∧
      algebraMap AA CC (chartBase RR TT XX TT) ∈ Q ∧ algebraMap AA CC FA ∈ Q}
  have hιmax : ∀ i : ι, i.1.IsMaximal := fun i => i.2.1
  have hιP (i : ι) := overlap_exceptional_point_comap_maximal RR TT XX i.1 i.2.2.1
  choose Φ hΦ using fun i : ι => completed_point_transport_left RR TT XX i.1
  choose Ψ hΨ using fun i : ι => completed_point_transport_right RR TT XX beta i.1
  have heT (i : ι) : (Φ i).symm (completedPointMap AA _ (chartBase RR TT XX TT)) * 1 =
      completedPointMap CC i.1 (overlapException RR TT XX) := by
    rw [mul_one, RingEquiv.symm_apply_eq]; exact (hΦ i _).symm
  -- points at `Z = 0` and at infinity
  let ι0 := {P : Ideal AA // P.IsMaximal ∧ chartBase RR TT XX TT ∈ P ∧ chartSlope RR TT XX ∈ P ∧
    FA ∈ P}
  have : Subsingleton ι0 := zero_points_subsingleton TT XX e he heZ FA
  have hι0max : ∀ k : ι0, k.1.IsMaximal := fun k => k.2.1
  let ιinf :=
    {P : Ideal BB // P.IsMaximal ∧ chartBase RR XX TT XX ∈ P ∧ chartSlope RR XX TT ∈ P ∧ FB ∈ P}
  have hιinfmax : ∀ l : ιinf, l.1.IsMaximal := fun l => l.2.1
  have hinf (l : ιinf) :=
    concrete_infinity_point_completion O pi hpi u a b ha l.1 l.2.2.1 l.2.2.2.1
  have : Subsingleton ιinf := ⟨fun l1 l2 => Subtype.ext ((hinf l1).1.trans (hinf l2).1.symm)⟩
  have hinf' (l : ιinf) :=
    concrete_infinity_strict_transform_transverse_finite O pi hpi u a b ha d c hne l.1 l.2.2.1
      l.2.2.2.1
  let D : TwoChartCurveData RR TT XX beta :=
    { ι := ι
      fin := points_finite TT XX e he heZ FA hgne
      Q := fun i => i.1
      inj := Subtype.val_injective
      onE := fun i => i.2.2.1
      g := fun i => (Φ i).symm (completedPointMap AA _ FA)
      transverse := fun i =>
        have := (hιP i).1
        mul_injective_quotient_transport _ isUnit_one (heT i) (hL _ (hιP i).2.2).1
      finite := fun i =>
        have := (hιP i).1
        transport_finite _ i.1 (Φ i) (hΦ i) _ _ (hL _ (hιP i).2.2).2.2
      leftIso := Φ
      leftIso_compat := hΦ
      rightIso := Ψ
      rightIso_compat := hΨ
      ι0 := ι0
      fin0 := Finite.of_subsingleton
      P0 := fun k => k.1
      maximal0 := fun k => k.2.1
      inj0 := Subtype.val_injective
      slope0 := fun k => k.2.2.2.1
      onE0 := fun k => k.2.2.1
      g0 := fun k => completedPointMap AA k.1 FA
      transverse0 := fun k => (hL k.1 k.2.2.1).1
      finite0 := fun k => (hL k.1 k.2.2.1).2.2
      ιinf := ιinf
      fininf := Finite.of_subsingleton
      Pinf := fun l => l.1
      maximalinf := fun l => l.2.1
      injinf := Subtype.val_injective
      slopeinf := fun l => l.2.2.2.1
      onEinf := fun l => l.2.2.1
      ginf := fun l => completedPointMap BB l.1 FB
      transverseinf := fun l => (hinf' l).1
      finiteinf := fun l => (hinf' l).2.2 }
  refine ⟨D, fun i => ⟨(Φ i).symm_apply_eq.2 (hΦ i FA).symm, i.2.2.2⟩,
    fun Q hQm hQt hQF => ⟨⟨Q, hQm, hQt, hQF⟩, rfl⟩,
    fun k => ⟨rfl, k.2.2.2.2⟩, fun P hPm hPt hPZ hPF => ⟨⟨P, hPm, hPt, hPZ, hPF⟩, rfl⟩,
    fun l => ⟨rfl, l.2.2.2.2⟩, fun P hPm hPx hPW hPF => ⟨⟨P, hPm, hPx, hPW, hPF⟩, rfl⟩⟩

/-- `curve_datum_of_parent_function` in the section notation, with the strict transforms
`F_A`, `F_B` of the form on the two charts. -/
private theorem exists_curve_datum_of_sum (hpi : Irreducible pi) (ha : 0 < a) (f : RR)
    (hc : f = ∑ i : Fin (d + 1), c i * TT ^ (d - i.val) * XX ^ i.val)
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {TT, XX}) (beta : BlowupRestriction (RR) TT XX) :
    ∃ D : TwoChartCurveData (RR) TT XX beta,
      (∀ s : D.ι ⊕ D.ι0, leftData D s = completedPointMap AA (leftPoint D s) FA ∧
        FA ∈ leftPoint D s) ∧
      (∀ P : Ideal AA, P.IsMaximal → (chartBase (RR) TT XX) TT ∈ P → FA ∈ P →
        ∃ s : D.ι ⊕ D.ι0, leftPoint D s = P) ∧
      (∀ s : D.ι ⊕ D.ιinf, Ideal.span {rightData D s} =
        Ideal.span {completedPointMap BB (rightPoint D s) FB} ∧ FB ∈ rightPoint D s) ∧
      (∀ P : Ideal BB, P.IsMaximal → (chartBase (RR) XX TT) XX ∈ P → FB ∈ P →
        ∃ s : D.ι ⊕ D.ιinf, rightPoint D s = P) ∧
      (∀ s : D.ι ⊕ D.ι0,
        strictTransformAt (RR) TT XX (leftPoint D s) d (Ideal.span {f}) = Ideal.span {leftData D s})
      ∧ ∀ s : D.ι ⊕ D.ιinf,
        strictTransformAt (RR) XX TT (rightPoint D s) d (Ideal.span {f}) =
          Ideal.span {rightData D s} := by
  -- Take the curve datum of `exists_curve_datum_points`; on each chart `f = t^d F_A = x^d F_B`
  -- with `t` (resp. `x`) regular, so the strict transforms are `(F_A)` and `(F_B)`.
  have : (Ideal.span ({TT, XX} : Set RR)).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  have hFA : algebraMap RR AA f = (chartBase RR TT XX TT)^d * FA := by
    rw [hc]; exact algebraMap_sum_eq_left _ _ d c
  have hFB : algebraMap RR BB f = (chartBase RR XX TT XX)^d * FB := by
    rw [hc]; exact algebraMap_sum_eq_right _ _ d c
  have hrel := overlap_relation TT XX beta d f _ _ hFA hFB
    (nonzerodivisor_survives_localization AA (chartBase RR TT XX TT) (chartSlope RR TT XX)
      (blowup_exceptional_parameter_regular RR TT XX
        (concrete_surface_regular_pair_tx O pi hpi.ne_zero u a b ha)))
  obtain ⟨D, hg, hQ, hg0, hP0, hginf, hPinf⟩ :=
    exists_curve_datum_points O pi u a b d c hpi ha hne beta
  have hleftP : ∀ s : D.ι ⊕ D.ι0,
      (leftPoint D s).IsMaximal ∧ chartBase RR TT XX TT ∈ leftPoint D s := by
    rintro (i | k)
    · obtain ⟨h1, -, h2⟩ := overlap_exceptional_point_comap_maximal RR TT XX (D.Q i) (D.onE i)
      exact ⟨h1, h2⟩
    · exact ⟨D.maximal0 k, D.onE0 k⟩
  have c1 : ∀ s : D.ι ⊕ D.ι0, leftData D s = completedPointMap AA (leftPoint D s) FA ∧
      FA ∈ leftPoint D s := by
    rintro (i | k)
    · exact ⟨(congrArg (D.leftIso i) (hg i).1).trans (D.leftIso_compat i _), (hg i).2⟩
    · exact hg0 k
  have c5 : ∀ s : D.ι ⊕ D.ι0, strictTransformAt RR TT XX (leftPoint D s) d (Ideal.span {f}) =
      Ideal.span {leftData D s} := by
    intro s
    have := (hleftP s).1
    rw [(c1 s).1]
    exact strictTransformAt_span_eq TT XX (leftPoint D s) d f FA hFA
      (concrete_left_point_exceptional_regular O pi hpi u a b ha (leftPoint D s) (hleftP s).2)
  refine ⟨D, c1, ?_, ?_, ?_, c5, ?_⟩
  · intro P hPm hPt hPF
    by_cases hZ : chartSlope RR TT XX ∈ P
    · obtain ⟨k, hk⟩ := hP0 P hPm hPt hZ hPF
      exact ⟨Sum.inr k, hk⟩
    · obtain ⟨hQm, hQc⟩ := localization_map_maximal (S := CC) (chartSlope RR TT XX) P hZ
      obtain ⟨i, hi⟩ := hQ _ hQm (Ideal.mem_map_of_mem _ hPt) (Ideal.mem_map_of_mem _ hPF)
      exact ⟨Sum.inl i, (congrArg (Ideal.comap _) hi).trans hQc⟩
  · rintro (i | l)
    · change Ideal.span {D.rightIso i (D.g i)} = _ ∧ _
      rw [(hg i).1]
      exact right_common_point_span TT XX d _ _ hrel (D.Q i) (hg i).2 _ (D.rightIso_compat i)
    · exact ⟨congrArg (fun y => Ideal.span {y}) (hginf l).1, (hginf l).2⟩
  · intro P hPm hPx hPF
    by_cases hW : chartSlope RR XX TT ∈ P
    · obtain ⟨l, hl⟩ := hPinf P hPm hPx hW hPF
      exact ⟨Sum.inr l, hl⟩
    · obtain ⟨Q, ⟨hQm, hQt, hQF⟩, hQc⟩ := right_point_of_overlap TT XX d _ _ hrel P hPx hPF hW
      obtain ⟨i, rfl⟩ := hQ Q hQm hQt hQF
      exact ⟨Sum.inl i, hQc⟩
  · rintro (i | l)
    · rw [← strict_transform_common_point_transport RR TT XX beta D i d (Ideal.span {f}),
        c5 (Sum.inl i)]
      refine (Ideal.map_span _ _).trans ?_
      rw [Set.image_singleton]
      exact congrArg (fun y => Ideal.span {D.rightIso i y}) ((D.leftIso i).symm_apply_apply _)
    · change _ = Ideal.span {D.ginf l}
      rw [(hginf l).1]
      exact strictTransformAt_span_eq XX TT (D.Pinf l) d f FB hFB
        (concrete_infinity_point_completion O pi hpi u a b ha (D.Pinf l) (D.onEinf l)
          (D.slopeinf l)).2.2.2.2

end Form

end Concrete

/-- A form `f = ∑ cᵢ t^(d-i) x^i` on the concrete surface with some `cᵢ` a unit yields two-chart
curve data: its strict transforms on the two blow-up charts, located at finitely many points of
the exceptional divisor. -/
theorem curve_datum_of_parent_function (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (d : ℕ) (f : ConcreteSurface O pi u a b)
    (c : Fin (d + 1) → ConcreteSurface O pi u a b)
    (hc : f = ∑ i : Fin (d + 1),
      c i * (surfaceT O pi u a b) ^ (d - i.val) * (surfaceX O pi u a b) ^ i.val)
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {(surfaceT O pi u a b), (surfaceX O pi u a b)})
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) :
    ∃ D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) beta,
      (∀ s : D.ι ⊕ D.ι0,
        leftData D s = completedPointMap
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (leftPoint D s)
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b))^i.val) ∧
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b))^i.val) ∈ leftPoint D s) ∧
      (∀ P : Ideal
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)),
        P.IsMaximal →
        (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (surfaceT O pi u a b) ∈ P →
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b))^i.val) ∈ P → ∃ s : D.ι ⊕ D.ι0, leftPoint D s = P) ∧
      (∀ s : D.ι ⊕ D.ιinf,
        Ideal.span {rightData D s} = Ideal.span
        {completedPointMap
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
        (rightPoint D s)
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
        (surfaceT O pi u a b))^(d - i.val))} ∧
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
        (surfaceT O pi u a b))^(d - i.val)) ∈ rightPoint D s) ∧
      (∀ P : Ideal
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)),
        P.IsMaximal →
        (chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
        (surfaceX O pi u a b) ∈ P →
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
        (surfaceT O pi u a b))^(d - i.val)) ∈ P → ∃ s : D.ι ⊕ D.ιinf, rightPoint D s = P) ∧
      (∀ s : D.ι ⊕ D.ι0,
        strictTransformAt (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
        (leftPoint D s) d (Ideal.span {f}) = Ideal.span {leftData D s}) ∧ ∀ s : D.ι ⊕ D.ιinf,
      strictTransformAt (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)
      (rightPoint D s) d (Ideal.span {f}) = Ideal.span {rightData D s} := by
  exact exists_curve_datum_of_sum O pi u a b d c hpi ha f hc hne beta

end SurfaceBlowup
