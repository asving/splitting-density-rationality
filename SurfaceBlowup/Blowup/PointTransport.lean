/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Surfaces.ConcretePoints

/-!
# Transport of points between blow-up charts

Comparison of the two affine charts of a point blow-up through their overlap: the gluing map and
its localization property, transport of maximal ideals, residue fields, local rings and their
completions between the charts and the overlap, together with the localization and
completion algebra this needs and the computation of strict transforms and their intersection
multiplicities on the concrete surface.

## Main results

* `SurfaceBlowup.blowup_overlap_isLocalization_right`: the overlap is a localization of either
  chart.
* `SurfaceBlowup.overlap_point_residue_field_equiv`,
  `SurfaceBlowup.completed_point_transport_left`, `SurfaceBlowup.completed_point_transport_right`:
  points on the exceptional divisor look the same from both charts.
* `SurfaceBlowup.concrete_strict_transform_generators`,
  `SurfaceBlowup.concrete_infinity_strict_transform_multiplicity`: strict transforms on the
  concrete surface.

Provenance: `Thm_SurfaceBlowupV2_` nodes `child_ideal_generator_transverse_finite`,
`concrete_infinity_strict_transform_multiplicity`, `linear_composition_index`,
`local_completion_transport`, `localization_map_{comap_comp,finite_iInf}`,
`finite_support_kernel_localize`, `localization_principal_quotient_commute`, `monomial_span_pow`,
`fixed_tangent_cell_generator_coefficients`, `negative_laurent_twist_has_no_kernel`,
`nonzerodivisor_survives_localization`, `normalization_linear_part_{is_quotient_matrix,
cokernel_length_eq}`, `opposite_untruncated_chart_restriction`,
`actual_blowup_restriction_exists`, `blowup_overlap_{symmetry,isLocalization_right}`,
`overlap_exceptional_point_comap_maximal{,_right}`, `overlap_exceptional_quotient_domain`,
`overlap_point_residue_field_equiv`, `overlap_prime_localization_{left,right}`,
`completed_point_transport_{left,right}`, `pairwise_distinct_irreducible_pow_iInf`,
`polynomial_ideal_of_irreducible_pow_le`, `polynomial_quotient_irreducible_pow_length`,
`principal_ideal_image`, `concrete_strict_transform_generators`,
`principal_ideal_unit_invariance`.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

private theorem transverse_of_concreteSurface_equiv (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (pi' : O') (hpi' : Irreducible pi') (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a')
    (ψ : S ≃+* ConcreteSurface O' pi' u' a' b') (e g : S) (he : ψ e = surfaceT O' pi' u' a' b')
    (n : ℕ) (hlen : Module.length S (S ⧸ (Ideal.span {g} ⊔ Ideal.span {e})) = (n : ℕ∞))
    (hreg : Function.Injective (fun y : S ↦ e * y)) :
    Function.Injective (fun w : S ⧸ Ideal.span {g} ↦ Ideal.Quotient.mk (Ideal.span {g}) e * w) ∧
    Function.Injective (fun w : S ⧸ Ideal.span {e} ↦ Ideal.Quotient.mk (Ideal.span {e}) g * w) ∧
    ∃ L : ℕ, (IsLocalRing.maximalIdeal S)^L ≤ Ideal.span {g, e} := by
  obtain ⟨q, -⟩ := concrete_surface_quotient_T_equiv O' pi' hpi' u' a' b' ha'
  have hE : ψ.symm (surfaceT O' pi' u' a' b') = e := by rw [← he]; simp
  obtain ⟨h1, -⟩ :=
    concrete_surface_equiv_curve_length_and_regular S O' pi' u' a' b' ψ q g
  rw [hE, Ideal.span_insert, hlen] at h1
  have hne : q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (ψ g)) ≠ 0 := by
    intro h0
    rw [h0, PowerSeries.order_zero] at h1
    exact absurd h1 (by simp)
  let Q : (S ⧸ Ideal.span {e}) ≃+* PowerSeries (IsLocalRing.ResidueField O') :=
    (Ideal.quotientEquiv (Ideal.span {e}) (Ideal.span {surfaceT O' pi' u' a' b'}) ψ
      (by rw [Ideal.map_span, Set.image_singleton]; simp [he])).trans q
  have hQ : Q (Ideal.Quotient.mk (Ideal.span {e}) g) =
      q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (ψ g)) := by
    simp [Q]
  exact transverse_of_reduction_ne_zero S e g hreg _ Q (by rw [hQ]; exact hne)

/-- Order of the reflected power series. -/
private theorem order_reflected_sum {k K : Type} [Field k] [Field K] (κ : k →+* K) (d : ℕ)
    (r : Fin (d + 1) → k) (hne : ∃ i, r i ≠ 0) :
    (∑ i : Fin (d+1), PowerSeries.C (κ (r i)) * PowerSeries.X ^ (d - i.val) : PowerSeries K).order =
    ((d - (∑ i : Fin (d+1), Polynomial.C (r i) * Polynomial.X^i.val :
      Polynomial k).natDegree : ℕ) : ℕ∞) := by
  set H : Polynomial k := ∑ i : Fin (d+1), Polynomial.C (r i) * Polynomial.X^i.val with hH
  have hcoeff : ∀ i : Fin (d+1), H.coeff i.val = r i := by
    intro i
    rw [hH, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro h; exact hj (Fin.ext h.symm)
    · simp
  have hdeg : H.natDegree ≤ d := by
    rw [hH]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ ↦ ?_)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have hH0 : H ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro h; apply hi; rw [← hcoeff i, h, Polynomial.coeff_zero]
  have hF : ∀ m, m ≤ d → PowerSeries.coeff m (∑ i : Fin (d+1), PowerSeries.C (κ (r i)) *
      PowerSeries.X ^ (d - i.val) : PowerSeries K) = κ (H.coeff (d - m)) := by
    intro m hm
    have := hcoeff ⟨d - m, by omega⟩
    simp only at this
    rw [this, map_sum, Finset.sum_eq_single (⟨d - m, by omega⟩ : Fin (d+1))]
    · rw [PowerSeries.coeff_C_mul_X_pow, if_pos (by simp; omega)]
    · intro j _ hj
      rw [PowerSeries.coeff_C_mul_X_pow, if_neg]
      intro h; apply hj; ext; simp; omega
    · simp
  rw [PowerSeries.order_eq_nat]
  refine ⟨?_, fun m hm ↦ ?_⟩
  · rw [hF _ (by omega), show d - (d - H.natDegree) = H.natDegree by omega,
      Polynomial.coeff_natDegree]
    simpa using hH0
  · rw [hF _ (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

/-- For linear maps `f : M → N` and injective `g : N → P`, the index of the range of `g ∘ f` is the
product of the indices of the ranges of `f` and `g`. -/
theorem linear_composition_index (R M N P : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hg : Function.Injective g) :
    (g.comp f).range.toAddSubgroup.index = f.range.toAddSubgroup.index * g.range.toAddSubgroup.index
    := by
  have h : (g.comp f).range.toAddSubgroup = f.range.toAddSubgroup.map g.toAddMonoidHom := by
    ext y
    simp [LinearMap.mem_range]
  have h2 : g.range.toAddSubgroup = g.toAddMonoidHom.range := by
    ext y
    simp [LinearMap.mem_range]
  rw [h, h2]
  exact AddSubgroup.index_map_of_injective _ (f := g.toAddMonoidHom) hg

open AdicCompletion in
private theorem local_completion_transport_factorPow_evalₐ {R : Type} [CommRing R] (I : Ideal R)
    {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I R x
  simp only [evalₐ_mk]
  have := AdicCauchySequence.mk_eq_mk h s
  rw [Submodule.Quotient.eq] at this
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq]
  simpa using this

open AdicCompletion in
private theorem local_completion_transport_lift {A B : Type} [CommRing A] [CommRing B] (I : Ideal A)
    (J : Ideal B) (ψ : A ≃+* B) (h : ∀ n : ℕ, J ^ n = (I ^ n).map ψ) :
    ∃ F : AdicCompletion I A →+* AdicCompletion J B, ∀ (n : ℕ) (x : AdicCompletion I A),
      evalₐ J n (F x) = Ideal.quotientEquiv (I ^ n) (J ^ n) ψ (h n) (evalₐ I n x) := by
  refine ⟨liftRingHom J (fun n ↦ (Ideal.quotientEquiv (I ^ n) (J ^ n) ψ (h n)).toRingHom.comp
    (evalₐ I n).toRingHom) ?_, ?_⟩
  · intro m n hle
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← local_completion_transport_factorPow_evalₐ I hle x]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    rw [← ha]
    rfl
  · intro n x
    rw [evalₐ_liftRingHom]
    rfl

/-- A ring isomorphism of Noetherian local rings induces an isomorphism of their maximal-adic
completions compatible with the completion maps. -/
private theorem local_completion_transport (S S' : Type) [CommRing S] [CommRing S'] [IsLocalRing S]
    [IsLocalRing S'] [IsNoetherianRing S] [IsNoetherianRing S'] (φ : S ≃+* S') :
    ∃ Φ : LocalCompletion S ≃+* LocalCompletion S', ∀ s : S, Φ
    (localCompletionMap S s) = localCompletionMap S' (φ s) := by
  have hm : (IsLocalRing.maximalIdeal S).map φ = IsLocalRing.maximalIdeal S' := by
    rw [← Ideal.comap_symm]
    exact IsLocalRing.maximalIdeal_comap (φ.symm : S' →+* S)
  have hm' : (IsLocalRing.maximalIdeal S').map φ.symm = IsLocalRing.maximalIdeal S := by
    rw [Ideal.map_symm]
    exact IsLocalRing.maximalIdeal_comap (φ : S →+* S')
  obtain ⟨F, hF⟩ := local_completion_transport_lift (IsLocalRing.maximalIdeal S)
    (IsLocalRing.maximalIdeal S') φ (fun n ↦ by rw [Ideal.map_pow, hm])
  obtain ⟨G, hG⟩ := local_completion_transport_lift (IsLocalRing.maximalIdeal S')
    (IsLocalRing.maximalIdeal S) φ.symm (fun n ↦ by rw [Ideal.map_pow, hm'])
  refine ⟨RingEquiv.ofRingHom F G ?_ ?_, ?_⟩
  · ext1 x
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    simp only [RingHom.comp_apply, RingHom.id_apply, hF, hG]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ n x)
    rw [← ha]
    exact congrArg (Ideal.Quotient.mk _) (RingEquiv.apply_symm_apply _ a)
  · ext1 x
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    simp only [RingHom.comp_apply, RingHom.id_apply, hF, hG]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ n x)
    rw [← ha]
    exact congrArg (Ideal.Quotient.mk _) (RingEquiv.symm_apply_apply _ a)
  · intro s
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    simp only [RingEquiv.ofRingHom_apply, hF, localCompletionMap]
    rw [AlgHom.commutes, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.algebraMap_eq]
    rfl

/-- Extending the contraction of `J` along `S → T` composed with the localization `A → S` recovers
the contraction of `J` to `S`. -/
private theorem localization_map_comap_comp (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] (T : Type) [CommRing T] (ψ : S →+* T) (J : Ideal T) :
    (J.comap (ψ.comp (algebraMap A S))).map (algebraMap A S) = J.comap ψ := by
  rw [← Ideal.comap_comap]
  exact IsLocalization.map_under M S (J.comap ψ)

/-- Extension of ideals along a localization commutes with finite infima. -/
private theorem localization_map_finite_iInf (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] (ι : Type) [Finite ι] (I : ι → Ideal A) :
    (⨅ i, I i).map (algebraMap A S) = ⨅ i, (I i).map (algebraMap A S) := by
  classical
  have := Fintype.ofFinite ι
  simp only [← Finset.inf_univ_eq_iInf]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp only [Finset.inf_empty]; exact Ideal.map_top _
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.inf_insert, IsLocalization.map_inf M, ih]

/-- Localizing a finite-support kernel: the extension to `S` of the finite-support kernel is the
infimum, over the points `i` that survive in `S`, of the transported completed ideals, the other
points collapsing to the unit ideal. -/
theorem finite_support_kernel_localize (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] (ι : Type) [Finite ι] (P : ι → Ideal A)
    [∀ i, (P i).IsPrime] (J : ∀ i, Ideal (CompletedLocalAt A (P i))) (σ : ι → Prop)
    (T : ι → Type) [∀ i, CommRing (T i)] (ψ : ∀ i, S →+* T i)
    (Φ : ∀ i, CompletedLocalAt A (P i) ≃+* T i)
    (hΦ : ∀ i, σ i → ∀ a : A, Φ i (completedPointMap A (P i) a) = ψ i (algebraMap A S a))
    (hcollapse : ∀ i, ¬ σ i → ∃ m ∈ M, m ∈ P i) (L : ι → ℕ)
    (hL : ∀ i, (P i)^(L i) ≤ (J i).comap (completedPointMap A (P i))) :
    (finiteSupportKernel A ι P J).map (algebraMap A S) = ⨅ i : {i // σ i},
    ((J i.val).map (Φ i.val)).comap (ψ i.val) := by
  have key : ∀ i, σ i → ((J i).comap (completedPointMap A (P i))).map (algebraMap A S)
      = ((J i).map (Φ i)).comap (ψ i) := by
    intro i hi
    have hc : (J i).comap (completedPointMap A (P i))
        = ((J i).map (Φ i)).comap ((ψ i).comp (algebraMap A S)) := by
      ext x
      rw [← Ideal.comap_symm, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap,
        RingHom.comp_apply, ← hΦ i hi]
      simp
    rw [hc]
    exact localization_map_comap_comp A S M (T i) (ψ i) _
  have top : ∀ i, ¬ σ i → ((J i).comap (completedPointMap A (P i))).map (algebraMap A S) = ⊤ := by
    intro i hi
    obtain ⟨m, hm, hmP⟩ := hcollapse i hi
    exact contracted_ideal_map_localization_top A S M (P i) _ (L i) (hL i) m hm hmP
  unfold finiteSupportKernel
  rw [localization_map_finite_iInf A S M ι]
  apply le_antisymm
  · exact le_iInf fun i ↦ iInf_le_of_le i.val (by rw [key i.val i.property])
  · refine le_iInf fun i ↦ ?_
    by_cases h : σ i
    · exact iInf_le_of_le ⟨i, h⟩ (by rw [key i h])
    · rw [top i h]; exact le_top

/-- Localizing at `z` commutes with taking the principal power quotient `A ⧸ (e)^j`. -/
theorem localization_principal_quotient_commute (A : Type) [CommRing A] (e z : A) (j : ℕ) :
    ∃ L : PrincipalPowerQuotient (Localization.Away z)
    (algebraMap A (Localization.Away z) e) j ≃+* Localization.Away
    (Ideal.Quotient.mk ((Ideal.span {e})^j) z), ∀ a : A, L
    (Ideal.Quotient.mk ((Ideal.span {algebraMap A (Localization.Away z) e})^j)
      (algebraMap A (Localization.Away z) a)) = algebraMap (PrincipalPowerQuotient A e j)
    (Localization.Away (Ideal.Quotient.mk ((Ideal.span {e})^j) z))
    (Ideal.Quotient.mk ((Ideal.span {e})^j) a) := by
  let φ0 : A →+* Localization.Away (Ideal.Quotient.mk ((Ideal.span {e})^j) z) :=
    (algebraMap (A ⧸ (Ideal.span {e})^j) _).comp (Ideal.Quotient.mk ((Ideal.span {e})^j))
  have hφ0 : IsUnit (φ0 z) :=
    IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk ((Ideal.span {e})^j) z)
  let φ : Localization.Away z →+* Localization.Away (Ideal.Quotient.mk ((Ideal.span {e})^j) z) :=
    IsLocalization.Away.lift z hφ0
  have hφ : ∀ a : A, φ (algebraMap A _ a) = φ0 a := fun a ↦ IsLocalization.Away.lift_eq z hφ0 a
  have hker : ∀ x ∈ (Ideal.span {algebraMap A (Localization.Away z) e})^j, φ x = 0 := by
    intro x hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    have : (Ideal.Quotient.mk ((Ideal.span {e})^j) e) ^ j = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    rw [map_mul, map_pow, hφ]
    simp only [φ0, RingHom.comp_apply]
    rw [← map_pow, this, map_zero, zero_mul]
  let f := Ideal.Quotient.lift _ φ hker
  have hf : ∀ a : A, f (Ideal.Quotient.mk _ (algebraMap A _ a)) =
      algebraMap (A ⧸ (Ideal.span {e})^j) _ (Ideal.Quotient.mk _ a) := hφ
  let ψ0 : A →+* Localization.Away z ⧸ (Ideal.span {algebraMap A (Localization.Away z) e})^j :=
    (Ideal.Quotient.mk _).comp (algebraMap A _)
  have hψ0 : ∀ x ∈ (Ideal.span {e})^j, ψ0 x = 0 := by
    intro x hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    simp only [ψ0, RingHom.comp_apply, map_mul, map_pow]
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr, zero_mul]
    rw [Ideal.span_singleton_pow, map_pow]
    exact Ideal.mem_span_singleton_self _
  let ψ := Ideal.Quotient.lift _ ψ0 hψ0
  have hψu : IsUnit (ψ (Ideal.Quotient.mk _ z)) := by
    simp only [ψ, Ideal.Quotient.lift_mk, ψ0, RingHom.comp_apply]
    exact (IsLocalization.Away.algebraMap_isUnit z).map _
  let g : Localization.Away (Ideal.Quotient.mk ((Ideal.span {e})^j) z) →+* _ :=
    IsLocalization.Away.lift (Ideal.Quotient.mk _ z) hψu
  have hg : ∀ a : A, g (algebraMap (A ⧸ (Ideal.span {e})^j) _ (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk _ (algebraMap A (Localization.Away z) a) :=
    fun a ↦ IsLocalization.Away.lift_eq _ hψu _
  have hgf : g.comp f = RingHom.id _ :=
    Ideal.Quotient.ringHom_ext <| IsLocalization.ringHom_ext (Submonoid.powers z) <|
      RingHom.ext fun a ↦ by simp only [RingHom.comp_apply, RingHom.id_apply, hf, hg]
  have hfg : f.comp g = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk ((Ideal.span {e})^j) z)) <|
      Ideal.Quotient.ringHom_ext <|
        RingHom.ext fun a ↦ by simp only [RingHom.comp_apply, RingHom.id_apply, hf, hg]
  exact ⟨RingEquiv.ofRingHom f g hfg hgf, hf⟩

/-- Every element of `(t, x)^j` is a homogeneous combination `∑ cᵢ t^(j-i) xⁱ` of degree-`j`
monomials. -/
theorem monomial_span_pow (R : Type) [CommRing R] (t x : R) (j : ℕ) (r : R)
    (hr : r ∈ (Ideal.span {t,x}) ^ j) :
    ∃ c : Fin (j+1) → R, r = ∑ i : Fin (j+1), c i * t^(j - i.val) * x^i.val := by
  have key : ∀ n : ℕ, (Ideal.span {t,x})^n ≤
      Ideal.span (Set.range fun i : Fin (n+1) ↦ t^(n - i.val) * x^i.val) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      refine (Ideal.mul_mono_right ih).trans ?_
      rw [Ideal.span_mul_span', Ideal.span_le]
      rintro _ ⟨a, ha, b, ⟨i, rfl⟩, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · apply Ideal.subset_span
        refine ⟨⟨i.val, by omega⟩, ?_⟩
        have hi := i.isLt
        simp only
        rw [show n + 1 - i.val = (n - i.val) + 1 by omega, pow_succ]
        ring
      · apply Ideal.subset_span
        refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
        have hi := i.isLt
        simp only
        rw [show n + 1 - (i.val + 1) = n - i.val by omega, pow_succ]
        ring
  have h := key j hr
  rw [Ideal.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [← hc]; simp [mul_assoc]⟩

/-- An ideal of a fixed-tangent cell is principal, generated by a form `∑ cᵢ t^(d-i) xⁱ` whose
coefficients reduce to those of a polynomial `H` with homogeneous divisor `Dv`, and some
coefficient is a unit. -/
theorem fixed_tangent_cell_generator_coefficients (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (s : State) (d : ℕ) (Dv : ExceptionalDivisor (IsLocalRing.ResidueField R))
    (J : Ideal R) (hJ : J ∈ fixedTangentCell O R S s d Dv) :
    ∃ (f : R) (c : Fin (d+1) → R) (H : Polynomial (IsLocalRing.ResidueField R)), J = Ideal.span
    {f} ∧ f = ∑ i : Fin (d+1), c i * S.t^(d - i.val) * S.x^i.val ∧ HasHomogeneousDivisor
    (IsLocalRing.ResidueField R) d H Dv ∧ (∀ i : Fin (d+1), IsLocalRing.residue R (c i) =
      H.coeff i.val) ∧ ∃ i : Fin (d+1), c i ∉ Ideal.span {S.t, S.x} := by
  obtain ⟨-, f, H, hJf, hH, hδ⟩ := hJ
  rw [← S.parameters] at hδ
  obtain ⟨c', hc'⟩ := monomial_span_pow R S.t S.x (d+1) _ hδ
  have htm : S.t ∈ IsLocalRing.maximalIdeal R := S.parameters ▸ Ideal.subset_span (by simp)
  have hxm : S.x ∈ IsLocalRing.maximalIdeal R := S.parameters ▸ Ideal.subset_span (by simp)
  have hrep : ∀ y, IsLocalRing.residue R (residueRepresentative R y) = y := fun y ↦
    Function.rightInverse_invFun IsLocalRing.residue_surjective y
  let c : Fin (d+1) → R := fun i ↦ residueRepresentative R (H.coeff i.val) + S.t * c' i.castSucc
    + (if i = Fin.last d then S.x * c' (Fin.last (d+1)) else 0)
  have hres : ∀ i : Fin (d+1), IsLocalRing.residue R (c i) = H.coeff i.val := by
    intro i
    have ht : IsLocalRing.residue R S.t = 0 := (IsLocalRing.residue_eq_zero_iff _).2 htm
    have hx : IsLocalRing.residue R S.x = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hxm
    simp only [c]
    split_ifs <;> simp [map_add, map_mul, ht, hx, hrep]
  refine ⟨f, c, H, hJf, ?_, hH, hres, ?_⟩
  · have hf : f = tangentLift O R S d H + (f - tangentLift O R S d H) := by ring
    rw [hf, hc', Fin.sum_univ_castSucc, tangentLift]
    simp only [c, add_mul, Finset.sum_add_distrib]
    have h1 : (∑ i : Fin (d+1),
        c' i.castSucc * S.t ^ (d + 1 - (i.castSucc : ℕ)) * S.x ^ (i.castSucc : ℕ))
        = ∑ i : Fin (d+1), S.t * c' i.castSucc * S.t ^ (d - (i : ℕ)) * S.x ^ (i : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_castSucc]
      have : d + 1 - i.val = (d - i.val) + 1 := by omega
      rw [this, pow_succ]; ring
    have h2 : (∑ i : Fin (d+1), (if i = Fin.last d then S.x * c' (Fin.last (d + 1)) else 0)
        * S.t ^ (d - (i : ℕ)) * S.x ^ (i : ℕ))
        = c' (Fin.last (d + 1)) * S.t ^ (d + 1 - ((Fin.last (d + 1) : Fin (d+2)) : ℕ))
          * S.x ^ ((Fin.last (d + 1) : Fin (d+2)) : ℕ) := by
      rw [Finset.sum_eq_single (Fin.last d)]
      · simp [pow_succ]; ring
      · intro b _ hb; simp [hb]
      · simp
    rw [h1, h2]; ring
  · refine ⟨⟨H.natDegree, by have := hH.2.1; omega⟩, ?_⟩
    rw [S.parameters, ← IsLocalRing.residue_eq_zero_iff, hres]
    simp only
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.2 hH.1

/-- For `m < 0`, `P(T) = T^m · Q(T⁻¹)` in `k[T, T⁻¹]` forces `P = Q = 0`. -/
theorem negative_laurent_twist_has_no_kernel (k : Type) [CommRing k] (m : ℤ) (hm : m < 0)
    (P Q : Polynomial k) (h : P.toLaurent - LaurentPolynomial.T m *
      (LaurentPolynomial.invert (R := k) Q.toLaurent) = 0) : P = 0 ∧ Q = 0 := by
  have hc : ∀ n : ℤ, P.toLaurent.coeff n = Q.toLaurent.coeff (m - n) := by
    intro n
    have := congrArg (fun f ↦ f.coeff n) (sub_eq_zero.mp h)
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul,
      LaurentPolynomial.invert_apply] at this
    rw [this]; congr 1; ring
  have hL : ∀ (f : Polynomial k) (i : ℕ), f.toLaurent.coeff (i : ℤ) = f.coeff i := by
    intro f i
    rw [LaurentPolynomial.coeff_toLaurent]
    exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ i
  have hN : ∀ (f : Polynomial k) (n : ℤ), n < 0 → f.toLaurent.coeff n = 0 := by
    intro f n hn
    rw [LaurentPolynomial.coeff_toLaurent]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨i, rfl⟩
    simp at hn
    omega
  constructor
  · ext i
    rw [← hL, hc, hN _ _ (by omega)]; simp
  · ext i
    have := hc (m - i)
    rw [hN _ _ (by omega), sub_sub_cancel, hL] at this
    simp [← this]

/-- A nonzerodivisor of `A` remains a nonzerodivisor in the localization `A[1/z]`. -/
theorem nonzerodivisor_survives_localization (A : Type) [CommRing A] (e z : A)
    (he : Function.Injective (fun a : A ↦ e*a)) :
    Function.Injective
      (fun a : Localization.Away z ↦ algebraMap A (Localization.Away z) e * a) := by
  have key : ∀ w : Localization.Away z, algebraMap A (Localization.Away z) e * w = 0 → w = 0 := by
    intro w hw
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers z) w
    simp only at hs
    have h1 : algebraMap A (Localization.Away z) (e * a) = 0 := by
      rw [map_mul, ← hs, ← mul_assoc, hw, zero_mul]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers z) _ _).1 h1
    have h2 : (m : A) * a = 0 := by
      apply he
      simp only [mul_zero]
      rw [← hm]; ring
    have h3 : algebraMap A (Localization.Away z) a = 0 :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers z) _ _).2 ⟨m, h2⟩
    rw [h3] at hs
    exact (IsLocalization.map_units (Localization.Away z) s).mul_left_eq_zero.1 hs
  exact fun x y hxy ↦ sub_eq_zero.1 (key (x - y) (by simp only at hxy; rw [mul_sub, hxy, sub_self]))

/-- The linear part of the normalization map, evaluated at a coordinate vector `z`, is the first
coordinate of any lift `w` of the image of `z` under the quotient map `phi`. -/
private theorem normalization_linear_part_is_quotient_matrix (O R C : Type) [CommRing O]
    [CommRing R]
    [CommRing C] [Algebra O R] [Algebra O C] (alpha : R →ₐ[O] C) (f : R) (g c : C) (n : ℕ)
    (b : Fin n → R) (bc : Fin n → C) (E : C ≃ₗ[O] ((Fin n → O) × C))
    (hE : ∀ w, E.symm w = divisionMap g bc w)
    (phi : (R ⧸ Ideal.span {f}) →ₗ[O] (C ⧸ Ideal.span {g}))
    (hphi : ∀ h : R, phi (Ideal.Quotient.mk (Ideal.span {f}) h) =
      Ideal.Quotient.mk (Ideal.span {g}) (c * alpha h)) (z : Fin n → O) (w : C)
    (hw : Ideal.Quotient.mk (Ideal.span {g}) w =
      phi (Ideal.Quotient.mk (Ideal.span {f}) (coordinateLift b z))) :
    normalizationLinearPart E (pulledVariation alpha c b) z = (E w).1 := by
  have hlin : coordinateLinear b z = coordinateLift b z := by
    simp [coordinateLinear, coordinateLift]
  have hH : pulledVariation alpha c b z = c * alpha (coordinateLift b z) := by
    simp [pulledVariation, hlin]
  rw [hphi, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hw
  obtain ⟨v, hv⟩ := hw
  have hw' : w = c * alpha (coordinateLift b z) + g * v := by rw [mul_comm g, hv]; ring
  have hgv : E (g * v) = (0, v) := by
    apply E.symm.injective
    rw [LinearEquiv.symm_apply_apply, hE]
    simp [divisionMap, coordinateLift]
  simp only [normalizationLinearPart, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearEquiv.coe_coe, hH, hw', map_add, hgv, Prod.fst_add, add_zero]

/-- The cokernel of the linear part of the normalization map has the same `O`-length as the cokernel
of the quotient map `phi`, and it is injective whenever `phi` is. -/
theorem normalization_linear_part_cokernel_length_eq (O R C : Type) [CommRing O] [CommRing R]
    [CommRing C] [Algebra O R] [Algebra O C] (alpha : R →ₐ[O] C) (f : R) (g e c : C) (d : ℕ)
    (_hf : alpha f = e ^ d * g) (n : ℕ) (pi : O) (s : ℕ)
    (_hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (b : Fin n → R) (bc : Fin n → C) (E : C ≃ₗ[O] ((Fin n → O) × C))
    (hE : ∀ w, E.symm w = divisionMap g bc w)
    (phi : (R ⧸ Ideal.span {f}) →ₗ[O] (C ⧸ Ideal.span {g}))
    (hphi : ∀ h : R, phi (Ideal.Quotient.mk (Ideal.span {f}) h) =
      Ideal.Quotient.mk (Ideal.span {g}) (c * alpha h))
    (EB : (R ⧸ Ideal.span {f}) ≃ₗ[O] (Fin n → O))
    (hEB : ∀ z : Fin n → O, EB.symm z = Ideal.Quotient.mk (Ideal.span {f}) (coordinateLift b z)) :
    Module.length O ((Fin n → O) ⧸ LinearMap.range
      (normalizationLinearPart E (pulledVariation alpha c b))) = Module.length O
    ((C ⧸ Ideal.span {g}) ⧸ LinearMap.range phi) ∧
    (Function.Injective phi → Function.Injective
      (normalizationLinearPart E (pulledVariation alpha c b))) := by
  obtain ⟨EC, hEC⟩ := division_equiv_child_coordinates O C n g bc E hE
  have hD : ∀ z, normalizationLinearPart E (pulledVariation alpha c b) z
      = EC (phi (EB.symm z)) := by
    intro z
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
      (phi (Ideal.Quotient.mk (Ideal.span {f}) (coordinateLift b z)))
    rw [normalization_linear_part_is_quotient_matrix O R C alpha f g c n
      b bc E hE phi hphi z w hw, ← hEC, hw, hEB]
  have hcomp : normalizationLinearPart E (pulledVariation alpha c b)
      = (EC.toLinearMap ∘ₗ phi) ∘ₗ EB.symm.toLinearMap := by
    ext z; simp [hD]
  have hrange : LinearMap.range (normalizationLinearPart E (pulledVariation alpha c b))
      = (LinearMap.range phi).map EC.toLinearMap := by
    rw [hcomp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range EB.symm),
      LinearMap.range_comp]
  refine ⟨?_, fun h ↦ ?_⟩
  · exact (Submodule.Quotient.equiv _ _ EC.symm.symm hrange.symm).length_eq.symm
  · rw [hcomp]
    exact (EC.injective.comp h).comp EB.symm.injective

/-- The opposite chart maps into the overlap, compatibly with the base and sending its slope to the
inverse of the slope. -/
private theorem opposite_untruncated_chart_restriction (R : Type) [CommRing R] (t x : R) :
    ∃ beta : (BlowupChart R x t) →+* (BlowupOverlap R t x),
    (∀ r : R, beta (chartBase R x t r) = (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))
      (chartBase R t x r)) ∧ beta (chartSlope R x t) = IsLocalization.Away.invSelf
    (chartSlope R t x) := by
  set a : R →+* BlowupOverlap R t x :=
    (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)).comp (chartBase R t x) with ha
  have hrel := blowup_chart_relation R t x
  have hinv := IsLocalization.Away.mul_invSelf (S := BlowupOverlap R t x) (chartSlope R t x)
  have hz : a x * IsLocalization.Away.invSelf (chartSlope R t x) = a t := by
    simp only [ha, RingHom.comp_apply, ← hrel, map_mul]
    rw [mul_assoc, hinv, mul_one]
  obtain ⟨psi, h1, h2⟩ := blowup_chart_universal R (BlowupOverlap R t x) x t a
    (IsLocalization.Away.invSelf (chartSlope R t x)) hz
  exact ⟨psi, fun r ↦ by rw [h1]; rfl, h2⟩

/-- A blow-up restriction (the gluing map of the opposite chart into the overlap) exists. -/
theorem actual_blowup_restriction_exists (R : Type) [CommRing R] (t x : R) :
    Nonempty (BlowupRestriction R t x) := by
  obtain ⟨beta, hbase, hslope⟩ := opposite_untruncated_chart_restriction R t x
  have hc : ∀ r : R, beta (algebraMap R (BlowupChart R x t) r) =
      algebraMap R (BlowupOverlap R t x) r := by
    intro r
    have h1 : algebraMap R (BlowupChart R x t) r = chartBase R x t r := rfl
    have h2 : algebraMap R (BlowupOverlap R t x) r =
        algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x r) := by
      rw [IsScalarTower.algebraMap_apply R (BlowupChart R t x) (BlowupOverlap R t x)]
      rfl
    rw [h1, h2, hbase]
  exact ⟨{ right := { beta with commutes' := hc }, slope := hslope }⟩

/-- The overlaps of the two charts are isomorphic, compatibly with the base maps and exchanging the
slope with its inverse. -/
private theorem blowup_overlap_symmetry (R : Type) [CommRing R] (t x : R) :
    ∃ e : BlowupOverlap R x t ≃+* BlowupOverlap R t x,
    (∀ r : R, e ((algebraMap (BlowupChart R x t) (BlowupOverlap R x t)) (chartBase R x t r)) =
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x r)) ∧ e
    ((algebraMap (BlowupChart R x t) (BlowupOverlap R x t)) (chartSlope R x t)) =
    IsLocalization.Away.invSelf (chartSlope R t x) := by
  obtain ⟨b1, hb1, hs1⟩ := opposite_untruncated_chart_restriction R t x
  obtain ⟨b2, hb2, hs2⟩ := opposite_untruncated_chart_restriction R x t
  have u1 : IsUnit (b1 (chartSlope R x t)) := by
    rw [hs1]
    exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (chartSlope R t x))
  have u2 : IsUnit (b2 (chartSlope R t x)) := by
    rw [hs2]
    exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (chartSlope R x t))
  let e1 : BlowupOverlap R x t →+* BlowupOverlap R t x :=
    IsLocalization.Away.lift (chartSlope R x t) u1
  let e2 : BlowupOverlap R t x →+* BlowupOverlap R x t :=
    IsLocalization.Away.lift (chartSlope R t x) u2
  have he1 : ∀ a, e1 (algebraMap _ _ a) = b1 a := fun a ↦
    IsLocalization.Away.lift_eq (chartSlope R x t) u1 a
  have he2 : ∀ a, e2 (algebraMap _ _ a) = b2 a := fun a ↦
    IsLocalization.Away.lift_eq (chartSlope R t x) u2 a
  have inv_map : ∀ {S T : Type} [CommRing S] [CommRing T] (s : S)
      (f : Localization.Away s →+* T) (w : T),
      f (algebraMap S _ s) * w = 1 →
      f (IsLocalization.Away.invSelf s) = w := by
    intro S T _ _ s f w hw
    have h1 : f (algebraMap S _ s) * f (IsLocalization.Away.invSelf s) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    linear_combination w * h1 - f (IsLocalization.Away.invSelf s) * hw
  have h21 : e2.comp e1 = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (chartSlope R x t))
    apply blowup_chart_ringHom_ext
    · exact fun r ↦ by simp only [RingHom.comp_apply, RingHom.id_apply, he1, hb1, he2, hb2]
    · simp only [RingHom.comp_apply, RingHom.id_apply, he1, hs1]
      exact inv_map _ _ _ (by rw [he2, hs2, mul_comm, IsLocalization.Away.mul_invSelf])
  have h12 : e1.comp e2 = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (chartSlope R t x))
    apply blowup_chart_ringHom_ext
    · exact fun r ↦ by simp only [RingHom.comp_apply, RingHom.id_apply, he1, hb1, he2, hb2]
    · simp only [RingHom.comp_apply, RingHom.id_apply, he2, hs2]
      exact inv_map _ _ _ (by rw [he1, hs1, mul_comm, IsLocalization.Away.mul_invSelf])
  exact ⟨RingEquiv.ofRingHom e1 e2 h12 h21, fun r ↦ (he1 _).trans (hb1 r), (he1 _).trans hs1⟩

/-- Via the gluing map, the overlap is the localization of the opposite chart away from its
slope. -/
theorem blowup_overlap_isLocalization_right (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) :
    @IsLocalization.Away (BlowupChart R x t) _ (chartSlope R x t)
    (BlowupOverlap R t x) _ beta.right.toRingHom.toAlgebra := by
  obtain ⟨e, he1, he2⟩ := blowup_overlap_symmetry R t x
  have h : e.toRingHom.comp (algebraMap (BlowupChart R x t) (BlowupOverlap R x t)) =
      beta.right.toRingHom := by
    apply blowup_chart_ringHom_ext R (BlowupOverlap R t x) x t
    · intro r
      have h1 : e ((algebraMap (BlowupChart R x t) (BlowupOverlap R x t)) (chartBase R x t r)) =
          algebraMap R (BlowupOverlap R t x) r := by
        rw [he1]
        exact (IsScalarTower.algebraMap_apply R (BlowupChart R t x) (BlowupOverlap R t x) r).symm
      have h2 : beta.right (chartBase R x t r) = algebraMap R (BlowupOverlap R t x) r :=
        beta.right.commutes r
      exact h1.trans h2.symm
    · exact he2.trans beta.slope.symm
  have key :=
    (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers (chartSlope R x t)) e).mp
    (inferInstance : IsLocalization.Away (chartSlope R x t) (BlowupOverlap R x t))
  rw [← h]
  exact key

/-- A maximal ideal of a localization `B` of the chart away from the slope, whose contraction
contains the exceptional parameter `t`, contracts to a maximal ideal of the chart. -/
private theorem comap_isMaximal_of_exceptional (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (B : Type) [CommRing B] [Algebra (BlowupChart R t x) B]
    [IsLocalization.Away (chartSlope R t x) B] (Q : Ideal B) [Q.IsMaximal]
    (htP : chartBase R t x t ∈ Q.comap (algebraMap (BlowupChart R t x) B)) :
    (Q.comap (algebraMap (BlowupChart R t x) B)).IsMaximal := by
  set P := Q.comap (algebraMap (BlowupChart R t x) B)
  let _ : Field (R ⧸ Ideal.span ({t,x} : Set R)) := Ideal.Quotient.field _
  obtain ⟨e0, hC, hX⟩ := exceptional_chart_is_affine_line R t x
  let ψ : BlowupChart R t x →+* Polynomial (R ⧸ Ideal.span ({t,x} : Set R)) :=
    e0.toRingHom.comp (Ideal.Quotient.mk (exceptionalLevelIdeal R t x 1))
  have hψs : Function.Surjective ψ :=
    e0.surjective.comp Ideal.Quotient.mk_surjective
  have hψZ : ψ (chartSlope R t x) = Polynomial.X := hX
  have hker : RingHom.ker ψ ≤ P := fun a ha ↦ by
    have h1 : e0 (Ideal.Quotient.mk (exceptionalLevelIdeal R t x 1) a) = 0 := ha
    rw [map_eq_zero_iff _ e0.injective, Ideal.Quotient.eq_zero_iff_mem, exceptionalLevelIdeal,
      pow_one] at h1
    exact (Ideal.span_le.mpr (by simpa using htP)) h1
  have hmapP : (P.map ψ).IsPrime := Ideal.map_isPrime_of_surjective hψs hker
  rw [← sup_eq_left.mpr hker, ← Ideal.comap_map_of_surjective' ψ hψs P]
  have key : ∃ f ∈ P.map ψ, f ≠ 0 := by
    by_cases h1 : chartSlope R t x - 1 ∈ P
    · refine ⟨ψ (chartSlope R t x - 1), Ideal.mem_map_of_mem _ h1, ?_⟩
      rw [map_sub, map_one, hψZ]
      exact Polynomial.X_sub_C_ne_zero 1
    · obtain ⟨y, i, hi, hy⟩ := Ideal.IsMaximal.exists_inv (inferInstance : Q.IsMaximal) h1
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (chartSlope R t x)) y
      have hg : a * (chartSlope R t x - 1) - (s : BlowupChart R t x) ∈ P := by
        change algebraMap (BlowupChart R t x) B _ ∈ Q
        have hs := IsLocalization.mk'_spec B a s
        have : algebraMap (BlowupChart R t x) B
            (a * (chartSlope R t x - 1) - (s : BlowupChart R t x))
            = - (algebraMap (BlowupChart R t x) B s * i) := by
          rw [map_sub, map_mul, ← hs]
          linear_combination (algebraMap (BlowupChart R t x) B s) * hy
        rw [this]
        exact Q.neg_mem_iff.mpr (Q.mul_mem_left _ hi)
      refine ⟨_, Ideal.mem_map_of_mem _ hg, ?_⟩
      obtain ⟨n, hn⟩ := s.2
      intro h0
      have := congrArg (Polynomial.eval 1) h0
      rw [map_sub, map_mul, ← hn, map_pow, map_sub, map_one, hψZ] at this
      simp at this
  obtain ⟨f, hf, hf0⟩ := key
  have : (P.map ψ).IsMaximal :=
    IsPrime.to_maximal_ideal fun hbot ↦ hf0 (by rwa [hbot, Ideal.mem_bot] at hf)
  exact Ideal.comap_isMaximal_of_surjective _ hψs

/-- A maximal ideal of the overlap containing the exceptional parameter contracts to a maximal ideal
of the chart that contains `t` but not the slope. -/
theorem overlap_exceptional_point_comap_maximal (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (Q : Ideal (BlowupOverlap R t x)) [Q.IsMaximal]
    (hQ : (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t) ∈ Q) :
    (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))).IsMaximal ∧
    chartSlope R t x ∉ Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) ∧
    chartBase R t x t ∈ Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) := by
  exact ⟨comap_isMaximal_of_exceptional R t x _ Q hQ, fun h ↦ Ideal.IsMaximal.ne_top ‹_›
    (Ideal.eq_top_of_isUnit_mem Q h (IsLocalization.Away.algebraMap_isUnit _)), hQ⟩

/-- A maximal ideal of the overlap containing the exceptional parameter contracts, along the gluing
map, to a maximal ideal of the opposite chart that contains `x` but not its slope. -/
theorem overlap_exceptional_point_comap_maximal_right (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (beta : BlowupRestriction R t x)
    (Q : Ideal (BlowupOverlap R t x)) [Q.IsMaximal]
    (hQ : (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t) ∈ Q) :
    (Q.comap beta.right.toRingHom).IsMaximal ∧ chartSlope R x t ∉ Q.comap beta.right.toRingHom ∧
    chartBase R x t x ∈ Q.comap beta.right.toRingHom := by
  set P := Q.comap beta.right.toRingHom with hPdef
  have htP : chartBase R x t x ∈ P := by
    change beta.right (chartBase R x t x) ∈ Q
    rw [show beta.right (chartBase R x t x) = algebraMap R (BlowupOverlap R t x) x from
      beta.right.commutes x, IsScalarTower.algebraMap_apply R (BlowupChart R t x),
      show algebraMap R (BlowupChart R t x) x = chartBase R t x t * chartSlope R t x from
      (blowup_chart_relation R t x).symm, map_mul]
    exact Q.mul_mem_right _ hQ
  have hZP : chartSlope R x t ∉ P := fun h ↦ by
    have h' : beta.right (chartSlope R x t) ∈ Q := h
    rw [beta.slope] at h'
    exact Ideal.IsMaximal.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem Q h'
      (.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (chartSlope R t x))))
  refine ⟨?_, hZP, htP⟩
  let _ := beta.right.toRingHom.toAlgebra
  have := blowup_overlap_isLocalization_right R t x beta
  have : (Ideal.span ({x,t} : Set R)).IsMaximal := by rw [Set.pair_comm]; infer_instance
  exact comap_isMaximal_of_exceptional R x t (BlowupOverlap R t x) Q htP

private theorem localizationAway_quotient_congr {S : Type} [CommRing S] (I J : Ideal S) (h : I = J)
    (z : S) :
    ∃ F : Localization.Away (Ideal.Quotient.mk I z) ≃+* Localization.Away
    (Ideal.Quotient.mk J z), ∀ a : S, F (algebraMap _ _ (Ideal.Quotient.mk I a)) = algebraMap _ _
    (Ideal.Quotient.mk J a) := by
  subst h; exact ⟨RingEquiv.refl _, fun _ ↦ rfl⟩

/-- The exceptional divisor of the overlap is the Laurent line `k[Z, Z⁻¹]` over the residue field
`k = R/(t, x)`, with constants coming from `R` and the slope going to `Z`. -/
private theorem overlap_exceptional_quotient_equiv_laurent (R : Type) [CommRing R] (t x : R) :
    ∃ E : BlowupOverlap R t x ⧸ Ideal.span {overlapException R t x} ≃+*
      LaurentPolynomial (R ⧸ Ideal.span ({t,x} : Set R)),
      (∀ r : R, E (Ideal.Quotient.mk _ (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
        (chartBase R t x r))) = LaurentPolynomial.C (Ideal.Quotient.mk _ r)) ∧
      E (Ideal.Quotient.mk _ (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
        (chartSlope R t x))) = LaurentPolynomial.T 1 := by
  set A := BlowupChart R t x
  set C := BlowupOverlap R t x
  obtain ⟨L, hL⟩ :=
    localization_principal_quotient_commute A (chartBase R t x t) (chartSlope R t x) 1
  have hI : (Ideal.span {chartBase R t x t})^1 = exceptionalLevelIdeal R t x 1 := by
    simp [exceptionalLevelIdeal]
  obtain ⟨F, hF⟩ := localizationAway_quotient_congr _ _ hI (chartSlope R t x)
  obtain ⟨E0, hE0C, hE0T⟩ := exceptional_overlap_is_laurent_line R t x
  have hJ : Ideal.span {overlapException R t x} =
      (Ideal.span {algebraMap A C (chartBase R t x t)})^1 := by
    simp [overlapException, A, C]
  let E := ((Ideal.quotEquivOfEq hJ).trans L).trans (F.trans E0)
  have hE : ∀ a : A, E (Ideal.Quotient.mk _ (algebraMap A C a)) =
      E0 (levelOverlapMap R t x 1 (Ideal.Quotient.mk _ a)) := by
    intro a
    simp only [E, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    rw [hL]; exact congrArg E0 (hF a)
  exact ⟨E, fun r ↦ (hE _).trans (hE0C r), (hE _).trans hE0T⟩

/-- The exceptional divisor of the overlap is integral, and an element of the opposite chart
vanishing on it lies in the exceptional ideal `(x)` of that chart. -/
theorem overlap_exceptional_quotient_domain (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (_hreg : RegularParameterPair R t x)
    (beta : BlowupRestriction R t x) :
    IsDomain (BlowupOverlap R t x ⧸ Ideal.span {overlapException R t x}) ∧ ∀ b : BlowupChart R x t,
    Ideal.Quotient.mk (Ideal.span {overlapException R t x}) (beta.right b) = 0 → b ∈ Ideal.span
    {chartBase R x t x} := by
  -- Both exceptional curves are identified with (open subsets of) `ℙ¹_k`: the overlap one with
  -- `k[Z, Z⁻¹]`, the chart one with `k[W]`, and the gluing becomes `W ↦ Z⁻¹`, which is injective.
  set A := BlowupChart R t x
  set C := BlowupOverlap R t x
  set k := R ⧸ Ideal.span ({t,x} : Set R)
  set e' := overlapException R t x
  obtain ⟨E, hEC, hET⟩ := overlap_exceptional_quotient_equiv_laurent R t x
  refine ⟨MulEquiv.isDomain _ E.toMulEquiv, fun b hb ↦ ?_⟩
  obtain ⟨P, hPC, hPX⟩ := exceptional_chart_is_affine_line R x t
  have hK : Ideal.span ({t,x} : Set R) = Ideal.span ({x,t} : Set R) := by rw [Set.pair_comm]
  let κ : k ≃+* (R ⧸ Ideal.span ({x,t} : Set R)) := Ideal.quotEquivOfEq hK
  have hbase : ∀ r : R, beta.right (chartBase R x t r) = algebraMap A C (chartBase R t x r) := by
    intro r
    have h1 : chartBase R x t r = algebraMap R (BlowupChart R x t) r := rfl
    rw [h1, beta.right.commutes, IsScalarTower.algebraMap_apply R A C]; rfl
  have hx : beta.right (chartBase R x t x) ∈ Ideal.span {e'} := by
    rw [hbase, ← blowup_chart_relation, map_mul, Ideal.mem_span_singleton]
    exact ⟨_, rfl⟩
  let f0 : BlowupChart R x t →+* C ⧸ Ideal.span {e'} :=
    (Ideal.Quotient.mk (Ideal.span {e'})).comp beta.right.toRingHom
  have hlift : ∀ a ∈ exceptionalLevelIdeal R x t 1, f0 a = 0 := by
    intro a ha
    simp only [exceptionalLevelIdeal, pow_one, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    simp only [f0, RingHom.comp_apply, map_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_mul]
  let g : ExceptionalChartLevel R x t 1 →+* LaurentPolynomial k :=
    E.toRingHom.comp (Ideal.Quotient.lift _ f0 hlift)
  have key : (g.comp P.symm.toRingHom).comp (Polynomial.mapRingHom κ.toRingHom) =
      (LaurentPolynomial.invert :
        LaurentPolynomial k ≃ₐ[k] LaurentPolynomial k).toRingEquiv.toRingHom.comp
        Polynomial.toLaurent := by
    have hg : ∀ a : BlowupChart R x t,
        g (Ideal.Quotient.mk _ a) = E (Ideal.Quotient.mk _ (beta.right a)) := fun a ↦ rfl
    apply Polynomial.ringHom_ext
    · intro a
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      have h1 : P.symm (Polynomial.C (Ideal.Quotient.mk (Ideal.span ({x,t} : Set R)) r)) =
          levelBase R x t 1 r := by
        rw [RingEquiv.symm_apply_eq, hPC]
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, κ,
        Polynomial.toLaurent_C, AlgEquiv.coe_ringEquiv, LaurentPolynomial.invert_C]
      have h2 : levelBase R x t 1 r = Ideal.Quotient.mk _ (chartBase R x t r) := rfl
      rw [Ideal.quotEquivOfEq_mk, h1, h2, hg, hbase]
      exact hEC r
    · have h1 : P.symm Polynomial.X = levelSlope R x t 1 := by
        rw [RingEquiv.symm_apply_eq, hPX]
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h1,
        Polynomial.toLaurent_X, AlgEquiv.coe_ringEquiv, LaurentPolynomial.invert_T]
      have h2 : levelSlope R x t 1 = Ideal.Quotient.mk _ (chartSlope R x t) := rfl
      rw [h2, hg, beta.slope]
      have hm : LaurentPolynomial.T 1 *
          E (Ideal.Quotient.mk _ (IsLocalization.Away.invSelf (chartSlope R t x) : C)) = 1 := by
        rw [← hET, ← map_mul, ← map_mul, IsLocalization.Away.mul_invSelf, map_one, map_one]
      exact (left_inv_eq_right_inv (by rw [← LaurentPolynomial.T_add]; simp) hm).symm
  have hb0 : g (Ideal.Quotient.mk _ b) = 0 := by
    simp only [g, f0, RingHom.comp_apply, Ideal.Quotient.lift_mk, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, hb, map_zero]
  set p := Polynomial.mapRingHom κ.symm.toRingHom (P (Ideal.Quotient.mk _ b))
  have hmm : (Polynomial.mapRingHom κ.toRingHom) p = P (Ideal.Quotient.mk _ b) := by
    simp only [p, Polynomial.coe_mapRingHom, Polynomial.map_map]
    convert Polynomial.map_id
    ext a; simp
  have hp : p = 0 := by
    have := congrArg (fun h ↦ h p) key
    simp only [RingHom.comp_apply] at this
    rw [hmm] at this
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply,
      hb0] at this
    rwa [eq_comm, map_eq_zero_iff _ (LaurentPolynomial.invert.toRingEquiv).injective,
      map_eq_zero_iff _ Polynomial.toLaurent_injective] at this
  have hq : Ideal.Quotient.mk (exceptionalLevelIdeal R x t 1) b = 0 :=
    P.injective (by rw [map_zero, ← hmm, hp, map_zero])
  rw [Ideal.Quotient.eq_zero_iff_mem] at hq
  simpa [exceptionalLevelIdeal] using hq

private theorem quotientMap_surjective_of_away {A C : Type} [CommRing A] [CommRing C] (f : A →+* C)
    (s : A) (hsurj : ∀ c : C, ∃ a : A, ∃ n : ℕ, c * f s ^ n = f a) (Q : Ideal C)
    (hP : (Q.comap f).IsMaximal) (hs : s ∉ Q.comap f) :
    Function.Surjective (Ideal.quotientMap Q f le_rfl) := by
  intro c'
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  obtain ⟨a, n, hc⟩ := hsurj c
  have hs' : Ideal.Quotient.mk (Q.comap f) (s ^ n) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h ↦ hs (hP.isPrime.mem_of_pow_mem n h)
  let _ := Ideal.Quotient.field (Q.comap f)
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (Q.comap f) (s ^ n))⁻¹
  have h1 : Ideal.Quotient.mk (Q.comap f) (u * s ^ n) = 1 := by
    rw [map_mul, hu, inv_mul_cancel₀ hs']
  have h2 : u * s ^ n - 1 ∈ Q.comap f := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
  refine ⟨Ideal.Quotient.mk _ (a * u), ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  have : f (a * u) - c = c * f (u * s ^ n - 1) := by
    rw [map_mul, ← hc, map_sub, map_mul, map_pow, map_one]; ring
  rw [this]
  exact Q.mul_mem_left _ h2

/-- At a maximal ideal of the overlap on the exceptional divisor, both charts have the same residue
field as the overlap, and hence the same residue length over `R`. -/
theorem overlap_point_residue_field_equiv (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (beta : BlowupRestriction R t x)
    (Q : Ideal (BlowupOverlap R t x)) [Q.IsMaximal]
    (hQ : (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t) ∈ Q) :
    (∃ φ : (BlowupChart R t x ⧸ Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) ≃+*
      (BlowupOverlap R t x ⧸ Q), ∀ a : BlowupChart R t x,
      φ (Ideal.Quotient.mk (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) a) =
      Ideal.Quotient.mk Q ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a)) ∧
    (∃ ψ : (BlowupChart R x t ⧸ Q.comap beta.right.toRingHom) ≃+* (BlowupOverlap R t x ⧸ Q),
      ∀ b : BlowupChart R x t, ψ (Ideal.Quotient.mk (Q.comap beta.right.toRingHom) b) =
      Ideal.Quotient.mk Q (beta.right b)) ∧ Module.length R
    (BlowupChart R t x ⧸ Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) =
    Module.length R (BlowupChart R x t ⧸ Q.comap beta.right.toRingHom) := by
  obtain ⟨hPl, hsl, -⟩ := overlap_exceptional_point_comap_maximal R t x Q hQ
  obtain ⟨hPr, hsr, -⟩ :=
    overlap_exceptional_point_comap_maximal_right R t x beta Q hQ
  set fl := algebraMap (BlowupChart R t x) (BlowupOverlap R t x) with hfl
  set fr := beta.right.toRingHom with hfr
  have surjl : ∀ c : BlowupOverlap R t x, ∃ a, ∃ n : ℕ, c * fl (chartSlope R t x) ^ n = fl a := by
    intro c
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (chartSlope R t x)) c
    exact ⟨a, n, by simpa [map_pow] using h⟩
  have surjr : ∀ c : BlowupOverlap R t x, ∃ a, ∃ n : ℕ, c * fr (chartSlope R x t) ^ n = fr a := by
    intro c
    let _ := fr.toAlgebra
    have := blowup_overlap_isLocalization_right R t x beta
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (chartSlope R x t)) c
    exact ⟨a, n, by simpa [map_pow, RingHom.algebraMap_toAlgebra] using h⟩
  let φ := RingEquiv.ofBijective (Ideal.quotientMap Q fl le_rfl)
    ⟨Ideal.quotientMap_injective, quotientMap_surjective_of_away fl _ surjl Q hPl hsl⟩
  let ψ := RingEquiv.ofBijective (Ideal.quotientMap Q fr le_rfl)
    ⟨Ideal.quotientMap_injective, quotientMap_surjective_of_away fr _ surjr Q hPr hsr⟩
  have hφ : ∀ a, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk Q (fl a) := fun a ↦ rfl
  have hψ : ∀ b, ψ (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk Q (fr b) := fun b ↦ rfl
  refine ⟨⟨φ, hφ⟩, ⟨ψ, hψ⟩, ?_⟩
  rw [(AlgEquiv.ofRingEquiv (R := R) (f := φ) fun r ↦ congrArg (Ideal.Quotient.mk Q)
      (IsScalarTower.algebraMap_apply R _ _ r).symm).toLinearEquiv.length_eq,
    (AlgEquiv.ofRingEquiv (R := R) (f := ψ) fun r ↦ congrArg (Ideal.Quotient.mk Q)
      (beta.right.commutes r)).toLinearEquiv.length_eq]

/-- At a prime of the overlap, the local ring of the overlap is the local ring of the chart at the
contracted prime. -/
private theorem overlap_prime_localization_left (R : Type) [CommRing R] (t x : R)
    (Q : Ideal (BlowupOverlap R t x)) [Q.IsPrime] :
    ∃ φ : Localization.AtPrime Q ≃+* Localization.AtPrime
    (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))), ∀ a : BlowupChart R t x, φ
    (algebraMap (BlowupOverlap R t x) (Localization.AtPrime Q)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a)) = algebraMap (BlowupChart R t x)
    (Localization.AtPrime (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)))) a := by
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (chartSlope R t x)) Q
  refine ⟨e.symm.toRingEquiv, fun a ↦ ?_⟩
  have h := e.symm.commutes a
  simp [← IsScalarTower.algebraMap_apply] at h ⊢

/-- At a prime of the overlap, the completed local ring of the overlap is the completed local ring
of the chart at the contracted prime. -/
theorem completed_point_transport_left (R : Type) [CommRing R] (t x : R)
    [IsNoetherianRing (BlowupChart R t x)] (Q : Ideal (BlowupOverlap R t x)) [Q.IsPrime] :
    ∃ Φ : CompletedLocalAt (BlowupOverlap R t x) Q ≃+* CompletedLocalAt (BlowupChart R t x)
    (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))), ∀ a : BlowupChart R t x, Φ
    (completedPointMap (BlowupOverlap R t x) Q
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a)) = completedPointMap
    (BlowupChart R t x) (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) a := by
  obtain ⟨φ, hφ⟩ := overlap_prime_localization_left R t x Q
  have : IsNoetherianRing (BlowupOverlap R t x) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (chartSlope R t x)) _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime
      (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)))) :=
    IsLocalization.isNoetherianRing
      (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))).primeCompl _ inferInstance
  obtain ⟨Φ, hΦ⟩ := local_completion_transport (Localization.AtPrime Q)
    (Localization.AtPrime (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)))) φ
  refine ⟨Φ, fun a ↦ ?_⟩
  simp only [completedPointMap, RingHom.comp_apply]
  rw [hΦ, hφ]

/-- At a prime of the overlap, the local ring of the overlap is the local ring of the opposite chart
at the prime contracted along the gluing map. -/
private theorem overlap_prime_localization_right (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (Q : Ideal (BlowupOverlap R t x)) [Q.IsPrime] :
    ∃ ψ : Localization.AtPrime Q ≃+* Localization.AtPrime
    (Q.comap beta.right.toRingHom), ∀ b : BlowupChart R x t, ψ
    (algebraMap (BlowupOverlap R t x) (Localization.AtPrime Q) (beta.right b)) = algebraMap
    (BlowupChart R x t) (Localization.AtPrime (Q.comap beta.right.toRingHom)) b := by
  let _ : Algebra (BlowupChart R x t) (BlowupOverlap R t x) := beta.right.toRingHom.toAlgebra
  have _ := blowup_overlap_isLocalization_right R t x beta
  have _ : IsScalarTower (BlowupChart R x t) (BlowupOverlap R t x) (Localization.AtPrime Q) :=
    inferInstance
  have hL : IsLocalization.AtPrime (Localization.AtPrime Q)
      (Q.comap (algebraMap (BlowupChart R x t) (BlowupOverlap R t x))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers (chartSlope R x t)) (Localization.AtPrime Q) Q
  let e := IsLocalization.algEquiv
    (Q.comap (algebraMap (BlowupChart R x t) (BlowupOverlap R t x))).primeCompl
    (Localization.AtPrime (Q.comap beta.right.toRingHom)) (Localization.AtPrime Q)
  refine ⟨e.symm.toRingEquiv, fun b ↦ ?_⟩
  exact e.symm.commutes b

/-- At a prime of the overlap, the completed local ring of the overlap is the completed local ring
of the opposite chart at the prime contracted along the gluing map. -/
theorem completed_point_transport_right (R : Type) [CommRing R] (t x : R)
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x)
    (Q : Ideal (BlowupOverlap R t x)) [Q.IsPrime] :
    ∃ Ψ : CompletedLocalAt (BlowupOverlap R t x) Q ≃+* CompletedLocalAt (BlowupChart R x t)
    (Q.comap beta.right.toRingHom), ∀ b : BlowupChart R x t, Ψ
    (completedPointMap (BlowupOverlap R t x) Q (beta.right b)) = completedPointMap
    (BlowupChart R x t) (Q.comap beta.right.toRingHom) b := by
  obtain ⟨φ, hφ⟩ := overlap_prime_localization_right R t x beta Q
  have hloc := blowup_overlap_isLocalization_right R t x beta
  have : IsNoetherianRing (BlowupOverlap R t x) := by
    let : Algebra (BlowupChart R x t) (BlowupOverlap R t x) := beta.right.toRingHom.toAlgebra
    exact IsLocalization.isNoetherianRing (Submonoid.powers (chartSlope R x t)) _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime (Q.comap beta.right.toRingHom)) :=
    IsLocalization.isNoetherianRing (Q.comap beta.right.toRingHom).primeCompl _ inferInstance
  obtain ⟨Φ, hΦ⟩ :=
    local_completion_transport (Localization.AtPrime Q)
      (Localization.AtPrime (Q.comap beta.right.toRingHom)) φ
  refine ⟨Φ, fun b ↦ ?_⟩
  simp only [completedPointMap, RingHom.comp_apply]
  rw [hΦ, hφ]

/-- For pairwise distinct monic irreducible polynomials `φᵢ`, the intersection of the ideals
`(φᵢ^rᵢ)` is generated by `∏ φᵢ^rᵢ`. -/
theorem pairwise_distinct_irreducible_pow_iInf (k : Type) [Field k] (ι : Type) [Fintype ι]
    (φ : ι → Polynomial k) (hm : ∀ i, (φ i).Monic) (hirr : ∀ i, Irreducible (φ i))
    (hinj : Function.Injective φ) (r : ι → ℕ) :
    (⨅ i, Ideal.span {φ i ^ r i}) = Ideal.span {∏ i, φ i ^ r i} := by
  apply Ideal.iInf_span_singleton
  intro i j hij
  exact (distinct_monic_irreducible_coprime k _ _ (hm i) (hm j) (hirr i) (hirr j)
    (fun h ↦ hij (hinj h))).pow

/-- An ideal of `k[X]` containing a power `φ^L` of an irreducible polynomial is `(φ^r)` for some `r
≤ L`. -/
theorem polynomial_ideal_of_irreducible_pow_le (k : Type) [Field k] (φ : Polynomial k)
    (hφ : Irreducible φ) (J : Ideal (Polynomial k)) (L : ℕ) (hL : Ideal.span {φ^L} ≤ J) :
    ∃ r : ℕ, r ≤ L ∧ J = Ideal.span {φ^r} := by
  have hp : Prime φ := hφ.prime
  have hmem : φ ^ L ∈ J := hL (Ideal.mem_span_singleton_self _)
  have hd : Submodule.IsPrincipal.generator J ∣ φ ^ L :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd J).1 hmem
  obtain ⟨r, hr, hass⟩ := (dvd_prime_pow hp L).1 hd
  refine ⟨r, hr, ?_⟩
  rw [← Ideal.span_singleton_eq_span_singleton.2 hass, Ideal.span_singleton_generator]

/-- For irreducible `φ`, `k[X] ⧸ (φ^r)` has length `r` over `k[X]` and dimension `r · deg φ` over
`k`. -/
theorem polynomial_quotient_irreducible_pow_length (k : Type) [Field k] (φ : Polynomial k)
    (hφ : Irreducible φ) (r : ℕ) :
    Module.length (Polynomial k) (Polynomial k ⧸ Ideal.span {φ^r}) = (r : ℕ∞) ∧ Module.finrank k
    (Polynomial k ⧸ Ideal.span {φ^r}) = r * φ.natDegree := by
  refine ⟨?_, by rw [finrank_quotient_span_eq_natDegree, Polynomial.natDegree_pow]⟩
  have hmax : (Ideal.span {φ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hφ
  have h1 : Module.length (Polynomial k) (Polynomial k ⧸ Ideal.span {φ}) = 1 := by
    have : IsSimpleModule (Polynomial k) (Polynomial k ⧸ Ideal.span {φ}) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, hmax, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have hφ0 : φ ≠ 0 := hφ.ne_zero
  induction r with
  | zero =>
    have : Subsingleton (Polynomial k ⧸ Ideal.span {φ ^ 0}) := by
      rw [pow_zero, Ideal.span_singleton_one]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero
  | succ r ih =>
    let P := Polynomial k
    let I : Submodule P P := Ideal.span {φ ^ r}
    let J : Submodule P P := Ideal.span {φ ^ (r + 1)}
    let S : Submodule P P := Ideal.span {φ}
    have hJI : J ≤ I := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow φ (Nat.le_succ r))
    let m : P →ₗ[P] P ⧸ J := J.mkQ ∘ₗ LinearMap.mulLeft P (φ ^ r)
    have hm : S ≤ LinearMap.ker m := by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp only [LinearMap.mem_ker, m, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulLeft_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton.mpr ⟨b, by ring⟩
    let f : P ⧸ S →ₗ[P] P ⧸ J := S.liftQ m hm
    let g : P ⧸ J →ₗ[P] P ⧸ I := Submodule.factor hJI
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective S x
      simp only [LinearMap.mem_ker, f, Submodule.liftQ_apply, m, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.mulLeft_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, J] at hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
      have : a = φ * c := by
        have h' : φ ^ r * a = φ ^ r * (φ * c) := by rw [hc]; ring
        exact mul_left_cancel₀ (pow_ne_zero r hφ0) h'
      simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton.mpr ⟨c, this⟩
    have hg : Function.Surjective g := Submodule.factor_surjective hJI
    have H : Function.Exact f g := by
      intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective J y
      change (Submodule.Quotient.mk a : P ⧸ I) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Set.mem_range]
      constructor
      · intro ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
        exact ⟨Submodule.Quotient.mk b, rfl⟩
      · rintro ⟨x, hx⟩
        obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective S x
        simp only [f, Submodule.liftQ_apply, m, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mulLeft_apply, Submodule.mkQ_apply] at hx
        rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero] at hx
        have := I.sub_mem (Ideal.mem_span_singleton.mpr ⟨b, rfl⟩ : φ ^ r * b ∈ I) (hJI hx)
        simpa using this
    rw [Module.length_eq_add_of_exact f g hf hg H, h1, ih]
    push_cast; ring

/-- The image of a principal ideal under a ring homomorphism is principal, generated by the image of
the generator. -/
theorem principal_ideal_image (R A : Type) [CommRing R] [CommRing A] (phi : R →+* A) (f : R) :
    (Ideal.span {f}).map phi = Ideal.span {phi f} := by
  rw [Ideal.map_span, Set.image_singleton]

private theorem map_span_colon_pow {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e F : S)
    (d : ℕ) (f : R) (h : φ f = e ^ d * F) (inj : Function.Injective (fun y : S ↦ e * y)) :
    ((Ideal.span {f}).map φ).colon {e ^ d} = Ideal.span {F} := by
  have injd : IsLeftRegular (e ^ d) := IsLeftRegular.pow d inj
  rw [principal_ideal_image, h]
  ext u
  rw [Submodule.mem_colon_singleton, Ideal.mem_span_singleton', Ideal.mem_span_singleton']
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, injd ?_⟩
    have : w * (e ^ d * F) = u * e ^ d := hw
    change e ^ d * (w * F) = e ^ d * u
    rw [← mul_assoc, mul_comm (e ^ d) w, mul_assoc, this]; ring
  · rintro ⟨w, hw⟩
    exact ⟨w, by change w * (e ^ d * F) = u • e ^ d; rw [smul_eq_mul, ← hw]; ring⟩

private theorem chartBase_eq_pow_mul (R : Type) [CommRing R] (t x : R) (d : ℕ) (f : R)
    (c : Fin (d + 1) → R) (hc : f = ∑ i : Fin (d + 1), c i * t ^ (d - i.val) * x ^ i.val) :
    chartBase R t x f = chartBase R t x t ^ d * ∑ i : Fin (d+1), algebraMap R (BlowupChart R t x)
    (c i) * (chartSlope R t x)^i.val := by
  subst hc
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : i.val ≤ d := Nat.lt_succ_iff.mp i.isLt
  have hx : chartBase R t x x = chartBase R t x t * chartSlope R t x :=
    (blowup_chart_relation R t x).symm
  have hd : chartBase R t x t ^ d =
      chartBase R t x t ^ (d - i.val) * chartBase R t x t ^ i.val := by
    rw [← pow_add]; congr 1; omega
  simp only [map_mul, map_pow, hx, mul_pow, hd]
  change _ = _ * (chartBase R t x (c i) * _)
  ring

private theorem chartBase_eq_pow_mul_opposite (R : Type) [CommRing R] (t x : R) (d : ℕ) (f : R)
    (c : Fin (d + 1) → R) (hc : f = ∑ i : Fin (d + 1), c i * t ^ (d - i.val) * x ^ i.val) :
    chartBase R x t f = chartBase R x t x ^ d * ∑ i : Fin (d+1), algebraMap R (BlowupChart R x t)
    (c i) * (chartSlope R x t)^(d - i.val) := by
  subst hc
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : i.val ≤ d := Nat.lt_succ_iff.mp i.isLt
  have ht : chartBase R x t t = chartBase R x t x * chartSlope R x t :=
    (blowup_chart_relation R x t).symm
  have hd : chartBase R x t x ^ d =
      chartBase R x t x ^ (d - i.val) * chartBase R x t x ^ i.val := by
    rw [← pow_add]; congr 1; omega
  simp only [map_mul, map_pow, ht, mul_pow, hd]
  change _ = _ * (chartBase R x t (c i) * _)
  ring

/-! ### Strict transforms on the concrete surface -/

private theorem maximalIdeal_completedLocalAt (A : Type) [CommRing A] (Q : Ideal A) [Q.IsPrime]
    [IsNoetherianRing A] :
    IsLocalRing.maximalIdeal (CompletedLocalAt A Q) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).map
        (localCompletionMap (Localization.AtPrime Q)) := by
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  exact AdicCompletion.maximalIdeal_eq_map

section ConcreteSurface

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
  (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)

-- Abbreviations for the concrete surface and its two parameters.
local notation "𝒮" => ConcreteSurface O pi u a b
local notation "𝒯" => surfaceT O pi u a b
local notation "𝒳" => surfaceX O pi u a b

include hpi ha

/-- On the concrete surface, a child generator at an exceptional point of either chart (left point
or point at infinity) whose curve meets the exceptional divisor with finite length is transverse
to it: the two multiplications are injective and the curve ideal contains a power of the maximal
ideal. -/
theorem child_ideal_generator_transverse_finite (P : Ideal (BlowupChart 𝒮 𝒯 𝒳)) [P.IsMaximal]
    [P.IsPrime] (hP : chartBase 𝒮 𝒯 𝒳 𝒯 ∈ P) (g : CompletedLocalAt (BlowupChart 𝒮 𝒯 𝒳) P)
    (n : ℕ) (hg : Module.length (CompletedLocalAt (BlowupChart 𝒮 𝒯 𝒳) P)
      (CompletedLocalAt (BlowupChart 𝒮 𝒯 𝒳) P ⧸ (Ideal.span {g} ⊔
        Ideal.span {completedPointMap (BlowupChart 𝒮 𝒯 𝒳) P (chartBase 𝒮 𝒯 𝒳 𝒯)})) = (n : ℕ∞))
    (Pinf : Ideal (BlowupChart 𝒮 𝒳 𝒯)) [Pinf.IsMaximal] [Pinf.IsPrime]
    (hx : chartBase 𝒮 𝒳 𝒯 𝒳 ∈ Pinf) (hW : chartSlope 𝒮 𝒳 𝒯 ∈ Pinf)
    (ginf : CompletedLocalAt (BlowupChart 𝒮 𝒳 𝒯) Pinf) (m : ℕ)
    (hginf : Module.length (CompletedLocalAt (BlowupChart 𝒮 𝒳 𝒯) Pinf)
      (CompletedLocalAt (BlowupChart 𝒮 𝒳 𝒯) Pinf ⧸ (Ideal.span {ginf} ⊔
        Ideal.span {completedPointMap (BlowupChart 𝒮 𝒳 𝒯) Pinf (chartBase 𝒮 𝒳 𝒯 𝒳)})) =
        (m : ℕ∞)) :
    (Function.Injective (fun w : CompletedLocalAt (BlowupChart 𝒮 𝒯 𝒳) P ⧸ Ideal.span {g} =>
        Ideal.Quotient.mk (Ideal.span {g})
          (completedPointMap (BlowupChart 𝒮 𝒯 𝒳) P (chartBase 𝒮 𝒯 𝒳 𝒯)) * w) ∧
      Function.Injective (fun w : CompletedLocalAt (BlowupChart 𝒮 𝒯 𝒳) P ⧸
          Ideal.span {completedPointMap (BlowupChart 𝒮 𝒯 𝒳) P (chartBase 𝒮 𝒯 𝒳 𝒯)} =>
        Ideal.Quotient.mk
          (Ideal.span {completedPointMap (BlowupChart 𝒮 𝒯 𝒳) P (chartBase 𝒮 𝒯 𝒳 𝒯)}) g * w) ∧
      ∃ L : ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
          (localCompletionMap (Localization.AtPrime P)))^L ≤
        finiteLocalCurveIdeal (BlowupChart 𝒮 𝒯 𝒳) P (chartBase 𝒮 𝒯 𝒳 𝒯) g 1) ∧
    (Function.Injective (fun w : CompletedLocalAt (BlowupChart 𝒮 𝒳 𝒯) Pinf ⧸ Ideal.span {ginf} =>
        Ideal.Quotient.mk (Ideal.span {ginf})
          (completedPointMap (BlowupChart 𝒮 𝒳 𝒯) Pinf (chartBase 𝒮 𝒳 𝒯 𝒳)) * w) ∧
      Function.Injective (fun w : CompletedLocalAt (BlowupChart 𝒮 𝒳 𝒯) Pinf ⧸
          Ideal.span {completedPointMap (BlowupChart 𝒮 𝒳 𝒯) Pinf (chartBase 𝒮 𝒳 𝒯 𝒳)} =>
        Ideal.Quotient.mk
          (Ideal.span {completedPointMap (BlowupChart 𝒮 𝒳 𝒯) Pinf (chartBase 𝒮 𝒳 𝒯 𝒳)}) ginf * w) ∧
      ∃ L : ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime Pinf)).map
          (localCompletionMap (Localization.AtPrime Pinf)))^L ≤
        finiteLocalCurveIdeal (BlowupChart 𝒮 𝒳 𝒯) Pinf (chartBase 𝒮 𝒳 𝒯 𝒳) ginf 1) := by
  have := blowupChart_concrete_isNoetherianRing O pi u a b 𝒯 𝒳
  have := blowupChart_concrete_isNoetherianRing O pi u a b 𝒳 𝒯
  obtain ⟨O', _, _, _, _, _, pi', u', a', b', hpi', ha', ψ, hψ⟩ :=
    concrete_left_point_completion_is_surface O pi hpi u a b ha P hP
  obtain ⟨_, -, _, -⟩ := concrete_left_point_completion_instances O pi hpi u a b ha P hP
  obtain ⟨-, ⟨ψi, hψi⟩, _, ⟨_, -⟩, hregi⟩ :=
    concrete_infinity_point_completion O pi hpi u a b ha Pinf hx hW
  have key := transverse_of_concreteSurface_equiv _ O' pi' hpi' u' a' b' ha' ψ _ g hψ n hg
    (concrete_left_point_exceptional_regular O pi hpi u a b ha P hP)
  have keyi := transverse_of_concreteSurface_equiv _ O pi hpi (xSubstUnit O u) (a + b) a
    (Nat.add_pos_left ha b) ψi _ ginf hψi m hginf hregi
  obtain ⟨L, hL⟩ := key.2.2
  obtain ⟨Li, hLi⟩ := keyi.2.2
  exact ⟨⟨key.1, key.2.1, L, by simpa [← maximalIdeal_completedLocalAt _ P, finiteLocalCurveIdeal]
      using hL⟩,
    ⟨keyi.1, keyi.2.1, Li, by
      simpa [← maximalIdeal_completedLocalAt _ Pinf, finiteLocalCurveIdeal] using hLi⟩⟩

/-- At the point at infinity of the concrete surface, the intersection length of the strict
transform of `∑ cᵢ tᵈ⁻ⁱ xⁱ` with the exceptional divisor is `d - deg H`, where `H = ∑ c̄ᵢ Zⁱ` is
the residue polynomial. -/
theorem concrete_infinity_strict_transform_multiplicity (d : ℕ) (c : Fin (d + 1) → 𝒮)
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {𝒯, 𝒳}) [IsLocalRing 𝒮]
    (P : Ideal (BlowupChart 𝒮 𝒳 𝒯)) [P.IsMaximal] [P.IsPrime]
    (hx : chartBase 𝒮 𝒳 𝒯 𝒳 ∈ P) (hW : chartSlope 𝒮 𝒳 𝒯 ∈ P) :
    Module.length (CompletedLocalAt (BlowupChart 𝒮 𝒳 𝒯) P)
      (CompletedLocalAt (BlowupChart 𝒮 𝒳 𝒯) P ⧸
        Ideal.span {completedPointMap (BlowupChart 𝒮 𝒳 𝒯) P
          (∑ i : Fin (d+1),
            algebraMap 𝒮 (BlowupChart 𝒮 𝒳 𝒯) (c i) * chartSlope 𝒮 𝒳 𝒯 ^ (d - i.val)),
        completedPointMap (BlowupChart 𝒮 𝒳 𝒯) P (chartBase 𝒮 𝒳 𝒯 𝒳)}) =
    ((d - (∑ i : Fin (d+1), Polynomial.C (IsLocalRing.residue 𝒮 (c i)) * Polynomial.X^i.val :
      Polynomial (IsLocalRing.ResidueField 𝒮)).natDegree : ℕ) : ℕ∞) := by
  have hP := (concrete_infinity_point_completion O pi hpi u a b ha P hx hW).1
  obtain ⟨ψ, hb, hs, -⟩ := x_chart_infinity_completion_equiv O pi hpi u a b ha P hP
  obtain ⟨q, hq⟩ := concrete_surface_quotient_T_equiv O pi hpi (xSubstUnit O u) (a + b) a (by omega)
  obtain ⟨e0, he0⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  have hmax := concrete_surface_maximalIdeal_eq O pi hpi u a b ha
  let κ : IsLocalRing.ResidueField 𝒮 ≃+* IsLocalRing.ResidueField O :=
    (Ideal.quotEquivOfEq hmax).trans e0
  have hκ : ∀ s : TwoSeries O, κ (IsLocalRing.residue _ (surfaceMk O pi u a b s)) =
      IsLocalRing.residue O (MvPowerSeries.constantCoeff s) := fun s ↦ by
    change e0 (Ideal.quotEquivOfEq hmax (Ideal.Quotient.mk _ (surfaceMk O pi u a b s))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact he0 s
  have hxT : ψ (completedPointMap _ P (chartBase _ _ _ 𝒳)) =
      surfaceT O pi (xSubstUnit O u) (a + b) a := by
    have h := hb (axisX O)
    rwa [(chartSubst_apply_generators O 0).2.2.2.2.2.1] at h
  rw [← RingEquiv.symm_apply_apply ψ (completedPointMap _ P (chartBase _ _ _ 𝒳)), hxT,
    (concrete_surface_equiv_curve_length_and_regular _ O pi (xSubstUnit O u) (a + b) a ψ q _).1]
  let Ψ : BlowupChart 𝒮 𝒳 𝒯 →+* PowerSeries (IsLocalRing.ResidueField O) :=
    q.toRingHom.comp ((Ideal.Quotient.mk _).comp (ψ.toRingHom.comp (completedPointMap _ P)))
  have hΨc : ∀ r : 𝒮, Ψ (algebraMap _ _ r) = PowerSeries.C (κ (IsLocalRing.residue _ r)) :=
      fun r ↦ by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    change q (Ideal.Quotient.mk _ (ψ (completedPointMap _ P (chartBase _ _ _
      (surfaceMk O pi u a b s))))) = _
    rw [hb, hq, residueKillT_xChartSubst O pi hpi]; exact congrArg _ (hκ s).symm
  have hΨW : Ψ (chartSlope _ _ _) = PowerSeries.X := by
    change q (Ideal.Quotient.mk _ (ψ (completedPointMap _ P _))) = _
    rw [hs, show surfaceX O pi (xSubstUnit O u) (a + b) a = surfaceMk _ _ _ _ _ (axisX O) from rfl,
      hq, (residueKillT_apply_ker O pi hpi).2.2.1]
  rw [show ∀ y, q (Ideal.Quotient.mk _ (ψ (completedPointMap _ P y))) = Ψ y from fun _ ↦ rfl]
  simp only [map_sum, map_mul, map_pow, hΨc, hΨW]
  obtain ⟨i, hi⟩ := hne
  refine order_reflected_sum κ.toRingHom d _ ⟨i, ?_⟩
  rwa [Ne, IsLocalRing.residue_eq_zero_iff, hmax]

/-- On the concrete surface, the strict transform of `(∑ cᵢ t^(d-i) xⁱ)` is generated by `∑ cᵢ zⁱ`
at a left exceptional point and by `∑ cᵢ w^(d-i)` at the point at infinity. -/
theorem concrete_strict_transform_generators (d : ℕ) (f : 𝒮) (c : Fin (d + 1) → 𝒮)
    (hc : f = ∑ i : Fin (d + 1), c i * 𝒯 ^ (d - i.val) * 𝒳 ^ i.val) (P : Ideal (BlowupChart 𝒮 𝒯 𝒳))
    [P.IsMaximal] [P.IsPrime] (hP : chartBase 𝒮 𝒯 𝒳 𝒯 ∈ P) (Pinf : Ideal (BlowupChart 𝒮 𝒳 𝒯))
    [Pinf.IsMaximal] [Pinf.IsPrime] (hx : chartBase 𝒮 𝒳 𝒯 𝒳 ∈ Pinf)
    (hW : chartSlope 𝒮 𝒳 𝒯 ∈ Pinf) :
    strictTransformAt 𝒮 𝒯 𝒳 P d (Ideal.span {f}) = Ideal.span {completedPointMap
      (BlowupChart 𝒮 𝒯 𝒳) P
      (∑ i : Fin (d+1), algebraMap 𝒮 (BlowupChart 𝒮 𝒯 𝒳) (c i) * chartSlope 𝒮 𝒯 𝒳 ^ i.val)} ∧
    strictTransformAt 𝒮 𝒳 𝒯 Pinf d (Ideal.span {f}) = Ideal.span {completedPointMap
      (BlowupChart 𝒮 𝒳 𝒯) Pinf
      (∑ i : Fin (d+1),
        algebraMap 𝒮 (BlowupChart 𝒮 𝒳 𝒯) (c i) * chartSlope 𝒮 𝒳 𝒯 ^ (d - i.val))} := by
  obtain ⟨_, _, _, inj⟩ :=
    (concrete_infinity_point_completion O pi hpi u a b ha Pinf hx hW).2
  refine ⟨map_span_colon_pow _ _ _ d f ?_
    (concrete_left_point_exceptional_regular O pi hpi u a b ha P hP),
    map_span_colon_pow _ _ _ d f ?_ inj⟩ <;> simp only [RingHom.comp_apply] <;>
    rw [← map_pow, ← map_mul]
  exacts [congrArg _ (chartBase_eq_pow_mul _ _ _ d f c hc),
    congrArg _ (chartBase_eq_pow_mul_opposite _ _ _ d f c hc)]

end ConcreteSurface

/-- Multiplying the generator of a principal ideal by a unit does not change the ideal. -/
theorem principal_ideal_unit_invariance (R : Type) [CommRing R] (f : R) (u : Rˣ) :
    Ideal.span {(u : R)*f} = Ideal.span {f} :=
  Ideal.span_singleton_mul_left_unit u.isUnit f

end SurfaceBlowup
