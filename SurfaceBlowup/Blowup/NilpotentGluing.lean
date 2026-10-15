/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.PointTransport
import Mathlib.Algebra.Group.NatPowAssoc

/-!
# Nilpotent gluing of exceptional levels

Gluing of the two chart descriptions of the exceptional levels of a point blow-up. The overlap
layers are Laurent polynomial modules, which makes the truncated Čech differential injective in
negative twist; the level kernels of finitely many transverse curve germs are principal, with
generators that are nonzerodivisors on all exceptional levels; and on the concrete surface we
compute residue series of strict transforms and boundary contact numbers.

## Main results

* `SurfaceBlowup.overlap_layer_laurent_coordinates`: the overlap layers are Laurent polynomial
  modules over `R ⧸ (t, x)`.
* `SurfaceBlowup.actual_negative_twist_kernel_zero`: the truncated Čech differential is injective
  in negative twist.
* `SurfaceBlowup.finite_support_level_kernels_principal`: level kernels of finitely many transverse
  curve germs are principal; `SurfaceBlowup.finite_support_level_generator_regular` and
  `SurfaceBlowup.overlap_level_generator_regular`: their generators are nonzerodivisors on all
  exceptional levels.
* `SurfaceBlowup.concrete_strict_transform_residue_series`: residue series of strict transforms at
  exceptional points of the concrete surface.
* `SurfaceBlowup.concrete_infinity_boundary_contact`,
  `SurfaceBlowup.concrete_zero_boundary_contact`: boundary contact numbers of a degree-`d` form
  with `T = 0` and `X = 0`.

Provenance: `Thm_SurfaceBlowupV2_` nodes `overlap_layer_laurent_coordinates`,
`actual_negative_twist_kernel_zero`, `principal_lift_from_nilpotent_saturation`,
`finite_curve_support_{principal_lift,generator_exists}`, `finite_support_level_kernels_principal`,
`principal_power_unit_lift`, `reduced_form_eq_of_residue_coeff`,
`curve_datum_surj_and_inf_clauses`, `regular_element_on_all_principal_power_quotients`,
`finite_support_level_generator_regular`, `overlap_level_generator_regular`,
`residueKillT_chartSubst`, `chart_point_residue_series_formula`,
`concrete_strict_transform_residue_series`, `residueKillX_apply_ker`,
`concrete_surface_quotient_X_equiv`, `concrete_{infinity,zero}_boundary_contact`.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-! ### Laurent coordinates on the overlap layers -/

/-- Each exceptional layer of the overlap is `R`-linearly isomorphic to the Laurent polynomial ring
`(R/(t,x))[Z, Z⁻¹]`, the monomial `r Z^ℓ` corresponding to the layer class of `r · z^ℓ`. -/
theorem overlap_layer_laurent_coordinates (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (j : ℕ) :
    ∃ L : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer (BlowupOverlap R t x)
    ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j, ∀ r : R,
    ∀ ell : ℤ, (L (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap (BlowupOverlap R t x)
    ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j
    ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x r) * selfZPow
      (chartSlope R t x) (BlowupOverlap R t x) ell) := by
  set A := BlowupChart R t x
  set C := BlowupOverlap R t x
  set z : A := chartSlope R t x
  set a : A := chartBase R t x t
  set e : C := algebraMap A C a with he_def
  have hA : Function.Injective (fun b : A ↦ a * b) :=
    blowup_exceptional_parameter_regular R t x hreg
  have hC : Function.Injective (fun b : C ↦ e * b) :=
    nonzerodivisor_survives_localization A a z hA
  obtain ⟨L1, hL1⟩ := principal_layer_quotient_equiv C e j hC
  obtain ⟨L2, hL2⟩ := localization_principal_quotient_commute A a z 1
  obtain ⟨L4, hL4b, hL4s⟩ := exceptional_overlap_is_laurent_line R t x
  -- step a
  let Φa : (C ⧸ Ideal.span {e}) ≃+* PrincipalPowerQuotient C e 1 :=
    Ideal.quotEquivOfEq (by rw [pow_one])
  -- step c
  have hI : (Ideal.span {a}) ^ 1 = exceptionalLevelIdeal R t x 1 := by
    simp only [exceptionalLevelIdeal, pow_one]; rfl
  let φ : PrincipalPowerQuotient A a 1 ≃+* ExceptionalChartLevel R t x 1 :=
    Ideal.quotEquivOfEq hI
  have hφ : ∀ b : A, φ (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b := fun b ↦ rfl
  let Φc : Localization.Away (Ideal.Quotient.mk ((Ideal.span {a})^1) z) ≃+*
      ExceptionalOverlapLevel R t x 1 :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers
        (Ideal.Quotient.mk ((Ideal.span {a})^1) z))
      (T := Submonoid.powers (levelSlope R t x 1)) _ _ φ (by
        rw [Submonoid.map_powers]; rfl)
  let Ψ : (C ⧸ Ideal.span {e}) ≃+* LaurentPolynomial (R ⧸ Ideal.span {t,x}) :=
    ((Φa.trans L2).trans Φc).trans L4
  have hΨ (b : A) : Ψ (Ideal.Quotient.mk _ (algebraMap A C b)) =
      L4 (levelOverlapMap R t x 1 (Ideal.Quotient.mk _ b)) := by
    simp only [Ψ, RingEquiv.trans_apply]
    congr 1
    have h1 : Φa (Ideal.Quotient.mk _ (algebraMap A C b)) =
        Ideal.Quotient.mk ((Ideal.span {e})^1) (algebraMap A C b) := rfl
    rw [h1, hL2]
    simp only [Φc]
    rw [IsLocalization.ringEquivOfRingEquiv_eq]
    rfl
  have hbase : ∀ r : R, Ψ (Ideal.Quotient.mk _ (algebraMap A C (chartBase R t x r))) =
      LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) :=
    fun r ↦ by rw [hΨ, ← hL4b]; rfl
  have hslope : Ψ (Ideal.Quotient.mk _ (algebraMap A C z)) = LaurentPolynomial.T 1 := by
    rw [hΨ, ← hL4s]; rfl
  have hz1 : selfZPow z C 1 = algebraMap A C z := by
    simpa using selfZPow_natCast z C 1
  have hT (ell : ℤ) : Ψ (Ideal.Quotient.mk _ (selfZPow z C ell)) = LaurentPolynomial.T ell := by
    induction ell using Int.induction_on with
    | zero => simp [LaurentPolynomial.T_zero]
    | succ i ih =>
      rw [selfZPow_add, map_mul, map_mul, ih, hz1, hslope, ← LaurentPolynomial.T_add]
    | pred i ih =>
      have h : selfZPow z C (-(i:ℤ)) = selfZPow z C (-(i:ℤ) - 1) * selfZPow z C 1 := by
        rw [← selfZPow_add]; congr 1; ring
      rw [h, map_mul, map_mul, hz1, hslope] at ih
      calc Ψ (Ideal.Quotient.mk _ (selfZPow z C (-(i:ℤ) - 1)))
          = Ψ (Ideal.Quotient.mk _ (selfZPow z C (-(i:ℤ) - 1))) * LaurentPolynomial.T 1 *
              LaurentPolynomial.T (-1) := by
            rw [LaurentPolynomial.mul_T_assoc]; simp [LaurentPolynomial.T_zero]
        _ = LaurentPolynomial.T (-(i:ℤ) - 1) := by
            rw [ih, ← LaurentPolynomial.T_add]; congr 1
  let Ψa : (C ⧸ Ideal.span {e}) ≃ₐ[R] LaurentPolynomial (R ⧸ Ideal.span {t,x}) :=
    AlgEquiv.ofRingEquiv (f := Ψ) fun r ↦ by rw [LaurentPolynomial.algebraMap_apply]; exact hbase r
  refine ⟨Ψa.symm.toLinearEquiv.trans (L1.restrictScalars R), fun r ell ↦ ?_⟩
  have hpre : Ψa.symm (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell) = Ideal.Quotient.mk _
        (algebraMap A C (chartBase R t x r) * selfZPow z C ell) := by
    rw [AlgEquiv.symm_apply_eq]
    change _ = Ψ _
    rw [map_mul, map_mul, hbase, hT]
  simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply,
      LinearEquiv.restrictScalars_apply]
  rw [hpre, hL1]

/-- `principalLayerMap` sends `a` to the class of `a eʲ`. -/
theorem principalLayerMap_apply_eq_mk (A : Type) [CommRing A] (e : A) (j : ℕ) (a : A) :
    principalLayerMap A e j a = Ideal.Quotient.mk ((Ideal.span {e})^(j+1)) (a * e^j) := by
  simp [principalLayerMap, LinearMap.toSpanSingleton_apply, Algebra.smul_def]

/-- `(1/w)^i = w^(-i)` in a localization away from `w`. -/
theorem invSelf_pow_eq_selfZPow (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (w : A)
    [IsLocalization.Away w B] (i : ℕ) :
    (IsLocalization.Away.invSelf (S := B) w)^i = selfZPow w B (-(i:ℤ)) := by
  rw [selfZPow_neg_natCast, IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow, one_pow]
  congr 1

/-- The algebra map to a blow-up chart is `chartBase`. -/
theorem algebraMap_chart_eq_chartBase (R : Type) [CommRing R] (t x r : R) :
    algebraMap R (BlowupChart R t x) r = chartBase R t x r := rfl

/-! ### Injectivity of the truncated Čech differential in negative twist -/

/-- The restriction `beta.right` is compatible with the structure maps from `R`. -/
theorem beta_right_chartBase {R : Type} [CommRing R] {t x : R}
    (beta : BlowupRestriction R t x) (r : R) : beta.right (chartBase R x t r) =
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x r) :=
  (beta.right.commutes r).trans (IsScalarTower.algebraMap_apply R _ _ r)

private lemma beta_monomial_mul_invSelf_pow (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (r : R) (i j d : ℕ) :
    beta.right (chartBase R x t r * chartSlope R x t ^ i * chartBase R x t x ^ j) *
      IsLocalization.Away.invSelf (chartSlope R t x) ^ d =
    algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x r) *
      selfZPow (chartSlope R t x) (BlowupOverlap R t x) ((j:ℤ) - d + -(i:ℤ)) *
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ^ j := by
  have hβr := beta_right_chartBase beta
  have hz : (j:ℤ) - d + -(i:ℤ) = -(i:ℤ) + j + -(d:ℤ) := by ring
  rw [map_mul, map_mul, map_pow, map_pow, hβr, hβr, beta.slope, ← blowup_chart_relation, map_mul,
    hz, selfZPow_add, selfZPow_add, ← invSelf_pow_eq_selfZPow, ← invSelf_pow_eq_selfZPow,
    selfZPow_natCast, mul_pow]
  ring

private lemma left_layer_coordinates_reduce (R : Type) [CommRing R] (t x : R) (j : ℕ)
    (LA : Polynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer (BlowupChart R t x)
      (chartBase R t x t) j)
    (hLA : ∀ r : R, ∀ i : ℕ,
      (LA (Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) * Polynomial.X^i)).val =
      principalLayerMap (BlowupChart R t x) (chartBase R t x t) j
        (chartBase R t x r * (chartSlope R t x)^i))
    (LO : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer (BlowupOverlap R t x)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j)
    (hLO : ∀ r : R, ∀ ell : ℤ, (LO (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap (BlowupOverlap R t x)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x r) * selfZPow
        (chartSlope R t x) (BlowupOverlap R t x) ell))
    (hψA : (Ideal.span {chartBase R t x t})^(j+1) ≤ ((Ideal.span
      {algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t)})^(j+1)).comap
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)))
    (P : Polynomial (R ⧸ Ideal.span {t,x})) :
    Ideal.quotientMap _ (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) hψA (LA P).val =
      (LO P.toLaurent).val := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Submodule.coe_add, map_add, hp, hq, map_add, map_add,
      Submodule.coe_add]
  | monomial i c =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← Polynomial.C_mul_X_pow_eq_monomial, hLA, Polynomial.toLaurent_C_mul_X_pow, hLO,
      principalLayerMap_apply_eq_mk, principalLayerMap_apply_eq_mk, Ideal.quotientMap_mk,
      selfZPow_natCast]
    simp only [map_mul, map_pow]

private lemma right_layer_coordinates_reduce_twist (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ)
    (LB : Polynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer (BlowupChart R x t)
      (chartBase R x t x) j)
    (hLB : ∀ r : R, ∀ i : ℕ,
      (LB (Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) * Polynomial.X^i)).val =
      principalLayerMap (BlowupChart R x t) (chartBase R x t x) j
        (chartBase R x t r * (chartSlope R x t)^i))
    (LO : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer (BlowupOverlap R t x)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j)
    (hLO : ∀ r : R, ∀ ell : ℤ, (LO (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap (BlowupOverlap R t x)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x r) * selfZPow
        (chartSlope R t x) (BlowupOverlap R t x) ell))
    (hψB : (Ideal.span {chartBase R x t x})^(j+1) ≤ ((Ideal.span
      {algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t)})^(j+1)).comap
      beta.right.toRingHom)
    (Q : Polynomial (R ⧸ Ideal.span {t,x})) :
    Ideal.quotientMap _ beta.right.toRingHom hψB (LB Q).val *
      Ideal.Quotient.mk _ ((IsLocalization.Away.invSelf (chartSlope R t x))^d) =
      (LO (LaurentPolynomial.T ((j:ℤ) - d) * LaurentPolynomial.invert Q.toLaurent)).val := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Submodule.coe_add, map_add, add_mul, hp, hq]
    simp only [map_add, mul_add, Submodule.coe_add]
  | monomial i c =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hT : LaurentPolynomial.T ((j:ℤ) - d) * LaurentPolynomial.invert
        (Polynomial.toLaurent (Polynomial.C (Ideal.Quotient.mk (Ideal.span {t, x}) r) *
          Polynomial.X ^ i)) = LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t, x}) r) *
          LaurentPolynomial.T ((j:ℤ) - d + -(i:ℤ)) := by
      rw [Polynomial.toLaurent_C_mul_X_pow]
      simp only [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
      rw [mul_left_comm, ← LaurentPolynomial.T_add]
    rw [← Polynomial.C_mul_X_pow_eq_monomial, hLB, hT, hLO, principalLayerMap_apply_eq_mk,
        principalLayerMap_apply_eq_mk, Ideal.quotientMap_mk, ← map_mul]
    congr 1
    exact beta_monomial_mul_invSelf_pow R t x beta r i j d

/-- An element of `(e) ^ j` defines an element of the `j`-th principal layer `(e)^j / (e)^(j+1)`. -/
theorem mk_mem_principalLayer {A : Type} [CommRing A] (e : A) (j : ℕ) {a : A}
    (ha : a ∈ (Ideal.span {e}) ^ j) :
    Ideal.Quotient.mk ((Ideal.span {e})^(j+1)) a ∈ PrincipalLayer A e j := by
  rw [LinearMap.mem_ker]
  simpa only [principalPowerReduction, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] using ha

private lemma cech_kernel_step (R : Type) [CommRing R] (t x : R) (hreg : RegularParameterPair R t x)
    (beta : BlowupRestriction R t x) (hregSwap : RegularParameterPair R x t) (d j : ℕ) (hj : j < d)
    (a : BlowupChart R t x) (b : BlowupChart R x t) (ha : a ∈ (Ideal.span {chartBase R t x t}) ^ j)
    (hb : b ∈ (Ideal.span {chartBase R x t x}) ^ j)
    (hD : fullCechDifferential R t x beta d (a, b) ∈
      (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
          (chartBase R t x t)}) ^ (j + 1)) :
    a ∈ (Ideal.span {chartBase R t x t})^(j+1) ∧ b ∈ (Ideal.span {chartBase R x t x})^(j+1) := by
  set ι := algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
  set eA := chartBase R t x t
  set eB := chartBase R x t x
  set eO := ι eA
  set W := chartSlope R t x
  have hβeB : beta.right eB = eO * ι W := by
    rw [beta_right_chartBase, ← blowup_chart_relation, map_mul]
  obtain ⟨LA, hLA⟩ := chart_layer_polynomial_coordinates R t x hreg j
  have hB := chart_layer_polynomial_coordinates R x t hregSwap j
  rw [Set.pair_comm x t] at hB
  obtain ⟨LB, hLB⟩ := hB
  obtain ⟨LO, hLO⟩ := overlap_layer_laurent_coordinates R t x hreg j
  -- the reduction maps
  have hψA : (Ideal.span {eA})^(j+1) ≤ ((Ideal.span {eO})^(j+1)).comap ι := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, Set.image_singleton]
  have hψB : (Ideal.span {eB})^(j+1) ≤ ((Ideal.span {eO})^(j+1)).comap beta.right.toRingHom := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    apply Ideal.pow_right_mono
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change beta.right eB ∈ _
    rw [hβeB]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hPA := left_layer_coordinates_reduce R t x j LA hLA LO hLO hψA
  have hPB := right_layer_coordinates_reduce_twist R t x beta d j LB hLB LO hLO hψB
  set P := LA.symm ⟨_, mk_mem_principalLayer eA j ha⟩ with hPdef
  set Q := LB.symm ⟨_, mk_mem_principalLayer eB j hb⟩ with hQdef
  have hP : (LA P).val = Ideal.Quotient.mk _ a := by rw [hPdef, LinearEquiv.apply_symm_apply]
  have hQ : (LB Q).val = Ideal.Quotient.mk _ b := by rw [hQdef, LinearEquiv.apply_symm_apply]
  have key : LO (P.toLaurent - LaurentPolynomial.T ((j:ℤ) - d) *
      LaurentPolynomial.invert Q.toLaurent) = 0 := by
    apply Subtype.ext
    rw [map_sub, Submodule.coe_sub, ← hPA, ← hPB, hP, hQ, Ideal.quotientMap_mk,
      Ideal.quotientMap_mk, ← map_mul, ← map_sub, ZeroMemClass.coe_zero,
      Ideal.Quotient.eq_zero_iff_mem]
    convert hD using 1
    change _ = ι a - _ * _
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    ring
  have hz := (LinearEquiv.map_eq_zero_iff LO).1 key
  obtain ⟨hP0, hQ0⟩ := negative_laurent_twist_has_no_kernel _ ((j:ℤ) - d) (by omega) P Q hz
  constructor
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← hP, hP0, map_zero]; rfl
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← hQ, hQ0, map_zero]; rfl

/-- In negative twist (`n ≤ d`), the finite Čech differential of the two-chart cover, truncated at
level `n`, is injective. -/
theorem actual_negative_twist_kernel_zero (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
    (hregSwap : RegularParameterPair R x t) (d n : ℕ) (hn : n ≤ d)
    (h : cechInputLattice R t x n ≤ (cechOutputLattice R t x n).comap
      (fullCechDifferential R t x beta d)) :
    Function.Injective (finiteCechDifferential R t x beta d n h) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨a, b⟩ := z
    rw [finiteCechDifferential, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    rw [Submodule.Quotient.mk_eq_zero]
    have hz' : fullCechDifferential R t x beta d (a, b) ∈
        (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
          (chartBase R t x t)})^n := hz
    have main (j : ℕ) (hj : j ≤ n) : a ∈ (Ideal.span {chartBase R t x t})^j ∧
        b ∈ (Ideal.span {chartBase R x t x})^j := by
      induction j with
      | zero => simp
      | succ j ih =>
        obtain ⟨ha, hb⟩ := ih (by omega)
        exact cech_kernel_step R t x hreg beta hregSwap d j (by omega) a b ha hb
          (Ideal.pow_le_pow_right (by omega) hz')
    exact main n le_rfl

/-! ### Principal level kernels -/

/-- If `e` is nilpotent and the ideal `J ∋ f` satisfies `J ≤ (f) + (e)` and `J ∩ (e) ≤ e J`, then
`J = (f)`. -/
private theorem principal_lift_from_nilpotent_saturation (A : Type) [CommRing A] (e f : A) (j : ℕ)
    (he : e ^ j = 0) (J : Ideal A) (hf : f ∈ J) (hred : J ≤ Ideal.span {f} ⊔ Ideal.span {e})
    (hsat : J ⊓ Ideal.span {e} ≤ Ideal.span {e} * J) : J = Ideal.span {f} := by
  have hfJ : Ideal.span {f} ≤ J := (Ideal.span_singleton_le_iff_mem J).mpr hf
  have step (x : A) (hx : x ∈ J) : ∃ a : A, ∃ y ∈ J, x = f * a + e * y := by
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (hred hx)
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hu
    have hvJ : v ∈ J := by
      rw [show v = x - a * f by rw [← huv]; ring]; exact J.sub_mem hx (hfJ hu)
    obtain ⟨w, hw, hew⟩ := (Ideal.mem_span_singleton_mul).mp (hsat ⟨hvJ, hv⟩)
    exact ⟨a, w, hw, by rw [← huv, ← hew]; ring⟩
  refine le_antisymm (fun x hx ↦ ?_) hfJ
  have key (k : ℕ) : ∃ a : A, ∃ y ∈ J, x = f * a + e ^ k * y := by
    induction k with
    | zero => exact ⟨0, x, hx, by ring⟩
    | succ k ih =>
      obtain ⟨a, y, hy, rfl⟩ := ih
      obtain ⟨b, z, hz, rfl⟩ := step y hy
      exact ⟨a + e ^ k * b, z, hz, by ring⟩
  obtain ⟨a, y, _, rfl⟩ := key j
  rw [he, zero_mul, add_zero]
  exact Ideal.mem_span_singleton'.mpr ⟨a, mul_comm a f⟩

/-- A level kernel of finitely many transverse curve germs is principal, generated by any of its
elements generating it modulo `e`. -/
private theorem finite_curve_support_principal_lift (A : Type) [CommRing A] [IsNoetherianRing A]
    (ι : Type) [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hP : Function.Injective P)
    (e : A) (j : ℕ) (hj : 0 < j) (g : ∀ i, CompletedLocalAt A (P i)) (L : ι → ℕ)
    (hfinite : ∀ i, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
      (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ finiteLocalCurveIdeal A (P i) e
      (g i) j) (htransverse : ∀ i, Function.Injective
      (fun a : CompletedLocalAt A (P i) ⧸ Ideal.span {g i} ↦ Ideal.Quotient.mk (Ideal.span {g i})
      (completedPointMap A (P i) e) * a)) (f : (A ⧸ (Ideal.span {e})^j))
    (hf : f ∈ finiteSupportLevelKernel A ι P (fun i ↦ finiteLocalCurveIdeal A (P i) e (g i) j) e j)
    (hred : finiteSupportLevelKernel A ι P (fun i ↦ finiteLocalCurveIdeal A (P i) e (g i) j) e j ≤
      Ideal.span {f} ⊔ Ideal.span {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)}) :
    finiteSupportLevelKernel A ι P (fun i ↦ finiteLocalCurveIdeal A (P i) e (g i) j) e j =
    Ideal.span {f} := by
  refine principal_lift_from_nilpotent_saturation _ _ f j ?_ _ hf hred
    (finite_curve_support_kernel_saturated A ι P hP e j hj g L hfinite htransverse)
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
  exact Ideal.subset_span rfl

/-- If the reduction modulo `e` of a level kernel of finitely many transverse curve germs is
generated by `h`, the kernel is generated by a lift of `h`. -/
private theorem finite_curve_support_generator_exists (A : Type) [CommRing A] [IsNoetherianRing A]
    (ι : Type) [Finite ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hP : Function.Injective P)
    (e : A) (j : ℕ) (hj : 0 < j) (g : ∀ i, CompletedLocalAt A (P i)) (L : ι → ℕ)
    (hfinite : ∀ i, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
      (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ finiteLocalCurveIdeal A (P i) e
      (g i) j) (htransverse : ∀ i, Function.Injective
      (fun a : CompletedLocalAt A (P i) ⧸ Ideal.span {g i} ↦ Ideal.Quotient.mk (Ideal.span {g i})
      (completedPointMap A (P i) e) * a)) (h : (A ⧸ (Ideal.span {e})^j) ⧸ Ideal.span
      {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)})
    (hred : (finiteSupportLevelKernel A ι P (fun i ↦ finiteLocalCurveIdeal A (P i) e (g i) j) e
      j).map (Ideal.Quotient.mk (Ideal.span {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)})) =
      Ideal.span {h}) :
    ∃ f : (A ⧸ (Ideal.span {e})^j), finiteSupportLevelKernel A ι P
    (fun i ↦ finiteLocalCurveIdeal A (P i) e (g i) j) e j = Ideal.span {f} ∧ Ideal.Quotient.mk
    (Ideal.span {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)}) f = h := by
  set I := finiteSupportLevelKernel A ι P (fun i ↦ finiteLocalCurveIdeal A (P i) e
      (g i) j) e j with hI
  set ρ := Ideal.Quotient.mk (Ideal.span {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)}) with hρ
  have hh : h ∈ I.map ρ := by rw [hred]; exact Ideal.mem_span_singleton_self h
  obtain ⟨f, hfI, hfh⟩ := (Ideal.mem_map_iff_of_surjective ρ Ideal.Quotient.mk_surjective).1 hh
  refine ⟨f, ?_, hfh⟩
  apply finite_curve_support_principal_lift A ι P hP e j hj g L hfinite htransverse f hfI
  intro x hx
  have hxm : ρ x ∈ Ideal.span {h} := by rw [← hred]; exact Ideal.mem_map_of_mem ρ hx
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hxm
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hdiff : x - a * f ∈ Ideal.span {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change ρ (x - a * f) = 0
    rw [map_sub, map_mul, hfh, ← hb, sub_self]
  have : x = a * f + (x - a * f) := by ring
  rw [this]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)) hdiff

private theorem isPrincipal_quotient_quotient (A : Type) [CommRing A] (e : A) (j : ℕ)
    (hPIR : IsPrincipalIdealRing (A ⧸ Ideal.span {e}))
    (I : Ideal ((A ⧸ (Ideal.span {e}) ^ j) ⧸ Ideal.span
        {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)})) :
    ∃ h, I = Ideal.span {h} := by
  let π : A →+* ((A ⧸ (Ideal.span {e})^j) ⧸ Ideal.span
      {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)}) :=
    (Ideal.Quotient.mk _).comp (Ideal.Quotient.mk _)
  have hπ : Function.Surjective π :=
    (Ideal.Quotient.mk_surjective).comp Ideal.Quotient.mk_surjective
  let ψ : A ⧸ Ideal.span {e} →+* ((A ⧸ (Ideal.span {e})^j) ⧸ Ideal.span
      {(Ideal.Quotient.mk ((Ideal.span {e})^j) e)}) :=
    Ideal.Quotient.lift (Ideal.span {e}) π (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp only [map_mul, π, RingHom.comp_apply]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), mul_zero])
  have hψ : Function.Surjective ψ := fun q ↦
    let ⟨a, ha⟩ := hπ q; ⟨Ideal.Quotient.mk _ a, ha⟩
  exact (@IsPrincipalIdealRing.principal _ _ (.of_surjective ψ hψ) I).principal

/-- On the chart, the level kernels of finitely many transverse curve germs at exceptional points
are principal at every level, generated by the images of chart elements `F j`. -/
theorem finite_support_level_kernels_principal (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)] (ι : Type)
    [Finite ι] (P : ι → Ideal (BlowupChart R t x)) [∀ i, (P i).IsMaximal]
    (hP : Function.Injective P) (_hPe : ∀ i, chartBase R t x t ∈ P i)
    (g : ∀ i, CompletedLocalAt (BlowupChart R t x) (P i))
    (htransverse : ∀ i, Function.Injective (fun a : CompletedLocalAt (BlowupChart R t x) (P i) ⧸
      Ideal.span {g i} => Ideal.Quotient.mk (Ideal.span {g i})
      (completedPointMap (BlowupChart R t x) (P i) (chartBase R t x t)) * a))
    (hfinite : ∀ j : ℕ, ∀ i, ∃ L : ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
      (localCompletionMap (Localization.AtPrime (P i))))^L ≤ finiteLocalCurveIdeal
      (BlowupChart R t x) (P i) (chartBase R t x t) (g i) j) :
    ∃ F : ℕ → BlowupChart R t x, ∀ j : ℕ, finiteSupportLevelKernel (BlowupChart R t x) ι P
    (fun i ↦ finiteLocalCurveIdeal (BlowupChart R t x) (P i) (chartBase R t x t) (g i) j)
    (chartBase R t x t) j = Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R t x t})^j)
      (F j)} := by
  obtain ⟨φ, -, -⟩ := exceptional_chart_is_affine_line R t x
  let _ : Field (R ⧸ Ideal.span ({t,x} : Set R)) := Ideal.Quotient.field _
  have hPIR1 : IsPrincipalIdealRing (ExceptionalChartLevel R t x 1) :=
    IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective
  have hEq : exceptionalLevelIdeal R t x 1 = Ideal.span {chartBase R t x t} := by
    simp [exceptionalLevelIdeal]
  have hPIR : IsPrincipalIdealRing (BlowupChart R t x ⧸ Ideal.span {chartBase R t x t}) :=
    IsPrincipalIdealRing.of_surjective (Ideal.quotEquivOfEq hEq).toRingHom
        (Ideal.quotEquivOfEq hEq).surjective
  have key (j : ℕ) : ∃ f : BlowupChart R t x, finiteSupportLevelKernel (BlowupChart R t x) ι P
      (fun i ↦ finiteLocalCurveIdeal (BlowupChart R t x) (P i) (chartBase R t x t) (g i) j)
      (chartBase R t x t) j = Ideal.span {Ideal.Quotient.mk
      ((Ideal.span {chartBase R t x t})^j) f} := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · refine ⟨0, ?_⟩
      have : Subsingleton (BlowupChart R t x ⧸ (Ideal.span {chartBase R t x t})^0) := by
        rw [pow_zero, Ideal.one_eq_top]; infer_instance
      exact Subsingleton.elim _ _
    · choose L hL using hfinite j
      obtain ⟨h, hh⟩ := isPrincipal_quotient_quotient (BlowupChart R t x) (chartBase R t x t) j hPIR
        ((finiteSupportLevelKernel (BlowupChart R t x) ι P
            (fun i ↦ finiteLocalCurveIdeal (BlowupChart R t x) (P i) (chartBase R t x t) (g i) j)
            (chartBase R t x t) j).map (Ideal.Quotient.mk _))
      obtain ⟨f, hf, -⟩ := finite_curve_support_generator_exists
          (BlowupChart R t x) ι P hP (chartBase R t x t) j hj g L hL htransverse h hh
      obtain ⟨f', rfl⟩ := Ideal.Quotient.mk_surjective f
      exact ⟨f', hf⟩
  exact ⟨_, fun j ↦ (key j).choose_spec⟩

/-- A unit of `A ⧸ (e)^j` (with `j ≥ 1`) lifts to an element of `A` whose image in `A ⧸ (e)^(j+1)`
is a unit. -/
theorem principal_power_unit_lift (A : Type) [CommRing A] (e : A) (j : ℕ) (hj : 1 ≤ j)
    (u : A ⧸ (Ideal.span {e}) ^ j) (hu : IsUnit u) :
    ∃ v : A, IsUnit (Ideal.Quotient.mk ((Ideal.span {e})^(j+1)) v) ∧ Ideal.Quotient.mk
    ((Ideal.span {e})^j) v = u := by
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (↑hu.unit⁻¹ : A ⧸ (Ideal.span {e})^j)
  refine ⟨v, ?_, hv⟩
  set I := Ideal.span {e}
  have hmem : v * w - 1 ∈ I ^ j := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hv, hw]
    simp
  have hnil : IsNilpotent (Ideal.Quotient.mk (I ^ (j+1)) (v * w - 1)) := by
    refine ⟨2, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    have h2 : (v * w - 1) ^ 2 ∈ I ^ (j + j) := by
      rw [pow_two, pow_add]; exact Ideal.mul_mem_mul hmem hmem
    exact Ideal.pow_le_pow_right (by omega) h2
  have hunit := hnil.isUnit_one_add
  rw [← map_one (Ideal.Quotient.mk (I ^ (j+1))), ← map_add, add_sub_cancel, map_mul] at hunit
  exact isUnit_of_mul_isUnit_left hunit

/-- If the residues of `c₀, …, c_d` are the coefficients of `H` with `deg H ≤ d`, then `∑ c̄ᵢ Xⁱ =
H`. -/
theorem reduced_form_eq_of_residue_coeff (R : Type) [CommRing R] [IsLocalRing R] (d : ℕ)
    (c : Fin (d + 1) → R) (H : Polynomial (IsLocalRing.ResidueField R)) (hH : H.natDegree ≤ d)
    (hcH : ∀ i : Fin (d+1), IsLocalRing.residue R (c i) = H.coeff i.val) :
    (∑ i : Fin (d+1), Polynomial.C (IsLocalRing.residue R (c i)) * Polynomial.X^i.val : Polynomial
      (IsLocalRing.ResidueField R)) = H := by
  conv_rhs => rw [Polynomial.as_sum_range' H (d+1) (Nat.lt_succ_of_le hH)]
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Polynomial.monomial i (H.coeff i)) (d+1)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hcH, Polynomial.C_mul_X_pow_eq_monomial]

/-! ### Curve data on the concrete surface

From here on we use local notations for the residue field and the two charts of the blow-up of
`R = ConcreteSurface O pi u a b` at `(t, x)`, taking the surface data as explicit arguments. -/

/-- The residue field of the concrete surface. -/
local notation:max "kRes" O:max pi:max u:max a:max b:max =>
  IsLocalRing.ResidueField (ConcreteSurface O pi u a b)

/-- The `t`-chart `R[x/t]` of the blow-up of the concrete surface `R` at `(t, x)`. -/
local notation:max "tChart" O:max pi:max u:max a:max b:max =>
  BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)

/-- The structure map `R → R[x/t]` of the `t`-chart. -/
local notation:max "tBase" O:max pi:max u:max a:max b:max =>
  chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)

/-- The slope `x/t` in the `t`-chart. -/
local notation:max "tSlope" O:max pi:max u:max a:max b:max =>
  chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)

/-- The exceptional ideal `(t)` of the `t`-chart. -/
local notation:max "tExc" O:max pi:max u:max a:max b:max =>
  chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)

/-- The `x`-chart `R[t/x]` of the blow-up of the concrete surface `R` at `(t, x)`. -/
local notation:max "xChart" O:max pi:max u:max a:max b:max =>
  BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)

/-- The structure map `R → R[t/x]` of the `x`-chart. -/
local notation:max "xBase" O:max pi:max u:max a:max b:max =>
  chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)

/-- The slope `t/x` in the `x`-chart. -/
local notation:max "xSlope" O:max pi:max u:max a:max b:max =>
  chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)

/-- If the last coefficient `c_d` lies in `(t, x)`, the strict transform `∑ cᵢ (t/x)^(d-i)` in the
`x`-chart passes through the point at infinity, so the curve datum has a point at infinity. -/
private theorem curve_datum_nonempty_inf (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (d : ℕ) (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hcd : c (Fin.last d) ∈ Ideal.span {surfaceT O pi u a b, surfaceX O pi u a b})
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
      beta)
    (hrightsurj : ∀ P : Ideal (xChart O pi u a b), P.IsMaximal →
      (xBase O pi u a b) (surfaceX O pi u a b) ∈ P → (∑ i : Fin (d+1), algebraMap
        (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) * (xSlope O pi u a b)^(d - i.val)) ∈
          P → ∃ s : D.ι ⊕ D.ιinf, rightPoint D s = P) :
    Nonempty D.ιinf := by
  have : (Ideal.span {surfaceT O pi u a b, surfaceX O pi u a b}).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  obtain ⟨_, _, S, -, hSt, hSx, -⟩ := concrete_surface_data_exists_unconditional O pi hpi u a b ha
  obtain ⟨hIM, hIx, hIW, -⟩ := infinity_point_maximal O (ConcreteSurface O pi u a b) S
  rw [hSt, hSx] at hIM hIx hIW
  have hbase : Ideal.span {surfaceT O pi u a b, surfaceX O pi u a b} ≤
      (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)).comap (xBase O pi u a b) := by
    rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · change _ ∈ infinityPoint _ _ _
      rw [← blowup_chart_relation]
      exact Ideal.mul_mem_right _ _ hIx
    · exact hIx
  obtain ⟨i | l, hs⟩ := hrightsurj _ hIM hIx (Ideal.sum_mem _ fun i _ ↦ by
    by_cases hi : i.val = d
    · obtain rfl : i = Fin.last d := Fin.ext hi
      simp only [Fin.val_last, Nat.sub_self, pow_zero, mul_one]
      exact hbase hcd
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hIW _ (by omega)))
  · exact ((overlap_exceptional_point_comap_maximal_right _ _ _ beta (D.Q i) (D.onE i)).2.1
      (show _ ∈ rightPoint D (Sum.inl i) by rw [hs]; exact hIW)).elim
  · exact ⟨l⟩

/-- For the strict transform of a degree-`d` form with residue polynomial `H` and homogeneous
divisor `Dv` on the concrete surface, the curve datum has a point over every direction in the
support of `Dv`, a point at the origin and at infinity when `Dv` charges them, and the
multiplicity at infinity is `Dv none`. -/
theorem curve_datum_surj_and_inf_clauses (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (d : ℕ) (f : (ConcreteSurface O pi u a b))
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (_hc : f = ∑ i : Fin (d + 1), c i * (surfaceT O pi u a b) ^ (d - i.val) *
      (surfaceX O pi u a b) ^ i.val)
    [IsLocalRing (ConcreteSurface O pi u a b)] (H : Polynomial (kRes O pi u a b))
    (Dv : ExceptionalDivisor (kRes O pi u a b))
    (hH : HasHomogeneousDivisor (kRes O pi u a b) d H Dv)
    (hcH : ∀ i : Fin (d+1), IsLocalRing.residue (ConcreteSurface O pi u a b) (c i) = H.coeff i.val)
    (e : ((tChart O pi u a b) ⧸ tExc O pi u a b) ≃+* Polynomial (kRes O pi u a b))
    (he : ∀ r : ConcreteSurface O pi u a b,
      e (Ideal.Quotient.mk (tExc O pi u a b) (tBase O pi u a b r)) =
        Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk (tExc O pi u a b) (tSlope O pi u a b)) = Polynomial.X)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
      beta)
    (_hleft : ∀ s : D.ι ⊕ D.ι0, leftData D s = completedPointMap (tChart O pi u a b) (leftPoint D s)
      (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b) (tChart O pi u a b) (c i) *
        (tSlope O pi u a b)^i.val) ∧ (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
          (tChart O pi u a b) (c i) * (tSlope O pi u a b)^i.val) ∈ leftPoint D s)
    (hleftsurj : ∀ P : Ideal (tChart O pi u a b), P.IsMaximal →
      (tBase O pi u a b) (surfaceT O pi u a b) ∈ P → (∑ i : Fin (d+1), algebraMap
        (ConcreteSurface O pi u a b) (tChart O pi u a b) (c i) * (tSlope O pi u a b)^i.val) ∈ P →
      ∃ s : D.ι ⊕ D.ι0, leftPoint D s = P)
    (hright : ∀ s : D.ι ⊕ D.ιinf, Ideal.span {rightData D s} = Ideal.span {completedPointMap
      (xChart O pi u a b) (rightPoint D s) (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
        (xChart O pi u a b) (c i) * (xSlope O pi u a b)^(d - i.val))} ∧
      (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) *
        (xSlope O pi u a b)^(d - i.val)) ∈ rightPoint D s)
    (hrightsurj : ∀ P : Ideal (xChart O pi u a b), P.IsMaximal →
      (xBase O pi u a b) (surfaceX O pi u a b) ∈ P → (∑ i : Fin (d+1), algebraMap
        (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) * (xSlope O pi u a b)^(d - i.val)) ∈
          P → ∃ s : D.ι ⊕ D.ιinf, rightPoint D s = P) :
    (∀ φ : AffineDirection (kRes O pi u a b), φ ≠ zeroAffine (kRes O pi u a b) → 0 < Dv (some φ) →
      ∃ i : D.ι, D.Q i = (directionPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b) e φ).map (algebraMap (tChart O pi u a b) (BlowupOverlap
          (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) ∧
    (0 < Dv (zeroDirection (kRes O pi u a b)) → Nonempty D.ι0) ∧
    (∀ l : D.ιinf, D.Pinf l = infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) ∧ Dv none = rightMultiplicity D (Sum.inr l)) ∧
    (0 < Dv none → Nonempty D.ιinf) := by
  have hmax : (Ideal.span {surfaceT O pi u a b, surfaceX O pi u a b}).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  have hne : ∃ i : Fin (d+1), c i ∉ Ideal.span {surfaceT O pi u a b, surfaceX O pi u a b} := by
    obtain ⟨j, hj⟩ : ∃ j, H.coeff j ≠ 0 := by
      by_contra h; push Not at h; exact hH.1 (Polynomial.ext h)
    have hjd := Nat.lt_succ_of_le ((Polynomial.le_natDegree_of_ne_zero hj).trans hH.2.1)
    refine ⟨⟨j, hjd⟩, fun hmem ↦ hj ?_⟩
    rw [← hcH ⟨j, hjd⟩]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (IsLocalRing.le_maximalIdeal hmax.ne_top hmem)
  have hHBAR := reduced_form_eq_of_residue_coeff (ConcreteSurface O pi u a b) d c H hH.2.1 hcH
  obtain ⟨hdp, -, -⟩ := directionPoint_properties (ConcreteSurface O pi u a b)
      (surfaceT O pi u a b) (surfaceX O pi u a b) e he heZ
  have heF : e (Ideal.Quotient.mk (tExc O pi u a b) (∑ i : Fin (d+1),
      algebraMap (ConcreteSurface O pi u a b) (tChart O pi u a b) (c i) *
        (tSlope O pi u a b)^i.val)) = H := by
    rw [← hHBAR, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_mul, map_pow, map_pow, heZ, ← he]
    rfl
  have hFmem (φ) (hφ : 0 < Dv (some φ)) : (∑ i : Fin (d+1), algebraMap
      (ConcreteSurface O pi u a b) (tChart O pi u a b) (c i) * (tSlope O pi u a b)^i.val) ∈
      directionPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b) e
        φ := by
    change _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, RingHom.comp_apply]
    change e _ ∈ _
    rw [heF, Ideal.mem_span_singleton, hH.2.2.2]
    exact dvd_mul_of_dvd_right ((count_normalizedFactors_divisorAffinePolynomial _ Dv _
      (Polynomial.leadingCoeff_ne_zero.2 hH.1) φ).2.2 hφ) _
  refine ⟨fun φ hφ0 hφ ↦ ?_, fun hφ ↦ ?_, fun l ↦ ?_, fun hpos ↦ ?_⟩
  · obtain ⟨hM, hT, hZ, -⟩ := hdp φ
    obtain ⟨i | k, hs⟩ := hleftsurj _ hM hT (hFmem φ hφ)
    · exact ⟨i, hs ▸ (IsLocalization.map_under (Submonoid.powers (tSlope O pi u a b)) _
        (D.Q i)).symm⟩
    · exact absurd (hZ.1 (hs ▸ D.slope0 k)) hφ0
  · obtain ⟨hM, hT, hZ, -⟩ := hdp (zeroAffine _)
    obtain ⟨i | k, hs⟩ := hleftsurj _ hM hT (hFmem _ hφ)
    · exact ((overlap_exceptional_point_comap_maximal _ _ _ (D.Q i) (D.onE i)).2.1
        (show _ ∈ leftPoint D (Sum.inl i) by rw [hs]; exact hZ.2 rfl)).elim
    · exact ⟨k⟩
  · refine ⟨(concrete_infinity_point_completion O pi hpi u a b ha (D.Pinf l) (D.onEinf l)
      (D.slopeinf l)).1, ?_⟩
    have : (rightPoint D (Sum.inr l)).IsMaximal := D.maximalinf l
    unfold rightMultiplicity rightLevelIdeal finiteLocalCurveIdeal
    rw [pow_one, Ideal.span_insert, (hright (Sum.inr l)).1, ← Ideal.span_insert,
      concrete_infinity_strict_transform_multiplicity O pi hpi u a b ha d c hne
        (rightPoint D (Sum.inr l)) (D.onEinf l) (D.slopeinf l), hHBAR, ENat.toNat_natCast, hH.2.2.1]
  · rw [hH.2.2.1] at hpos
    have hlt : H.natDegree < d := by omega
    have hcd : c (Fin.last d) ∈ Ideal.span {surfaceT O pi u a b, surfaceX O pi u a b} := by
      have hm := concrete_surface_maximalIdeal_eq O pi hpi u a b ha
      unfold surfaceParameterIdeal at hm
      rw [← hm, ← IsLocalRing.residue_eq_zero_iff, hcH]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    exact curve_datum_nonempty_inf O pi hpi u a b ha d c hcd beta D hrightsurj

/-! ### Regularity of the level generators -/

/-- If `e` is a nonzerodivisor and `f` is a nonzerodivisor modulo `e`, then `f` is a nonzerodivisor
modulo every power `(e)^j`. -/
private theorem regular_element_on_all_principal_power_quotients (A : Type) [CommRing A] (e f : A)
    (he : Function.Injective (fun a : A ↦ e*a))
    (hf : Function.Injective
      (fun a : A ⧸ Ideal.span {e} ↦ Ideal.Quotient.mk (Ideal.span {e}) f * a)) (j : ℕ) :
    Function.Injective
      (fun a : A ⧸ (Ideal.span {e})^j ↦ Ideal.Quotient.mk ((Ideal.span {e})^j) f * a) := by
  have key (n : ℕ) : ∀ a : A, e ^ n ∣ f * a → e ^ n ∣ a := by
    induction n with
    | zero => intro a _; simp
    | succ n ih =>
      rintro a ⟨c, hc⟩
      have h1 : Ideal.Quotient.mk (Ideal.span {e}) f * Ideal.Quotient.mk (Ideal.span {e}) a
          = Ideal.Quotient.mk (Ideal.span {e}) f * 0 := by
        rw [mul_zero, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hc]
        exact ⟨e ^ n * c, by ring⟩
      have h2 := hf h1
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2
      obtain ⟨b, rfl⟩ := h2
      have h3 : f * b = e ^ n * c :=
        he (show e * (f * b) = e * (e ^ n * c) by linear_combination hc)
      obtain ⟨d, hd⟩ := ih b ⟨c, h3⟩
      exact ⟨d, by rw [hd]; ring⟩
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hxy' : Ideal.Quotient.mk ((Ideal.span {e})^j) (f * a)
      = Ideal.Quotient.mk ((Ideal.span {e})^j) (f * b) := by
    simpa only [map_mul] using hxy
  rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← mul_sub] at hxy'
  rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact key j _ hxy'

private theorem sup_pow_le_sup_pow {B : Type} [CommRing B] (I J : Ideal B) (n : ℕ) :
    (I ⊔ J) ^ n ≤ I ⊔ J ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le (Ideal.mul_le_left.trans le_sup_left)
      (Ideal.mul_le_left.trans le_sup_left)) (sup_le (Ideal.mul_le_right.trans le_sup_left)
        le_sup_right)

private theorem map_ne_bot_of_prod_pow_le {A Q k : Type} [CommRing A] [CommRing Q] [CommRing k]
    [IsDomain k] (f : Q ≃+* Polynomial k) (π : A →+* Q) (hπ : Function.Surjective π) {ι : Type}
    [Fintype ι] (P : ι → Ideal A) [∀ i, (P i).IsMaximal] (hk : ∀ i, RingHom.ker π ≤ P i) (L : ι → ℕ)
    (K : Ideal A) (hle : ∏ i, P i ^ L i ≤ K) : K.map π ≠ ⊥ := by
  have : IsDomain Q := f.toMulEquiv.isDomain
  have hnf : ¬ IsField Q := fun h ↦ Polynomial.not_isField _ (f.symm.toMulEquiv.isField h)
  have hne : ∀ i, (P i).map π ≠ ⊥ := fun i ↦
    Ring.ne_bot_of_isMaximal_of_not_isField (Ideal.IsMaximal.map_of_surjective_of_ker_le hπ
        (hk i)) hnf
  intro hbot
  have h2 := Ideal.map_mono (f := π) hle
  have hmp := map_prod (Ideal.mapHom π) (fun i ↦ P i ^ L i) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [hbot, le_bot_iff, hmp] at h2
  simp only [Ideal.map_pow] at h2
  rw [Ideal.zero_eq_bot.symm, Finset.prod_eq_zero_iff] at h2
  obtain ⟨i, -, hi⟩ := h2
  exact hne i (pow_eq_zero_iff'.mp hi).1

private theorem map_mk_ne_bot_of_prod_pow_le {A k : Type} [CommRing A] [CommRing k] [IsDomain k]
    (I : Ideal A) (f : A ⧸ I ≃+* Polynomial k) {ι : Type} [Fintype ι] (P : ι → Ideal A)
    [∀ i, (P i).IsMaximal] (hk : ∀ i, I ≤ P i) (L : ι → ℕ) (K : Ideal A) (hle : ∏ i,
        P i ^ L i ≤ K) :
    K.map (Ideal.Quotient.mk I) ≠ ⊥ :=
  map_ne_bot_of_prod_pow_le f (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective P
    (fun i ↦ by rw [Ideal.mk_ker]; exact hk i) L K hle

/-- If the level kernels of finitely many exceptional points of the chart are generated by the
elements `F j`, then each `F j` with `j > 0` does not vanish on the exceptional divisor. -/
private theorem level_generator_ne_zero (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (ι : Type) [Finite ι]
    (P : ι → Ideal (BlowupChart R t x)) [∀ i, (P i).IsMaximal] (hPe : ∀ i, chartBase R t x t ∈ P i)
    (g : ∀ i, CompletedLocalAt (BlowupChart R t x) (P i)) (L : ι → ℕ)
    (hfin : ∀ i, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
      (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ finiteLocalCurveIdeal
      (BlowupChart R t x) (P i) (chartBase R t x t) (g i) 1) (F : ℕ → BlowupChart R t x)
    (hF : ∀ j : ℕ, finiteSupportLevelKernel (BlowupChart R t x) ι P
      (fun i ↦ finiteLocalCurveIdeal (BlowupChart R t x) (P i) (chartBase R t x t) (g i) j)
      (chartBase R t x t) j = Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R t x t})^j)
      (F j)}) (j : ℕ) (hj : 0 < j) : Ideal.Quotient.mk (chartExceptional R t x) (F j) ≠ 0 := by
  have := Fintype.ofFinite ι
  set K := finiteSupportKernel (BlowupChart R t x) ι P
      (fun i ↦ finiteLocalCurveIdeal (BlowupChart R t x) (P i) (chartBase R t x t) (g i) j)
  have hle : ∏ i, P i ^ (L i * j) ≤ K := by
    refine Ideal.prod_le_inf.trans ?_
    rw [Finset.inf_univ_eq_iInf]
    refine iInf_mono fun i ↦ completed_point_power_contraction _ (P i) (L i * j) _ ?_
    rw [pow_mul]
    refine (Ideal.pow_right_mono (hfin i) j).trans ?_
    dsimp only
    unfold finiteLocalCurveIdeal
    rw [Ideal.span_insert, Ideal.span_insert]
    refine (sup_pow_le_sup_pow _ _ j).trans ?_
    rw [Ideal.span_singleton_pow, pow_one]
  obtain ⟨e, -, -⟩ := exceptional_chart_is_affine_line R t x
  have e0 : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* ExceptionalChartLevel R t x 1 :=
    Ideal.quotEquivOfEq (by rw [exceptionalLevelIdeal, pow_one]; rfl)
  let f := e0.trans e
  have hKne : K.map (Ideal.Quotient.mk (chartExceptional R t x)) ≠ ⊥ := by
    refine map_mk_ne_bot_of_prod_pow_le (chartExceptional R t x) f P ?_ (fun i ↦ L i * j) K hle
    intro i; rw [chartExceptional, Ideal.span_le]; simpa using hPe i
  have hIj : chartExceptional R t x ^ j ≤ chartExceptional R t x := Ideal.pow_le_self hj.ne'
  intro h0
  apply hKne
  have hfac : Ideal.Quotient.mk (chartExceptional R t x) =
      (Ideal.Quotient.factor hIj).comp (Ideal.Quotient.mk (chartExceptional R t x ^ j)) :=
    (Ideal.Quotient.factor_comp_mk hIj).symm
  have : Ideal.map (Ideal.Quotient.mk (chartExceptional R t x ^ j)) K =
      Ideal.span {Ideal.Quotient.mk (chartExceptional R t x ^ j) (F j)} := hF j
  rw [hfac, ← Ideal.map_map, this, Ideal.map_span, Set.image_singleton]
  simpa using h0

/-- The generators `F j` of the level kernels of finitely many exceptional points of the chart are
nonzerodivisors modulo the powers of the exceptional divisor. -/
theorem finite_support_level_generator_regular (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (ι : Type) [Finite ι]
    (P : ι → Ideal (BlowupChart R t x)) [∀ i, (P i).IsMaximal] (hPe : ∀ i, chartBase R t x t ∈ P i)
    (g : ∀ i, CompletedLocalAt (BlowupChart R t x) (P i)) (L : ι → ℕ)
    (hfin : ∀ i, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
      (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ finiteLocalCurveIdeal
      (BlowupChart R t x) (P i) (chartBase R t x t) (g i) 1) (hreg : RegularParameterPair R t x)
    (F : ℕ → BlowupChart R t x) (hF : ∀ j : ℕ,
      finiteSupportLevelKernel (BlowupChart R t x) ι P
      (fun i ↦ finiteLocalCurveIdeal (BlowupChart R t x) (P i) (chartBase R t x t) (g i) j)
      (chartBase R t x t) j = Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R t x t})^j)
      (F j)}) (j : ℕ) :
    Function.Injective (fun c : BlowupChart R t x ⧸ (chartExceptional R t x)^j ↦ Ideal.Quotient.mk
      ((chartExceptional R t x)^j) (F j) * c) := by
  have := Fintype.ofFinite ι
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact fun a b _ ↦ Subsingleton.elim (h := Ideal.Quotient.subsingleton_iff.mpr (by simp)) a b
  have hFne := level_generator_ne_zero R t x ι P hPe g L hfin F hF j hj
  obtain ⟨e, -, -⟩ := exceptional_chart_is_affine_line R t x
  have e0 : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* ExceptionalChartLevel R t x 1 :=
    Ideal.quotEquivOfEq (by rw [exceptionalLevelIdeal, pow_one]; rfl)
  have : IsDomain (BlowupChart R t x ⧸ chartExceptional R t x) := (e0.trans e).toMulEquiv.isDomain
  have hinj1 : Function.Injective (fun a : BlowupChart R t x ⧸ chartExceptional R t x ↦
      Ideal.Quotient.mk (chartExceptional R t x) (F j) * a) := fun _ _ ↦ mul_left_cancel₀ hFne
  exact regular_element_on_all_principal_power_quotients (BlowupChart R t x) (chartBase R t x t)
    (F j) (blowup_exceptional_parameter_regular R t x hreg) hinj1 j

/-- The images in the overlap of the generators `F j` of the level kernels of the opposite chart are
nonzerodivisors modulo the powers of the exceptional divisor. -/
theorem overlap_level_generator_regular (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (hreg : RegularParameterPair R t x)
    (_hregSwap : RegularParameterPair R x t) (beta : BlowupRestriction R t x) (ι : Type) [Finite ι]
    (P : ι → Ideal (BlowupChart R x t)) [∀ i, (P i).IsMaximal] (hPe : ∀ i, chartBase R x t x ∈ P i)
    (g : ∀ i, CompletedLocalAt (BlowupChart R x t) (P i)) (L : ι → ℕ)
    (hfin : ∀ i, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
      (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ finiteLocalCurveIdeal
      (BlowupChart R x t) (P i) (chartBase R x t x) (g i) 1) (F : ℕ → BlowupChart R x t)
    (hF : ∀ j : ℕ, finiteSupportLevelKernel (BlowupChart R x t) ι P
      (fun i ↦ finiteLocalCurveIdeal (BlowupChart R x t) (P i) (chartBase R x t x) (g i) j)
      (chartBase R x t x) j = Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R x t x})^j)
      (F j)}) (j : ℕ) :
    Function.Injective (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j ↦
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j) (beta.right (F j)) * c) := by
  have := Fintype.ofFinite ι
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact fun a b _ ↦ Subsingleton.elim (h := Ideal.Quotient.subsingleton_iff.mpr (by simp)) a b
  have : (Ideal.span ({x,t} : Set R)).IsMaximal := by rw [Set.pair_comm]; infer_instance
  have hFne := level_generator_ne_zero R x t ι P hPe g L hfin F hF j hj
  obtain ⟨hdom, hker⟩ := overlap_exceptional_quotient_domain R t x hreg beta
  have hFne' : Ideal.Quotient.mk (Ideal.span {overlapException R t x}) (beta.right (F j)) ≠ 0 :=
    fun h0 ↦ hFne (Ideal.Quotient.eq_zero_iff_mem.mpr (hker _ h0))
  exact regular_element_on_all_principal_power_quotients (BlowupOverlap R t x)
    (overlapException R t x) (beta.right (F j))
    (nonzerodivisor_survives_localization _ _ _ (blowup_exceptional_parameter_regular R t x hreg))
    (fun a b hab ↦ mul_left_cancel₀ hFne' hab) j

/-! ### Residue series of strict transforms -/

/-- Killing `T` and reducing after a chart substitution of a series with coefficients mapped along
`ρ` leaves the residue of its (mapped) constant term. -/
private theorem residueKillT_chartSubst (O O' : Type) [CommRing O] [CommRing O'] [IsDomain O']
    [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi') (ρ : O →+* O') (alpha : O')
    (s : TwoSeries O) :
    residueKillT O' (chartSubst O' alpha (MvPowerSeries.map ρ s)) = PowerSeries.C
    (IsLocalRing.residue O' (ρ (MvPowerSeries.constantCoeff s))) := by
  obtain ⟨hC, hT, hX, -⟩ := chartSubst_apply_generators O' alpha
  obtain ⟨kC, kT, kX, -, -⟩ := residueKillT_apply_ker O' pi' hpi'
  let L : TwoSeries O →+* PowerSeries (IsLocalRing.ResidueField O') :=
    (residueKillT O').comp ((chartSubst O' alpha : TwoSeries O' →+* TwoSeries O').comp
        (MvPowerSeries.map ρ))
  let R : TwoSeries O →+* PowerSeries (IsLocalRing.ResidueField O') :=
    (PowerSeries.C).comp ((IsLocalRing.residue O').comp (ρ.comp MvPowerSeries.constantCoeff))
  have hmT : MvPowerSeries.map ρ (axisT O) = axisT O' := by simp [axisT, MvPowerSeries.map_X]
  have hmX : MvPowerSeries.map ρ (axisX O) = axisX O' := by simp [axisX, MvPowerSeries.map_X]
  have LT : L (axisT O) = 0 := by
    simp only [L, RingHom.comp_apply]
    change residueKillT O' (chartSubst O' alpha (MvPowerSeries.map ρ (axisT O))) = 0
    rw [hmT, hT, kT]
  have LX : L (axisX O) = 0 := by
    change residueKillT O' (chartSubst O' alpha (MvPowerSeries.map ρ (axisX O))) = 0
    rw [hmX, hX, map_mul, kT, zero_mul]
  have RT : R (axisT O) = 0 := by simp [R, axisT]
  have RX : R (axisX O) = 0 := by simp [R, axisX]
  have h : L = R := by
    apply twoSeries_ringHom_ext_of_isNilpotent O _ L R
    · intro c
      change residueKillT O' (chartSubst O' alpha (MvPowerSeries.map ρ (MvPowerSeries.C c))) = _
      simp [R, MvPowerSeries.map_C, hC, kC]
    · rw [LT, RT]
    · rw [LX, RX]
    · rw [LT]; exact IsNilpotent.zero
    · rw [LX]; exact IsNilpotent.zero
  exact congrArg (fun f ↦ f s) h

/-- If a map from the chart into a concrete surface sends the base and slope to chart substitutions,
then the reduction modulo `T` of the image of any chart element is the residue polynomial of
that element, shifted by the residue of `alphaTilde`. -/
private theorem chart_point_residue_series_formula (O O' : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    [IsLocalRing (ConcreteSurface O pi u a b)] [CommRing O'] [IsDomain O']
    [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi') (u' : (TwoSeries O')ˣ)
    (a' b' : ℕ) (ρ : O →+* O') (alphaTilde : O') (S : Type) [CommRing S]
    (Eq : S ≃+* ConcreteSurface O' pi' u' a' b') (ψ : (tChart O pi u a b) →+* S)
    (hbase : ∀ s : TwoSeries O, Eq (ψ (tBase O pi u a b (surfaceMk O pi u a b s))) =
      surfaceMk O' pi' u' a' b' (chartSubst O' alphaTilde (MvPowerSeries.map ρ s)))
    (hslope : Eq (ψ (tSlope O pi u a b)) =
      surfaceX O' pi' u' a' b' + algebraMap O' (ConcreteSurface O' pi' u' a' b') alphaTilde)
    (q : (ConcreteSurface O' pi' u' a' b' ⧸ Ideal.span {surfaceT O' pi' u' a' b'}) ≃+*
      PowerSeries (IsLocalRing.ResidueField O'))
    (hq : ∀ s' : TwoSeries O',
      q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (surfaceMk O' pi' u' a' b' s')) =
        residueKillT O' s')
    (e : ((tChart O pi u a b) ⧸ tExc O pi u a b) ≃+* Polynomial (kRes O pi u a b))
    (he : ∀ r : ConcreteSurface O pi u a b,
      e (Ideal.Quotient.mk (tExc O pi u a b) (tBase O pi u a b r)) =
        Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk (tExc O pi u a b) (tSlope O pi u a b)) = Polynomial.X)
    (ι : kRes O pi u a b →+* (IsLocalRing.ResidueField O'))
    (hι : ∀ s : TwoSeries O,
      ι (IsLocalRing.residue (ConcreteSurface O pi u a b) (surfaceMk O pi u a b s)) =
        IsLocalRing.residue O' (ρ (MvPowerSeries.constantCoeff s))) :
    ∀ FA : tChart O pi u a b,
      q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (Eq (ψ FA))) =
        ((((e (Ideal.Quotient.mk (tExc O pi u a b) FA)).map ι).comp
          (Polynomial.X + Polynomial.C (IsLocalRing.residue O' alphaTilde)) :
          Polynomial (IsLocalRing.ResidueField O')) :
          PowerSeries (IsLocalRing.ResidueField O')) := by
  have hker := residueKillT_apply_ker O' pi' hpi'
  intro FA
  let Θ : tChart O pi u a b →+* PowerSeries (IsLocalRing.ResidueField O') :=
    ((q.toRingHom.comp (Ideal.Quotient.mk _)).comp Eq.toRingHom).comp ψ
  let Λ : tChart O pi u a b →+* PowerSeries (IsLocalRing.ResidueField O') :=
    ((((Polynomial.coeToPowerSeries.ringHom).comp
      (Polynomial.compRingHom (Polynomial.X + Polynomial.C
          (IsLocalRing.residue O' alphaTilde)))).comp
      (Polynomial.mapRingHom ι)).comp e.toRingHom).comp (Ideal.Quotient.mk _)
  have key : Θ = Λ := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro r
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
      have h1 := hbase s
      have h2 := he (surfaceMk O pi u a b s)
      have h3 := hι s
      simp only [chartBase, surfaceMk, RingHom.comp_apply] at h1 h2 h3
      simp only [Θ, Λ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        h1, h2]
      rw [show Ideal.Quotient.mk _ (chartSubst O' alphaTilde (MvPowerSeries.map ρ s)) =
        surfaceMk O' pi' u' a' b' (chartSubst O' alphaTilde (MvPowerSeries.map ρ s)) from rfl, hq,
        residueKillT_chartSubst O O' pi' hpi' ρ alphaTilde s]
      simp [Polynomial.compRingHom, h3]
    · have h1 := hslope
      have h2 := heZ
      simp only [chartSlope] at h1 h2
      simp only [Θ, Λ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        h1, h2]
      rw [show surfaceX O' pi' u' a' b' + algebraMap O'
          (ConcreteSurface O' pi' u' a' b') alphaTilde =
        surfaceMk O' pi' u' a' b' (axisX O' + MvPowerSeries.C alphaTilde) from rfl, hq, map_add,
        hker.2.2.1, hker.1]
      simp [Polynomial.compRingHom]
  exact congrArg (fun f ↦ f FA) key

private theorem residue_series_of_completion_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    [IsLocalRing (ConcreteSurface O pi u a b)] (P : Ideal (tChart O pi u a b)) [P.IsMaximal]
    [P.IsPrime] (e : ((tChart O pi u a b) ⧸ tExc O pi u a b) ≃+* Polynomial (kRes O pi u a b))
    (he : ∀ r : ConcreteSurface O pi u a b,
      e (Ideal.Quotient.mk (tExc O pi u a b) (tBase O pi u a b r)) =
        Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk (tExc O pi u a b) (tSlope O pi u a b)) = Polynomial.X)
    (φ : Polynomial (kRes O pi u a b))
    (hPφ : (P.map (Ideal.Quotient.mk (tExc O pi u a b))).map e = Ideal.span {φ}) (O' : Type)
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi')
    (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a') (ρ : O →+* O') (alphaTilde : O')
    (Eq : CompletedLocalAt (tChart O pi u a b) P ≃+* ConcreteSurface O' pi' u' a' b')
    (hbase : ∀ s : TwoSeries O, Eq
      (completedPointMap (tChart O pi u a b) P (tBase O pi u a b (surfaceMk O pi u a b s))) =
      surfaceMk O' pi' u' a' b' (chartSubst O' alphaTilde (MvPowerSeries.map ρ s)))
    (hslope : Eq (completedPointMap (tChart O pi u a b) P (tSlope O pi u a b)) = surfaceX O' pi' u'
      a' b' + algebraMap O' (ConcreteSurface O' pi' u' a' b') alphaTilde)
    (ι : kRes O pi u a b →+* (IsLocalRing.ResidueField O'))
    (hι : ∀ s : TwoSeries O,
      ι (IsLocalRing.residue (ConcreteSurface O pi u a b) (surfaceMk O pi u a b s)) =
        IsLocalRing.residue O' (ρ (MvPowerSeries.constantCoeff s)))
    (g2 : tChart O pi u a b) (hPg : P = Ideal.span {tBase O pi u a b (surfaceT O pi u a b), g2})
    (hg2 : ∀ q : (ConcreteSurface O' pi' u' a' b' ⧸ Ideal.span {surfaceT O' pi' u' a' b'}) ≃+*
      PowerSeries (IsLocalRing.ResidueField O'),
      (∀ s' : TwoSeries O', q
        (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (surfaceMk O' pi' u' a' b' s')) =
        residueKillT O' s') →
      PowerSeries.constantCoeff (q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'})
        (Eq (completedPointMap (tChart O pi u a b) P g2)))) = 0) :
    ∃ (q : (ConcreteSurface O' pi' u' a' b' ⧸ Ideal.span {surfaceT O' pi' u' a' b'}) ≃+*
        PowerSeries (IsLocalRing.ResidueField O'))
      (ι : kRes O pi u a b →+* IsLocalRing.ResidueField O')
      (alphaBar : IsLocalRing.ResidueField O'),
      Eq (completedPointMap (tChart O pi u a b) P (tBase O pi u a b (surfaceT O pi u a b))) =
        surfaceT O' pi' u' a' b' ∧ (φ.map ι).eval alphaBar = 0 ∧
      ∀ FA : tChart O pi u a b, q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'})
        (Eq (completedPointMap (tChart O pi u a b) P FA))) =
        ((((e (Ideal.Quotient.mk (tExc O pi u a b) FA)).map ι).comp
          (Polynomial.X + Polynomial.C alphaBar) : Polynomial (IsLocalRing.ResidueField O')) :
          PowerSeries (IsLocalRing.ResidueField O')) := by
  obtain ⟨q, hq⟩ := concrete_surface_quotient_T_equiv O' pi' hpi' u' a' b' ha'
  have hform := chart_point_residue_series_formula O O' pi u a b pi' hpi' u' a' b' ρ alphaTilde
    _ Eq (completedPointMap _ P) hbase hslope q hq e he heZ ι hι
  have hT : Eq (completedPointMap (tChart O pi u a b) P (tBase O pi u a b (surfaceT O pi u a b))) =
      surfaceT O' pi' u' a' b' := by
    have h := hbase (axisT O)
    rwa [show axisT O = MvPowerSeries.X 0 from rfl, MvPowerSeries.map_X,
      show (MvPowerSeries.X 0 : TwoSeries O') = axisT O' from rfl,
      (chartSubst_apply_generators O' alphaTilde).2.1] at h
  refine ⟨q, ι, IsLocalRing.residue O' alphaTilde, hT, ?_, hform⟩
  let Ψ : tChart O pi u a b →+* IsLocalRing.ResidueField O' :=
    PowerSeries.constantCoeff.comp (q.toRingHom.comp ((Ideal.Quotient.mk _).comp
      (Eq.toRingHom.comp (completedPointMap _ P))))
  have hle : P ≤ RingHom.ker Ψ := by
    rw [hPg, Ideal.span_le]
    rintro z (rfl | rfl)
    · simp only [SetLike.mem_coe, RingHom.mem_ker, Ψ, RingHom.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hT]
      rw [(Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self _), map_zero, map_zero]
    · exact hg2 q hq
  have hφmem : φ ∈ (P.map (Ideal.Quotient.mk (tExc O pi u a b))).map e := by
    rw [hPφ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).1 hφmem
  obtain ⟨FA, hFA, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
  have h0 : Ψ FA = 0 := hle hFA
  have h1 := congrArg PowerSeries.constantCoeff (hform FA)
  simp only [Ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h0
  rw [h0, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp] at h1
  simpa using h1.symm

/-- Under an identification `q` of `S ⧸ (T)` with `k⟦X⟧` through `residueKillT`, the class of `X`
has zero constant term. -/
private theorem constantCoeff_quotient_surfaceX (O' : Type) [CommRing O'] [IsDomain O']
    [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi') (u' : (TwoSeries O')ˣ)
    (a' b' : ℕ) (q : (ConcreteSurface O' pi' u' a' b' ⧸ Ideal.span {surfaceT O' pi' u' a' b'}) ≃+*
      PowerSeries (IsLocalRing.ResidueField O'))
    (hq : ∀ s', q (Ideal.Quotient.mk _ (surfaceMk O' pi' u' a' b' s')) = residueKillT O' s') :
    PowerSeries.constantCoeff (q (Ideal.Quotient.mk _ (surfaceX O' pi' u' a' b'))) = 0 := by
  rw [show surfaceX O' pi' u' a' b' = surfaceMk O' pi' u' a' b' (axisX O') from rfl, hq,
    (residueKillT_apply_ker O' pi' hpi').2.2.1]
  simp

/-- Under an identification `q` of `S ⧸ (T)` with `k⟦X⟧` through `residueKillT`, the class of a
constant `c` has constant term the residue of `c`. -/
private theorem constantCoeff_quotient_algebraMap (O' : Type) [CommRing O'] [IsDomain O']
    [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi') (u' : (TwoSeries O')ˣ)
    (a' b' : ℕ) (q : (ConcreteSurface O' pi' u' a' b' ⧸ Ideal.span {surfaceT O' pi' u' a' b'}) ≃+*
      PowerSeries (IsLocalRing.ResidueField O'))
    (hq : ∀ s', q (Ideal.Quotient.mk _ (surfaceMk O' pi' u' a' b' s')) = residueKillT O' s')
    (c : O') : PowerSeries.constantCoeff (q (Ideal.Quotient.mk _
      (algebraMap O' (ConcreteSurface O' pi' u' a' b') c))) = IsLocalRing.residue O' c := by
  rw [show algebraMap O' (ConcreteSurface O' pi' u' a' b') c =
    surfaceMk O' pi' u' a' b' (MvPowerSeries.C c) from rfl, hq,
    (residueKillT_apply_ker O' pi' hpi').1]
  simp

/-- At an exceptional point of the left chart of the concrete surface, the completed local ring is
again a concrete surface, and the reduction modulo `T` of a chart element is its residue
polynomial shifted by a root `ᾱ` of the direction polynomial `φ`. -/
theorem concrete_strict_transform_residue_series (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsLocalRing (ConcreteSurface O pi u a b)]
    (P : Ideal (tChart O pi u a b)) [P.IsMaximal] [P.IsPrime]
    (hP : tBase O pi u a b (surfaceT O pi u a b) ∈ P)
    (e : ((tChart O pi u a b) ⧸ tExc O pi u a b) ≃+* Polynomial (kRes O pi u a b))
    (he : ∀ r : ConcreteSurface O pi u a b,
      e (Ideal.Quotient.mk (tExc O pi u a b) (tBase O pi u a b r)) =
        Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk (tExc O pi u a b) (tSlope O pi u a b)) = Polynomial.X)
    (φ : Polynomial (kRes O pi u a b)) (_hφ : φ.Monic ∧ Irreducible φ)
    (hPφ : (P.map (Ideal.Quotient.mk (tExc O pi u a b))).map e = Ideal.span {φ}) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O')
      (_ : Finite (IsLocalRing.ResidueField O'))
      (pi' : O') (u' : (TwoSeries O')ˣ) (a' b' : ℕ), Irreducible pi' ∧ 0 < a' ∧
    ∃ (Eq : CompletedLocalAt (tChart O pi u a b) P ≃+* ConcreteSurface O' pi' u' a' b')
      (q : (ConcreteSurface O' pi' u' a' b' ⧸ Ideal.span {surfaceT O' pi' u' a' b'}) ≃+*
        PowerSeries (IsLocalRing.ResidueField O'))
      (ι : kRes O pi u a b →+* IsLocalRing.ResidueField O')
      (alphaBar : IsLocalRing.ResidueField O'),
      Eq (completedPointMap (tChart O pi u a b) P (tBase O pi u a b (surfaceT O pi u a b))) =
        surfaceT O' pi' u' a' b' ∧ (φ.map ι).eval alphaBar = 0 ∧
      ∀ FA : tChart O pi u a b, q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'})
        (Eq (completedPointMap (tChart O pi u a b) P FA))) =
        ((((e (Ideal.Quotient.mk (tExc O pi u a b) FA)).map ι).comp
          (Polynomial.X + Polynomial.C alphaBar) : Polynomial (IsLocalRing.ResidueField O')) :
          PowerSeries (IsLocalRing.ResidueField O')) := by
  obtain ⟨e0, he0⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  have h461 := concrete_surface_maximalIdeal_eq O pi hpi u a b ha
  let κ : kRes O pi u a b ≃+* IsLocalRing.ResidueField O :=
    (Ideal.quotEquivOfEq h461).trans e0
  have hκ (s : TwoSeries O) : κ (IsLocalRing.residue (ConcreteSurface O pi u a b)
      (surfaceMk O pi u a b s)) = IsLocalRing.residue O (MvPowerSeries.constantCoeff s) := by
    change e0 (Ideal.quotEquivOfEq h461 (Ideal.Quotient.mk _ (surfaceMk O pi u a b s))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact he0 s
  rcases concrete_chart_point_span_form O pi hpi u a b ha P hP with
    hP1 | ⟨α, hα, hP2⟩ | ⟨Φ, hΦ, h2, hP3⟩
  · obtain ⟨Eq, hb, hs, -⟩ := t_chart_origin_completion_equiv O pi hpi u a b ha P hP1
    refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, pi,
      substUnit O 0 u, a + b, b, hpi, by omega, Eq, ?_⟩
    refine residue_series_of_completion_equiv O pi u a b P e he heZ φ hPφ O pi hpi
      (substUnit O 0 u) (a + b) b (by omega) (RingHom.id O) 0 Eq
      (fun s ↦ by rw [MvPowerSeries.map_id]; exact hb s) (by rw [hs, map_zero, add_zero])
      κ.toRingHom hκ _ hP1 fun q hq ↦ ?_
    rw [hs]; exact constantCoeff_quotient_surfaceX O pi hpi _ _ _ q hq
  · obtain ⟨Eq, hb, hs, hc⟩ := t_chart_unit_point_completion_equiv O pi hpi u a b ha α hα P hP2
    refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, pi,
      substUnit O α u * shiftUnit O α hα ^ b, a + b, 0, hpi, by omega, Eq, ?_⟩
    refine residue_series_of_completion_equiv O pi u a b P e he heZ φ hPφ O pi hpi _ (a + b) 0
      (by omega) (RingHom.id O) α Eq (fun s ↦ by rw [MvPowerSeries.map_id]; exact hb s) hs
      κ.toRingHom hκ _ hP2 fun q hq ↦ ?_
    rw [map_sub, map_sub, hs, hc, add_sub_cancel_right]
    exact constantCoeff_quotient_surfaceX O pi hpi _ _ _ q hq
  · have hθ := unramified_root_isUnit_of_two_le_natDegree O Φ hΦ h2
    obtain ⟨Eq, hb, hs, hc, -, -⟩ :=
      t_chart_nonrational_point_completion_equiv O pi hpi u a b ha Φ hΦ hθ P hP3
    obtain ⟨hdom, hloc, hdvr, -, hirr, hcomp, hfin, -⟩ := unramified_is_dvr O Φ hΦ
    let ρ : O →+* AdjoinRoot Φ := algebraMap O (AdjoinRoot Φ)
    have : IsLocalHom ρ := by
      refine ⟨fun x hx ↦ by_contra fun hnu ↦ ?_⟩
      have hxm : x ∈ IsLocalRing.maximalIdeal O := hnu
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer pi).1 hpi,
        Ideal.mem_span_singleton] at hxm
      exact (hirr pi hpi).not_isUnit (isUnit_of_dvd_unit (map_dvd ρ hxm) hx)
    refine ⟨AdjoinRoot Φ, inferInstance, hdom, hdvr, hcomp, hfin, ρ pi, _, a + b, 0, hirr pi hpi,
      by omega, Eq, ?_⟩
    refine residue_series_of_completion_equiv O pi u a b P e he heZ φ hPφ (AdjoinRoot Φ) (ρ pi)
      (hirr pi hpi) _ (a + b) 0 (by omega) ρ (AdjoinRoot.root Φ) Eq hb hs
      ((IsLocalRing.ResidueField.map ρ).comp κ.toRingHom) ?_ _ hP3 ?_
    · exact fun s ↦ by simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, hκ, IsLocalRing.ResidueField.map_residue]
    · intro q hq
      let Ψ : tChart O pi u a b →+* IsLocalRing.ResidueField (AdjoinRoot Φ) :=
        PowerSeries.constantCoeff.comp (q.toRingHom.comp ((Ideal.Quotient.mk _).comp
          (Eq.toRingHom.comp (completedPointMap _ P))))
      change Ψ _ = 0
      rw [Polynomial.hom_eval₂]
      have h1 : Ψ.comp ((tBase O pi u a b).comp (algebraMap O (ConcreteSurface O pi u a b))) =
          (IsLocalRing.residue (AdjoinRoot Φ)).comp ρ := by
        ext c
        simp only [Ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hc]
        exact constantCoeff_quotient_algebraMap (AdjoinRoot Φ) (ρ pi) (hirr pi hpi) _ _ _ q hq (ρ c)
      have h2 : Ψ (tSlope O pi u a b) = IsLocalRing.residue (AdjoinRoot Φ) (AdjoinRoot.root Φ) := by
        simp only [Ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hs,
          map_add]
        rw [constantCoeff_quotient_surfaceX (AdjoinRoot Φ) (ρ pi) (hirr pi hpi) _ _ _ q hq,
          constantCoeff_quotient_algebraMap (AdjoinRoot Φ) (ρ pi) (hirr pi hpi) _ _ _ q hq,
          zero_add]
      rw [h1, h2, ← Polynomial.hom_eval₂, show ρ = AdjoinRoot.of Φ from rfl, AdjoinRoot.eval₂_root,
        map_zero]

private theorem coeff_killX (O : Type) [CommRing O] (g : TwoSeries O) (n : ℕ) :
    PowerSeries.coeff n (killX O g) = MvPowerSeries.coeff (Finsupp.single 0 n) g :=
  coeff_substAlgHom_kill O _ (killXFamily_hasSubst O) 1 0 (by decide) rfl rfl g n

private theorem coeff_residueKillX (O : Type) [CommRing O] [IsLocalRing O] (g : TwoSeries O)
    (n : ℕ) : PowerSeries.coeff n (residueKillX O g) =
      IsLocalRing.residue O (MvPowerSeries.coeff (Finsupp.single 0 n) g) := by
  rw [← coeff_killX]
  rfl

/-- `residueKillX` sends constants to their residues, `T ↦ X` and `X ↦ 0`; it is surjective with
kernel `(π, X)`, and it is compatible with the chart substitutions. -/
private theorem residueKillX_apply_ker (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) :
    (∀ c : O, residueKillX O (MvPowerSeries.C c) = PowerSeries.C (IsLocalRing.residue O c)) ∧
    residueKillX O (axisT O) = PowerSeries.X ∧ residueKillX O (axisX O) = 0 ∧ Function.Surjective
    (residueKillX O) ∧ RingHom.ker (residueKillX O) = Ideal.span
    {(MvPowerSeries.C pi : TwoSeries O), axisX O} ∧
    (∀ s : TwoSeries O, killX O (xChartSubst O s) = killT O s) ∧ ∀ s : TwoSeries O, killX O
    (chartSubst O 0 s) = killX O s := by
  have hX : ∀ i, MvPowerSeries.subst (killXFamily O) (MvPowerSeries.X i : TwoSeries O) =
      killXFamily O i := fun i ↦ MvPowerSeries.subst_X (killXFamily_hasSubst O) i
  have hM := fun a b : TwoSeries O ↦ MvPowerSeries.subst_mul (killXFamily_hasSubst O) a b
  refine ⟨fun c ↦ ?_, ?_, ?_, ?_, ?_, fun s ↦ ?_, fun s ↦ ?_⟩
  · ext n
    rw [coeff_residueKillX]
    by_cases hn : n = 0
    · subst hn; simp [MvPowerSeries.coeff_C]
    · simp [MvPowerSeries.coeff_C, PowerSeries.coeff_C, hn]
  · ext n
    rw [coeff_residueKillX]
    by_cases hn : n = 1
    · subst hn; simp [axisT, MvPowerSeries.coeff_X]
    · simp only [Fin.isValue, axisT, MvPowerSeries.coeff_X, MonoidWithZeroHom.map_ite_one_zero,
        PowerSeries.coeff_X, hn, ↓reduceIte, ite_eq_right_iff, one_ne_zero, imp_false]
      intro h; have := congrArg (fun f ↦ f 0) h
      simp only [Fin.isValue, Finsupp.single_eq_same] at this; exact hn this
  · ext n
    rw [coeff_residueKillX]
    simp only [Fin.isValue, axisX, MvPowerSeries.coeff_X, MonoidWithZeroHom.map_ite_one_zero,
      map_zero, ite_eq_right_iff, one_ne_zero, imp_false]
    intro h; have := congrArg (fun f ↦ f 1) h; simp at this
  · intro h
    let g : TwoSeries O := fun m ↦
      if m 1 = 0 then (IsLocalRing.residue_surjective (PowerSeries.coeff (m 0) h)).choose else 0
    refine ⟨g, ?_⟩
    ext n
    rw [coeff_residueKillX]
    change IsLocalRing.residue O (if _ then _ else _) = _
    simp only [Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true, Finsupp.single_eq_of_ne,
      ↓reduceIte, Finsupp.single_eq_same]
    exact (IsLocalRing.residue_surjective (PowerSeries.coeff n h)).choose_spec
  · ext g
    rw [RingHom.mem_ker, axisX, mvPowerSeries_mem_span_C_var_iff]
    have hm (x : O) : IsLocalRing.residue O x = 0 ↔ pi ∣ x := by
      rw [IsLocalRing.residue_eq_zero_iff, hpi.maximalIdeal_eq, Ideal.mem_span_singleton]
    constructor
    · intro hg m hm0
      have := congrArg (PowerSeries.coeff (m (0 : Fin 2))) hg
      rw [coeff_residueKillX, map_zero (PowerSeries.coeff _), hm] at this
      have hmeq : Finsupp.single (0 : Fin 2) (m (0 : Fin 2)) = m := by
        ext i; fin_cases i <;> simp [hm0]
      rwa [hmeq] at this
    · refine fun hg ↦ PowerSeries.ext fun n ↦ ?_
      rw [coeff_residueKillX, map_zero, hm]
      exact hg _ (by simp)
  · simp only [killX, xChartSubst, killT, MvPowerSeries.coe_substAlgHom]
    rw [MvPowerSeries.subst_comp_subst_apply (xChartFamily_hasSubst O) (killXFamily_hasSubst O)]
    congr 1
    funext i
    fin_cases i
    · simp only [xChartFamily, axisT, axisX, Fin.zero_eta, Matrix.cons_val_zero]
      rw [hM, hX, hX]; simp [killXFamily, killTFamily]
    · simp only [xChartFamily, axisT, axisX, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [hX]; simp [killXFamily, killTFamily]
  · simp only [killX, chartSubst, MvPowerSeries.coe_substAlgHom]
    rw [MvPowerSeries.subst_comp_subst_apply (tChartFamily_hasSubst O 0) (killXFamily_hasSubst O)]
    congr 1
    funext i
    fin_cases i
    · simp only [tChartFamily, axisT, axisX, Fin.zero_eta, Matrix.cons_val_zero]
      rw [hX]
    · simp only [tChartFamily, axisT, axisX, map_zero, add_zero, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [hM, hX, hX]; simp [killXFamily]

/-- For `b > 0`, the quotient of the concrete surface by `X` is the power series ring over the
residue field, via `residueKillX`. -/
private theorem concrete_surface_quotient_X_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (hb : 0 < b) :
    ∃ q : (ConcreteSurface O pi u a b ⧸ Ideal.span {surfaceX O pi u a b}) ≃+* PowerSeries
    (IsLocalRing.ResidueField O), ∀ s : TwoSeries O, q
    (Ideal.Quotient.mk (Ideal.span {surfaceX O pi u a b}) (surfaceMk O pi u a b s)) =
    residueKillX O s := by
  obtain ⟨-, -, -, hsurj, hker, -⟩ := residueKillX_apply_ker O pi hpi
  set I := surfaceIdeal O pi u a b
  set J : Ideal (TwoSeries O) := Ideal.span {axisX O}
  have h1 : Ideal.span {surfaceX O pi u a b} = J.map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  have hdiff : surfaceRelation O pi u a b - MvPowerSeries.C pi ∈ J := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have : surfaceRelation O pi u a (b'+1) - MvPowerSeries.C pi
        = axisX O * (-(u : TwoSeries O) * axisT O ^ a * axisX O ^ b') := by
      unfold surfaceRelation; ring
    rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hX : axisX O ∈ J := Ideal.subset_span rfl
  have h2 : I ⊔ J = RingHom.ker (residueKillX O) := by
    rw [hker]
    apply le_antisymm
    · refine sup_le ?_ ?_
      · refine Ideal.span_le.2 ?_
        rintro _ rfl
        have : surfaceRelation O pi u a b =
            (surfaceRelation O pi u a b - MvPowerSeries.C pi) + MvPowerSeries.C pi := by ring
        change _ ∈ _
        rw [this]
        refine Ideal.add_mem _ ?_ (Ideal.subset_span (by simp))
        exact (Ideal.span_mono (by simp) : J ≤ _) hdiff
      · exact Ideal.span_mono (by simp)
    · refine Ideal.span_le.2 ?_
      rintro _ (rfl | rfl)
      · have : (MvPowerSeries.C pi : TwoSeries O) = surfaceRelation O pi u a b -
          (surfaceRelation O pi u a b - MvPowerSeries.C pi) := by ring
        rw [SetLike.mem_coe, this]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.subset_span rfl))
            (Ideal.mem_sup_right hdiff)
      · exact Ideal.mem_sup_right hX
  refine ⟨((Ideal.quotEquivOfEq h1).trans (DoubleQuot.quotQuotEquivQuotSup I J)).trans
    ((Ideal.quotEquivOfEq h2).trans (RingHom.quotientKerEquivOfSurjective hsurj)), fun _ ↦ rfl⟩

/-! ### Boundary contact numbers -/

private theorem length_quotient_comap_of_surjective {S T : Type} [CommRing S] [CommRing T]
    (φ : S →+* T) (hφ : Function.Surjective φ) (J : Ideal T) :
    Module.length S (S ⧸ J.comap φ) = Module.length T (T ⧸ J) := by
  have : RingHomSurjective φ := ⟨hφ⟩
  let g := Ideal.quotientMap J φ le_rfl
  let f : (S ⧸ J.comap φ) →ₛₗ[φ] (T ⧸ J) :=
    { toFun := g
      map_add' := map_add g
      map_smul' := by
        intro s x
        induction x using Quotient.inductionOn' with
        | h x =>
          change g (Ideal.Quotient.mk _ (s * x)) = _
          simp only [g, Ideal.quotientMap_mk, map_mul]
          rfl }
  have hb : Function.Bijective f := ⟨Ideal.quotientMap_injective,
      Ideal.quotientMap_surjective (H := le_rfl) hφ⟩
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hb)]

private theorem length_quotient_sup_eq_order {S k : Type} [CommRing S] [Field k]
    (φ : S →+* PowerSeries k) (hφ : Function.Surjective φ) (w g : S)
    (hker : RingHom.ker φ = Ideal.span {w}) :
    Module.length S (S ⧸ (Ideal.span {g} ⊔ Ideal.span {w})) = (φ g).order := by
  have h1 : Ideal.span {g} ⊔ Ideal.span {w} = (Ideal.span {φ g}).comap φ := by
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, hker]
  rw [h1, length_quotient_comap_of_surjective φ hφ,
      (powerSeries_quotient_length_eq_order k _).1]

/-- Composing a ring isomorphism `E : S ≃+* T` with the projection onto `T ⧸ (y)` and an
isomorphism `q` of that quotient with `k⟦X⟧` gives a surjection with kernel `(w)`, where
`E w = y`. -/
private theorem surjective_ker_comp_quotient_equiv {S T k : Type} [CommRing S] [CommRing T]
    [Field k] (E : S ≃+* T) (y : T) (q : (T ⧸ Ideal.span {y}) ≃+* PowerSeries k) (w : S)
    (hw : E w = y) :
    Function.Surjective (q.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {y})).comp E.toRingHom)) ∧
    RingHom.ker (q.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {y})).comp E.toRingHom)) =
      Ideal.span {w} := by
  refine ⟨q.surjective.comp (Ideal.Quotient.mk_surjective.comp E.surjective), ?_⟩
  have hspan : Ideal.span {y} = (Ideal.span {w}).map E.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]; exact congrArg _ (congrArg _ hw.symm)
  rw [RingHom.ker_comp_of_injective _ q.injective, ← RingHom.comap_ker, Ideal.mk_ker, hspan]
  exact Ideal.comap_map_of_bijective E.toRingHom E.bijective

/-- The intersection length of a degree-`d` form with `(T)` on the concrete surface is `d` plus the
intersection length of its strict transform with the exceptional divisor at the point at
infinity. -/
theorem concrete_infinity_boundary_contact (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (d : ℕ) (f : (ConcreteSurface O pi u a b))
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hc : f = ∑ i : Fin (d + 1), c i * (surfaceT O pi u a b) ^ (d - i.val) *
      (surfaceX O pi u a b) ^ i.val)
    (Pinf : Ideal (xChart O pi u a b)) [Pinf.IsMaximal] [Pinf.IsPrime]
    (hx : xBase O pi u a b (surfaceX O pi u a b) ∈ Pinf) (hW : xSlope O pi u a b ∈ Pinf) :
    Module.length (ConcreteSurface O pi u a b)
    ((ConcreteSurface O pi u a b) ⧸ (Ideal.span {f} ⊔ Ideal.span {(surfaceT O pi u a b)})) =
    (d : ℕ∞) + Module.length (CompletedLocalAt (xChart O pi u a b) Pinf)
    (CompletedLocalAt (xChart O pi u a b) Pinf ⧸
      (Ideal.span {completedPointMap (xChart O pi u a b) Pinf
          (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) *
            (xSlope O pi u a b)^(d - i.val))} ⊔
        Ideal.span {completedPointMap (xChart O pi u a b) Pinf (xSlope O pi u a b)})) := by
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (c (Fin.last d))
  change surfaceMk O pi u a b s = _ at hs
  have hvan : ∀ {M : Type} [CommMonoidWithZero M] (i : Fin d), (0 : M) ^
      (d - (Fin.castSucc i).val) = 0 :=
    fun i ↦ zero_pow (by simp; omega)
  -- parent side
  obtain ⟨q, hq⟩ := concrete_surface_quotient_T_equiv O pi hpi u a b ha
  let φ := q.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {surfaceT O pi u a b}))
  have hφs : Function.Surjective φ := q.surjective.comp Ideal.Quotient.mk_surjective
  have hφk : RingHom.ker φ = Ideal.span {surfaceT O pi u a b} := by
    rw [RingHom.ker_comp_of_injective _ q.injective, Ideal.mk_ker]
  have hφ : ∀ t, φ (surfaceMk O pi u a b t) = residueKillT O t := fun t ↦ hq t
  obtain ⟨hC, hT, hX, -⟩ := residueKillT_apply_ker O pi hpi
  rw [length_quotient_sup_eq_order φ hφs _ f hφk]
  have hf : φ f = residueKillT O s * PowerSeries.X ^ d := by
    rw [hc, map_sum, Fin.sum_univ_castSucc]
    simp only [map_mul, map_pow, surfaceT, surfaceX, hφ, hT, hX]
    rw [Finset.sum_eq_zero (fun i _ ↦ by rw [hvan i, mul_zero, zero_mul])]
    simp [← hs, hφ]
  -- child side
  obtain ⟨hP, -⟩ := concrete_infinity_point_completion O pi hpi u a b ha Pinf hx hW
  obtain ⟨E, hE1, hE2, -⟩ := x_chart_infinity_completion_equiv O pi hpi u a b ha Pinf hP
  obtain ⟨q', hq'⟩ := concrete_surface_quotient_X_equiv O pi hpi (xSubstUnit O u) (a + b) a ha
  obtain ⟨-, -, hX', -, -, hKX, -⟩ := residueKillX_apply_ker O pi hpi
  let ψ := q'.toRingHom.comp
    ((Ideal.Quotient.mk (Ideal.span {surfaceX O pi (xSubstUnit O u) (a + b) a})).comp E.toRingHom)
  obtain ⟨hψs, hψk⟩ := surjective_ker_comp_quotient_equiv E _ q' _ hE2
  rw [length_quotient_sup_eq_order ψ hψs _ _ hψk]
  have hψW : ψ (completedPointMap _ Pinf (xSlope O pi u a b)) = 0 := by
    change q' (Ideal.Quotient.mk _ (E _)) = 0
    rw [hE2, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  have hψB (t) : ψ (completedPointMap _ Pinf (xBase O pi u a b (surfaceMk O pi u a b t))) =
      residueKillT O t := by
    change q' (Ideal.Quotient.mk _ (E _)) = _
    rw [hE1, hq']
    simp only [residueKillX, residueKillT, RingHom.comp_apply]
    exact congrArg _ (hKX t)
  have hg : ψ (completedPointMap _ Pinf (∑ i : Fin (d+1),
      algebraMap (ConcreteSurface O pi u a b) (xChart O pi u a b) (c i) *
      (xSlope O pi u a b)^(d - i.val))) = residueKillT O s := by
    rw [map_sum, map_sum, Fin.sum_univ_castSucc]
    simp only [map_mul, map_pow, hψW]
    rw [Finset.sum_eq_zero (fun i _ ↦ by rw [hvan i, mul_zero])]
    simp only [Fin.val_last, Nat.sub_self, pow_zero, mul_one, zero_add, ← hs]
    exact hψB s
  rw [hf, hg, PowerSeries.order_mul, PowerSeries.order_X_pow, add_comm]

/-- The intersection length of a degree-`d` form with `(X)` on the concrete surface is `d` plus the
intersection length of its strict transform with the exceptional divisor at the origin of the
left chart. -/
theorem concrete_zero_boundary_contact (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (d : ℕ) (f : (ConcreteSurface O pi u a b))
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hc : f = ∑ i : Fin (d + 1), c i * (surfaceT O pi u a b) ^ (d - i.val) *
      (surfaceX O pi u a b) ^ i.val)
    (P : Ideal (tChart O pi u a b)) [P.IsPrime]
    (hP : P = Ideal.span {tBase O pi u a b (surfaceT O pi u a b), (tSlope O pi u a b)}) :
    Module.length (ConcreteSurface O pi u a b)
    ((ConcreteSurface O pi u a b) ⧸ (Ideal.span {f} ⊔ Ideal.span {(surfaceX O pi u a b)})) =
    (d : ℕ∞) + Module.length (CompletedLocalAt (tChart O pi u a b) P)
    (CompletedLocalAt (tChart O pi u a b) P ⧸
      (Ideal.span {completedPointMap (tChart O pi u a b) P
          (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b) (tChart O pi u a b) (c i) *
            (tSlope O pi u a b)^i.val)} ⊔
        Ideal.span {completedPointMap (tChart O pi u a b) P (tSlope O pi u a b)})) := by
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (c 0)
  change surfaceMk O pi u a b s = _ at hs
  have hvan : ∀ {M : Type} [CommMonoidWithZero M] (i : Fin d), (0 : M) ^ (Fin.succ i).val = 0 :=
    fun i ↦ zero_pow (by simp)
  -- parent side
  obtain ⟨q, hq⟩ := concrete_surface_quotient_X_equiv O pi hpi u a b hb
  let φ := q.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {surfaceX O pi u a b}))
  have hφs : Function.Surjective φ := q.surjective.comp Ideal.Quotient.mk_surjective
  have hφk : RingHom.ker φ = Ideal.span {surfaceX O pi u a b} := by
    rw [RingHom.ker_comp_of_injective _ q.injective, Ideal.mk_ker]
  have hφ : ∀ t, φ (surfaceMk O pi u a b t) = residueKillX O t := fun t ↦ hq t
  obtain ⟨hC, hT, hX, -, -, -, hKX⟩ := residueKillX_apply_ker O pi hpi
  rw [length_quotient_sup_eq_order φ hφs _ f hφk]
  have hf : φ f = residueKillX O s * PowerSeries.X ^ d := by
    rw [hc, map_sum, Fin.sum_univ_succ]
    simp only [map_mul, map_pow, surfaceT, surfaceX, hφ, hT, hX]
    rw [Finset.sum_eq_zero (fun i _ ↦ by rw [hvan i, mul_zero])]
    simp [← hs, hφ]
  -- child side
  obtain ⟨E, hE1, hE2, -⟩ := t_chart_origin_completion_equiv O pi hpi u a b ha P hP
  obtain ⟨q', hq'⟩ := concrete_surface_quotient_X_equiv O pi hpi (substUnit O 0 u) (a + b) b hb
  let ψ := q'.toRingHom.comp
    ((Ideal.Quotient.mk (Ideal.span {surfaceX O pi (substUnit O 0 u) (a + b) b})).comp E.toRingHom)
  obtain ⟨hψs, hψk⟩ := surjective_ker_comp_quotient_equiv E _ q' _ hE2
  rw [length_quotient_sup_eq_order ψ hψs _ _ hψk]
  have hψW : ψ (completedPointMap _ P (tSlope O pi u a b)) = 0 := by
    change q' (Ideal.Quotient.mk _ (E _)) = 0
    rw [hE2, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  have hψB (t) : ψ (completedPointMap _ P (tBase O pi u a b (surfaceMk O pi u a b t))) =
      residueKillX O t := by
    change q' (Ideal.Quotient.mk _ (E _)) = _
    rw [hE1, hq']
    simp only [residueKillX, RingHom.comp_apply]
    exact congrArg _ (hKX t)
  have hg : ψ (completedPointMap _ P (∑ i : Fin (d+1),
      algebraMap (ConcreteSurface O pi u a b) (tChart O pi u a b) (c i) *
      (tSlope O pi u a b)^i.val)) = residueKillX O s := by
    rw [map_sum, map_sum, Fin.sum_univ_succ]
    simp only [map_mul, map_pow, hψW]
    rw [Finset.sum_eq_zero (fun i _ ↦ by rw [hvan i, mul_zero])]
    simp only [Fin.val_zero, pow_zero, mul_one, add_zero, ← hs]
    exact hψB s
  rw [hf, hg, PowerSeries.order_mul, PowerSeries.order_X_pow, add_comm]

end SurfaceBlowup
