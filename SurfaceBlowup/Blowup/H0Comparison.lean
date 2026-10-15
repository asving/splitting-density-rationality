/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.NilpotentGluing

/-!
# Comparing surface functions with Čech data on the blow-up

For a regular parameter pair `(t, x)` of `R`, the blow-up is covered by the two charts
`R[x/t]` and `R[t/x]`; truncating modulo powers of the exceptional ideals gives a tower of
two-term Čech complexes with twisted differentials. This file shows that `R` computes the
degree-`0` cohomology of this tower: the surface-to-Čech map has kernel `(t, x) ^ j` and image
the closed classes at each level, and for `(t, x)`-adically complete `R` it is an isomorphism
onto compatible closed threads. Consequences: glued generators come from a unique surface
function of order `d`, closed twisted classes come from surface functions, and the connecting
class of a curve section is detected by the curve ideal lattice. The file also records basic
facts on surface states and tangent divisors, and partitions a fixed tangent cell inside a
coordinate chart into `pi`-adic cosets.

## Main results

* `surface_to_cech_kernel`, `surface_to_cech_range`, `surface_threads_injective`,
  `surface_threads_range`: the `H⁰` comparison.
* `glued_function_exists_unique`, `glued_function_initial_form`.
* `twisted_kernel_from_surface`, `curve_section_connecting_class_zero_iff`.
* `has_tangent_divisor_multiplicity`, `surface_state_vertical_perturbation`.
* `fixed_tangent_cell_chart_partition`, `fixed_tangent_cell_chart_measurable`.

Provenance: `Thm_SurfaceBlowupV2_*` nodes `surface_layer_kernel_lift`,
`surface_parameters_mem_maximal`, `has_tangent_divisor_multiplicity`,
`initial_form_lift_independent`, `surface_section_closed`, `surface_state_{ideal_proper,
generator_mem_maximal, vertical_perturbation}`, `surface_to_cech_{kernel, range}`,
`glued_function_{order, initial_form, exists_unique}`, `surface_threads_{injective, range}`,
`curve_section_connecting_class_zero_iff`, `surface_to_curve_limit_exists`,
`surface_vertical_parameter`, `surface_tangent_jet_small_perturbation`,
`fixed_tangent_cell_chart_{partition, measurable}`, `transition_unit_congruent_one`,
`twisted_kernel_from_surface`.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-! ### Lifting through the layers of the Čech complex -/

/-- In the chart `R[x/t]`, `x = t * (x/t)`. -/
theorem chartBase_x_eq (R : Type) [CommRing R] (t x : R) :
    chartBase R t x x = chartBase R t x t * chartSlope R t x := by
  simp only [chartBase, chartSlope, RingHom.comp_apply, ← map_mul]
  rw [eq_comm, Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

/-- Overlap image of a right-chart monomial, twisted by `(x/t)⁻ᵈ`. -/
private theorem beta_right_monomial (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x)
    (r : R) (i j d : ℕ) :
    beta.right (chartBase R x t r * chartSlope R x t ^ i * chartBase R x t x ^ j) *
      IsLocalization.Away.invSelf (chartSlope R t x) ^ d =
    algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x r) *
      selfZPow (chartSlope R t x) (BlowupOverlap R t x) ((j:ℤ) - d + -(i:ℤ)) *
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) ^ j := by
  have hβr := beta_right_chartBase beta
  have hz : (j:ℤ) - d + -(i:ℤ) = -(i:ℤ) + j + -(d:ℤ) := by ring
  rw [map_mul, map_mul, map_pow, map_pow, hβr, hβr, beta.slope, chartBase_x_eq, map_mul, hz,
    selfZPow_add, selfZPow_add, ← invSelf_pow_eq_selfZPow, ← invSelf_pow_eq_selfZPow,
        selfZPow_natCast, mul_pow]
  ring


/-- The left chart's layer coordinates are compatible with the overlap's Laurent coordinates. -/
private theorem cech_layer_coordinates_left (R : Type) [CommRing R] (t x : R) (j : ℕ)
    (LA : Polynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R]
      PrincipalLayer (BlowupChart R t x) (chartBase R t x t) j)
    (hLA : ∀ r : R, ∀ i : ℕ,
      (LA (Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) * Polynomial.X^i)).val =
        principalLayerMap (BlowupChart R t x) (chartBase R t x t) j
          (chartBase R t x r * (chartSlope R t x)^i))
    (LO : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer (BlowupOverlap R t x)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j)
    (hLO : ∀ r : R, ∀ ell : ℤ, (LO (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap (BlowupOverlap R t x)
        ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j
        ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x r) *
          selfZPow (chartSlope R t x) (BlowupOverlap R t x) ell))
    (hψ : (Ideal.span {chartBase R t x t})^(j+1) ≤ ((Ideal.span
      {(algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)})^(j+1)).comap
        (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)))
    (P : Polynomial (R ⧸ Ideal.span {t,x})) :
    Ideal.quotientMap _ (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) hψ (LA P).val =
      (LO P.toLaurent).val := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, Submodule.coe_add, map_add, hp, hq, map_add, map_add, Submodule.coe_add]
  | monomial i c =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← Polynomial.C_mul_X_pow_eq_monomial, hLA, Polynomial.toLaurent_C_mul_X_pow, hLO,
      principalLayerMap_apply_eq_mk, principalLayerMap_apply_eq_mk, Ideal.quotientMap_mk,
      selfZPow_natCast]
    simp only [map_mul, map_pow]

/-- The right chart's layer coordinates, twisted by `(x/t)⁻ᵈ`, are compatible with the overlap's
Laurent coordinates. -/
private theorem cech_layer_coordinates_right (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ)
    (LB : Polynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R]
      PrincipalLayer (BlowupChart R x t) (chartBase R x t x) j)
    (hLB : ∀ r : R, ∀ i : ℕ,
      (LB (Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) * Polynomial.X^i)).val =
        principalLayerMap (BlowupChart R x t) (chartBase R x t x) j
          (chartBase R x t r * (chartSlope R x t)^i))
    (LO : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer (BlowupOverlap R t x)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j)
    (hLO : ∀ r : R, ∀ ell : ℤ, (LO (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap (BlowupOverlap R t x)
        ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j
        ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x r) *
          selfZPow (chartSlope R t x) (BlowupOverlap R t x) ell))
    (hψ : (Ideal.span {chartBase R x t x})^(j+1) ≤ ((Ideal.span
      {(algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)})^(j+1)).comap
        beta.right.toRingHom)
    (Q : Polynomial (R ⧸ Ideal.span {t,x})) :
    Ideal.quotientMap _ beta.right.toRingHom hψ (LB Q).val *
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
    exact congrArg _ (beta_right_monomial R t x beta r i j d)

/-- Polynomial coordinates on the `j`-th layers: a Čech input pair `(a, b)` of order `j` with
twist-`d` differential of order `j + 1` has coordinates `P, Q` with `P = Tʲ⁻ᵈ · Q(T⁻¹)`. -/
private theorem cech_layer_coordinates (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x)
    (beta : BlowupRestriction R t x) (hregSwap : RegularParameterPair R x t) (d j : ℕ)
    (a : BlowupChart R t x) (b : BlowupChart R x t)
    (ha : a ∈ (Ideal.span {chartBase R t x t}) ^ j) (hb : b ∈ (Ideal.span {chartBase R x t x}) ^ j)
    (hD : fullCechDifferential R t x beta d (a, b) ∈
      (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t)}) ^
        (j + 1))
          :
    ∃ LA : Polynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R]
        PrincipalLayer (BlowupChart R t x) (chartBase R t x t) j,
    ∃ LB : Polynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R]
        PrincipalLayer (BlowupChart R x t) (chartBase R x t x) j,
    (∀ r : R, ∀ i : ℕ,
        (LA (Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) * Polynomial.X^i)).val
      = principalLayerMap (BlowupChart R t x) (chartBase R t x t) j
          (chartBase R t x r * (chartSlope R t x)^i)) ∧
    (∀ r : R, ∀ i : ℕ,
        (LB (Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) * Polynomial.X^i)).val
      = principalLayerMap (BlowupChart R x t) (chartBase R x t x) j
          (chartBase R x t r * (chartSlope R x t)^i)) ∧
    ∃ P Q : Polynomial (R ⧸ Ideal.span {t,x}),
      (LA P).val = Ideal.Quotient.mk _ a ∧ (LB Q).val = Ideal.Quotient.mk _ b ∧
      P.toLaurent - LaurentPolynomial.T ((j:ℤ) - d) * LaurentPolynomial.invert Q.toLaurent = 0 := by
  set ι := algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
  set eA := chartBase R t x t
  set eB := chartBase R x t x
  set eO := ι eA
  set W := chartSlope R t x
  have hιx : ι (chartBase R t x x) = eO * algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
      W := by
    rw [chartBase_x_eq, map_mul]
  have hβr : ∀ r : R, beta.right (chartBase R x t r) = ι (chartBase R t x r) :=
    beta_right_chartBase beta
  have hβeB : beta.right eB = eO * algebraMap (BlowupChart R t x) (BlowupOverlap R t x) W := by
      rw [hβr, hιx]
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
  let ψA := Ideal.quotientMap _ ι hψA
  let ψB := Ideal.quotientMap _ beta.right.toRingHom hψB
  let c : (BlowupOverlap R t x) ⧸ (Ideal.span {eO})^(j+1) :=
    Ideal.Quotient.mk _ ((IsLocalization.Away.invSelf W)^d)
  have hPA : ∀ P, ψA (LA P).val = (LO P.toLaurent).val :=
    cech_layer_coordinates_left R t x j LA hLA LO hLO hψA
  have hPB : ∀ Q, ψB (LB Q).val * c =
      (LO (LaurentPolynomial.T ((j:ℤ) - d) * LaurentPolynomial.invert Q.toLaurent)).val :=
    cech_layer_coordinates_right R t x beta d j LB hLB LO hLO hψB
  set P := LA.symm ⟨_, mk_mem_principalLayer _ j ha⟩ with hPdef
  set Q := LB.symm ⟨_, mk_mem_principalLayer _ j hb⟩ with hQdef
  have hP : (LA P).val = Ideal.Quotient.mk _ a := by rw [hPdef, LinearEquiv.apply_symm_apply]
  have hQ : (LB Q).val = Ideal.Quotient.mk _ b := by rw [hQdef, LinearEquiv.apply_symm_apply]
  have key : LO (P.toLaurent - LaurentPolynomial.T ((j:ℤ) - d) *
      LaurentPolynomial.invert Q.toLaurent) = 0 := by
    apply Subtype.ext
    rw [map_sub, Submodule.coe_sub, ← hPA, ← hPB, hP, hQ]
    simp only [ψA, ψB, c]
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, ← map_mul, ← map_sub, ZeroMemClass.coe_zero,
      Ideal.Quotient.eq_zero_iff_mem]
    convert hD using 1
    change _ = ι a - _ * _
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    ring
  exact ⟨LA, LB, hLA, hLB, P, Q, hP, hQ, (LinearEquiv.map_eq_zero_iff LO).1 key⟩


/-- One lifting step: such a pair agrees to order `j + 1` with `(tᵈ r, xᵈ r)` for some
`r ∈ (t, x) ^ (j - d)`. -/
private theorem cech_layer_step (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x)
    (beta : BlowupRestriction R t x) (hregSwap : RegularParameterPair R x t) (d j : ℕ)
    (a : BlowupChart R t x) (b : BlowupChart R x t)
    (ha : a ∈ (Ideal.span {chartBase R t x t}) ^ j) (hb : b ∈ (Ideal.span {chartBase R x t x}) ^ j)
    (hD : fullCechDifferential R t x beta d (a, b) ∈
      (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t)}) ^
        (j + 1))
          :
    ∃ r ∈ (Ideal.span {t,x})^(j - d),
      a - (chartBase R t x t)^d * chartBase R t x r ∈ (Ideal.span {chartBase R t x t})^(j+1) ∧
      b - (chartBase R x t x)^d * chartBase R x t r ∈ (Ideal.span {chartBase R x t x})^(j+1) := by
  obtain ⟨LA, LB, hLA, hLB, P, Q, hP, hQ, hz⟩ :=
    cech_layer_coordinates R t x hreg beta hregSwap d j a b ha hb hD
  rcases lt_or_ge j d with hjd | hjd
  · obtain ⟨hP0, hQ0⟩ := negative_laurent_twist_has_no_kernel _ ((j:ℤ) - d) (by omega) P Q hz
    refine ⟨0, Ideal.zero_mem _, ?_, ?_⟩
    · rw [map_zero, mul_zero, sub_zero, ← Ideal.Quotient.eq_zero_iff_mem, ← hP, hP0, map_zero]; rfl
    · rw [map_zero, mul_zero, sub_zero, ← Ideal.Quotient.eq_zero_iff_mem, ← hQ, hQ0, map_zero]; rfl
  obtain ⟨m, rfl⟩ : ∃ m, j = d + m := ⟨j - d, by omega⟩
  have hz' : P.toLaurent = LaurentPolynomial.T (m : ℤ) * LaurentPolynomial.invert Q.toLaurent := by
    rw [sub_eq_zero] at hz
    rw [hz]
    congr 2
    push_cast
    ring
  obtain ⟨hdeg, hcoef⟩ := laurent_nonnegative_twist_kernel _ m P Q hz'
  choose c hc using fun i => Ideal.Quotient.mk_surjective (I := Ideal.span {t,x}) (P.coeff i)
  have hPsum : P = ∑ i ∈ Finset.range (m+1),
      Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) (c i)) * Polynomial.X^i := by
    ext n
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hc]
    rw [Finset.sum_ite_eq]
    split_ifs with hn
    · rfl
    · simp only [Finset.mem_range, not_lt] at hn
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hQsum : Q = ∑ i ∈ Finset.range (m+1),
      Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) (c (m - i))) * Polynomial.X^i := by
    ext n
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hc]
    rw [Finset.sum_ite_eq, hcoef n]
    simp only [Finset.mem_range]
    split_ifs <;> first | rfl | omega
  refine ⟨∑ i ∈ Finset.range (m+1), c i * t^(m-i) * x^i, ?_, ?_, ?_⟩
  · rw [Nat.add_sub_cancel_left]
    refine Ideal.sum_mem _ fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [mul_assoc]
    refine Ideal.mul_mem_left _ _ ?_
    have := Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_insert t {x})) (m-i))
      (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_insert_of_mem t (Set.mem_singleton x))) i)
    rwa [← pow_add, Nat.sub_add_cancel hi'] at this
  · rw [← Ideal.Quotient.eq, ← hP, hPsum, map_sum, Submodule.coe_sum]
    simp_rw [hLA, principalLayerMap_apply_eq_mk]
    rw [← map_sum]
    congr 1
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := by simp at hi; omega
    simp only [map_mul, map_pow, chartBase_x_eq]
    rw [show d + m = d + (m - i) + i by omega, pow_add, pow_add, mul_pow]
    ring
  · rw [← Ideal.Quotient.eq, ← hQ, hQsum, map_sum, Submodule.coe_sum]
    simp_rw [hLB, principalLayerMap_apply_eq_mk]
    rw [← map_sum]
    congr 1
    rw [map_sum, Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := by simp at hi; omega
    simp only [map_mul, map_pow, chartBase_x_eq R x t, Nat.add_sub_cancel]
    rw [show m - (m - i) = i by omega, show d + m = d + i + (m - i) by omega, pow_add, pow_add,
      mul_pow]
    ring

/-- A Čech input class of level `j + 1` that is closed (for twist `0`) and vanishes at level
`j` comes from a surface function `r ∈ (t, x) ^ j`. -/
private theorem surface_layer_kernel_lift (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t)
    (beta : BlowupRestriction R t x) (j : ℕ)
    (hnext : cechInputLattice R t x (j + 1) ≤ (cechOutputLattice R t x (j + 1)).comap
    (fullCechDifferential R t x beta 0)) (w : CechLevelInput R t x (j + 1))
    (hw : finiteCechDifferential R t x beta 0 (j + 1) hnext w = 0)
    (hred : cechInputReduction R t x j w = 0) :
    ∃ r ∈ (Ideal.span {t,x})^j, surfaceToCechInput R t x (j+1) r = w := by
  induction w using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨a, b⟩ := z
    rw [finiteCechDifferential, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hw
    change Submodule.Quotient.mk (a, b) = (0 : CechLevelInput R t x j) at hred
    rw [Submodule.Quotient.mk_eq_zero] at hred
    have hD : fullCechDifferential R t x beta 0 (a, b) ∈
        (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
          (chartBase R t x t)})^(j+1) := hw
    have ha : a ∈ (Ideal.span {chartBase R t x t})^j := hred.1
    have hb : b ∈ (Ideal.span {chartBase R x t x})^j := hred.2
    obtain ⟨r, hr, hA, hB⟩ := cech_layer_step R t x hreg beta hregSwap 0 j a b ha hb hD
    rw [pow_zero, one_mul] at hA hB
    refine ⟨r, hr, ?_⟩
    rw [surfaceToCechInput, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.mem_prod.2 ⟨sub_mem_comm_iff.mp hA, sub_mem_comm_iff.mp hB⟩

/-! ### Tangent divisors and surface states -/

/-- The surface parameters `t` and `x` lie in the maximal ideal. -/
private theorem surface_parameters_mem_maximal (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) :
    S.t ∈ IsLocalRing.maximalIdeal R ∧ S.x ∈ IsLocalRing.maximalIdeal R := by
  rw [← S.parameters]
  exact ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩

/-- An ideal with a tangent divisor of degree `d` has multiplicity exactly `d`. -/
theorem has_tangent_divisor_multiplicity (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (hreg : RegularParameterPair R S.t S.x) (J : Ideal R) (d : ℕ)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField R)) (hJ : HasTangentDivisor O R S J d Dv) :
    HasMultiplicity R J d := by
  obtain ⟨f, H, rfl, ⟨hH, hdeg, -, -⟩, hf⟩ := hJ
  obtain ⟨ht, hx⟩ := surface_parameters_mem_maximal O R S
  set m := IsLocalRing.maximalIdeal R with hm
  have hspan : Ideal.span ({S.t, S.x} : Set R) = m := S.parameters
  have hlift : tangentLift O R S d H ∈ m ^ d := by
    unfold tangentLift
    refine Ideal.sum_mem _ fun i _ => ?_
    have h1 : S.t ^ (d - i.val) * S.x ^ i.val ∈ m ^ d := by
      have : m ^ (d - i.val) * m ^ i.val ≤ m ^ d := by
        rw [← pow_add]; apply Ideal.pow_le_pow_right; omega
      exact this (Ideal.mul_mem_mul (Ideal.pow_mem_pow ht _) (Ideal.pow_mem_pow hx _))
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ h1
  have hpow : m ^ (d+1) ≤ m ^ d := Ideal.pow_le_pow_right (by omega)
  refine ⟨?_, ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have h2 : f = (f - tangentLift O R S d H) + tangentLift O R S d H := by ring
    rw [h2]; exact Ideal.add_mem _ (hpow hf) hlift
  · intro hle
    have hfm : f ∈ m ^ (d+1) := hle (Ideal.mem_span_singleton_self f)
    have hlm : tangentLift O R S d H ∈ m ^ (d+1) := by
      have h2 : tangentLift O R S d H = f - (f - tangentLift O R S d H) := by ring
      rw [h2]; exact Ideal.sub_mem _ hfm hf
    obtain ⟨i₀, hi₀⟩ : ∃ i : ℕ, H.coeff i ≠ 0 :=
      ⟨H.natDegree, Polynomial.leadingCoeff_ne_zero.mpr hH⟩
    have hi₀d : i₀ ≤ d := le_trans (Polynomial.le_natDegree_of_ne_zero hi₀) hdeg
    have : (Ideal.span ({S.t, S.x} : Set R)).IsMaximal := by rw [hspan]; infer_instance
    have key := homogeneous_form_not_mem_pow_succ R S.t S.x hreg d
      (fun i => residueRepresentative R (H.coeff i.val)) ⟨i₀, by omega⟩ (by
        rw [hspan, hm, ← IsLocalRing.residue_eq_zero_iff]
        have : IsLocalRing.residue R (residueRepresentative R (H.coeff i₀)) = H.coeff i₀ :=
          Function.rightInverse_invFun (IsLocalRing.residue_surjective) _
        rw [this]; exact hi₀)
    apply key
    rw [hspan]
    exact hlm

/-- Two degree-`d` forms in `t, x` whose coefficients agree modulo the maximal ideal differ by
an element of `𝔪 ^ (d + 1)`. -/
theorem initial_form_lift_independent (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (d : ℕ) (b c : Fin (d + 1) → R)
    (hbc : ∀ i, b i - c i ∈ IsLocalRing.maximalIdeal R) :
    (∑ i : Fin (d+1), b i*S.t^(d-i.val)*S.x^i.val) - (∑ i : Fin (d+1), c i*S.t^(d-i.val)*S.x^i.val)
      ∈ (IsLocalRing.maximalIdeal R)^(d+1) := by
  obtain ⟨ht, hx⟩ := surface_parameters_mem_maximal O R S
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hi : i.val ≤ d := Nat.lt_succ_iff.mp i.isLt
  have key : (b i - c i) * (S.t ^ (d - i.val) * S.x ^ i.val) ∈ (IsLocalRing.maximalIdeal R) ^
      (d+1) := by
    rw [pow_succ']
    refine Ideal.mul_mem_mul (hbc i) ?_
    have h := Ideal.mul_mem_mul (Ideal.pow_mem_pow ht (d - i.val)) (Ideal.pow_mem_pow hx i.val)
    rwa [← pow_add, Nat.sub_add_cancel hi] at h
  have e : b i * S.t ^ (d - i.val) * S.x ^ i.val - c i * S.t ^ (d - i.val) * S.x ^ i.val
      = (b i - c i) * (S.t ^ (d - i.val) * S.x ^ i.val) := by ring
  rw [e]; exact key

/-- Surface functions give closed Čech inputs: the twist-`0` Čech differential kills the image
of `surfaceToCechInput`. -/
private theorem surface_section_closed (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x)
    (j : ℕ) (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta 0)) (r : R) :
    finiteCechDifferential R t x beta 0 j h (surfaceToCechInput R t x j r) = 0 := by
  simp only [finiteCechDifferential, surfaceToCechInput, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.mapQ_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  convert (cechOutputLattice R t x j).zero_mem
  simp only [fullCechDifferential, ringCechDifferential, IsScalarTower.coe_toAlgHom', pow_zero,
    one_mul, surfaceToChartPair, LinearMap.prod_apply, Function.prod_apply,
    Algebra.linearMap_apply, LinearMap.coe_mk, AddHom.coe_mk, AlgHom.commutes]
  rw [← IsScalarTower.algebraMap_apply, sub_self]

/-- Every ideal in the surface state set of a state is proper. -/
theorem surface_state_ideal_proper (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (s : State) (J : Ideal R) (hJ : J ∈ surfaceStateSet O R S s) :
    J ≠ ⊤ := by
  intro hT
  have h0 : ∀ y : R, idealContact R J y = 0 := by
    intro y
    unfold idealContact
    rw [hT, top_sup_eq]
    have : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero
  obtain ⟨_, hv, hs⟩ := hJ
  cases s with
  | single a c =>
    obtain ⟨_, _, hc⟩ := hs
    rw [h0] at hc
    have : c = 0 := by exact_mod_cast hc.symm
    exact absurd hv.2 (by omega)
  | crossing a b c h =>
    obtain ⟨_, _, hc, _⟩ := hs
    rw [h0] at hc
    have : c = 0 := by exact_mod_cast hc.symm
    exact absurd hv.2.2.1 (by omega)

/-- A generator of an ideal in a surface state set lies in the maximal ideal. -/
theorem surface_state_generator_mem_maximal (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (s : State) (J : Ideal R) (hJ : J ∈ surfaceStateSet O R S s) (f : R)
    (hf : J = Ideal.span {f}) :
    f ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact fun hu => surface_state_ideal_proper O R S s J hJ (hf ▸ Ideal.span_singleton_eq_top.mpr hu)

/-- `(f + p * h) + (y) = (f) + (y)` whenever `y ∣ p`. -/
private theorem span_add_mul_sup_span_of_dvd {R : Type} [CommRing R] (f p h y : R) (hy : y ∣ p) :
    Ideal.span {f + p * h} ⊔ Ideal.span {y} = Ideal.span {f} ⊔ Ideal.span {y} := by
  obtain ⟨c, rfl⟩ := hy
  have hyI : ∀ I : Ideal R, y ∈ I ⊔ Ideal.span {y} :=
    fun I => Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)
  have hmul : ∀ I : Ideal R, y * c * h ∈ I ⊔ Ideal.span {y} := fun I => by
    rw [mul_assoc]; exact Ideal.mul_mem_right _ _ (hyI I)
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self f)) (hmul _)
  · refine sup_le ?_ le_sup_right
    rw [Ideal.span_singleton_le_iff_mem]
    simpa using Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (f + y * c * h)))
        (hmul _)

/-- Surface state sets are stable under vertical perturbation: if `(f)` is in the state set,
so is `(f + pi * h)`. -/
theorem surface_state_vertical_perturbation (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (s : State) (f h : R) (hf : Ideal.span {f} ∈ surfaceStateSet O R S s) :
    Ideal.span {f + algebraMap O R S.pi * h} ∈ surfaceStateSet O R S s := by
  have ht : S.t ∣ algebraMap O R S.pi := by
    rw [S.vertical]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero S.a_pos.ne'
    rw [hk, pow_succ]
    exact ⟨S.unit * S.t ^ k * S.x ^ S.b, by ring⟩
  obtain ⟨-, hv, hm⟩ := hf
  refine ⟨⟨_, rfl⟩, hv, ?_⟩
  cases s with
  | single a c =>
    obtain ⟨h1, h2, h3⟩ := hm
    refine ⟨h1, h2, ?_⟩
    unfold idealContact at *
    rw [span_add_mul_sup_span_of_dvd _ _ _ _ ht]; exact h3
  | crossing a b c e =>
    obtain ⟨h1, h2, h3, h4⟩ := hm
    have hx : S.x ∣ algebraMap O R S.pi := by
      rw [S.vertical]
      have hb : 0 < S.b := h2 ▸ hv.2.1
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
      rw [hk, pow_succ]
      exact ⟨S.unit * S.t ^ S.a * S.x ^ k, by ring⟩
    refine ⟨h1, h2, ?_, ?_⟩
    · unfold idealContact at *
      rw [span_add_mul_sup_span_of_dvd _ _ _ _ ht]; exact h3
    · unfold idealContact at *
      rw [span_add_mul_sup_span_of_dvd _ _ _ _ hx]; exact h4

/-! ### The surface-to-Čech comparison -/

/-- Membership in the kernel of the surface-to-Čech map, chart by chart. -/
private theorem mem_ker_surfaceToCechInput_iff (R : Type) [CommRing R] (t x : R) (j : ℕ) (r : R) :
    r ∈ LinearMap.ker (surfaceToCechInput R t x j) ↔
      chartBase R t x r ∈ (chartExceptional R t x)^j ∧
      chartBase R x t r ∈ (chartExceptional R x t)^j := by
  rw [LinearMap.mem_ker]
  unfold surfaceToCechInput
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- `(t, x)` maps into the exceptional ideal of the chart `R[x/t]`. -/
private theorem map_span_le_chartExceptional (R : Type) [CommRing R] (t x : R) :
    Ideal.map (chartBase R t x) (Ideal.span {t, x}) ≤ chartExceptional R t x := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨y, hy, rfl⟩
  rcases hy with rfl | rfl
  · exact Ideal.subset_span rfl
  · rw [← blowup_chart_relation]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- `(t, x) ^ j` maps into the `j`-th power of the exceptional ideal. -/
private theorem chartBase_mem_chartExceptional_pow (R : Type) [CommRing R] (t x : R) (j : ℕ) (r : R)
    (hr : r ∈ (Ideal.span {t, x}) ^ j) : chartBase R t x r ∈ (chartExceptional R t x)^j := by
  have h1 : chartBase R t x r ∈ Ideal.map (chartBase R t x) ((Ideal.span {t, x})^j) :=
    Ideal.mem_map_of_mem _ hr
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (map_span_le_chartExceptional R t x) j h1

/-- If `r ∈ (t, x) ^ j` and its image lies in the `(j + 1)`-st power of the exceptional ideal,
then `r ∈ (t, x) ^ (j + 1)`. -/
private theorem mem_span_pow_succ_of_chartBase_mem (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (j : ℕ)
    (r : R) (hr : r ∈ (Ideal.span {t, x}) ^ j)
    (hA : chartBase R t x r ∈ (chartExceptional R t x) ^ (j + 1)) :
    r ∈ (Ideal.span {t, x})^(j+1) := by
  obtain ⟨c, rfl⟩ := monomial_span_pow R t x j r hr
  set T := chartBase R t x t
  set Z := chartSlope R t x
  set P : BlowupChart R t x := ∑ i : Fin (j+1), chartBase R t x (c i) * Z ^ i.val with hP
  have hrel : T * Z = chartBase R t x x := blowup_chart_relation R t x
  have himg : chartBase R t x (∑ i : Fin (j+1), c i * t^(j - i.val) * x^i.val) = T^j * P := by
    rw [hP, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : j - i.val + i.val = j := Nat.sub_add_cancel (Nat.lt_succ_iff.mp i.isLt)
    rw [map_mul, map_mul, map_pow, map_pow, ← hrel, mul_pow]
    rw [← pow_sub_mul_pow T (Nat.lt_succ_iff.mp i.isLt)]
    ring
  rw [himg, chartExceptional, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hA
  obtain ⟨q, hq⟩ := hA
  have hreg' : IsLeftRegular T := blowup_exceptional_parameter_regular R t x hreg
  have hPq : P = T * q := by
    apply hreg'.pow j
    simp only
    rw [← hq]; ring
  have hmk : Ideal.Quotient.mk (exceptionalLevelIdeal R t x 1) P = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, exceptionalLevelIdeal, pow_one, hPq]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  obtain ⟨e, he1, he2⟩ := exceptional_chart_is_affine_line R t x
  have hmk' : Ideal.Quotient.mk (exceptionalLevelIdeal R t x 1) P =
      ∑ i : Fin (j+1), levelBase R t x 1 (c i) * levelSlope R t x 1 ^ i.val := by
    rw [hP, map_sum]
    rfl
  have hpoly : (∑ i : Fin (j+1), Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) (c i)) *
      Polynomial.X ^ i.val) = 0 := by
    rw [← map_zero e, ← hmk, hmk', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, he1, he2]
  have hc : ∀ i : Fin (j+1), c i ∈ Ideal.span {t, x} := by
    intro i
    have := congrArg (fun p => Polynomial.coeff p i.val) hpoly
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero]
        at this
    rw [Finset.sum_eq_single i] at this
    · simpa [Ideal.Quotient.eq_zero_iff_mem] using this
    · intro b _ hb
      rw [if_neg]
      intro h; exact hb (Fin.ext h.symm)
    · simp
  refine Ideal.sum_mem _ fun i _ => ?_
  have hi : j - i.val + i.val = j := Nat.sub_add_cancel (Nat.lt_succ_iff.mp i.isLt)
  have hmon : t^(j - i.val) * x^i.val ∈ (Ideal.span {t, x})^j := by
    have h := Ideal.mul_mem_mul
        (Ideal.pow_mem_pow (Ideal.subset_span (by simp) : t ∈ Ideal.span {t, x}) (j - i.val))
      (Ideal.pow_mem_pow (Ideal.subset_span (by simp) : x ∈ Ideal.span {t, x}) i.val)
    rwa [← pow_add, hi] at h
  rw [mul_assoc, pow_succ']
  exact Ideal.mul_mem_mul (hc i) hmon

/-- The kernel of the surface-to-Čech map at level `j` is `(t, x) ^ j`. -/
theorem surface_to_cech_kernel (R : Type) [CommRing R] (t x : R) (hreg : RegularParameterPair R t x)
    (j : ℕ) :
    LinearMap.ker (surfaceToCechInput R t x j) = (Ideal.span {t,x})^j := by
  ext r
  rw [mem_ker_surfaceToCechInput_iff]
  constructor
  · rintro ⟨hA, -⟩
    induction j generalizing r with
    | zero => simp
    | succ j ih =>
      exact mem_span_pow_succ_of_chartBase_mem R t x hreg j r
          (ih r (Ideal.pow_le_pow_right (Nat.le_succ j) hA)) hA
  · intro hr
    refine ⟨chartBase_mem_chartExceptional_pow R t x j r hr, ?_⟩
    rw [Set.pair_comm] at hr
    exact chartBase_mem_chartExceptional_pow R x t j r hr

/-- A surface function whose Čech images are the glued generator pairs lies in `(t, x) ^ d`. -/
theorem glued_function_order (R : Type) [CommRing R] (t x : R) (beta : BlowupRestriction R t x)
    (d : ℕ) (G : GluedGenerators R t x beta d) (hreg : RegularParameterPair R t x) (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f = (cechInputLattice R t x j).mkQ
    (gluedFunctionPair R t x G j)) :
    f ∈ (Ideal.span {t,x})^d := by
  rw [← surface_to_cech_kernel R t x hreg d, LinearMap.mem_ker, hf d,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  unfold cechInputLattice gluedFunctionPair
  rw [Submodule.mem_prod]
  exact ⟨Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) d),
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) d)⟩

/-- Telescoping lemma used to identify the initial form of a glued function. -/
private theorem sub_mem_span_of_pow_mul_sub_mem {A : Type} [CommRing A] (T : A)
    (hinj : Function.Injective (fun a : A => T * a))
    (L : ℕ → A) (hL : ∀ j : ℕ, L (j+1) - L j ∈ (Ideal.span {T})^j) (d : ℕ) (P : A)
    (h : T^d * P - T^d * L (d+1) ∈ (Ideal.span {T})^(d+1)) :
    L 1 - P ∈ Ideal.span {T} := by
  have hinjd : ∀ n : ℕ, IsLeftRegular (T ^ n) := fun n => IsLeftRegular.pow n hinj
  have htel : ∀ k : ℕ, L (k+1) - L 1 ∈ Ideal.span {T} := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := Ideal.pow_le_self (Nat.succ_ne_zero k) (hL (k+1))
      have e : L (k+1+1) - L 1 = (L (k+1+1) - L (k+1)) + (L (k+1) - L 1) := by ring
      rw [e]; exact Ideal.add_mem _ this ih
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  have hPL : P - L (d+1) = T * y := by
    apply hinjd d
    simp only
    rw [mul_sub, ← hy]; ring
  have h1 : P - L (d+1) ∈ Ideal.span {T} := by
    rw [hPL]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self T)
  have e : L 1 - P = -((P - L (d+1)) + (L (d+1) - L 1)) := by ring
  rw [e]; exact (Ideal.neg_mem_iff _).mpr (Ideal.add_mem _ h1 (htel d))

/-- The glued function is a degree-`d` form `∑ cᵢ t^(d-i) xⁱ` whose dehomogenizations agree with
the first glued generators modulo the exceptional ideals of the two charts. -/
theorem glued_function_initial_form (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t) (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f = (cechInputLattice R t x j).mkQ
    (gluedFunctionPair R t x G j)) :
    ∃ c : Fin (d+1) → R, f = ∑ i : Fin (d+1), c i * t^(d - i.val) * x^i.val ∧ G.left 1 - ∑ i : Fin
      (d+1), algebraMap R (BlowupChart R t x) (c i) * (chartSlope R t x)^i.val ∈ chartExceptional R
      t x ∧ G.right 1 - ∑ i : Fin (d+1), algebraMap R (BlowupChart R x t) (c i) *
      (chartSlope R x t)^(d - i.val) ∈ chartExceptional R x t := by
  obtain ⟨c, hc⟩ := monomial_span_pow R t x d f
    (glued_function_order R t x beta d G hreg f hf)
  refine ⟨c, hc, ?_, ?_⟩
  · have hA : ∀ r : R, algebraMap R (BlowupChart R t x) r = chartBase R t x r := fun _ => rfl
    have hrel := blowup_chart_relation R t x
    have hmap : algebraMap R (BlowupChart R t x) f = (chartBase R t x t)^d *
        ∑ i : Fin (d+1), algebraMap R (BlowupChart R t x) (c i) * (chartSlope R t x)^i.val := by
      rw [hc, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hi : i.val + (d - i.val) = d := by omega
      simp only [map_mul, map_pow, hA, ← hrel]
      rw [show (chartBase R t x t)^d = (chartBase R t x t)^i.val * (chartBase R t x t)^(d - i.val)
          from by rw [← pow_add, hi]]
      ring
    have h := glued_function_left_chart R t x beta d G f hf (d+1)
    rw [hmap] at h
    exact sub_mem_span_of_pow_mul_sub_mem _ (blowup_exceptional_parameter_regular R t x hreg)
      G.left G.left_compat d _ h
  · have hA : ∀ r : R, algebraMap R (BlowupChart R x t) r = chartBase R x t r := fun _ => rfl
    have hrel := blowup_chart_relation R x t
    have hmap : algebraMap R (BlowupChart R x t) f = (chartBase R x t x)^d *
        ∑ i : Fin (d+1), algebraMap R (BlowupChart R x t) (c i) *
            (chartSlope R x t)^(d - i.val) := by
      rw [hc, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hi : (d - i.val) + i.val = d := by omega
      simp only [map_mul, map_pow, hA, ← hrel]
      rw [show (chartBase R x t x)^d = (chartBase R x t x)^(d - i.val) * (chartBase R x t x)^i.val
          from by rw [← pow_add, hi]]
      ring
    have h := glued_function_right_chart R t x beta d G f hf (d+1)
    rw [hmap] at h
    exact sub_mem_span_of_pow_mul_sub_mem _ (blowup_exceptional_parameter_regular R x t hregSwap)
      G.right G.right_compat d _ h

/-- For `(t, x)`-adically complete `R`, the map from `R` to compatible Čech threads is injective. -/
theorem surface_threads_injective (R : Type) [CommRing R] (t x : R)
    [IsAdicComplete (Ideal.span {t,x}) R] (hreg : RegularParameterPair R t x) :
    Function.Injective (surfaceThreads R t x) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro r hr
  rw [LinearMap.mem_ker] at hr
  have hj : ∀ j : ℕ, r ∈ (Ideal.span {t,x})^j := by
    intro j
    rw [← surface_to_cech_kernel R t x hreg j, LinearMap.mem_ker]
    exact (congrArg (cechInputThreadLinear R t x j) hr).trans (map_zero _)
  have h := IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {t,x}) (M := R)) r
    (fun n => by
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact hj n)
  simpa using h

/-- Exactness at level `j`: the image of the surface-to-Čech map is the kernel of the twist-`0`
Čech differential. -/
theorem surface_to_cech_range (R : Type) [CommRing R] (t x : R) (hreg : RegularParameterPair R t x)
    (hregSwap : RegularParameterPair R x t) (beta : BlowupRestriction R t x) (j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta 0)) :
    LinearMap.range (surfaceToCechInput R t x j) = LinearMap.ker
      (finiteCechDifferential R t x beta 0 j h) := by
  have key : ∀ k (w : CechLevelInput R t x k),
      finiteCechDifferential R t x beta 0 k
        (actual_cech_preserves_exceptional_lattices R t x beta 0 k) w = 0 →
      w ∈ LinearMap.range (surfaceToCechInput R t x k) := by
    intro k
    induction k with
    | zero =>
      intro w _
      refine ⟨0, ?_⟩
      induction w using Submodule.Quotient.induction_on with
      | H z =>
        rw [map_zero, eq_comm, Submodule.Quotient.mk_eq_zero]
        simp only [cechInputLattice]
        refine ⟨?_, ?_⟩
        · change z.1 ∈ (1 : Ideal (BlowupChart R t x))
          exact (Ideal.one_eq_top (R := BlowupChart R _ _)) ▸ Submodule.mem_top
        · change z.2 ∈ (1 : Ideal (BlowupChart R x t))
          exact (Ideal.one_eq_top (R := BlowupChart R _ _)) ▸ Submodule.mem_top
    | succ k ih =>
      intro w hw
      have hcomm := actual_cech_differentials_commute_with_reduction R t x beta 0 k
        (actual_cech_preserves_exceptional_lattices R t x beta 0 (k+1))
        (actual_cech_preserves_exceptional_lattices R t x beta 0 k)
      have hw' : finiteCechDifferential R t x beta 0 k
          (actual_cech_preserves_exceptional_lattices R t x beta 0 k)
          (cechInputReduction R t x k w) = 0 := by
        have := congrArg (fun f => f w) hcomm
        simp only [LinearMap.comp_apply] at this
        rw [← this, hw, map_zero]
      obtain ⟨r, hr⟩ := ih _ hw'
      have hred : cechInputReduction R t x k (surfaceToCechInput R t x (k+1) r) =
          surfaceToCechInput R t x k r := rfl
      obtain ⟨r', -, hr'⟩ := surface_layer_kernel_lift R t x hreg hregSwap beta k
        (actual_cech_preserves_exceptional_lattices R t x beta 0 (k+1))
        (w - surfaceToCechInput R t x (k+1) r)
        (by rw [map_sub, hw, surface_section_closed, sub_zero])
        (by rw [map_sub, hred, hr, sub_self])
      exact ⟨r + r', by rw [map_add, hr', add_sub_cancel]⟩
  ext w
  exact ⟨by rintro ⟨r, rfl⟩; exact surface_section_closed R t x beta j h r, key j w⟩

private theorem sub_mem_span_sup_of_sub_mem {A : Type} [CommRing A] (g a p s : A) (K : Ideal A)
    (h : s - (p - g * a) ∈ K) : p - s ∈ Ideal.span {g} ⊔ K := by
  rw [show p - s = g * a + -(s - (p - g * a)) by ring]
  exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    (neg_mem h)

/-- If the twist-`d` Čech differential preserves the level-`j` lattices, so does the twist-`0`
one: the twist `(x/t)⁻ᵈ` is a unit modulo the overlap exceptional ideal. -/
private theorem cechInputLattice_le_comap_twist_zero (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta d)) :
    cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
      (fullCechDifferential R t x beta 0) := by
  set u := IsLocalization.Away.invSelf (chartSlope R t x) (S := BlowupOverlap R t x)
  let π := Ideal.Quotient.mk ((Ideal.span {overlapException R t x}) ^ j)
  have hπ : ∀ w, w ∈ cechOutputLattice R t x j ↔ π w = 0 :=
    fun w => (Ideal.Quotient.eq_zero_iff_mem).symm
  have hfc : ∀ (d' : ℕ) (a : BlowupChart R t x) (b : BlowupChart R x t),
      fullCechDifferential R t x beta d' (a, b) =
        algebraMap _ (BlowupOverlap R t x) a - u ^ d' * beta.right b := fun _ _ _ => rfl
  have hpow : (π (overlapSlope R t x) * π u) ^ d = 1 := by
    rw [← map_mul, show overlapSlope R t x * u = 1 from IsLocalization.Away.mul_invSelf _, map_one,
      one_pow]
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  have hA' := (hπ _).1 (h (show (a, 0) ∈ cechInputLattice R t x j from ⟨ha, zero_mem _⟩))
  have hB' := (hπ _).1 (h (show (0, b) ∈ cechInputLattice R t x j from ⟨zero_mem _, hb⟩))
  change _ ∈ cechOutputLattice R t x j
  rw [hπ, hfc]
  rw [hfc] at hA' hB'
  simp only [map_sub, map_mul, map_pow, map_zero, map_neg, mul_zero, sub_zero, zero_sub,
    pow_zero, one_mul] at hA' hB' ⊢
  linear_combination hA' + (π (overlapSlope R t x)) ^ d * hB' + π (beta.right b) * hpow

/-- The connecting class of a curve section vanishes iff the section differs from the image of
a surface function by an element of the curve ideal lattice. -/
theorem curve_section_connecting_class_zero_iff (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t) (j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta d))
    (hregF : Function.Injective
    (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j => Ideal.Quotient.mk
    ((Ideal.span {overlapException R t x})^j)
    ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (p : BlowupChart R t x × BlowupChart R x t) (hp : p ∈ curveSections R t x beta G j)
    (c : BlowupOverlap R t x)
    (hc : fullCechDifferential R t x beta 0 p -
    (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * c ∈
    (Ideal.span {overlapException R t x})^j) :
    (LinearMap.range (finiteCechDifferential R t x beta d j h)).mkQ
      ((cechOutputLattice R t x j).mkQ c) = 0 ↔ ∃ r : R, p - surfaceToChartPair R t x r ∈
      curveIdealLattice R t x beta G j := by
  set E := (Ideal.span {overlapException R t x})^j with hE
  set α := algebraMap (BlowupChart R t x) (BlowupOverlap R t x) with hα
  set u := IsLocalization.Away.invSelf (chartSlope R t x) (S := BlowupOverlap R t x) with hu
  have hmemE : ∀ w, w ∈ cechOutputLattice R t x j ↔ w ∈ E := fun _ => Iff.rfl
  have hfc : ∀ (d' : ℕ) (a : BlowupChart R t x) (b : BlowupChart R x t),
      fullCechDifferential R t x beta d' (a, b) = α a - u ^ d' * beta.right b := fun _ _ _ => rfl
  let π := Ideal.Quotient.mk E
  have hπ : ∀ w, w ∈ E ↔ π w = 0 := fun w => (Ideal.Quotient.eq_zero_iff_mem).symm
  have hpow : (π (overlapSlope R t x) * π u) ^ d = 1 := by
    rw [← map_mul, show overlapSlope R t x * u = 1 from IsLocalization.Away.mul_invSelf _, map_one,
      one_pow]
  -- u^d α F_A ≡ β F_B
  have hov : π (u ^ d * α (G.left j)) = π (beta.right (G.right j)) := by
    have h1 := (hπ _).1 (G.overlap j)
    simp only [map_sub, map_mul, map_pow] at h1 ⊢
    rw [← hα] at h1
    linear_combination (π u) ^ d * h1 + π (beta.right (G.right j)) * hpow
  have h0 := cechInputLattice_le_comap_twist_zero R t x beta d j h
  obtain ⟨p1, p2⟩ := p
  have hc' := (hπ _).1 hc
  rw [hfc] at hc'
  simp only [map_sub, map_mul, pow_zero, one_mul] at hc'
  have hαr : ∀ r : R, α (algebraMap R _ r) = algebraMap R (BlowupOverlap R t x) r := fun r =>
    (IsScalarTower.algebraMap_apply R (BlowupChart R t x) (BlowupOverlap R t x) r).symm
  have hβr : ∀ r : R, beta.right (algebraMap R _ r) = algebraMap R (BlowupOverlap R t x) r :=
    fun r => beta.right.commutes r
  simp only [map_mul, map_pow] at hov
  constructor
  · intro hz
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨q, hq⟩ := hz
    obtain ⟨⟨a', b'⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [finiteCechDifferential, Submodule.mapQ_apply, Submodule.Quotient.eq, hmemE, hπ, hfc] at hq
    simp only [map_sub, map_mul, map_pow] at hq
    have hker : (Submodule.Quotient.mk (p1 - G.left j * a', p2 - G.right j * b') :
        CechLevelInput R t x j) ∈ LinearMap.ker (finiteCechDifferential R t x beta 0 j h0) := by
      rw [LinearMap.mem_ker, finiteCechDifferential, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero, hmemE, hπ, hfc]
      simp only [map_sub, map_mul, pow_zero, one_mul]
      linear_combination hc' - π (α (G.left j)) * hq - π (beta.right b') * hov
    rw [← surface_to_cech_range R t x hreg hregSwap beta j h0] at hker
    obtain ⟨r, hr⟩ := hker
    rw [surfaceToCechInput, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hr
    obtain ⟨hr1, hr2⟩ := hr
    exact ⟨r, sub_mem_span_sup_of_sub_mem _ _ _ _ _ hr1, sub_mem_span_sup_of_sub_mem _ _ _ _ _ hr2⟩
  · rintro ⟨r, h1, h2⟩
    change p1 - algebraMap R _ r ∈ leftCurveIdeal R t x beta G j at h1
    change p2 - algebraMap R _ r ∈ rightCurveIdeal R t x beta G j at h2
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨y', hy', z', hz', hyz'⟩ := Submodule.mem_sup.1 h2
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hy'
    have hzz := (hπ _).1 ((hmemE _).1 (h0 (show (z, z') ∈ cechInputLattice R t x j from ⟨hz, hz'⟩)))
    rw [hfc] at hzz
    simp only [map_sub, pow_zero, one_mul] at hzz
    have ep1 : p1 = a' * G.left j + z + algebraMap R _ r := by linear_combination -hyz
    have ep2 : p2 = b' * G.right j + z' + algebraMap R _ r := by linear_combination -hyz'
    rw [ep1, ep2] at hc'
    simp only [map_add, map_mul, hαr, hβr] at hc'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨Submodule.Quotient.mk (a', b'), ?_⟩
    rw [finiteCechDifferential, Submodule.mapQ_apply, Submodule.Quotient.eq, hmemE, hπ, hfc]
    have key : π c = π (α a' - u ^ d * beta.right b') := by
      apply hregF
      change π (α (G.left j)) * π c = π (α (G.left j)) * π (α a' - u ^ d * beta.right b')
      simp only [map_sub, map_mul, map_pow]
      linear_combination -hc' + hzz + π (beta.right b') * hov
    rw [map_sub, key, sub_self]

/-- For complete `R`, the image of `R` in Čech threads is the intersection of the kernels of the
levelwise twist-`0` Čech differentials. -/
theorem surface_threads_range (R : Type) [CommRing R] (t x : R)
    [IsAdicComplete (Ideal.span {t,x}) R] (hreg : RegularParameterPair R t x)
    (hregSwap : RegularParameterPair R x t) (beta : BlowupRestriction R t x)
    (hpres : ∀ j : ℕ, cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta 0)) :
    LinearMap.range (surfaceThreads R t x) = ⨅ j : ℕ, LinearMap.ker
      ((finiteCechDifferential R t x beta 0 j (hpres j)).comp (cechInputThreadLinear R t x j)) := by
  set I : Ideal R := Ideal.span {t,x}
  -- key: equal images iff difference in I^j
  have hEq : ∀ (j : ℕ) (r s : R), surfaceToCechInput R t x j r = surfaceToCechInput R t x j s ↔
      r - s ∈ I ^ j := by
    intro j r s
    rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, surface_to_cech_kernel R t x hreg j]
  have hcoord : ∀ (r : R) (j : ℕ), cechInputThreadLinear R t x j (surfaceThreads R t x r) =
      surfaceToCechInput R t x j r := fun _ _ => rfl
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    rw [Submodule.mem_iInf]
    intro j
    rw [LinearMap.mem_ker, LinearMap.comp_apply, hcoord]
    exact surface_section_closed R t x beta j (hpres j) r
  · intro a ha
    rw [Submodule.mem_iInf] at ha
    have hr : ∀ j, ∃ r : R, surfaceToCechInput R t x j r = cechInputThreadLinear R t x j a := by
      intro j
      have := ha j
      rwa [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker,
        ← surface_to_cech_range R t x hreg hregSwap beta j (hpres j)] at this
    choose f hf using hr
    have hcompat : ∀ j, cechInputReduction R t x j (cechInputThreadLinear R t x (j+1) a) =
        cechInputThreadLinear R t x j a :=
      fun j => (sub_eq_zero.mp (congrFun (LinearMap.mem_ker.mp a.2) j :)).symm
    have hstep : ∀ j, f (j+1) - f j ∈ I ^ j := by
      intro j
      rw [← hEq, hf j, ← hcompat j, ← hf (j+1)]
      rfl
    have hcauchy : ∀ m n, m ≤ n → f n - f m ∈ I ^ m := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih => simpa using Submodule.add_mem _ (Ideal.pow_le_pow_right hmn (hstep n)) ih
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := I) (M := R))
      (f := f) (fun {m n} hmn => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
        exact hcauchy m n hmn)
    refine ⟨L, ?_⟩
    apply Subtype.ext
    funext j
    change surfaceToCechInput R t x j L = cechInputThreadLinear R t x j a
    rw [← hf j, hEq]
    have := hL j
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    rwa [← neg_mem_iff, neg_sub]

/-- For complete `R`, there is a unique surface function whose Čech images are the glued
generator pairs at every level. -/
theorem glued_function_exists_unique (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    [IsAdicComplete (Ideal.span {t,x}) R] (hreg : RegularParameterPair R t x)
    (hregSwap : RegularParameterPair R x t) :
    ∃! f : R, ∀ j : ℕ, surfaceToCechInput R t x j f = (cechInputLattice R t x j).mkQ
      (gluedFunctionPair R t x G j) := by
  let v : ∀ j, CechLevelInput R t x j :=
    fun j => (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j)
  have hv : v ∈ towerThreads R (fun j => CechLevelInput R t x j) (cechInputReduction R t x) := by
    rw [towerThreads, LinearMap.mem_ker]
    funext j
    change v j - cechInputReduction R t x j (v (j+1)) = 0
    rw [sub_eq_zero]
    exact (glued_function_pair_compatible R t x beta d G j).symm
  let a : CechInputThreads R t x := ⟨v, hv⟩
  have hpres := fun j => actual_cech_preserves_exceptional_lattices R t x beta 0 j
  have ha : a ∈ LinearMap.range (surfaceThreads R t x) := by
    rw [surface_threads_range R t x hreg hregSwap beta hpres, Submodule.mem_iInf]
    intro j
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact glued_function_pair_closed R t x beta d G j (hpres j)
  obtain ⟨f, hf⟩ := ha
  refine ⟨f, fun j => ?_, fun g hg => ?_⟩
  · exact congrArg (fun b => cechInputThreadLinear R t x j b) hf
  · apply surface_threads_injective R t x hreg
    rw [hf]
    apply Subtype.ext
    funext j
    exact hg j

/-- Surface functions map linearly to the curve order limit, through constant curve threads. -/
theorem surface_to_curve_limit_exists (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d) :
    ∃ σ : R →ₗ[R] CurveOrderLimit R t x beta G, ∀ r : R, ∃ p : curveThreads R t x beta G, σ r =
      curveLimitMk R t x beta G p ∧ ∀ j : ℕ, p.val j = surfaceToChartPair R t x r := by
  have hmem : ∀ r : R, (fun _ : ℕ => surfaceToChartPair R t x r) ∈ curveThreads R t x beta G := by
    intro r
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, Submodule.mem_pi]
      intro j _
      rw [curveSections, Submodule.mem_comap]
      have : fullCechDifferential R t x beta 0 (surfaceToChartPair R t x r) = 0 := by
        simp [fullCechDifferential, surfaceToChartPair, ringCechDifferential, ←
            IsScalarTower.algebraMap_apply]
      rw [this]; exact Submodule.zero_mem _
    · rw [SetLike.mem_coe, Submodule.mem_comap]
      have : towerDelta R (fun _ => ChartPair R t x) (fun _ => LinearMap.id)
          (fun _ : ℕ => surfaceToChartPair R t x r) = 0 := by
        ext j <;> simp [towerDelta]
      rw [this]; exact Submodule.zero_mem _
  let f : R →ₗ[R] curveThreads R t x beta G :=
    LinearMap.codRestrict _ (LinearMap.pi fun _ : ℕ => surfaceToChartPair R t x) hmem
  refine ⟨(curveLimitMk R t x beta G).comp f, fun r => ⟨f r, rfl, fun j => rfl⟩⟩

/-! ### Fixed tangent cells in coordinate charts -/

/-- The image of the uniformizer `pi` in `R` is nonzero and lies in the maximal ideal. -/
theorem surface_vertical_parameter (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) :
    algebraMap O R S.pi ≠ 0 ∧ algebraMap O R S.pi ∈ IsLocalRing.maximalIdeal R := by
  refine ⟨?_, ?_⟩
  · intro h
    apply S.pi_irreducible.ne_zero
    apply S.base_injective
    rw [h, map_zero]
  · have ht : S.t ∈ IsLocalRing.maximalIdeal R := by
      rw [← S.parameters]
      exact Ideal.subset_span (by simp)
    rw [S.vertical]
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_left
    exact Ideal.pow_mem_of_mem _ ht _ S.a_pos

/-- Perturbing a generator by a multiple of `pi ^ M` with `M ≥ d + 1` does not change its tangent
divisor of degree `d`. -/
private theorem surface_tangent_jet_small_perturbation (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (d M : ℕ) (hM : d + 1 ≤ M) (f h : R)
    (H : Polynomial (IsLocalRing.ResidueField R))
    (D : ExceptionalDivisor (IsLocalRing.ResidueField R))
    (hD : HasHomogeneousDivisor (IsLocalRing.ResidueField R) d H D)
    (hjet : f - tangentLift O R S d H ∈ (IsLocalRing.maximalIdeal R) ^ (d + 1)) :
    HasTangentDivisor O R S (Ideal.span {f + algebraMap O R S.pi^M * h}) d D := by
  refine ⟨f + algebraMap O R S.pi^M * h, H, rfl, hD, ?_⟩
  have hpi := (surface_vertical_parameter O R S).2
  have h1 : algebraMap O R S.pi ^ M * h ∈ (IsLocalRing.maximalIdeal R)^(d+1) := by
    apply Ideal.mul_mem_right
    exact Ideal.pow_le_pow_right hM (Ideal.pow_mem_pow hpi M)
  have : f + algebraMap O R S.pi ^ M * h - tangentLift O R S d H
      = (f - tangentLift O R S d H) + algebraMap O R S.pi ^ M * h := by ring
  rw [this]
  exact Ideal.add_mem _ hjet h1

/-- `coordinateLift` is additive. -/
private theorem coordinateLift_add {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {n : ℕ}
    (b : Fin n → R) (z w : Fin n → O) :
    coordinateLift b (z + w) = coordinateLift b z + coordinateLift b w := by
  unfold coordinateLift
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_smul]

/-- Having a given tangent divisor of degree `d ≤ M` is constant on `pi ^ M`-congruence classes
of chart coordinates. -/
private theorem hasTangentDivisor_of_adicCongr (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (n : ℕ) (b : Fin n → R) (f : R)
    (d M : ℕ) (hM : d ≤ M) (D : ExceptionalDivisor (IsLocalRing.ResidueField R))
    (z z' : Fin n → O) (hc : adicCongr (Ideal.span {S.pi}) M z z')
    (ht : HasTangentDivisor O R S (coordinateIdeal S.pi f b z') d D) :
    HasTangentDivisor O R S (coordinateIdeal S.pi f b z) d D := by
  rw [finite_coordinate_adic_congruence] at hc
  have hy : ∀ i, ∃ y : O, z i = z' i + S.pi ^ M * y := by
    intro i
    have := hc i
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
    obtain ⟨y, hy⟩ := this
    exact ⟨y, by rw [← hy]; ring⟩
  choose y hy using hy
  have hz : z = z' + S.pi ^ M • y := by
    funext i; simp [hy i]
  obtain ⟨g, H, hJ, hD, hjet⟩ := ht
  unfold coordinateIdeal normalizedIdeal normalizedGenerator at hJ ⊢
  rw [Ideal.span_singleton_eq_span_singleton] at hJ
  obtain ⟨u, hu⟩ := hJ
  have hgen : f + coordinateLift b (S.pi • z) =
      f + coordinateLift b (S.pi • z') + algebraMap O R S.pi ^ (M+1) * coordinateLift b y := by
    rw [hz, smul_add, coordinateLift_add, smul_smul,
      coordinateLift_smul_eq_mul b (S.pi * S.pi ^ M)]
    simp only [map_mul, map_pow]
    ring
  have := surface_tangent_jet_small_perturbation O R S d (M+1) (by omega) g
    (coordinateLift b y * (u : R)) H D hD hjet
  rw [← hu] at this
  rw [hgen, ← Ideal.span_singleton_mul_right_unit u.isUnit]
  convert this using 3
  ring

open scoped Classical in
/-- Inside a coordinate chart, the fixed tangent cell is the disjoint union of the chart images
of the `pi ^ M`-cosets of those representatives that have the prescribed tangent divisor. -/
theorem fixed_tangent_cell_chart_partition (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (st : State) (n : ℕ) (b : Fin n → R) (f : R)
    (hf : Ideal.span {f} ∈ surfaceStateSet O R S st)
    (hinj : Function.Injective (coordinateIdeal S.pi f b)) (d M : ℕ) (hM : d ≤ M)
    (D : ExceptionalDivisor (IsLocalRing.ResidueField R)) (reps : Finset (Fin n → O))
    (hreps : ∀ z : Fin n → O, ∃! z₀, z₀ ∈ reps ∧ adicCongr (Ideal.span {S.pi}) M z z₀) :
    fixedTangentCell O R S st d D ∩ Set.range (coordinateIdeal S.pi f b) = ⋃ z₀ ∈ reps.filter
      (fun z₀ => HasTangentDivisor O R S (coordinateIdeal S.pi f b z₀) d D), coordinateIdeal S.pi f
      b '' coordinateCoset S.pi M z₀ ∧ (reps : Set (Fin n → O)).PairwiseDisjoint
      (fun z₀ => coordinateIdeal S.pi f b '' coordinateCoset S.pi M z₀) := by
  have hsymm : ∀ z z' : Fin n → O, adicCongr (Ideal.span {S.pi}) M z z' →
      adicCongr (Ideal.span {S.pi}) M z' z := by
    intro z z' h
    unfold adicCongr at *
    rw [← neg_sub]; exact Submodule.neg_mem _ h
  have hstate : ∀ z, coordinateIdeal S.pi f b z ∈ surfaceStateSet O R S st := by
    intro z
    unfold coordinateIdeal normalizedIdeal normalizedGenerator
    rw [coordinateLift_smul_eq_mul]
    exact surface_state_vertical_perturbation O R S st f _ hf
  refine ⟨?_, ?_⟩
  · ext J
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_iUnion, Finset.mem_filter,
      exists_prop, Set.mem_image]
    constructor
    · rintro ⟨⟨_, htd⟩, z, rfl⟩
      obtain ⟨z₀, ⟨hz₀, hc⟩, _⟩ := hreps z
      exact ⟨z₀, ⟨hz₀, hasTangentDivisor_of_adicCongr O R S n b f d M hM D z₀ z (hsymm _ _ hc) htd⟩,
          z, hc, rfl⟩
    · rintro ⟨z₀, ⟨_, htd⟩, z, hz, rfl⟩
      exact ⟨⟨hstate z, hasTangentDivisor_of_adicCongr O R S n b f d M hM D z z₀ hz htd⟩, z, rfl⟩
  · intro a ha a' ha' hne
    simp only [Function.onFun]
    rw [Set.disjoint_image_iff hinj]
    refine Set.disjoint_left.mpr fun z hz hz' => hne ?_
    obtain ⟨w, _, huniq⟩ := hreps z
    rw [huniq a ⟨ha, hz⟩, huniq a' ⟨ha', hz'⟩]

/-- The part of a fixed tangent cell inside a coordinate chart is measurable for the chart
σ-algebra. -/
theorem fixed_tangent_cell_chart_measurable (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    [MeasurableSpace O] (S : SurfaceData O R) (st : State) (n : ℕ) (b : Fin n → R) (f : R)
    (hf : Ideal.span {f} ∈ surfaceStateSet O R S st)
    (hinj : Function.Injective (coordinateIdeal S.pi f b)) (hchart : IsDivisionChart O R S.pi f b)
    (d M : ℕ) (hM : d ≤ M) (D : ExceptionalDivisor (IsLocalRing.ResidueField R))
    (reps : Finset (Fin n → O))
    (hreps : ∀ z : Fin n → O, ∃! z₀, z₀ ∈ reps ∧ adicCongr (Ideal.span {S.pi}) M z z₀)
    (hcoset : ∀ z₀ : Fin n → O, MeasurableSet (coordinateCoset S.pi M z₀)) :
    @MeasurableSet (Ideal R) (idealChartSigma O R S.pi)
      (fixedTangentCell O R S st d D ∩ Set.range (coordinateIdeal S.pi f b)) := by
  rw [(fixed_tangent_cell_chart_partition O R S st n b f hf hinj d M hM D reps hreps).1]
  let := idealChartSigma O R S.pi
  exact Finset.measurableSet_biUnion _ fun z₀ _ =>
    chart_image_measurable_chart_sigma O R S.pi n f b hchart _ (hcoset z₀)

/-! ### Twisted kernels -/

/-- A transition unit relating two compatible chart representatives is congruent to `1` modulo
the `j`-th power of the overlap exceptional ideal. -/
theorem transition_unit_congruent_one (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ) (a a2 : BlowupChart R t x) (b b2 : BlowupChart R x t)
    (ha : a2 - a ∈ (chartExceptional R t x) ^ j) (hb : b2 - b ∈ (chartExceptional R x t) ^ j)
    (hlevel : (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a - (overlapSlope R t x) ^ d *
    beta.right b ∈ (Ideal.span {overlapException R t x}) ^ j)
    (hregB : Function.Injective
    (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j => Ideal.Quotient.mk
    ((Ideal.span {overlapException R t x})^j) ((overlapSlope R t x)^d * beta.right b) * c))
    (v : BlowupOverlap R t x)
    (hv : (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a2 - v *
    ((overlapSlope R t x)^d * beta.right b2) ∈ (Ideal.span {overlapException R t x})^j) :
    v - 1 ∈ (Ideal.span {overlapException R t x})^j := by
  set I := (Ideal.span {overlapException R t x})^j with hI
  set α := algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
  have hA : α a2 - α a ∈ I := by
    have h := Ideal.mem_map_of_mem α ha
    rw [Ideal.map_pow, chartExceptional, Ideal.map_span, Set.image_singleton] at h
    rw [← map_sub]; exact h
  have hx : beta.right (chartBase R x t x) ∈ Ideal.span {overlapException R t x} := by
    have h1 : beta.right (chartBase R x t x) = algebraMap R (BlowupOverlap R t x) x :=
      beta.right.commutes x
    have h2 : α (chartBase R t x x) = algebraMap R (BlowupOverlap R t x) x :=
      (IsScalarTower.toAlgHom R (BlowupChart R t x) (BlowupOverlap R t x)).commutes x
    rw [h1, ← h2, ← blowup_chart_relation, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hB : beta.right b2 - beta.right b ∈ I := by
    have h := Ideal.mem_map_of_mem beta.right.toRingHom hb
    rw [Ideal.map_pow, chartExceptional, Ideal.map_span, Set.image_singleton] at h
    rw [← map_sub]
    refine Ideal.pow_right_mono ?_ j h
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hx
  have key : (v - 1) * ((overlapSlope R t x)^d * beta.right b) ∈ I := by
    have e : (v - 1) * ((overlapSlope R t x)^d * beta.right b) =
      -(α a2 - v * ((overlapSlope R t x)^d * beta.right b2)) + (α a2 - α a)
        + (α a - (overlapSlope R t x)^d * beta.right b)
        - (v * (overlapSlope R t x)^d) * (beta.right b2 - beta.right b) := by ring
    rw [e]
    exact I.sub_mem (I.add_mem (I.add_mem (I.neg_mem hv) hA) hlevel) (I.mul_mem_left _ hB)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hregB
  simp only
  rw [← map_mul, mul_comm, Ideal.Quotient.eq_zero_iff_mem.mpr key, mul_zero]

/-- Every closed Čech input class for twist `d` is the class of `(tᵈ r, xᵈ r)` for some surface
function `r`. -/
theorem twisted_kernel_from_surface (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t)
    (beta : BlowupRestriction R t x) (d j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta d)) (w : CechLevelInput R t x j)
    (hw : finiteCechDifferential R t x beta d j h w = 0) :
    ∃ r : R, w = (cechInputLattice R t x j).mkQ
      ((chartBase R t x t)^d * algebraMap R (BlowupChart R t x) r, (chartBase R x t x)^d *
      algebraMap R (BlowupChart R x t) r) := by
  have hβr := beta_right_chartBase beta
  have hD0 : ∀ r : R, fullCechDifferential R t x beta d
      ((chartBase R t x t)^d * chartBase R t x r, (chartBase R x t x)^d * chartBase R x t r) =
          0 := by
    intro r
    change algebraMap (BlowupChart R t x) (BlowupOverlap R t x) _ -
      (IsLocalization.Away.invSelf (chartSlope R t x))^d * beta.right _ = 0
    rw [map_mul, map_mul, map_pow, map_pow, hβr, hβr, chartBase_x_eq, map_mul]
    have hu : (IsLocalization.Away.invSelf (chartSlope R t x) *
        algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x))^d = 1 := by
      rw [mul_comm, IsLocalization.Away.mul_invSelf, one_pow]
    linear_combination
        (-(algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t)^d *
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x r))) * hu
  have main : ∀ n : ℕ, ∀ (a : BlowupChart R t x) (b : BlowupChart R x t),
      fullCechDifferential R t x beta d (a, b) ∈
        (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t)})^n →
      ∃ r : R, a - (chartBase R t x t)^d * chartBase R t x r ∈ (Ideal.span {chartBase R t x t})^n ∧
        b - (chartBase R x t x)^d * chartBase R x t r ∈ (Ideal.span {chartBase R x t x})^n := by
    intro n
    induction n with
    | zero => exact fun _ _ _ => ⟨0, by simp, by simp⟩
    | succ n ih =>
      intro a b hab
      obtain ⟨r, har, hbr⟩ := ih a b (Ideal.pow_le_pow_right (Nat.le_succ n) hab)
      have hD' : fullCechDifferential R t x beta d
          (a - (chartBase R t x t)^d * chartBase R t x r, b - (chartBase R x t x)^d * chartBase R x
              t r) ∈
          (Ideal.span
              {algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
                  (chartBase R t x t)})^(n+1) := by
        rw [← Prod.mk_sub_mk, map_sub, hD0, sub_zero]
        exact hab
      obtain ⟨r', -, ha', hb'⟩ := cech_layer_step R t x hreg beta hregSwap d n _ _ har hbr hD'
      refine ⟨r + r', ?_, ?_⟩
      · convert ha' using 1; rw [map_add]; ring
      · convert hb' using 1; rw [map_add]; ring
  induction w using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨a, b⟩ := z
    rw [finiteCechDifferential, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hw
    obtain ⟨r, har, hbr⟩ := main j a b hw
    refine ⟨r, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact ⟨har, hbr⟩

end SurfaceBlowup
