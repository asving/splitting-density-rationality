/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.CurveOrders

/-!
# Exceptional layers of the point blow-up

Points and layers of the exceptional divisor of the blow-up of a two-dimensional local ring at
`(t, x)`. We identify the closed points of the exceptional fibre of the chart with monic
irreducible polynomials (affine directions) together with the point at infinity of the opposite
chart, compute their residue lengths, describe the principal layers `(e)^j ⧸ (e)^(j+1)` as
polynomial modules, and normalize glued generators at exceptional level one via Laurent
polynomial arithmetic.

## Main results

* `SurfaceBlowup.direction_point_maximal`, `SurfaceBlowup.infinity_point_maximal`: the closed
  points of the exceptional divisor and their lengths.
* `SurfaceBlowup.chart_point_eq_directionPoint`: every exceptional chart point is a direction
  point.
* `SurfaceBlowup.chart_layer_polynomial_coordinates`: layers are polynomial modules.
* `SurfaceBlowup.glued_level_one_normalization`: normalization of glued generators.

Provenance: `Thm_SurfaceBlowupV2_` nodes `laurent_monomial_shift_trailing_degree`,
`glued_level_one_normalization`, `laurent_nonnegative_twist_kernel`,
`laurent_split_nonnegative_twist`, `length_eq_of_surjective_onto_field`,
`blowup_chart_exceptional_point_polynomial`, `chart_point_eq_directionPoint`,
`direction_point_maximal`, `direction_point_overlap_maximal`, `infinity_point_maximal`,
`principal_layer_map_{kernel,range}`, `principal_layer_quotient_equiv`,
`chart_layer_polynomial_coordinates`, `rootMultiplicity_map_eq_count_normalizedFactors`.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-- If `PA = c T^m · T^d · PB(T⁻¹)` in `k[T, T⁻¹]` with `PA, PB ≠ 0`, then the trailing degree of
`PA` is `m + d - deg PB`. -/
private theorem laurent_monomial_shift_trailing_degree (k : Type) [Field k] (PA PB : Polynomial k)
    (hA : PA ≠ 0) (hB : PB ≠ 0) (c : k) (m : ℤ) (d : ℕ)
    (h : PA.toLaurent = LaurentPolynomial.C c * LaurentPolynomial.T m *
      (LaurentPolynomial.T (d : ℤ) * LaurentPolynomial.invert (R := k) PB.toLaurent)) :
    (PA.natTrailingDegree : ℤ) = m + (d : ℤ) - (PB.natDegree : ℤ) := by
  set e : ℤ := m + d - PB.natDegree with he
  set a : ℕ := e.toNat
  set b : ℕ := (-e).toNat
  have hab : (a : ℤ) - b = e := by omega
  have hinv : LaurentPolynomial.invert (R := k) PB.toLaurent
      = PB.reverse.toLaurent * LaurentPolynomial.T (-(PB.natDegree : ℤ)) := by
    rw [LaurentPolynomial.toLaurent_reverse, mul_assoc, ← LaurentPolynomial.T_add]
    simp
  have key : PA * Polynomial.X ^ b = Polynomial.C c * Polynomial.X ^ a * PB.reverse := by
    apply Polynomial.toLaurent_injective
    simp only [map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, h, hinv]
    have : LaurentPolynomial.T (R := k) m * (LaurentPolynomial.T (d : ℤ) *
        LaurentPolynomial.T (-(PB.natDegree : ℤ))) * LaurentPolynomial.T (b : ℤ)
        = LaurentPolynomial.T (a : ℤ) := by
      simp only [← LaurentPolynomial.T_add]; congr 1; omega
    rw [← this]
    ring
  have hc : c ≠ 0 := by
    rintro rfl
    exact hA (by simpa using key)
  have hR : PB.reverse.natTrailingDegree = 0 := Polynomial.natTrailingDegree_reverse _
  have := congrArg Polynomial.natTrailingDegree key
  rw [Polynomial.natTrailingDegree_mul hA (pow_ne_zero _ Polynomial.X_ne_zero),
    Polynomial.natTrailingDegree_mul (mul_ne_zero (Polynomial.C_ne_zero.2 hc)
      (pow_ne_zero _ Polynomial.X_ne_zero)) (by simpa using hB),
    Polynomial.natTrailingDegree_mul (Polynomial.C_ne_zero.2 hc)
      (pow_ne_zero _ Polynomial.X_ne_zero), hR] at this
  simp at this
  omega

/-- The coefficients of `∑_{i ≤ N} f i X^i`. -/
private theorem coeff_sum_fin_C_mul_X_pow {S : Type} [Semiring S] (N : ℕ)
    (f : Fin (N + 1) → S) (j : ℕ) :
    (∑ i : Fin (N + 1), Polynomial.C (f i) * Polynomial.X ^ i.val).coeff j =
      if h : j < N + 1 then f ⟨j, h⟩ else 0 := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩ (fun i _ hi ↦ if_neg fun hj ↦ hi (Fin.ext hj.symm))
      (by simp)]
    simp
  · exact Finset.sum_eq_zero fun i _ ↦ if_neg (by omega)

open LaurentPolynomial in
/-- The exceptional fibre of the overlap chart of the blow-up at `(t, x)` embeds into the Laurent
polynomial ring `(R ⧸ (t, x))[z, z⁻¹]`, sending constants to constants and the slope to `z`; the
embedding has a ring-hom left inverse. -/
private theorem exists_overlap_exceptional_laurent (R : Type) [CommRing R] (t x : R) :
    ∃ (φ : (BlowupOverlap R t x ⧸ Ideal.span {overlapException R t x}) →+*
        LaurentPolynomial (R ⧸ Ideal.span ({t,x} : Set R)))
      (ψ : LaurentPolynomial (R ⧸ Ideal.span ({t,x} : Set R)) →+*
        (BlowupOverlap R t x ⧸ Ideal.span {overlapException R t x})),
      ψ.comp φ = RingHom.id _ ∧
      (∀ r : R, φ (Ideal.Quotient.mk _ (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
        (chartBase R t x r))) = C (Ideal.Quotient.mk _ r)) ∧
      φ (Ideal.Quotient.mk _ (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
        (chartSlope R t x))) = T 1 := by
  set I : Ideal R := Ideal.span ({t,x} : Set R)
  set E : Ideal (BlowupOverlap R t x) := Ideal.span {overlapException R t x}
  have htI : t ∈ I := Ideal.subset_span (by simp)
  have hxI : x ∈ I := Ideal.subset_span (by simp)
  let zQ : (BlowupOverlap R t x ⧸ E)ˣ :=
    ((IsLocalization.Away.algebraMap_isUnit (chartSlope R t x)).map (Ideal.Quotient.mk E)).unit
  let fK : (R ⧸ I) →+* (BlowupOverlap R t x ⧸ E) :=
    Ideal.Quotient.lift I ((Ideal.Quotient.mk E).comp (algebraMap R (BlowupOverlap R t x)))
      fun a ha ↦ by
        refine (Ideal.span_le.2 (Set.pair_subset ?_ ?_) : I ≤ RingHom.ker _) ha <;>
          simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply,
            Ideal.Quotient.eq_zero_iff_mem] <;>
          rw [IsScalarTower.algebraMap_apply R (BlowupChart R t x)]
        · exact Ideal.subset_span rfl
        · change algebraMap _ _ (chartBase R t x x) ∈ _
          rw [← blowup_chart_relation, map_mul]
          exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  let ψ := eval₂ fK zQ
  let φ₀ : BlowupChart R t x →+* LaurentPolynomial (R ⧸ I) :=
    Ideal.Quotient.lift _ (Polynomial.eval₂RingHom (C.comp (Ideal.Quotient.mk I)) (T 1))
      fun a ha ↦ by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        simp [blowupRelation, Ideal.Quotient.eq_zero_iff_mem.mpr htI,
          Ideal.Quotient.eq_zero_iff_mem.mpr hxI]
  have hφ₀ : IsUnit (φ₀ (chartSlope R t x)) := by
    simpa [φ₀, chartSlope] using isUnit_T (R := R ⧸ I) 1
  let φ₁ : BlowupOverlap R t x →+* LaurentPolynomial (R ⧸ I) :=
    IsLocalization.Away.lift (chartSlope R t x) hφ₀
  let φ : (BlowupOverlap R t x ⧸ E) →+* LaurentPolynomial (R ⧸ I) :=
    Ideal.Quotient.lift E φ₁ fun a ha ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [φ₁, overlapException, φ₀, chartBase, Ideal.Quotient.eq_zero_iff_mem.mpr htI]
  have hφA : ∀ a : BlowupChart R t x,
      φ (Ideal.Quotient.mk E (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) a)) = φ₀ a :=
    fun a ↦ by simp only [φ, φ₁, Ideal.Quotient.lift_mk, IsLocalization.Away.lift_eq]
  have hφ₀C : ∀ r : R, φ₀ (chartBase R t x r) = C (Ideal.Quotient.mk I r) :=
    fun r ↦ by simp [φ₀, chartBase]
  have hφ₀Z : φ₀ (chartSlope R t x) = T 1 := by simp [φ₀, chartSlope]
  have hψC : ∀ r : R, ψ (C (Ideal.Quotient.mk I r)) = Ideal.Quotient.mk E
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x r)) := fun r ↦ by
    simp only [ψ, eval₂_C, fK]
    rfl
  have hψφ : ψ.comp φ = RingHom.id _ := by
    refine Ideal.Quotient.ringHom_ext <|
      IsLocalization.ringHom_ext (Submonoid.powers (chartSlope R t x)) <|
      Ideal.Quotient.ringHom_ext <| Polynomial.ringHom_ext (fun a ↦ ?_) ?_ <;>
      simp only [RingHom.comp_apply, RingHom.id_apply] <;> rw [hφA]
    · have := hφ₀C a
      simp only [chartBase, RingHom.comp_apply] at this hψC
      rw [this]; exact hψC a
    · change ψ (φ₀ (chartSlope R t x)) = _
      rw [hφ₀Z]; simp [ψ, zQ, chartSlope]
  exact ⟨φ, ψ, hψφ, fun r ↦ (hφA _).trans (hφ₀C r), (hφA _).trans hφ₀Z⟩

open LaurentPolynomial in
/-- Normalization of glued generators at exceptional level one: if the images of the chart elements
`gA` and `gB` generate the same principal ideal of the exceptional divisor of the overlap, `gA`
reduces to a polynomial of trailing degree `r` and `gB` to one of degree `n` with `r + n = d`,
then `gA ≡ u · z^d · gB` modulo the exceptional divisor for some unit `u` of `R`. -/
theorem glued_level_one_normalization (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsLocalRing R] (_hreg : RegularParameterPair R t x)
    (beta : BlowupRestriction R t x) (d : ℕ) (gA : BlowupChart R t x) (gB : BlowupChart R x t)
    (hoverlap : Ideal.span {Ideal.Quotient.mk (Ideal.span {overlapException R t x})
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) gA)} =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {overlapException R t x}) (beta.right gB)})
    (hregB : Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x}) => Ideal.Quotient.mk
      (Ideal.span {overlapException R t x}) (beta.right gB) * c)) (m n : ℕ) (cA : Fin (m+1) → R)
    (cB : Fin (n+1) → R) (hgA : gA - ∑ i : Fin (m+1),
      algebraMap R (BlowupChart R t x) (cA i) * (chartSlope R t x)^i.val ∈ chartExceptional R t x)
    (hgB : gB - ∑ i : Fin (n+1), algebraMap R (BlowupChart R x t) (cB i) * (chartSlope R x t)^i.val
      ∈ chartExceptional R x t) (r : ℕ) (hlow : ∀ i : Fin (m+1), i.val < r →
      cA i ∈ Ideal.span {t,x}) (hr : ∀ i : Fin (m+1), i.val = r → cA i ∉ Ideal.span {t,x})
    (hrm : r ≤ m) (htop : cB (Fin.last n) ∉ Ideal.span {t,x}) (hdeg : r + n = d) :
    ∃ u : Rˣ, (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) gA - algebraMap R
    (BlowupOverlap R t x) (u : R) * ((overlapSlope R t x)^d * beta.right gB) ∈
    (Ideal.span {overlapException R t x}) := by
  -- Reduce both generators to Laurent polynomials over `R ⧸ (t, x)` on the exceptional fibre
  -- of the overlap; they differ by a unit `c z^m'` there, and comparing degrees gives `m' = d`.
  set I : Ideal R := Ideal.span ({t,x} : Set R)
  set E : Ideal (BlowupOverlap R t x) := Ideal.span {overlapException R t x}
  have htI : t ∈ I := Ideal.subset_span (by simp)
  have hxI : x ∈ I := Ideal.subset_span (by simp)
  obtain ⟨φ, ψ, hψφ, hφC, hφZ⟩ := exists_overlap_exceptional_laurent R t x
  have hψ : ∀ y, ψ (φ y) = y := RingHom.congr_fun hψφ
  set PA : Polynomial (R ⧸ I) :=
    ∑ i : Fin (m+1), Polynomial.C (Ideal.Quotient.mk I (cA i)) * Polynomial.X ^ i.val with hPA
  set PB : Polynomial (R ⧸ I) :=
    ∑ i : Fin (n+1), Polynomial.C (Ideal.Quotient.mk I (cB i)) * Polynomial.X ^ i.val with hPB
  have hPAr : PA.coeff r ≠ 0 := by
    rw [hPA, coeff_sum_fin_C_mul_X_pow, dif_pos (by omega), Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hr ⟨r, by omega⟩ rfl
  have hPA0 : PA ≠ 0 := fun h ↦ hPAr (by simp [h])
  have hPAtr : PA.natTrailingDegree = r :=
    le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hPAr) <|
      Polynomial.le_natTrailingDegree hPA0 fun j hj ↦ by
        rw [hPA, coeff_sum_fin_C_mul_X_pow, dif_pos (by omega)]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hlow ⟨j, by omega⟩ hj)
  have hPBn : PB.coeff n ≠ 0 := by
    rw [hPB, coeff_sum_fin_C_mul_X_pow, dif_pos (by omega), Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact htop
  have hPB0 : PB ≠ 0 := fun h ↦ hPBn (by simp [h])
  have hPBdeg : PB.natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (Polynomial.natDegree_le_iff_coeff_eq_zero.2
      fun j hj ↦ by rw [hPB, coeff_sum_fin_C_mul_X_pow, dif_neg (by omega)]) hPBn
  -- images
  let ΦA : BlowupChart R t x →+* LaurentPolynomial (R ⧸ I) :=
    φ.comp ((Ideal.Quotient.mk E).comp (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)))
  have hΦAexc : ∀ y ∈ chartExceptional R t x, ΦA y = 0 := fun y hy ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [map_mul, show ΦA (chartBase R t x t) = _ from hφC t,
      Ideal.Quotient.eq_zero_iff_mem.mpr htI, map_zero, mul_zero]
  have hφa : φ (Ideal.Quotient.mk E (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) gA)) =
      PA.toLaurent := by
    change ΦA gA = _
    rw [sub_eq_zero.1 ((map_sub ΦA _ _).symm.trans (hΦAexc _ hgA)), hPA, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, Polynomial.toLaurent_C_mul_X_pow, show ΦA (chartSlope R t x) = _ from hφZ,
      T_pow, mul_one]
    exact congrArg (· * _) (hφC _)
  let ΦB : BlowupChart R x t →+* LaurentPolynomial (R ⧸ I) :=
    φ.comp ((Ideal.Quotient.mk E).comp beta.right.toRingHom)
  have hΦBC : ∀ c : R,
      ΦB (algebraMap R (BlowupChart R x t) c) = C (Ideal.Quotient.mk I c) := by
    intro c
    simp only [ΦB, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R (BlowupChart R t x) (BlowupOverlap R t x)]
    exact hφC c
  have hΦBW : ΦB (chartSlope R x t) = T (-1) := by
    simp only [ΦB, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, beta.slope]
    have h1 : φ (Ideal.Quotient.mk E (IsLocalization.Away.invSelf (chartSlope R t x))) *
        T 1 = 1 := by
      rw [← hφZ, ← map_mul, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one,
        map_one]
    have h2 : T (-1) * T (R := R ⧸ I) 1 = 1 := by rw [← T_add]; simp
    exact (isUnit_T (R := R ⧸ I) 1).mul_left_injective (h1.trans h2.symm)
  have hΦBexc : ∀ y ∈ chartExceptional R x t, ΦB y = 0 := fun y hy ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [map_mul, show chartBase R x t x = algebraMap R _ x from rfl, hΦBC,
      Ideal.Quotient.eq_zero_iff_mem.mpr hxI, map_zero, mul_zero]
  have hφb : φ (Ideal.Quotient.mk E (beta.right gB)) = invert PB.toLaurent := by
    change ΦB gB = _
    rw [sub_eq_zero.1 ((map_sub ΦB _ _).symm.trans (hΦBexc _ hgB)), hPB, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, Polynomial.toLaurent_C_mul_X_pow, hΦBW, T_pow, hΦBC,
      map_mul, invert_C, invert_T]
    congr 2
    ring
  -- unit comparison
  obtain ⟨v, hv⟩ := regular_principal_generators_associated (BlowupOverlap R t x ⧸ E)
    (Ideal.Quotient.mk E (beta.right gB))
    (Ideal.Quotient.mk E (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) gA))
    (fun y₁ y₂ h ↦ hregB (by simpa [mul_comm] using h)) hoverlap.symm
  obtain ⟨c, hc, m', hm'⟩ :=
    (letI := Ideal.Quotient.field I; laurent_isUnit_iff_monomial (R ⧸ I) (φ v)).mp (v.isUnit.map φ)
  have hmain : PA.toLaurent = C c * T m' *
      (T ((0:ℕ):ℤ) * invert (R := R ⧸ I) PB.toLaurent) := by
    rw [← hφa, hv, map_mul, hm', hφb]; simp
  have hdeg' := letI := Ideal.Quotient.field I
    laurent_monomial_shift_trailing_degree (R ⧸ I) PA PB hPA0 hPB0 c m' 0 hmain
  rw [hPAtr, hPBdeg] at hdeg'
  have hm'd : m' = (d : ℤ) := by push_cast at hdeg'; omega
  obtain ⟨u, hu⟩ := units_lift_from_local_quotient R I
    (IsLocalRing.le_maximalIdeal (Ideal.IsMaximal.ne_top inferInstance))
    (letI := Ideal.Quotient.field I; isUnit_iff_ne_zero.mpr hc).unit
  simp only [IsUnit.unit_spec] at hu
  refine ⟨u, ?_⟩
  rw [← Ideal.Quotient.eq, hv, ← hψ v, hm', hm'd, ← hu, show T (d : ℤ) = T 1 ^ d by
    rw [T_pow, mul_one], ← hφC, ← hφZ, ← map_pow, ← map_mul, hψ]
  rw [show algebraMap R (BlowupOverlap R t x) u =
    algebraMap (BlowupChart R t x) _ (chartBase R t x u) from rfl]
  simp only [map_mul, map_pow, overlapSlope]
  ring

private theorem laurent_twist_kernel_coeff_toLaurent {k : Type} [CommRing k] (f : Polynomial k)
    (z : ℤ) : f.toLaurent.coeff z = if 0 ≤ z then f.coeff z.toNat else 0 := by
  split_ifs with hz
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [LaurentPolynomial.coeff_toLaurent]
    have := Finsupp.mapDomain_apply (Nat.castEmbedding (R := ℤ)).injective f.toFinsupp.coeff n
    simp only [Nat.castEmbedding_apply] at this
    simp only [Int.toNat_natCast]; exact this.trans rfl
  · rw [LaurentPolynomial.coeff_toLaurent]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨n, hn⟩
    simp at hn
    omega

private theorem toLaurent_coeff_of_eq_T_mul_invert {k : Type} [CommRing k] (m : ℕ)
    (P Q : Polynomial k)
    (h : P.toLaurent = LaurentPolynomial.T (m : ℤ) * LaurentPolynomial.invert (R := k) Q.toLaurent)
    (n : ℤ) : P.toLaurent.coeff n = Q.toLaurent.coeff (m - n) := by
  rw [h, LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply,
    LaurentPolynomial.invert_apply, one_mul]
  congr 1; ring

/-- If `P(T) = T^m · Q(T⁻¹)` in `k[T, T⁻¹]` with `m ≥ 0`, then `deg P ≤ m` and `Q` is the reversal
of `P` at level `m`. -/
theorem laurent_nonnegative_twist_kernel (k : Type) [CommRing k] (m : ℕ) (P Q : Polynomial k)
    (h : P.toLaurent =
      LaurentPolynomial.T (m : ℤ) * LaurentPolynomial.invert (R := k) Q.toLaurent) :
    P.natDegree ≤ m ∧ ∀ i : ℕ, Q.coeff i = if i ≤ m then P.coeff (m - i) else 0 := by
  have key := toLaurent_coeff_of_eq_T_mul_invert m P Q h
  simp only [laurent_twist_kernel_coeff_toLaurent] at key
  refine ⟨?_, fun i ↦ ?_⟩
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    have := key n
    simp only [Nat.cast_nonneg, if_true, Int.toNat_natCast] at this
    rw [this, if_neg]
    have : (m : ℕ) < n := by exact_mod_cast hn
    omega
  · split_ifs with hi
    · have := key ((m - i : ℕ) : ℤ)
      simp only [Nat.cast_nonneg, if_true, Int.toNat_natCast] at this
      rw [this, if_pos (by omega)]
      congr 1; omega
    · have := key ((m : ℤ) - i)
      rw [if_neg (by omega), if_pos (by omega)] at this
      rw [show ((m : ℤ) - ((m : ℤ) - i)).toNat = i by omega] at this
      exact this.symm

/-- For `m ≥ -1`, every Laurent polynomial can be written as `P(T) - T^m · Q(T⁻¹)` with `P, Q`
polynomials. -/
theorem laurent_split_nonnegative_twist (k : Type) [CommRing k] (m : ℤ) (hm : -1 ≤ m)
    (F : LaurentPolynomial k) :
    ∃ P Q : Polynomial k, F = P.toLaurent - LaurentPolynomial.T m *
    (LaurentPolynomial.invert (R := k) Q.toLaurent) := by
  induction F using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P1, Q1, h1⟩ := hp
    obtain ⟨P2, Q2, h2⟩ := hq
    refine ⟨P1 + P2, Q1 + Q2, ?_⟩
    rw [h1, h2]
    simp only [map_add]
    ring
  | C_mul_T n a =>
    rcases le_or_gt 0 n with hn | hn
    · refine ⟨Polynomial.C a * Polynomial.X ^ n.toNat, 0, ?_⟩
      simp only [map_zero, mul_zero, sub_zero, map_mul, Polynomial.toLaurent_C,
        Polynomial.toLaurent_X_pow]
      rw [Int.toNat_of_nonneg hn]
    · refine ⟨0, -(Polynomial.C a * Polynomial.X ^ (m - n).toNat), ?_⟩
      simp only [map_zero, map_neg, map_mul, Polynomial.toLaurent_C,
        Polynomial.toLaurent_X_pow, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        zero_sub, mul_neg, neg_neg]
      rw [Int.toNat_of_nonneg (by omega), mul_left_comm, ← LaurentPolynomial.T_add]
      congr 2
      ring

/-- If `R` acts on a finite-dimensional `k`-vector space `M` through a surjection `f : R → k`, then
the `R`-length of `M` equals its `k`-dimension. -/
private theorem length_eq_of_surjective_onto_field (R k M : Type) [CommRing R] [Field k]
    [AddCommGroup M]
    [Module R M] [Module k M] (f : R →+* k) (hf : Function.Surjective f)
    (hcompat : ∀ (r : R) (m : M), r • m = f r • m) [Module.Finite k M] :
    Module.length R M = (Module.finrank k M : ℕ∞) := by
  have : RingHomSurjective f := ⟨hf⟩
  let g : M →ₛₗ[f] M := ⟨AddHom.id M, fun r m ↦ hcompat r m⟩
  rw [← Module.length_eq_finrank k M]
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective g Function.bijective_id)]

/-- Given an identification `e` of the exceptional fibre of the chart with `(R/(t,x))[Z]`, a maximal
ideal `P` containing `t` corresponds to a monic irreducible `φ`: `P` maps onto `(φ)`, contains
the slope iff `φ = Z`, and has `R`-length `deg φ`. -/
theorem blowup_chart_exceptional_point_polynomial (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial
      (R ⧸ Ideal.span ({t,x} : Set R))) (he : ∀ r : R,
      e (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.span ({t,x} : Set R)) r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X)
    (P : Ideal (BlowupChart R t x)) [P.IsMaximal] (hP : chartBase R t x t ∈ P) :
    ∃ φ : Polynomial (R ⧸ Ideal.span ({t,x} : Set R)), φ.Monic ∧ Irreducible φ ∧
    (P.map (Ideal.Quotient.mk (chartExceptional R t x))).map e = Ideal.span {φ} ∧
    (chartSlope R t x ∈ P ↔ φ = Polynomial.X) ∧ Module.length R (BlowupChart R t x ⧸ P) =
    (φ.natDegree : ℕ∞) := by
  let : Field (R ⧸ Ideal.span ({t,x} : Set R)) := Ideal.Quotient.field _
  have hIP : chartExceptional R t x ≤ P := by
    rw [show chartExceptional R t x = Ideal.span {chartBase R t x t} from rfl, Ideal.span_le]
    simpa using hP
  set Pb := P.map (Ideal.Quotient.mk (chartExceptional R t x)) with hPb
  have hmk : Function.Surjective (Ideal.Quotient.mk (chartExceptional R t x)) :=
    Ideal.Quotient.mk_surjective
  have hcomap : Pb.comap (Ideal.Quotient.mk (chartExceptional R t x)) = P := by
    rw [hPb, Ideal.comap_map_of_surjective _ hmk]
    exact le_antisymm
      (sup_le le_rfl fun a ha ↦ hIP (by simpa [Ideal.Quotient.eq_zero_iff_mem] using ha))
      le_sup_left
  have hPbmax : Pb.IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hmk ‹P.IsMaximal›).resolve_left fun h ↦
      Ideal.IsMaximal.ne_top ‹_› (by rw [← hcomap, hPb, h, Ideal.comap_top])
  set Q := Pb.map e with hQ
  have hQmax : Q.IsMaximal := (Ideal.isMaximal_map_iff_of_bijective _ e.bijective).2 hPbmax
  obtain ⟨ψ, hψ'⟩ := IsPrincipalIdealRing.principal Q
  rw [Ideal.submodule_span_eq] at hψ'
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    rw [hψ', Ideal.span_singleton_eq_bot.2 rfl] at hQmax
    exact Polynomial.not_isField _ (Ring.isField_iff_maximal_bot.2 hQmax)
  have hψprime : Prime ψ := (Ideal.span_singleton_prime hψ0).1 (hψ' ▸ hQmax.isPrime)
  have hu : IsUnit (Polynomial.C ψ.leadingCoeff⁻¹) :=
    Polynomial.isUnit_C.2 (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hψ0)).isUnit
  set φ := ψ * Polynomial.C ψ.leadingCoeff⁻¹ with hφ
  have hmon : φ.Monic := Polynomial.monic_mul_leadingCoeff_inv hψ0
  have hirr : Irreducible φ := (associated_mul_unit_right ψ _ hu).irreducible hψprime.irreducible
  have hQφ : Ideal.span {φ} = Q := by rw [hφ, Ideal.span_singleton_mul_right_unit hu, ← hψ']
  refine ⟨φ, hmon, hirr, hQφ.symm, ?_, ?_⟩
  · rw [← hcomap, Ideal.mem_comap, ← Ideal.apply_mem_of_equiv_iff (f := e), heZ, ← hQ, ← hQφ,
      Ideal.mem_span_singleton]
    exact ⟨fun h ↦ Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
      (associated_of_dvd_dvd h (hirr.dvd_symm Polynomial.irreducible_X h)), fun h ↦ h ▸ dvd_rfl⟩
  · let Ψ : (BlowupChart R t x ⧸ P) ≃+*
        (Polynomial (R ⧸ Ideal.span ({t,x} : Set R)) ⧸ Ideal.span {φ}) :=
      (DoubleQuot.quotQuotEquivQuotOfLE hIP).symm.trans (Ideal.quotientEquiv _ _ e hQφ)
    have hΨ : ∀ r : R, Ψ (Ideal.Quotient.mk P (chartBase R t x r)) =
        Ideal.Quotient.mk (Ideal.span {φ})
          (Polynomial.C (Ideal.Quotient.mk (Ideal.span ({t,x} : Set R)) r)) := by
      intro r
      simp only [Ψ, RingEquiv.trans_apply, DoubleQuot.quotQuotEquivQuotOfLE_symm_mk]
      exact congrArg _ (he r)
    let L := (AlgEquiv.ofRingEquiv (R := R) (f := Ψ) (fun r ↦ hΨ r)).toLinearEquiv
    rw [L.length_eq]
    have : Module.Finite (R ⧸ Ideal.span ({t,x} : Set R))
        (Polynomial (R ⧸ Ideal.span ({t,x} : Set R)) ⧸ Ideal.span {φ}) :=
      Module.finite_of_finrank_pos
        (by rw [finrank_quotient_span_eq_natDegree]; exact hirr.natDegree_pos)
    rw [length_eq_of_surjective_onto_field R (R ⧸ Ideal.span ({t,x} : Set R)) _
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective ?_, finrank_quotient_span_eq_natDegree]
    intro r m
    exact (algebraMap_smul (R ⧸ Ideal.span ({t,x} : Set R)) r m).symm

/-- Every maximal ideal of the chart containing `t` is the direction point of an affine direction
`φ` over the residue field; it maps onto `(φ)` in the exceptional fibre and contains the slope
iff `φ` is the zero direction. -/
theorem chart_point_eq_directionPoint (R : Type) [CommRing R] [IsLocalRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (IsLocalRing.ResidueField R))
    (he : ∀ r : R, e (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) =
      Polynomial.C (IsLocalRing.residue R r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X)
    (P : Ideal (BlowupChart R t x)) [P.IsMaximal] (hP : chartBase R t x t ∈ P) :
    ∃ φ : AffineDirection (IsLocalRing.ResidueField R), P = directionPoint R t x e φ ∧
    (P.map (Ideal.Quotient.mk (chartExceptional R t x))).map e = Ideal.span {φ.val} ∧
    (chartSlope R t x ∈ P ↔ φ = zeroAffine (IsLocalRing.ResidueField R)) := by
  have hm : Ideal.span ({t,x} : Set R) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal ‹_›
  let κ : (R ⧸ Ideal.span ({t,x} : Set R)) ≃+* IsLocalRing.ResidueField R :=
    Ideal.quotEquivOfEq hm
  have hκ : ∀ r : R, κ (Ideal.Quotient.mk _ r) = IsLocalRing.residue R r := fun r ↦ rfl
  let M := Polynomial.mapEquiv κ
  let e₀ := e.trans M.symm
  have he₀ : ∀ r : R, e₀ (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.span ({t,x} : Set R)) r) := by
    intro r
    apply M.injective
    simp only [e₀, RingEquiv.trans_apply, RingEquiv.apply_symm_apply, he]
    simp [M, Polynomial.mapEquiv_apply, hκ]
  have heZ₀ :
      e₀ (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X := by
    apply M.injective
    simp only [e₀, RingEquiv.trans_apply, RingEquiv.apply_symm_apply, heZ]
    simp [M, Polynomial.mapEquiv_apply]
  obtain ⟨φ₀, hmon, hirr, himg, hZ, -⟩ :=
    blowup_chart_exceptional_point_polynomial R t x e₀ he₀ heZ₀ P hP
  have hirr' : Irreducible (Polynomial.map κ.toRingHom φ₀) :=
    (MulEquiv.irreducible_iff M.toMulEquiv).2 hirr
  let φ : AffineDirection (IsLocalRing.ResidueField R) :=
    ⟨Polynomial.map κ.toRingHom φ₀, hmon.map _, hirr'⟩
  have himg' : (P.map (Ideal.Quotient.mk (chartExceptional R t x))).map e = Ideal.span {φ.val} := by
    have he : e.toRingHom = M.toRingHom.comp e₀.toRingHom := by
      exact RingHom.ext fun a ↦ by simp [e₀]
    change Ideal.map e.toRingHom _ = _
    rw [he, ← Ideal.map_map]
    change Ideal.map M (Ideal.map e₀ _) = _
    rw [himg, Ideal.map_span, Set.image_singleton]
    rfl
  refine ⟨φ, ?_, himg', ?_⟩
  · let ψ := e.toRingHom.comp (Ideal.Quotient.mk (chartExceptional R t x))
    have hψ : Function.Surjective ψ :=
      e.surjective.comp Ideal.Quotient.mk_surjective
    have hmap : P.map ψ = Ideal.span {φ.val} := by
      rw [← himg']
      change _ = Ideal.map e.toRingHom _
      rw [Ideal.map_map]
    change P = (Ideal.span {φ.val}).comap ψ
    rw [← hmap, Ideal.comap_map_of_surjective _ hψ]
    have hker : Ideal.comap ψ ⊥ = chartExceptional R t x := by
      rw [← RingHom.ker_eq_comap_bot]
      ext a
      simp [ψ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hker, eq_comm, sup_eq_left]
    exact (Ideal.span_singleton_le_iff_mem _).2 hP
  · rw [hZ]
    refine ⟨by rintro rfl; apply Subtype.ext; simp [φ, zeroAffine], fun h ↦ M.injective ?_⟩
    have := congrArg Subtype.val h
    simp only [φ, zeroAffine] at this
    simpa [M] using this

/-- The direction point of an affine direction `φ` is a maximal ideal containing `t`; it contains
the slope iff `φ` is the zero direction, maps onto `(φ)` in the exceptional fibre, has
`R`-length `deg φ`, and depends injectively on `φ`. -/
theorem direction_point_maximal (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R] (S : SurfaceData O R)
    (e : (BlowupChart R S.t S.x ⧸ chartExceptional R S.t S.x) ≃+* Polynomial
      (IsLocalRing.ResidueField R)) (he : ∀ r : R,
      e (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartBase R S.t S.x r)) =
      Polynomial.C (IsLocalRing.residue R r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartSlope R S.t S.x)) = Polynomial.X)
    (φ : AffineDirection (IsLocalRing.ResidueField R)) :
    (directionPoint R S.t S.x e φ).IsMaximal ∧
    chartBase R S.t S.x S.t ∈ directionPoint R S.t S.x e φ ∧
    (chartSlope R S.t S.x ∈ directionPoint R S.t S.x e φ ↔ φ =
      zeroAffine (IsLocalRing.ResidueField R)) ∧
    ((directionPoint R S.t S.x e φ).map (Ideal.Quotient.mk (chartExceptional R S.t S.x))).map e =
    Ideal.span {φ.val} ∧ Module.length R (BlowupChart R S.t S.x ⧸ directionPoint R S.t S.x e φ) =
    (φ.val.natDegree : ℕ∞) ∧ Function.Injective (directionPoint R S.t S.x e) := by
  set k := IsLocalRing.ResidueField R
  set A := BlowupChart R S.t S.x
  set ψ : A →+* Polynomial k :=
    e.toRingHom.comp (Ideal.Quotient.mk (chartExceptional R S.t S.x))
  have hψ : Function.Surjective ψ :=
    e.surjective.comp Ideal.Quotient.mk_surjective
  have hP : ∀ φ' : AffineDirection k,
      directionPoint R S.t S.x e φ' = (Ideal.span {φ'.val}).comap ψ := fun _ ↦ rfl
  have hmap : ∀ φ' : AffineDirection k,
      ((directionPoint R S.t S.x e φ').map (Ideal.Quotient.mk (chartExceptional R S.t S.x))).map e
        = Ideal.span {φ'.val} := by
    intro φ'
    change Ideal.map e.toRingHom (Ideal.map (Ideal.Quotient.mk _) _) = _
    rw [Ideal.map_map, hP]
    exact Ideal.map_comap_of_surjective ψ hψ _
  have hmon : ∀ φ₁ φ₂ : AffineDirection k, Ideal.span {φ₁.val} = Ideal.span {φ₂.val} → φ₁ = φ₂ := by
    intro φ₁ φ₂ h
    rw [Ideal.span_singleton_eq_span_singleton] at h
    exact Subtype.ext (Polynomial.eq_of_monic_of_associated φ₁.2.1 φ₂.2.1 h)
  have hbase : ∀ r : R, ψ (chartBase R S.t S.x r) = Polynomial.C (IsLocalRing.residue R r) := he
  refine ⟨?_, ?_, ?_, hmap φ, ?_, ?_⟩
  · rw [hP]
    have := PrincipalIdealRing.isMaximal_of_irreducible φ.2.2
    exact Ideal.comap_isMaximal_of_surjective ψ hψ
  · rw [hP, Ideal.mem_comap, hbase]
    have ht : S.t ∈ IsLocalRing.maximalIdeal R := by
      rw [← S.parameters]; exact Ideal.subset_span (by simp)
    rw [(IsLocalRing.residue_eq_zero_iff _).2 ht, map_zero]
    exact zero_mem _
  · rw [hP, Ideal.mem_comap]
    change e (Ideal.Quotient.mk _ (chartSlope R S.t S.x)) ∈ _ ↔ _
    rw [heZ, Ideal.mem_span_singleton]
    constructor
    · intro h
      exact Subtype.ext (Polynomial.eq_of_monic_of_associated φ.2.1 Polynomial.monic_X
        (φ.2.2.associated_of_dvd Polynomial.irreducible_X h))
    · rintro rfl; exact dvd_refl _
  · let E : (A ⧸ directionPoint R S.t S.x e φ) ≃+* Polynomial k ⧸ Ideal.span {φ.val} :=
      (Ideal.quotEquivOfEq (by rw [← RingHom.comap_ker, Ideal.mk_ker, hP])).trans
        (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk (Ideal.span {φ.val})).comp ψ)
          (Ideal.Quotient.mk_surjective.comp hψ))
    let L := (AlgEquiv.ofRingEquiv (R := R) (f := E)
      fun r ↦ congrArg (Ideal.Quotient.mk _) (hbase r)).toLinearEquiv
    rw [L.length_eq]
    have : Module.Finite k (Polynomial k ⧸ Ideal.span {φ.val}) := Module.finite_of_finrank_pos
      (by rw [finrank_quotient_span_eq_natDegree]; exact φ.2.2.natDegree_pos)
    rw [length_eq_of_surjective_onto_field R k _ (IsLocalRing.residue R)
      IsLocalRing.residue_surjective ?_, finrank_quotient_span_eq_natDegree]
    intro r m
    exact (algebraMap_smul k r m).symm
  · intro φ₁ φ₂ h
    apply hmon
    rw [← hmap φ₁, ← hmap φ₂, h]

/-- For a nonzero affine direction, the direction point generates a maximal ideal of the overlap
chart that contains `t` and contracts back to the direction point. -/
theorem direction_point_overlap_maximal (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (e : (BlowupChart R S.t S.x ⧸ chartExceptional R S.t S.x) ≃+* Polynomial
      (IsLocalRing.ResidueField R)) (he : ∀ r : R,
      e (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartBase R S.t S.x r)) =
      Polynomial.C (IsLocalRing.residue R r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartSlope R S.t S.x)) = Polynomial.X)
    (φ : AffineDirection (IsLocalRing.ResidueField R))
    (hφ : φ ≠ zeroAffine (IsLocalRing.ResidueField R)) :
    ((directionPoint R S.t S.x e φ).map (algebraMap (BlowupChart R S.t S.x)
      (BlowupOverlap R S.t S.x))).IsMaximal ∧
    (algebraMap (BlowupChart R S.t S.x) (BlowupOverlap R S.t S.x)) (chartBase R S.t S.x S.t) ∈
    (directionPoint R S.t S.x e φ).map (algebraMap (BlowupChart R S.t S.x)
      (BlowupOverlap R S.t S.x)) ∧ ((directionPoint R S.t S.x e φ).map
      (algebraMap (BlowupChart R S.t S.x) (BlowupOverlap R S.t S.x))).comap
    (algebraMap (BlowupChart R S.t S.x) (BlowupOverlap R S.t S.x)) =
      directionPoint R S.t S.x e φ := by
  obtain ⟨hmax, ht, hZ, -⟩ := direction_point_maximal O R S e he heZ φ
  set P := directionPoint R S.t S.x e φ
  have hZP : chartSlope R S.t S.x ∉ P := fun h ↦ hφ (hZ.mp h)
  have hd : Disjoint ((Submonoid.powers (chartSlope R S.t S.x) : Submonoid _) :
      Set (BlowupChart R S.t S.x)) (P : Set _) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hZP (hmax.isPrime.mem_of_pow_mem n hn)
  have hcomap : (P.map (algebraMap (BlowupChart R S.t S.x) (BlowupOverlap R S.t S.x))).comap
      (algebraMap (BlowupChart R S.t S.x) (BlowupOverlap R S.t S.x)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (chartSlope R S.t S.x)) _
      hmax.isPrime hd
  have hprime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (chartSlope R S.t S.x))
    (BlowupOverlap R S.t S.x) P hmax.isPrime hd
  refine ⟨?_, Ideal.mem_map_of_mem _ ht, hcomap⟩
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hprime.ne_top
  have hcM : M.comap (algebraMap (BlowupChart R S.t S.x) (BlowupOverlap R S.t S.x)) = P := by
    refine (hmax.eq_of_le (Ideal.comap_ne_top _ hM.ne_top) ?_).symm
    rw [← hcomap]; exact Ideal.comap_mono hle
  have : M = P.map (algebraMap (BlowupChart R S.t S.x) (BlowupOverlap R S.t S.x)) := by
    rw [← hcM]; exact (IsLocalization.map_under (Submonoid.powers (chartSlope R S.t S.x)) _ M).symm
  rw [← this]; exact hM

/-- The point at infinity of the opposite chart is a maximal ideal containing `x` and the slope,
with `R`-length one. -/
theorem infinity_point_maximal (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R] (S : SurfaceData O R) :
    (infinityPoint R S.t S.x).IsMaximal ∧ chartBase R S.x S.t S.x ∈ infinityPoint R S.t S.x ∧
    chartSlope R S.x S.t ∈ infinityPoint R S.t S.x ∧ Module.length R
    (BlowupChart R S.x S.t ⧸ infinityPoint R S.t S.x) = 1 := by
  have hker : ∃ φ : BlowupChart R S.x S.t →+* IsLocalRing.ResidueField R,
      (∀ r, φ (chartBase R S.x S.t r) = IsLocalRing.residue R r) ∧
      φ (chartSlope R S.x S.t) = 0 ∧ RingHom.ker φ = infinityPoint R S.t S.x := by
    have hx : IsLocalRing.residue R S.x = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, ← S.parameters]
      exact Ideal.subset_span (by simp)
    have ht : IsLocalRing.residue R S.t = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, ← S.parameters]
      exact Ideal.subset_span (by simp)
    let ψ : Polynomial R →+* IsLocalRing.ResidueField R :=
      Polynomial.eval₂RingHom (IsLocalRing.residue R) 0
    have hψ : Ideal.span {blowupRelation R S.x S.t} ≤ RingHom.ker ψ := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      simp [ψ, blowupRelation, ht]
    refine ⟨Ideal.Quotient.lift _ ψ fun a ha ↦ hψ ha, fun r ↦ ?_, ?_, ?_⟩
    · change ψ (Polynomial.C r) = _
      simp [ψ]
    · change ψ Polynomial.X = _
      simp [ψ]
    · ext b
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hrel := blowup_chart_relation R S.x S.t
      have hI_x : chartBase R S.x S.t S.x ∈ infinityPoint R S.t S.x := Ideal.subset_span (by simp)
      have hI_W : chartSlope R S.x S.t ∈ infinityPoint R S.t S.x := Ideal.subset_span (by simp)
      have hI_t : chartBase R S.x S.t S.t ∈ infinityPoint R S.t S.x := by
        rw [← hrel]; exact Ideal.mul_mem_right _ _ hI_x
      have hp := Polynomial.divX_mul_X_add p
      have hmk : Ideal.Quotient.mk (Ideal.span {blowupRelation R S.x S.t}) p =
          Ideal.Quotient.mk (Ideal.span {blowupRelation R S.x S.t}) (p.divX) * chartSlope R S.x S.t
          + chartBase R S.x S.t (p.coeff 0) := by
        conv_lhs => rw [← hp]
        simp [chartSlope, chartBase]
      have hψp : ψ p = IsLocalRing.residue R (p.coeff 0) := by
        simp [ψ, Polynomial.eval₂_at_zero]
      simp only [RingHom.mem_ker]
      change ψ p = 0 ↔ _
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · rw [hψp, IsLocalRing.residue_eq_zero_iff, ← S.parameters] at h
        rw [hmk]
        refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hI_W) ?_
        have : Ideal.map (chartBase R S.x S.t) (Ideal.span {S.t, S.x}) ≤
            infinityPoint R S.t S.x := by
          rw [Ideal.map_span, Ideal.span_le]
          rintro _ ⟨y, hy, rfl⟩
          rcases hy with rfl | rfl
          · exact hI_t
          · exact hI_x
        exact this (Ideal.mem_map_of_mem _ h)
      · have hle : infinityPoint R S.t S.x ≤
            RingHom.ker (Ideal.Quotient.lift _ ψ fun a ha ↦ hψ ha) := by
          rw [infinityPoint, Ideal.span_le]
          rintro _ (rfl | rfl)
          · change ψ (Polynomial.C S.x) = 0
            simpa [ψ] using hx
          · change ψ Polynomial.X = 0
            simp [ψ]
        exact hle h
  obtain ⟨φ, hφ1, hφ2, hφk⟩ := hker
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨chartBase R S.x S.t r, hφ1 r⟩
  have hmax : (infinityPoint R S.t S.x).IsMaximal := by
    rw [← hφk]; exact RingHom.ker_isMaximal_of_surjective φ hsurj
  refine ⟨hmax, Ideal.subset_span (by simp), Ideal.subset_span (by simp), ?_⟩
  let e0 : (BlowupChart R S.x S.t ⧸ infinityPoint R S.t S.x) ≃+* IsLocalRing.ResidueField R :=
    (Ideal.quotEquivOfEq hφk.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  rw [(AlgEquiv.ofRingEquiv (R := R) (f := e0) fun r ↦ hφ1 r).toLinearEquiv.length_eq,
    length_eq_of_surjective_onto_field R _ _ (IsLocalRing.residue R)
      IsLocalRing.residue_surjective fun r m ↦ rfl]
  simp

/-- If `e` is a nonzerodivisor, the kernel of the layer map `a ↦ e^j a` into `A ⧸ (e)^(j+1)` is
`(e)`. -/
private theorem principal_layer_map_kernel (A : Type) [CommRing A] (e : A) (j : ℕ)
    (he : Function.Injective (fun a : A ↦ e*a)) :
    LinearMap.ker (principalLayerMap A e j) = Ideal.span {e} := by
  have hinj : IsLeftRegular (e ^ j) := IsLeftRegular.pow j he
  ext a
  simp only [LinearMap.mem_ker, principalLayerMap, LinearMap.toSpanSingleton_apply,
    Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hinj (show e ^ j * a = e ^ j * (e * b) by linear_combination hb)⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, by ring⟩

/-- The range of the layer map `a ↦ e^j a` into `A ⧸ (e)^(j+1)` is the kernel of the reduction to `A
⧸ (e)^j`. -/
private theorem principal_layer_map_range (A : Type) [CommRing A] (e : A) (j : ℕ) :
    LinearMap.range (principalLayerMap A e j) = LinearMap.ker
    (principalPowerReduction A e j).toLinearMap := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [principalLayerMap, LinearMap.toSpanSingleton_apply, principalPowerReduction,
      AlgHom.toLinearMap_apply, map_smul, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]
    rw [(Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self e) j),
      smul_zero]
  · intro hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_ker] at hx
    simp only [principalPowerReduction, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply,
      Ideal.Quotient.factor_mk] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    refine ⟨a, ?_⟩
    simp only [principalLayerMap, LinearMap.toSpanSingleton_apply]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]

/-- If `e` is a nonzerodivisor, the layer map induces an `A`-linear isomorphism from `A ⧸ (e)` onto
the principal layer `(e)^j ⧸ (e)^(j+1)`. -/
theorem principal_layer_quotient_equiv (A : Type) [CommRing A] (e : A) (j : ℕ)
    (he : Function.Injective (fun a : A ↦ e*a)) :
    ∃ L : (A ⧸ Ideal.span {e}) ≃ₗ[A] PrincipalLayer A e j, ∀ a : A,
    (L (Ideal.Quotient.mk (Ideal.span {e}) a)).val = principalLayerMap A e j a := by
  have hk := principal_layer_map_kernel A e j he
  have hr := principal_layer_map_range A e j
  refine ⟨((Submodule.quotEquivOfEq _ _ hk.symm).trans
    (LinearMap.quotKerEquivRange (principalLayerMap A e j))).trans (LinearEquiv.ofEq _ _ hr), ?_⟩
  intro a
  rfl

/-- Each exceptional layer of the chart is `R`-linearly isomorphic to `(R/(t,x))[Z]`, the monomial
`r Z^i` corresponding to the layer class of `r · z^i`. -/
theorem chart_layer_polynomial_coordinates (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (j : ℕ) :
    ∃ L : Polynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer (BlowupChart R t x)
    (chartBase R t x t) j, ∀ r : R, ∀ i : ℕ,
    (L (Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) * Polynomial.X^i)).val =
    principalLayerMap (BlowupChart R t x) (chartBase R t x t) j
    (chartBase R t x r * (chartSlope R t x)^i) := by
  have he := blowup_exceptional_parameter_regular R t x hreg
  obtain ⟨L1, hL1⟩ := principal_layer_quotient_equiv (BlowupChart R t x)
    (chartBase R t x t) j he
  obtain ⟨e1, he1b, he1s⟩ := exceptional_chart_is_affine_line R t x
  have hI : exceptionalLevelIdeal R t x 1 = Ideal.span {chartBase R t x t} := by
    simp [exceptionalLevelIdeal]
  let φ : (BlowupChart R t x ⧸ Ideal.span {chartBase R t x t}) ≃+*
      Polynomial (R ⧸ Ideal.span {t,x}) :=
    (Ideal.quotEquivOfEq hI.symm).trans e1
  have hφ : ∀ a : BlowupChart R t x,
      φ (Ideal.Quotient.mk _ a) = e1 (Ideal.Quotient.mk (exceptionalLevelIdeal R t x 1) a) := by
    intro a; rfl
  have hφb : ∀ r : R, φ (Ideal.Quotient.mk _ (chartBase R t x r)) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) := by
    intro r; rw [hφ]; exact he1b r
  have hφs : φ (Ideal.Quotient.mk _ (chartSlope R t x)) = Polynomial.X := by
    rw [hφ]; exact he1s
  let φl := (AlgEquiv.ofRingEquiv (R := R) (f := φ) fun r ↦ hφb r).toLinearEquiv
  refine ⟨φl.symm.trans (L1.restrictScalars R), ?_⟩
  intro r i
  have key : φl.symm (Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) * Polynomial.X^i)
      = Ideal.Quotient.mk _ (chartBase R t x r * (chartSlope R t x)^i) := by
    rw [LinearEquiv.symm_apply_eq]
    change _ = φ _
    rw [map_mul, map_pow, map_mul, map_pow, hφb, hφs]
  simp only [LinearEquiv.trans_apply, key, LinearEquiv.restrictScalars_apply]
  exact hL1 _

open scoped Classical in
open Polynomial UniqueFactorizationMonoid in
/-- Over a finite field `k`, if `ᾱ` is a root of the monic irreducible `φ` in an extension `k'`,
then the multiplicity of `ᾱ` as a root of `G` equals the multiplicity of `φ` among the
normalized factors of `G`. -/
theorem rootMultiplicity_map_eq_count_normalizedFactors (k k' : Type) [Field k] [Finite k]
    [Field k'] (ι : k →+* k') (G : Polynomial k) (hG : G ≠ 0) (φ : Polynomial k)
    (hφ : φ.Monic ∧ Irreducible φ) (alphaBar : k') (hroot : (φ.map ι).eval alphaBar = 0) :
    Polynomial.rootMultiplicity alphaBar (G.map ι) = Multiset.count φ
    (UniqueFactorizationMonoid.normalizedFactors G) := by
  have key : ∀ ψ : k[X], ψ.Monic → Irreducible ψ →
      rootMultiplicity alphaBar (ψ.map ι) = Multiset.count φ {ψ} := by
    intro ψ hm hi
    rw [Multiset.count_singleton]
    split_ifs with h
    · subst h
      have := PerfectField.ofFinite (K := k)
      have hsep : (φ.map ι).Separable := (PerfectField.separable_of_irreducible hi).map
      have hne : φ.map ι ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
      have h1 := rootMultiplicity_le_one_of_separable hsep alphaBar
      have h2 : 0 < rootMultiplicity alphaBar (φ.map ι) :=
        (rootMultiplicity_pos hne).2 hroot
      omega
    · rw [rootMultiplicity_eq_zero_iff]
      intro hr
      exfalso
      obtain ⟨a, b, hab⟩ := (EuclideanDomain.dvd_or_coprime φ ψ hφ.2).resolve_left (by
        intro hd
        exact h (eq_of_monic_of_associated hφ.1 hm (hφ.2.associated_of_dvd hi hd)))
        |>.map (mapRingHom ι)
      have := congrArg (eval alphaBar) hab
      simp only [coe_mapRingHom, eval_add, eval_mul, hroot, hr.eq_zero, mul_zero, add_zero,
        eval_one] at this
      exact zero_ne_one this
  induction G using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hG
  | h₂ x hx =>
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.1 hx
    rw [normalizedFactors_of_isUnit hx, Polynomial.map_C, rootMultiplicity_C]
    rfl
  | h₃ a p ha hp ih =>
    have ha0 : a ≠ 0 := right_ne_zero_of_mul hG
    have hp0 : p ≠ 0 := hp.ne_zero
    rw [normalizedFactors_mul hp0 ha0, Multiset.count_add, Polynomial.map_mul,
      rootMultiplicity_mul (by simpa using hG), ih ha0,
      normalizedFactors_irreducible hp.irreducible]
    congr 1
    rw [← key _ (Polynomial.monic_normalize hp0)
      ((normalize_associated p).symm.irreducible hp.irreducible), normalize_apply,
      Polynomial.map_mul,
      rootMultiplicity_mul (by simpa [Polynomial.map_ne_zero_iff ι.injective] using hp0),
      coe_normUnit, Polynomial.map_C, rootMultiplicity_C, add_zero]

end SurfaceBlowup
