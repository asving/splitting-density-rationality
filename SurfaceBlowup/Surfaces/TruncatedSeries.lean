/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Surfaces.PowerSeries

/-!
# Truncations of `k⟦T, X⟧` and contacts on the special fibre

Elementary facts about the two-variable power series ring `k⟦T, X⟧` over a field, shared by the
residue-ideal counts of the crossing state `k⟦T, X⟧ ⧸ (T^a X^b)` and the single state
`k⟦T, X⟧ ⧸ (T^a)`: the maximal ideal `(T, X)` and residue field; the length
`ℓ(k⟦T, X⟧ ⧸ (F, X_s))` as the order of `F` along the other axis, and its identification with
the contact of `F` with an axis of the special fibre; the truncation
`k⟦T, X⟧ ⧸ ((T^a X^b) + (T, X)^L) ≃ k^(truncIndex a b L)` by coefficients; and the common
counting argument for principal ideals of the special fibre whose generators are described by
vanishing and non-vanishing of truncated coefficients.

## Main results

* `maximalIdeal_twoSeries`, `twoSeriesResidueEquiv`: the maximal ideal and the residue field.
* `axisQuotientLength_eq_iff`, `contact_fiberT_eq_axisQuotientLength`,
  `contact_fiberX_eq_axisQuotientLength`: contacts as orders along an axis.
* `isUnit_mk_truncIdeal_iff`: units of the truncated quotient (which is identified with its
  coefficient vectors by the linear equivalence `truncEval`).
* `card_mul_eq_zero_eq_card_quotient`: annihilator and quotient of a finite ring have equal size.
* `principal_residue_ideal_count`: the shared core of the crossing and single residue-ideal counts.

Provenance: the shared helpers of `crossing_residue_ideal_count` and `single_residue_ideal_count`
(formerly duplicated as `crc_*` in `Measure/Normalizer.lean` and `sric_*` in
`Measure/StateVolumes.lean`).
-/

namespace SurfaceBlowup

/-- A series lies in the ideal `(T, X)` of `k⟦T, X⟧` iff its constant coefficient vanishes. -/
private theorem mem_axisIdeal_iff (k : Type) [Field k] (φ : TwoSeries k) :
    φ ∈ Ideal.span {axisT k, axisX k} ↔ MvPowerSeries.constantCoeff φ = 0 :=
  mvPowerSeries_fin_two_mem_variableIdeal_iff k φ

/-- The ideal `(T, X)` of `k⟦T, X⟧` is maximal. -/
private theorem axisIdeal_isMaximal (k : Type) [Field k] :
    (Ideal.span {axisT k, axisX k}).IsMaximal := by
  have : Ideal.span {axisT k, axisX k} =
      RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin 2) (R := k)) := by
    ext φ; rw [mem_axisIdeal_iff, RingHom.mem_ker]
  rw [this]
  exact RingHom.ker_isMaximal_of_surjective _ (fun x => ⟨MvPowerSeries.C x, by simp⟩)

/-- The maximal ideal of `k⟦T, X⟧` is `(T, X)`. -/
theorem maximalIdeal_twoSeries (k : Type) [Field k] :
    IsLocalRing.maximalIdeal (TwoSeries k) = Ideal.span {axisT k, axisX k} :=
  (IsLocalRing.eq_maximalIdeal (axisIdeal_isMaximal k)).symm

private theorem fin_two_eq_or {s t : Fin 2} (hst : s ≠ t) (i : Fin 2) : i = s ∨ i = t := by
  omega

/-- An exponent vector vanishing at `s` is supported on the other axis `t`. -/
private theorem eq_single_of_apply_eq_zero {s t : Fin 2} (hst : s ≠ t) {m : Fin 2 →₀ ℕ}
    (hm : m s = 0) : m = Finsupp.single t (m t) := by
  ext i; rcases fin_two_eq_or hst i with rfl | rfl <;> simp [hm, hst]

/-- The length of `k⟦T, X⟧ ⧸ (F, X_s)`, where `X_0 = T` and `X_1 = X`. -/
noncomputable def axisQuotientLength (k : Type) [Field k] (s : Fin 2) (F : TwoSeries k) : ℕ∞ :=
  Module.length (TwoSeries k) (TwoSeries k ⧸ (Ideal.span {F} ⊔ Ideal.span {MvPowerSeries.X s}))

/-- If `F` vanishes on the axis `X_t`, then `ℓ(k⟦T, X⟧ ⧸ (F, X_s)) = ⊤`. -/
theorem axisQuotientLength_eq_top (k : Type) [Field k] {s t : Fin 2} (hst : s ≠ t)
    (F : TwoSeries k)
    (h : ∀ j, MvPowerSeries.coeff (Finsupp.single t j) F = 0) : axisQuotientLength k s F = ⊤ := by
  have hdvd : MvPowerSeries.X s ∣ F := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [eq_single_of_apply_eq_zero hst hm]; exact h _
  rw [axisQuotientLength, sup_eq_right.mpr (Ideal.span_singleton_le_span_singleton.mpr hdvd)]
  exact axis_quotient_length_top k s t hst

/-- If the restriction of `F` to the axis `X_t` has order `d`, then
`ℓ(k⟦T, X⟧ ⧸ (F, X_s)) = d`. -/
theorem axisQuotientLength_eq (k : Type) [Field k] {s t : Fin 2} (hst : s ≠ t)
    (F : TwoSeries k)
    (d : ℕ) (hlow : ∀ j < d, MvPowerSeries.coeff (Finsupp.single t j) F = 0)
    (hd : MvPowerSeries.coeff (Finsupp.single t d) F ≠ 0) : axisQuotientLength k s F = d := by
  set Xs : TwoSeries k := MvPowerSeries.X s
  set Xt : TwoSeries k := MvPowerSeries.X t
  let F0 : TwoSeries k := fun m => if m s = 0 then MvPowerSeries.coeff m F else 0
  have hF0 : ∀ m, MvPowerSeries.coeff m F0 = if m s = 0 then MvPowerSeries.coeff m F else 0 :=
    fun m => rfl
  have hT : Xs ∣ F - F0 := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [map_sub, hF0, if_pos hm, sub_self]
  have hX : Xt ^ d ∣ F0 := by
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [hF0]
    split_ifs with h0
    · rw [eq_single_of_apply_eq_zero hst h0]; exact hlow _ hm
    · rfl
  obtain ⟨U, hU⟩ := hX
  obtain ⟨G, hG⟩ := hT
  have hU0 : MvPowerSeries.constantCoeff U ≠ 0 := by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single t d)) hU
    rw [hF0, if_pos (by simp [hst]), MvPowerSeries.X_pow_eq,
      MvPowerSeries.coeff_monomial_mul, if_pos le_rfl, one_mul, tsub_self,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    rw [← this]; exact hd
  have hUu : IsUnit U := MvPowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hU0)
  have hFe : F = Xs * G + Xt ^ d * U := by
    rw [← hG, ← hU]; ring
  have hid : Ideal.span {F} ⊔ Ideal.span {Xs} = Ideal.span {Xs} ⊔ Ideal.span {Xt ^ d} := by
    have hXs := Ideal.mem_span_singleton_self Xs
    simp only [le_antisymm_iff, sup_le_iff, Ideal.span_singleton_le_iff_mem]
    refine ⟨⟨?_, Ideal.mem_sup_left hXs⟩, Ideal.mem_sup_right hXs, ?_⟩
    · rw [hFe]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_sup_left hXs))
        (Ideal.mul_mem_right _ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    · obtain ⟨V, hV⟩ := hUu.exists_right_inv
      rw [show Xt ^ d = (F - Xs * G) * V by rw [hFe, add_sub_cancel_left, mul_assoc, hV, mul_one]]
      exact Ideal.mul_mem_right _ _ (Ideal.sub_mem _
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
        (Ideal.mul_mem_right _ _ (Ideal.mem_sup_right hXs)))
  have hcancel : ∀ x, Xt * x ∈ Ideal.span {Xs} → x ∈ Ideal.span {Xs} := by
    intro x hx
    refine axis_pow_mul_mem_span_cancel k t Xs ?_ 1 x (by rwa [pow_one])
    intro hmem
    rw [Ideal.mem_span_singleton, MvPowerSeries.X_dvd_iff] at hmem
    simpa [Xs, MvPowerSeries.coeff_X] using hmem (Finsupp.single s 1) (by simp [hst])
  have h1 :
      Module.length (TwoSeries k) (TwoSeries k ⧸ (Ideal.span {Xs} ⊔ Ideal.span {Xt})) = 1 := by
    have : Ideal.span {Xs} ⊔ Ideal.span {Xt} = Ideal.span {axisT k, axisX k} := by
      rw [Ideal.span_insert]
      fin_cases s <;> fin_cases t <;> first | exact absurd rfl hst | rfl | exact sup_comm _ _
    rw [this, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
    exact (axisIdeal_isMaximal k).out
  rw [axisQuotientLength, hid, length_quotient_sup_pow_eq_mul _ _ _ hcancel d, h1, mul_one]

/-- `ℓ(k⟦T, X⟧ ⧸ (F, X_s)) = c` iff the restriction of `F` to the other axis `X_t` has order
exactly `c`. -/
theorem axisQuotientLength_eq_iff (k : Type) [Field k] {s t : Fin 2} (hst : s ≠ t) (F : TwoSeries k)
    (c : ℕ) : axisQuotientLength k s F = c ↔
      (∀ j < c, MvPowerSeries.coeff (Finsupp.single t j) F = 0) ∧
      MvPowerSeries.coeff (Finsupp.single t c) F ≠ 0 := by
  classical
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => axisQuotientLength_eq k hst F c h1 h2⟩
  by_cases hex : ∃ j, MvPowerSeries.coeff (Finsupp.single t j) F ≠ 0
  · have hmin : ∀ j < Nat.find hex, MvPowerSeries.coeff (Finsupp.single t j) F = 0 :=
      fun j hj => not_not.mp (Nat.find_min hex hj)
    have hc : Nat.find hex = c := by
      exact_mod_cast (axisQuotientLength_eq k hst F _ hmin (Nat.find_spec hex)).symm.trans h
    exact hc ▸ ⟨hmin, Nat.find_spec hex⟩
  · push Not at hex
    exact absurd (h.symm.trans (axisQuotientLength_eq_top k hst F hex)) (ENat.natCast_ne_top c)

/-- On the special fibre `k⟦T, X⟧ ⧸ (T^a X^b)` with `0 < a`, the contact of `F` with `T` is
`ℓ(k⟦T, X⟧ ⧸ (F, T))`. -/
theorem contact_fiberT_eq_axisQuotientLength (k : Type) [Field k] (a b : ℕ) (ha : 0 < a)
    (F : TwoSeries k) :
    contact (Ideal.Quotient.mk (monomialIdeal k a b) F) (fiberT k a b) =
      axisQuotientLength k 0 F := by
  have hJT : monomialIdeal k a b ≤ Ideal.span {F, axisT k} := by
    refine le_trans ?_ (Ideal.span_mono (Set.subset_insert F {axisT k}))
    rw [monomialIdeal, Ideal.span_singleton_le_span_singleton]
    exact Dvd.dvd.mul_right (dvd_pow_self _ ha.ne') _
  have h1 := length_double_quotient_eq (TwoSeries k) (monomialIdeal k a b) (Ideal.span {F, axisT k})
  rw [Ideal.map_span, Set.image_pair, sup_eq_right.mpr hJT] at h1
  rw [contact, fiberT, h1, axisQuotientLength, ← Ideal.span_insert]; rfl

/-- On the special fibre `k⟦T, X⟧ ⧸ (T^a X^b)` with `0 < b`, the contact of `F` with `X` is
`ℓ(k⟦T, X⟧ ⧸ (F, X))`. -/
theorem contact_fiberX_eq_axisQuotientLength (k : Type) [Field k] (a b : ℕ) (hb : 0 < b)
    (F : TwoSeries k) :
    contact (Ideal.Quotient.mk (monomialIdeal k a b) F) (fiberX k a b) =
      axisQuotientLength k 1 F := by
  have hJT : monomialIdeal k a b ≤ Ideal.span {F, axisX k} := by
    refine le_trans ?_ (Ideal.span_mono (Set.subset_insert F {axisX k}))
    rw [monomialIdeal, Ideal.span_singleton_le_span_singleton]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ hb.ne') _
  have h1 := length_double_quotient_eq (TwoSeries k) (monomialIdeal k a b) (Ideal.span {F, axisX k})
  rw [Ideal.map_span, Set.image_pair, sup_eq_right.mpr hJT] at h1
  rw [contact, fiberX, h1, axisQuotientLength, ← Ideal.span_insert]; rfl

/-- The exponents `(i, j)` with `i + j < L` outside the quadrant `i ≥ a, j ≥ b`: the monomials
surviving in `k⟦T, X⟧ ⧸ ((T^a X^b) + (T, X)^L)`. -/
def truncIndex (a b L : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range L ×ˢ Finset.range L).filter fun ij => ij.1+ij.2<L ∧ ¬(a ≤ ij.1 ∧ b ≤ ij.2)

/-- An initial segment `{e 0, …, e (c - 1)}` of an axis `f = 0` (parametrized by `g`) inside
`truncIndex a b L` has `c` elements. -/
theorem card_truncIndex_axis_segment (a b L c : ℕ) (f g : ℕ × ℕ → ℕ) (e : ℕ → ℕ × ℕ)
    (hfe : ∀ j, f (e j) = 0 ∧ g (e j) = j) (hef : ∀ x, f x = 0 → e (g x) = x)
    (hmem : ∀ j < c, e j ∈ truncIndex a b L) :
    (Finset.univ.filter fun s : truncIndex a b L => f s.1 = 0 ∧ g s.1 < c).card = c := by
  refine (Finset.card_bij (t := Finset.range c) (fun s _ => g s.1) ?_ ?_ ?_).trans
    (Finset.card_range c)
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simpa using hs.2
  · intro s₁ h₁ s₂ h₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact Subtype.ext (by rw [← hef _ h₁.1, ← hef _ h₂.1, h])
  · intro j hj
    rw [Finset.mem_range] at hj
    exact ⟨⟨e j, hmem j hj⟩, by simp [hfe, hj], (hfe j).2⟩

/-- The ideal `(T^a X^b) + (T, X)^L` of `k⟦T, X⟧`. -/
private noncomputable def truncIdeal (k : Type) [Field k] (a b L : ℕ) : Ideal (TwoSeries k) :=
  monomialIdeal k a b ⊔ (Ideal.span {axisT k, axisX k})^L

/-- The exponent vector `T^i X^j` of a pair `(i, j)`. -/
noncomputable def truncExponent (ij : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ij.1 + Finsupp.single 1 ij.2

/-- The coefficients of a series at the exponents of `truncIndex a b L`. -/
noncomputable def truncCoeffs (k : Type) [Field k] (a b L : ℕ) : TwoSeries k →ₗ[k]
    (truncIndex a b L → k) :=
  LinearMap.pi (fun s => MvPowerSeries.coeff (truncExponent s.1))

/-- Evaluation of `truncCoeffs`. -/
theorem truncCoeffs_apply (k : Type) [Field k] (a b L : ℕ) (F : TwoSeries k)
    (s : truncIndex a b L) :
    truncCoeffs k a b L F s = MvPowerSeries.coeff (truncExponent s.1) F := rfl

private theorem truncCoeffs_surjective_and_ker (k : Type) [Field k] (a b L : ℕ) :
    Function.Surjective (truncCoeffs k a b L) ∧
      ∀ φ, truncCoeffs k a b L φ = 0 ↔ φ ∈ truncIdeal k a b L := by
  let e : ℕ × ℕ → (Fin 2 →₀ ℕ) := truncExponent
  have e0 : ∀ ij, e ij 0 = ij.1 := fun ij => by simp [e, truncExponent]
  have e1 : ∀ ij, e ij 1 = ij.2 := fun ij => by simp [e, truncExponent]
  have eeq : ∀ m : Fin 2 →₀ ℕ, e (m 0, m 1) = m := fun m => by
    ext i; fin_cases i <;> simp [e0, e1]
  have einj : Function.Injective e := fun p q h => by
    have h0 := congrArg (fun m => m 0) h
    have h1 := congrArg (fun m => m 1) h
    simp only [e0, e1] at h0 h1
    exact Prod.ext h0 h1
  refine ⟨?_, ?_⟩
  · intro v
    refine ⟨∑ s, MvPowerSeries.monomial (e s.1) (v s), ?_⟩
    funext s₀
    simp only [truncCoeffs, LinearMap.pi_apply, map_sum, MvPowerSeries.coeff_monomial]
    rw [Finset.sum_eq_single s₀]
    · simp [e]
    · intro s _ hs
      rw [if_neg]
      intro h
      exact hs (Subtype.ext (einj h.symm))
    · simp
  · intro φ
    constructor
    · intro hφ
      have hz : ∀ s : truncIndex a b L, MvPowerSeries.coeff (e s.1) φ = 0 :=
        fun s => congrFun hφ s
      let x : TwoSeries k := fun m => if a ≤ m 0 ∧ b ≤ m 1 then MvPowerSeries.coeff m φ else 0
      have hx : ∀ m, MvPowerSeries.coeff m x =
          if a ≤ m 0 ∧ b ≤ m 1 then MvPowerSeries.coeff m φ else 0 :=
        fun m => rfl
      rw [show φ = x + (φ - x) by ring]
      refine Submodule.add_mem_sup ?_ ?_
      · rw [monomialIdeal_mem_iff]
        intro m hm
        rw [hx, if_neg hm]
      · rw [axis_ideal_pow_mem_iff]
        intro m hm
        rw [map_sub, hx]
        split_ifs with h
        · simp
        · have := hz ⟨(m 0, m 1), by
            simp only [truncIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            exact ⟨⟨by omega, by omega⟩, hm, h⟩⟩
          simp only [eeq] at this
          simp [this]
    · intro hφ
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hφ
      rw [monomialIdeal_mem_iff] at hx
      rw [axis_ideal_pow_mem_iff] at hy
      funext s
      obtain ⟨ij, hij⟩ := s
      simp only [truncIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hij
      simp only [truncCoeffs, LinearMap.pi_apply, map_add, Pi.zero_apply]
      rw [hx _ (by rw [e0, e1]; exact hij.2.2), hy _ (by rw [e0, e1]; exact hij.2.1), add_zero]

/-- The coefficient vector of a class in `k⟦T, X⟧ ⧸ truncIdeal k a b L`, as a linear
equivalence (first isomorphism theorem for `truncCoeffs`). -/
private noncomputable def truncEval (k : Type) [Field k] (a b L : ℕ) :
    (TwoSeries k ⧸ truncIdeal k a b L) ≃ₗ[k] (truncIndex a b L → k) :=
  (Submodule.Quotient.restrictScalarsEquiv k (truncIdeal k a b L)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ (LinearMap.ker _) (Submodule.ext fun φ ↦
      ((truncCoeffs_surjective_and_ker k a b L).2 φ).symm) ≪≫ₗ
    (truncCoeffs k a b L).quotKerEquivOfSurjective (truncCoeffs_surjective_and_ker k a b L).1

/-- `truncEval` on the class of a series `F` is the coefficient vector of `F`. -/
private theorem truncEval_mk (k : Type) [Field k] (a b L : ℕ) (F : TwoSeries k) :
    truncEval k a b L (Ideal.Quotient.mk _ F) = truncCoeffs k a b L F :=
  rfl

private theorem truncIdeal_le_axisIdeal (k : Type) [Field k] (a b L : ℕ) (ha : 0 < a) (hL : 0 < L) :
    truncIdeal k a b L ≤ Ideal.span {axisT k, axisX k} := by
  apply sup_le
  · rw [monomialIdeal, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.subset_span (by simp)) _ ha)
  · exact Ideal.pow_le_self hL.ne'

/-- For `0 < a` and `0 < L`, the class of `F` in `k⟦T, X⟧ ⧸ truncIdeal k a b L` is a unit iff
the constant coefficient of `F` is nonzero. -/
theorem isUnit_mk_truncIdeal_iff (k : Type) [Field k] (a b L : ℕ) (ha : 0 < a) (hL : 0 < L)
    (F : TwoSeries k) :
    IsUnit (Ideal.Quotient.mk (truncIdeal k a b L) F) ↔ MvPowerSeries.constantCoeff F ≠ 0 := by
  constructor
  · intro h hF
    obtain ⟨y, hy⟩ := h.exists_right_inv
    obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (truncIdeal k a b L)), Ideal.Quotient.eq] at hy
    have := (mem_axisIdeal_iff k _).mp (truncIdeal_le_axisIdeal k a b L ha hL hy)
    simp [hF] at this
  · intro h
    exact (MvPowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h)).map _

/-- For `0 < a` and `0 < L`, the ideal `truncIdeal k a b L` is proper. -/
private theorem truncIdeal_ne_top (k : Type) [Field k] (a b L : ℕ) (ha : 0 < a) (hL : 0 < L) :
    truncIdeal k a b L ≠ ⊤ := fun h =>
  (axisIdeal_isMaximal k).ne_top (top_le_iff.mp (h ▸ truncIdeal_le_axisIdeal k a b L ha hL))

/-- In a finite commutative ring, the annihilator of `x` and `B ⧸ (x)` have the same cardinality. -/
theorem card_mul_eq_zero_eq_card_quotient (B : Type) [CommRing B] [Finite B] (x : B) :
    Nat.card {r : B // r * x = 0} = Nat.card (B ⧸ Ideal.span {x}) := by
  let μ := LinearMap.toSpanSingleton B B x
  have hker : Nat.card {r : B // r * x = 0} = Nat.card (LinearMap.ker μ) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun r => by simp [μ, LinearMap.mem_ker])
  have hrange : LinearMap.range μ = Ideal.span {x} := (LinearMap.span_singleton_eq_range B B x).symm
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker μ)
  have h2 := Submodule.card_eq_card_quotient_mul_card (Ideal.span {x} : Submodule B B)
  have h3 : Nat.card (B ⧸ LinearMap.ker μ) = Nat.card (Ideal.span {x} : Submodule B B) := by
    rw [← hrange]; exact Nat.card_congr μ.quotKerEquivRange.toEquiv
  rw [h3] at h1
  have hpos : 0 < Nat.card (Ideal.span {x} : Submodule B B) := Nat.card_pos
  rw [hker]
  have : Nat.card (LinearMap.ker μ) * Nat.card (Ideal.span {x} : Submodule B B) =
      Nat.card (B ⧸ Ideal.span {x}) * Nat.card (Ideal.span {x} : Submodule B B) := by
    rw [← h1, mul_comm, ← h2]
  exact Nat.eq_of_mul_eq_mul_right hpos this

/-- The residue field of `k⟦T, X⟧` is `k`, via the constant coefficient. -/
noncomputable def twoSeriesResidueEquiv (k : Type) [Field k] :
    IsLocalRing.ResidueField (TwoSeries k) ≃+* k :=
  (Ideal.quotEquivOfEq (by
    rw [maximalIdeal_twoSeries]; ext φ; rw [mem_axisIdeal_iff, RingHom.mem_ker])).trans
    (RingHom.quotientKerEquivOfSurjective (f := (MvPowerSeries.constantCoeff (σ := Fin 2) (R := k)))
      (fun x => ⟨MvPowerSeries.C x, by simp⟩))

/-- If `k⟦T, X⟧ ⧸ ((T^a X^b) + (F))` has length `N`, then it is already a quotient of the
truncation `k⟦T, X⟧ ⧸ ((T^a X^b) + (T, X)^(N + 1))`. -/
private theorem truncIdeal_le_of_length (k : Type) [Field k] (a b N : ℕ) (F : TwoSeries k)
    (hlen : Module.length (TwoSeries k)
      (TwoSeries k ⧸ (monomialIdeal k a b ⊔ Ideal.span {F})) = N) :
    truncIdeal k a b (N + 1) ≤ monomialIdeal k a b ⊔ Ideal.span {F} := by
  have h65 := maximal_ideal_power_kills (TwoSeries k) _ N hlen
  refine sup_le le_sup_left ?_
  rw [← maximalIdeal_twoSeries]
  refine (Ideal.pow_le_pow_right N.le_succ).trans fun x hx => ?_
  have := Submodule.smul_mem_smul hx
    (Submodule.mem_top (x := Ideal.Quotient.mk (monomialIdeal k a b ⊔ Ideal.span {F}) 1))
  rw [h65, Submodule.mem_bot] at this
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simpa [Algebra.smul_def] using this

/-- With `q = #k`, the truncation `k⟦T, X⟧ ⧸ truncIdeal k a b L` (for `0 < a`, `0 < L`) has
`(q - 1) q^(#truncIndex a b L - 1)` units: those with nonzero constant coefficient. -/
private theorem card_units_truncQuotient (k : Type) [Field k] [Finite k] (a b L : ℕ) (ha : 0 < a)
    (hL : 0 < L) : Nat.card (TwoSeries k ⧸ truncIdeal k a b L)ˣ =
      (Nat.card k - 1) * Nat.card k ^ (Fintype.card (truncIndex a b L) - 1) := by
  have : Fintype k := Fintype.ofFinite k
  have h00 : ((0 : ℕ), (0 : ℕ)) ∈ truncIndex a b L := by simp [truncIndex]; omega
  have h61 := coordinate_constraint_count k (truncIndex a b L) ∅ {⟨_, h00⟩}
    (Finset.disjoint_empty_left _)
  rw [Finset.card_singleton, Finset.card_empty, pow_one, Nat.sub_zero,
    ← Nat.card_eq_fintype_card] at h61
  rw [← h61]
  have hunit : ∀ x : TwoSeries k ⧸ truncIdeal k a b L, IsUnit x ↔
      (∀ s ∈ (∅ : Finset (truncIndex a b L)), truncEval k a b L x s = 0) ∧
        ∀ s ∈ ({⟨_, h00⟩} : Finset (truncIndex a b L)), truncEval k a b L x s ≠ 0 := by
    intro x; obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [isUnit_mk_truncIdeal_iff k a b _ ha hL, truncEval_mk]
    simp [truncCoeffs_apply, truncExponent, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine Nat.card_congr (.ofBijective (fun u => ⟨truncEval k a b L u, (hunit u).mp u.isUnit⟩)
    ⟨?_, ?_⟩)
  · exact fun u v h => Units.ext ((truncEval k a b L).injective (by simpa using h))
  · rintro ⟨g, hg⟩
    obtain ⟨x, rfl⟩ := (truncEval k a b L).surjective g
    exact ⟨((hunit x).mpr hg).unit, rfl⟩

/-- Fibre counting for `x ↦ (x)` on a set `G` of elements of a finite ring that is closed under
generating the same principal ideal: if every fibre has `u / c` elements, then
`#G * c = #{(x) : x ∈ G} * u`. -/
private theorem card_mul_eq_card_principal_mul {B : Type} [CommRing B] [Finite B] (G : Set B)
    (c u : ℕ) (hfib : ∀ x ∈ G, Nat.card {g : B // Ideal.span {g} = Ideal.span {x}} * c = u)
    (hclos : ∀ x ∈ G, ∀ y : B, Ideal.span {y} = Ideal.span {x} → y ∈ G) :
    Nat.card G * c = Nat.card {I : Ideal B // ∃ x ∈ G, I = Ideal.span {x}} * u := by
  have : Fintype B := Fintype.ofFinite B
  let Pr := {I : Ideal B // ∃ x ∈ G, I = Ideal.span {x}}
  let π : G → Pr := fun x => ⟨Ideal.span {x.1}, x.1, x.2, rfl⟩
  have : Finite Pr := Finite.of_surjective π fun ⟨_, x, hx, h⟩ => ⟨⟨x, hx⟩, Subtype.ext h.symm⟩
  have : Fintype Pr := Fintype.ofFinite Pr
  have hfib' : ∀ I : Pr, Nat.card {z : G // π z = I} * c = u := by
    rintro ⟨I, x, hx, rfl⟩
    rw [← hfib x hx]
    congr 1
    exact Nat.card_congr
      { toFun := fun z => ⟨z.1.1, congrArg Subtype.val z.2⟩
        invFun := fun g => ⟨⟨g.1, hclos x hx g.1 g.2⟩, Subtype.ext g.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv π), Nat.card_sigma, Finset.sum_mul,
    Finset.sum_congr rfl (fun I _ => hfib' I), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card (α := Pr)]

/-- In a local ring, two generators of the same nonzero principal ideal differ by a unit. -/
private theorem exists_isUnit_mul_eq_of_span_eq {B : Type} [CommRing B] [IsLocalRing B] {x y : B}
    (hx : x ≠ 0) (hy : Ideal.span {y} = Ideal.span {x}) : ∃ r, IsUnit r ∧ r * x = y := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hy ▸ Ideal.mem_span_singleton_self y)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (hy.symm ▸ Ideal.mem_span_singleton_self x)
  refine ⟨r, ?_, hr⟩
  by_contra hnu
  have h1 := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    (Ideal.mul_mem_left _ s ((IsLocalRing.mem_maximalIdeal r).mpr hnu))
  refine hx (h1.mul_right_eq_zero.mp ?_)
  rw [sub_mul, one_mul, mul_assoc, hr, hs, sub_self]

/-- If `I ≤ J ≤ I + (F)`, then the principal ideal `(F)` of `S ⧸ I` is the preimage of the
principal ideal `(F)` of `S ⧸ J`. -/
private theorem comap_factor_span_singleton {S : Type} [CommRing S] {I J : Ideal S} (h : I ≤ J)
    {F : S} (hJ : J ≤ I ⊔ Ideal.span {F}) :
    Ideal.comap (Ideal.Quotient.factor h) (Ideal.span {Ideal.Quotient.mk J F}) =
      Ideal.span {Ideal.Quotient.mk I F} := by
  rw [← Ideal.Quotient.factor_mk h, ← Set.image_singleton, ← Ideal.map_span,
    Ideal.comap_map_of_surjective _ (Ideal.Quotient.factor_surjective h), sup_eq_left]
  intro z hz
  obtain ⟨Z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hz
  obtain ⟨M, hM, Y, hY, rfl⟩ := Submodule.mem_sup.mp (hJ hz)
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hY
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hM, zero_add, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- Count of the principal ideals `(f)` of the special fibre `k⟦T, X⟧ ⧸ (T^a X^b)` whose generator
satisfies a unit-invariant condition `P` of colength `N` that, read on the truncation
`k⟦T, X⟧ ⧸ truncIdeal k a b (N + 1)`, says: the coefficients on `A` vanish and those on `B` do not.
With `q = #k`, the count times `(q - 1) q^(#A + #B - 1)` is `(q - 1)^#B q^N`. -/
theorem principal_residue_ideal_count (k : Type) [Field k] [Finite k] (a b N : ℕ) (ha : 0 < a)
    (P : TwoSeries k → Prop) (Q : SpecialFiber k a b → Prop)
    (hQ : ∀ F, Q (Ideal.Quotient.mk _ F) ↔ P F) (hunit : ∀ U F, IsUnit U → P F → P (U * F))
    (hlen : ∀ F, P F → Module.length (TwoSeries k)
      (TwoSeries k ⧸ (monomialIdeal k a b ⊔ Ideal.span {F})) = N)
    (hcard : ∀ F, P F →
      Nat.card (TwoSeries k ⧸ (monomialIdeal k a b ⊔ Ideal.span {F})) = Nat.card k ^ N)
    (A B : Finset (truncIndex a b (N + 1))) (hAB : Disjoint A B) (hB : B.Nonempty)
    (hcrit : ∀ F, P F ↔ (∀ s ∈ A, truncCoeffs k a b (N + 1) F s = 0) ∧
      ∀ s ∈ B, truncCoeffs k a b (N + 1) F s ≠ 0) :
    Nat.card {I : Ideal (SpecialFiber k a b) // ∃ f, I = Ideal.span {f} ∧ Q f} *
        ((Nat.card k - 1) * Nat.card k ^ (A.card + B.card - 1)) =
      (Nat.card k - 1) ^ B.card * Nat.card k ^ N := by
  -- Work in the finite local truncation `R' = k⟦T, X⟧ ⧸ truncIdeal k a b (N + 1)`: count the
  -- generators `G` by coefficients, the fibres of `x ↦ (x)` by units, and transport to `Q`.
  have : Fintype k := Fintype.ofFinite k
  have hL0 : 0 < N + 1 := N.succ_pos
  let J := truncIdeal k a b (N + 1)
  let R' := TwoSeries k ⧸ J
  let mk' : TwoSeries k →+* R' := Ideal.Quotient.mk J
  have hmk' : Function.Surjective mk' := Ideal.Quotient.mk_surjective
  have : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr (truncIdeal_ne_top k a b _ ha hL0)
  have : IsLocalRing R' := .of_surjective' mk' hmk'
  let ev := truncEval k a b (N + 1)
  have hev : ∀ F, ev (mk' F) = truncCoeffs k a b (N + 1) F := truncEval_mk k a b (N + 1)
  let eqv : R' ≃ (truncIndex a b (N + 1) → k) := ev.toEquiv
  have : Fintype R' := .ofEquiv _ eqv.symm
  have hmonJ : monomialIdeal k a b ≤ J := le_sup_left
  have hkill : ∀ F, P F → J ≤ monomialIdeal k a b ⊔ Ideal.span {F} := fun F hF ↦
    truncIdeal_le_of_length k a b N F (hlen F hF)
  have hcardq : ∀ F, P F → Nat.card (R' ⧸ Ideal.span {mk' F}) = Nat.card k ^ N := by
    intro F hF
    have e := DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {F})
    rw [Ideal.map_span, Set.image_singleton, le_antisymm (sup_le (hkill F hF) le_sup_right)
      (sup_le_sup_right hmonJ _)] at e
    rw [Nat.card_congr e.toEquiv, hcard F hF]
  -- the generators, the units and the fibres of `x ↦ (x)`
  let G : Set R' := {x | (∀ s ∈ A, ev x s = 0) ∧ ∀ s ∈ B, ev x s ≠ 0}
  have hPG : ∀ F, mk' F ∈ G ↔ P F := fun F => by rw [hcrit]; simp only [G, Set.mem_ofPred_eq, hev]
  have hcardG : Nat.card G =
      (Nat.card k - 1) ^ B.card * Nat.card k ^ (Fintype.card (truncIndex a b (N + 1)) -
        A.card - B.card) := by
    rw [Nat.card_eq_fintype_card (α := k), ← coordinate_constraint_count k _ A B hAB]
    exact Nat.card_congr (eqv.subtypeEquiv fun _ => Iff.rfl)
  have hne0 : ∀ x ∈ G, x ≠ 0 := by
    rintro x ⟨-, h⟩ rfl
    obtain ⟨s, hs⟩ := hB
    exact h s hs (by rw [← map_zero mk', hev, map_zero]; rfl)
  have hfib : ∀ x ∈ G,
      Nat.card {g : R' // Ideal.span {g} = Ideal.span {x}} * Nat.card k ^ N = Nat.card R'ˣ := by
    intro x hx
    obtain ⟨F, rfl⟩ := hmk' x
    rw [← hcardq F ((hPG F).1 hx), ← card_mul_eq_zero_eq_card_quotient]
    exact principal_generator_orbit_count R' _ (hne0 _ hx)
  have hclos : ∀ x ∈ G, ∀ y : R', Ideal.span {y} = Ideal.span {x} → y ∈ G := by
    intro x hx y hy
    obtain ⟨F, rfl⟩ := hmk' x
    obtain ⟨r, hru, hr⟩ := exists_isUnit_mul_eq_of_span_eq (hne0 _ hx) hy
    obtain ⟨Gr, rfl⟩ := hmk' r
    have hGu : IsUnit Gr := MvPowerSeries.isUnit_iff_constantCoeff.mpr
      (isUnit_iff_ne_zero.mpr ((isUnit_mk_truncIdeal_iff k a b _ ha hL0 Gr).mp hru))
    rw [← hr, ← map_mul, hPG]
    exact hunit _ _ hGu ((hPG F).1 hx)
  have hU := card_units_truncQuotient k a b (N + 1) ha hL0
  -- counting the principal ideals of `R'` generated in `G`
  have hGP := card_mul_eq_card_principal_mul G _ _ hfib hclos
  -- residue ideals correspond to principal ideals of `R'` generated in `G`
  let ψ := Ideal.Quotient.factor hmonJ
  have hmapI : ∀ F, Ideal.map ψ (Ideal.span {Ideal.Quotient.mk (monomialIdeal k a b) F}) =
      Ideal.span {mk' F} := fun F => by
    rw [Ideal.map_span, Set.image_singleton, Ideal.Quotient.factor_mk]
  let Φ : {I : Ideal (SpecialFiber k a b) // ∃ f, I = Ideal.span {f} ∧ Q f} →
      {I : Ideal R' // ∃ x ∈ G, I = Ideal.span {x}} :=
    fun I => ⟨Ideal.map ψ I.1, by
      obtain ⟨_, f, rfl, hf⟩ := I
      obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
      exact ⟨mk' F, (hPG F).2 ((hQ F).1 hf), hmapI F⟩⟩
  have hΦ : Function.Bijective Φ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨_, f₁, rfl, hf₁⟩ ⟨_, f₂, rfl, hf₂⟩ h
      obtain ⟨F₁, rfl⟩ := Ideal.Quotient.mk_surjective f₁
      obtain ⟨F₂, rfl⟩ := Ideal.Quotient.mk_surjective f₂
      have h' := congrArg Subtype.val h
      simp only [Φ, hmapI] at h'
      apply Subtype.ext
      change Ideal.span {_} = Ideal.span {_}
      rw [← comap_factor_span_singleton hmonJ (hkill F₁ ((hQ F₁).1 hf₁)),
        ← comap_factor_span_singleton hmonJ (hkill F₂ ((hQ F₂).1 hf₂))]
      exact congrArg _ h'
    · rintro ⟨_, x, hx, rfl⟩
      obtain ⟨F, rfl⟩ := hmk' x
      exact ⟨⟨_, _, rfl, (hQ F).2 ((hPG F).1 hx)⟩, Subtype.ext (hmapI F)⟩
  rw [Nat.card_congr (Equiv.ofBijective Φ hΦ)]
  rw [hcardG, hU] at hGP
  have hℓ : A.card + B.card ≤ Fintype.card (truncIndex a b (N + 1)) :=
    Finset.card_union_of_disjoint hAB ▸ Finset.card_le_univ _
  have hB1 := hB.card_pos
  set m := Fintype.card (truncIndex a b (N + 1)) - A.card - B.card
  have hpos : 0 < Nat.card k ^ m := pow_pos Nat.card_pos _
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [show Fintype.card (truncIndex a b (N + 1)) - 1 = m + (A.card + B.card - 1) by omega,
    pow_add] at hGP
  linarith

end SurfaceBlowup
