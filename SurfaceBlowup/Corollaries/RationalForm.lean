/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Corollaries.Nonneg

/-!
# The three laws as rational functions, and reciprocity as an automorphism of `ℚ(q)`

`main_dvr` and `main_dvr_cluster` give the densities as values `Expr.eval` of syntactic
expressions, and `recip_main` states reciprocity through the syntactic substitution
`Expr.subst (.inv .var)`. This file restates everything in terms of the rational functions
`A = (monicExpr n σ).rational`, `B = (clusterExpr n σ).rational` and
`R = (projectiveExpr n σ).rational` in `ℚ(q)` and of Mathlib's `RatFunc.eval`, so that no
convention of `Expr` has to be audited:

* `SurfaceBlowup.cluster_rational_eval`: `B` evaluates at a prime power to the value of the cluster
  expression (the analogue of `global_rational_eval`, which covers `A` and `R`).
* `SurfaceBlowup.universal_type_laws`: Theorem 1.1 in one statement. There are `A, B, R ∈ ℚ(q)`,
  regular and nonnegative at every prime power, such that over every complete discrete valuation
  ring with finite residue field of size `q` the monic, cluster and projective probabilities of
  type `σ` are the nonnegative rational numbers `A(q)`, `B(q)`, `R(q)`.
* `SurfaceBlowup.reciprocity_recipRat`, `SurfaceBlowup.reciprocity_ringHom`: Theorem 1.2 for the
  same `A, B, R`, in every degree `n` (including `n = 0`): `A = v(B)` and `v(R) = R` for the ring
  endomorphism `v` of `ℚ(q)` with `v(q) = q⁻¹`.
* `SurfaceBlowup.clusterExpr_subst_inv_rational`: the syntactic right side of `recip_main` is
  `v(B)`.

No existing declaration is modified.
-/

open scoped ENNReal

namespace SurfaceBlowup

/-! ### Evaluating the rational function of a safe expression -/

/-- Evaluating the rational function of a safe expression at `q` gives its value at `q`. (This is
the statement of the private lemma `expression_rational_eval` of `Formula.RationalEval`, with the
same proof.) -/
theorem Expr.rational_eval_of_safe (x : Expr) (q : ℚ) (hx : x.safe q) :
    RatFunc.eval (RingHom.id ℚ) q x.rational = x.eval q := by
  obtain ⟨hQ, hval⟩ := expression_fraction x q hx
  have hrat : x.rational = algebraMap _ _ x.fraction.1 / algebraMap _ _ x.fraction.2 := rfl
  have hQ0 : x.fraction.2 ≠ 0 := by
    intro h; apply hQ; rw [h]; simp
  have hQ0' : algebraMap (Polynomial ℚ) (RatFunc ℚ) x.fraction.2 ≠ 0 :=
    RatFunc.algebraMap_ne_zero hQ0
  have hden : (RatFunc.denom x.rational).eval₂ (RingHom.id ℚ) q ≠ 0 := by
    intro h
    have hd : RatFunc.denom x.rational ∣ x.fraction.2 := by
      rw [hrat]; exact RatFunc.denom_div_dvd _ _
    exact hQ (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hd h)
  have h2 : x.rational * algebraMap _ _ x.fraction.2 = algebraMap _ _ x.fraction.1 := by
    rw [hrat]; exact div_mul_cancel₀ _ hQ0'
  have h3 := RatFunc.eval_mul (f := RingHom.id ℚ) (a := q) (x := x.rational)
    (y := algebraMap _ _ x.fraction.2) hden
    (by rw [RatFunc.denom_algebraMap]; simp)
  rw [h2] at h3
  have eP : RatFunc.eval (RingHom.id ℚ) q (algebraMap _ _ x.fraction.1) = x.fraction.1.eval q := by
    rw [RatFunc.eval_algebraMap]; simp [Polynomial.eval₂_id]
  have eQ : RatFunc.eval (RingHom.id ℚ) q (algebraMap _ _ x.fraction.2) = x.fraction.2.eval q := by
    rw [RatFunc.eval_algebraMap]; simp [Polynomial.eval₂_id]
  rw [eP, eQ] at h3
  rw [hval, eq_div_iff hQ]
  exact h3.symm

/-! ### The cluster law as a rational function -/

/-- The cluster expression `B_{n,σ}` is safe at every integer `q ≥ 2`: no denominator vanishes. -/
theorem clusterExpr_allSafe (n : ℕ) (σ : FactorType) : (clusterExpr n σ).allSafe := by
  intro q hq
  have hL : LawSafe (rootLaw n) := by
    unfold rootLaw
    split_ifs with h
    · intro z hz q _
      simp only [lawOne, List.mem_singleton] at hz
      subst hz
      trivial
    · exact local_law_safe _ ⟨Nat.one_pos, Nat.pos_of_ne_zero h⟩
  refine expression_sum_safe _ _ fun x hx => ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
  by_cases h : z.1 = σ
  · simp only [h, ite_true]; exact hL z hz q hq
  · simp [h, Expr.safe]

/-- **The cluster rational function evaluates correctly.** At every prime power `q`, the rational
function `B_{n,σ} = (clusterExpr n σ).rational` takes the value of the cluster expression. Together
with `cluster_formula_regular` and `main_dvr_cluster` this identifies `B_{n,σ}(q)` with the cluster
probability. -/
theorem cluster_rational_eval (n : ℕ) (σ : FactorType) :
    ∀ q : ℕ, PrimePower q →
      RatFunc.eval (RingHom.id ℚ) q (clusterExpr n σ).rational = (clusterExpr n σ).eval q :=
  fun q hq =>
    Expr.rational_eval_of_safe _ _ (clusterExpr_allSafe n σ q (prime_power_ge_two q hq))

/-! ### Theorem 1.1 in one statement -/

/-- **Theorem 1.1 (universal type laws), packaged.** For every degree `n` and every type `σ` there
are rational functions `A, B, R ∈ ℚ(q)` — namely the rational functions of `monicExpr n σ`,
`clusterExpr n σ`, `projectiveExpr n σ` — such that

* `A`, `B`, `R` are regular at every prime power, and their values there are nonnegative;
* over every complete discrete valuation ring `O` with finite residue field `k` (any
  characteristic, any ramification; adic topology, Borel σ-algebra, normalized Haar measure), with
  `q = |k|`, the values `A(q)`, `B(q)`, `R(q)` are nonnegative rational numbers and the monic,
  cluster and projective probabilities of type `σ` are `A(q)`, `B(q)`, `R(q)`.

Each probability clause has the form `0 ≤ r ∧ density = ENNReal.ofReal r`. The two parts together
determine the density exactly: `ENNReal.ofReal` is injective on nonnegative reals, so no clamping
at `0` is possible, and the density is finite. The values are those of Mathlib's `RatFunc.eval`,
so the convention `0⁻¹ = 0` of `Expr.eval` does not enter the statement. -/
theorem universal_type_laws (n : ℕ) (σ : FactorType) :
    ∃ A B R : RatFunc ℚ,
      A = (monicExpr n σ).rational ∧ B = (clusterExpr n σ).rational ∧
      R = (projectiveExpr n σ).rational ∧
      (∀ q : ℕ, PrimePower q → RegularAt A q ∧ RegularAt B q ∧ RegularAt R q) ∧
      (∀ q : ℕ, PrimePower q →
        0 ≤ RatFunc.eval (RingHom.id ℚ) (q : ℚ) A ∧ 0 ≤ RatFunc.eval (RingHom.id ℚ) (q : ℚ) B ∧
        0 ≤ RatFunc.eval (RingHom.id ℚ) (q : ℚ) R) ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
        [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
        [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O],
        IsAdic (IsLocalRing.maximalIdeal O) →
          (0 ≤ RatFunc.eval (RingHom.id ℚ) ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) A ∧
            monicDensity O n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
              ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) A : ℚ) : ℝ)) ∧
          (0 ≤ RatFunc.eval (RingHom.id ℚ) ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) B ∧
            clusterDensity O n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
              ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) B : ℚ) : ℝ)) ∧
          (0 ≤ RatFunc.eval (RingHom.id ℚ) ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) R ∧
            projectiveDensity O n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
              ((Nat.card (IsLocalRing.ResidueField O) : ℕ) : ℚ) R : ℚ) : ℝ)) := by
  refine ⟨_, _, _, rfl, rfl, rfl, fun q hq => ?_, fun q hq => ?_, ?_⟩
  · exact ⟨(global_formula_regular n σ q hq).1, cluster_formula_regular n σ q hq,
      (global_formula_regular n σ q hq).2⟩
  · obtain ⟨e1, e2⟩ := global_rational_eval n σ q hq
    rw [e1, e2, cluster_rational_eval n σ q hq]
    exact ⟨monicExpr_eval_nonneg n σ q hq, clusterExpr_eval_nonneg n σ q hq,
      projectiveExpr_eval_nonneg n σ q hq⟩
  · intro O _ _ _ _ _ _ _ _ _ _ _ _ htop
    have hq := finite_field_card_primePower (IsLocalRing.ResidueField O)
    obtain ⟨e1, e2⟩ := global_rational_eval n σ _ hq
    obtain ⟨h1, h2⟩ := main_dvr O htop n σ
    rw [e1, e2, cluster_rational_eval n σ _ hq]
    exact ⟨⟨monicExpr_eval_nonneg n σ _ hq, h1⟩,
      ⟨clusterExpr_eval_nonneg n σ _ hq, main_dvr_cluster O htop n σ⟩,
      ⟨projectiveExpr_eval_nonneg n σ _ hq, h2⟩⟩

/-! ### Reciprocity as an automorphism of `ℚ(q)` -/

/-- For a well-formed law, substituting `q ↦ 1/q` syntactically in the `σ`-coefficient and then
taking the rational function is the same as applying the automorphism `recipRat` (`q ↦ q⁻¹`) of
`ℚ(q)` to the rational function of the coefficient. -/
theorem rational_subst_inv_lawCoeff (L : Law) (hL : LawWf L) (σ : FactorType) :
    ((lawCoeff L σ).subst (.inv .var)).rational = recipRat (lawCoeff L σ).rational := by
  rw [← coeff_recipCoef_lawCoef L hL σ, recipCoef_coeff, coeff_lawCoef L hL σ]

/-- The root law consists of well-formed expressions, in every degree (including `rootLaw 0`, the
unit law). -/
theorem lawWf_rootLaw (n : ℕ) : LawWf (rootLaw n) := by
  unfold rootLaw
  split_ifs with h
  · intro z hz
    simp only [lawOne, List.mem_singleton] at hz
    subst hz
    trivial
  · exact lawWf_stateLaw _ ⟨Nat.one_pos, Nat.pos_of_ne_zero h⟩

/-- In degree `0` the global monic law is `1`. -/
theorem lawCoef_globalLaw_false_zero : lawCoef (globalLaw false 0) = 1 := by
  rw [lawCoef_globalLaw_false, ← coeff_eulerSer, coeff_zero_eulerSer, mul_one, Nat.cast_zero,
    neg_zero, qpow_zero]

/-- In degree `0` the root law is `1`. -/
theorem lawCoef_rootLaw_zero : lawCoef (rootLaw 0) = 1 := by
  simp [rootLaw, lawOne, lawCoef, Expr.rational_const, AddMonoidAlgebra.one_def]

/-- **Affine reciprocity in every degree.** `A_n = B_n^∨` as elements of `ℚ(q)[Z]`, including
`n = 0`, where both sides are `1` (`lawCoef_globalLaw_false_eq_recipCoef` assumes `0 < n`). -/
theorem lawCoef_globalLaw_false_eq_recipCoef_rootLaw (n : ℕ) :
    lawCoef (globalLaw false n) = recipCoef (lawCoef (rootLaw n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [lawCoef_globalLaw_false_zero, lawCoef_rootLaw_zero, map_one]
  · exact lawCoef_globalLaw_false_eq_recipCoef n hn

/-- **Theorem 1.2 (reciprocity), in terms of the automorphism `q ↦ q⁻¹`, in every degree.** For
every `n` and every type `σ`, `A_{n,σ} = v(B_{n,σ})` and `v(R_{n,σ}) = R_{n,σ}` in `ℚ(q)`, where
`v = recipRat` is the ring endomorphism of `ℚ(q)` with `v(q) = q⁻¹` (`recipRat_X`) and `A`, `B`,
`R` are the rational functions of the monic, cluster and projective expressions. Unlike
`recip_main`, there is no hypothesis `0 < n` and no syntactic substitution in the statement. -/
theorem reciprocity_recipRat (n : ℕ) (σ : FactorType) :
    (monicExpr n σ).rational = recipRat (clusterExpr n σ).rational ∧
    recipRat (projectiveExpr n σ).rational = (projectiveExpr n σ).rational := by
  refine ⟨?_, ?_⟩
  · change (monicExpr n σ).rational = recipRat (lawCoeff (rootLaw n) σ).rational
    rw [← coeff_lawCoef_globalLaw_false, lawCoef_globalLaw_false_eq_recipCoef_rootLaw,
      recipCoef_coeff, coeff_lawCoef _ (lawWf_rootLaw n) σ]
  · rw [← coeff_lawCoef_globalLaw_true, ← recipCoef_coeff, recipCoef_lawCoef_globalLaw_true]

/-- The syntactic right side of `recip_main` is the automorphism `q ↦ q⁻¹` applied to the cluster
rational function: `((clusterExpr n σ).subst (.inv .var)).rational = v(B_{n,σ})`. -/
theorem clusterExpr_subst_inv_rational (n : ℕ) (σ : FactorType) :
    ((clusterExpr n σ).subst (.inv .var)).rational = recipRat (clusterExpr n σ).rational :=
  rational_subst_inv_lawCoeff (rootLaw n) (lawWf_rootLaw n) σ

/-- `recip_main` without the hypothesis `0 < n`: the syntactic form of reciprocity holds in every
degree. -/
theorem recip_main_all_degrees (n : ℕ) (σ : FactorType) :
    (monicExpr n σ).rational = ((clusterExpr n σ).subst (.inv .var)).rational ∧
    (projectiveExpr n σ).rational = ((projectiveExpr n σ).subst (.inv .var)).rational := by
  obtain ⟨h1, h2⟩ := reciprocity_recipRat n σ
  exact ⟨by rw [clusterExpr_subst_inv_rational, h1],
    by rw [show projectiveExpr n σ = lawCoeff (globalLaw true n) σ from rfl,
      rational_subst_inv_lawCoeff _ (lawWf_globalLaw true n) σ]; exact h2.symm⟩

/-- **Theorem 1.2 (reciprocity), stated with Mathlib notions only.** For every degree `n` and
every type `σ` there is a ring endomorphism `v` of `ℚ(q)` with `v(q) = q⁻¹` such that `A = v(B)`
and `v(R) = R`, where `A`, `B`, `R` are the rational functions of `universal_type_laws`. A ring
endomorphism of the field `ℚ(q)` is determined by the image of `q`, so `v` is the substitution
`q ↦ 1/q`. -/
theorem reciprocity_ringHom (n : ℕ) (σ : FactorType) :
    ∃ v : RatFunc ℚ →+* RatFunc ℚ, v RatFunc.X = (RatFunc.X)⁻¹ ∧
      (monicExpr n σ).rational = v (clusterExpr n σ).rational ∧
      v (projectiveExpr n σ).rational = (projectiveExpr n σ).rational :=
  ⟨recipRat, recipRat_X, reciprocity_recipRat n σ⟩

end SurfaceBlowup
