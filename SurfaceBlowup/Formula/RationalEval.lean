/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import SurfaceBlowup.Formula.StateCombinatorics

/-!
# Evaluating the universal rational functions

The rational function `Expr.rational` of a safe expression evaluates at `q` to the value of the
expression; in particular the monic and projective expressions evaluate correctly at every prime
power.

## Main results

* `SurfaceBlowup.global_rational_eval`

Provenance: `Thm_SurfaceBlowupV2_{expression_rational_eval, global_rational_eval}` (moved from
`Blowup/CurveOrders.lean`).
-/

namespace SurfaceBlowup

/-- Evaluating the rational function of a safe expression at `q` gives its value at `q`. -/
private theorem expression_rational_eval (x : Expr) (q : ℚ) (hx : x.safe q) :
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

/-- The rational functions of the monic and projective expressions evaluate correctly at
prime powers. -/
theorem global_rational_eval (n : ℕ) (σ : FactorType) :
    ∀ q : ℕ, PrimePower q → RatFunc.eval (RingHom.id ℚ) q (monicExpr n σ).rational =
        (monicExpr n σ).eval q ∧ RatFunc.eval (RingHom.id ℚ) q (projectiveExpr n σ).rational =
        (projectiveExpr n σ).eval q := by
  intro q hq
  have h2 := prime_power_ge_two q hq
  obtain ⟨h1, h3⟩ := global_coefficients_safe n σ
  exact ⟨expression_rational_eval _ _ (h1 q h2),
    expression_rational_eval _ _ (h3 q h2)⟩

end SurfaceBlowup
