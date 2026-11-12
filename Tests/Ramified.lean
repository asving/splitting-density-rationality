/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Corollaries.AdicCompact
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Non-vacuity over a ramified base: `ℚ_p(√p)`

`Tests/PadicInt.lean` applies the main theorem to `ℤ_p`. This file applies it to the ring of
integers of the ramified quadratic extension `K = ℚ_p(√p) = ℚ_p[X]/(X² - p)`, for every prime `p`
including `p = 2`.

## Main results

* `irreducible_sqrtPoly`: `X² - p` is irreducible over `ℚ_p` (it has no root, by valuations).
* `not_padicUnramified`: `K/ℚ_p` is ramified: `p = √p · √p` in `𝒪_K`, so `p` is not irreducible.
* `main_field_form_sqrtP`: the monic and projective type densities over `𝒪_K`, with its `𝔪`-adic
  topology and Borel σ-algebra, are the values of the universal rational functions at the residue
  cardinality of `𝒪_K`. No topological hypothesis is assumed.
-/

open Polynomial IsLocalRing

namespace SurfaceBlowup.Tests

section Ramified

variable (p : ℕ) [hp : Fact p.Prime]

/-- The polynomial `X² - p` over `ℚ_p`. -/
noncomputable abbrev sqrtPoly : ℚ_[p][X] := X ^ 2 - C (p : ℚ_[p])

/-- `p` is not a square in `ℚ_p`: its valuation is odd. -/
theorem not_isSquare_p (x : ℚ_[p]) : x ^ 2 ≠ (p : ℚ_[p]) := by
  intro h
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    exact hp.out.ne_zero (by exact_mod_cast h.symm)
  have hv := congrArg Padic.valuation h
  rw [Padic.valuation_pow, Padic.valuation_p] at hv
  omega

theorem irreducible_sqrtPoly : Irreducible (sqrtPoly p) := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun x hx => not_isSquare_p p x ?_
  · rw [sqrtPoly, natDegree_X_pow_sub_C]; decide
  · simpa [sqrtPoly, IsRoot, sub_eq_zero] using hx

instance : Fact (Irreducible (sqrtPoly p)) := ⟨irreducible_sqrtPoly p⟩

/-- The field `ℚ_p(√p)`. -/
noncomputable abbrev QpSqrtP : Type := AdjoinRoot (sqrtPoly p)

instance : FiniteDimensional ℚ_[p] (QpSqrtP p) :=
  (AdjoinRoot.powerBasis (irreducible_sqrtPoly p).ne_zero).finite

/-- `√p` is integral over `ℤ_p`. -/
theorem isIntegral_root : IsIntegral ℤ_[p] (AdjoinRoot.root (sqrtPoly p)) := by
  refine ⟨X ^ 2 - C (p : ℤ_[p]), ?_, ?_⟩
  · exact monic_X_pow_sub_C _ two_ne_zero
  · have h := AdjoinRoot.eval₂_root (sqrtPoly p)
    simp only [sqrtPoly, eval₂_sub, eval₂_X_pow, eval₂_C] at h ⊢
    simpa [map_natCast] using h

/-- `ℚ_p(√p)` is ramified over `ℚ_p`: `p` is the square of `√p` in the ring of integers. -/
theorem not_padicUnramified : ¬ PadicUnramified p (QpSqrtP p) := by
  intro hirr
  let s : padicIntegers p (QpSqrtP p) := ⟨_, isIntegral_root p⟩
  have hs : s * s = (p : padicIntegers p (QpSqrtP p)) := by
    apply Subtype.ext
    have h := AdjoinRoot.eval₂_root (sqrtPoly p)
    simp only [sqrtPoly, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
    simpa [s, pow_two, map_natCast] using h
  rcases hirr.isUnit_or_isUnit hs.symm with hu | hu <;>
    exact hirr.not_isUnit (hs ▸ hu.mul hu)

/-- **Main theorem over `ℤ_p[√p]`.** With the `𝔪`-adic topology and Borel σ-algebra on the ring of
integers of the ramified field `ℚ_p(√p)`, the type densities are the values of the universal
rational functions at the residue cardinality. -/
theorem main_field_form_sqrtP (n : ℕ) (σ : FactorType) :
    letI := padicIntegers_isDVR p (QpSqrtP p)
    haveI := padicIntegers_maximal_adic_complete p (QpSqrtP p) this
    haveI := padicIntegers_residueField_finite p (QpSqrtP p) (padicIntegers_isDVR p (QpSqrtP p))
    letI := (maximalIdeal (padicIntegers p (QpSqrtP p))).adicTopology
    letI : MeasurableSpace (padicIntegers p (QpSqrtP p)) := borel _
    haveI : BorelSpace (padicIntegers p (QpSqrtP p)) := ⟨rfl⟩
    haveI := isTopologicalRing_of_isAdic (I := maximalIdeal (padicIntegers p (QpSqrtP p))) rfl
    haveI := compactSpace_of_isAdic (O := padicIntegers p (QpSqrtP p)) rfl
    haveI := t2Space_of_isAdic (O := padicIntegers p (QpSqrtP p)) rfl
    haveI := secondCountableTopology_of_isAdic (O := padicIntegers p (QpSqrtP p)) rfl
    monicDensity (padicIntegers p (QpSqrtP p)) n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
        (Nat.card (ResidueField (padicIntegers p (QpSqrtP p))) : ℚ) (monicExpr n σ).rational :
          ℚ) : ℝ) ∧
      projectiveDensity (padicIntegers p (QpSqrtP p)) n σ = ENNReal.ofReal ((RatFunc.eval
        (RingHom.id ℚ) (Nat.card (ResidueField (padicIntegers p (QpSqrtP p))) : ℚ)
          (projectiveExpr n σ).rational : ℚ) : ℝ) :=
  main_field_form_ramified_adic n σ p (QpSqrtP p)

end Ramified

end SurfaceBlowup.Tests
