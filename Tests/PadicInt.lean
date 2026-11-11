/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Corollaries.RationalForm
import Tests.Regression
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Non-vacuity in mixed characteristic: the `p`-adic integers

`Tests.NonVacuity` shows that the hypotheses of `SurfaceBlowup.main_dvr` are satisfiable in equal
characteristic (`𝔽_q⟦X⟧`). This file does the same in mixed characteristic, for the ring `ℤ_[p]` of
`p`-adic integers with **Mathlib's own topology** (the one induced by the `p`-adic norm): it is a
complete discrete valuation ring with residue field `𝔽_p`, a compact Hausdorff second-countable
topological ring, and its norm topology is the `(p)`-adic one. Equipping it with the Borel
σ-algebra (`padicIntMeasurableSpace`, a local instance: no topology or metric is declared here),
`main_dvr` applies. This is the case of the conjecture of
Bhargava–Cremona–Fisher–Gajović, which is stated over `ℤ_p`.

## Main results

* `SurfaceBlowup.Tests.isAdic_maximalIdeal_padicInt`: the norm topology on `ℤ_[p]` is `(p)`-adic.
* `SurfaceBlowup.Tests.main_dvr_padicInt`: `main_dvr` for `ℤ_[p]`, with `q = p`.
* `SurfaceBlowup.Tests.universal_type_laws_padicInt`: the monic, cluster and projective
  probabilities over `ℤ_[p]` are the (nonnegative) values at `p` of the three universal rational
  functions.
* `SurfaceBlowup.Tests.monicDensity_padicInt_two_ramified`: a random monic quadratic over `ℤ_[p]`
  is ramified with probability `1 / (p + 1)`, for every prime `p` including `p = 2`.

Only `ℤ_[p]` itself is instantiated. For the ring of integers of a ramified finite extension of
`ℚ_[p]`, `main_field_form_ramified` still takes the compact adic topology as a hypothesis; no
instance of it is constructed here.
-/

open IsLocalRing Topology

namespace SurfaceBlowup.Tests

section PadicInt

variable (p : ℕ) [hp : Fact p.Prime]

/-- The residue field of `ℤ_[p]` is `ZMod p`, hence finite. -/
instance : Finite (ResidueField ℤ_[p]) :=
  .of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv

/-- The Borel σ-algebra on `ℤ_[p]`. The pinned Mathlib has no `MeasurableSpace` instance on
`ℤ_[p]`; this one is local to this file, so it cannot clash with an instance added elsewhere. -/
noncomputable local instance padicIntMeasurableSpace : MeasurableSpace ℤ_[p] := borel _

/-- The Borel σ-algebra makes `ℤ_[p]` a Borel space. -/
local instance padicIntBorelSpace : BorelSpace ℤ_[p] := ⟨rfl⟩

/-- The norm topology on `ℤ_[p]` is the `(p)`-adic topology: the ideal `(p)ⁿ` is the closed ball of
radius `p⁻ⁿ`, which is open because the `p`-adic distance is an ultrametric, and these balls form a
basis of neighbourhoods of `0`. -/
theorem isAdic_maximalIdeal_padicInt : IsAdic (maximalIdeal ℤ_[p]) := by
  rw [PadicInt.maximalIdeal_eq_span_p, isAdic_iff]
  have hball : ∀ n : ℕ, ((Ideal.span {(p : ℤ_[p])} ^ n : Ideal ℤ_[p]) : Set ℤ_[p]) =
      Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) := by
    intro n
    ext x
    rw [Ideal.span_singleton_pow, SetLike.mem_coe, ← PadicInt.norm_le_pow_iff_mem_span_pow,
      mem_closedBall_zero_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · rw [hball]
    exact IsUltrametricDist.isOpen_closedBall _
      (zpow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
  · obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
    refine ⟨k, ?_⟩
    rw [hball]
    exact (Metric.closedBall_subset_ball hk).trans hεs

/-- The residue field of `ℤ_[p]` has `p` elements. -/
theorem card_residueField_padicInt : Nat.card (ResidueField ℤ_[p]) = p := by
  rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv, Nat.card_zmod]

/-- **`main_dvr` over `ℤ_[p]`.** With Mathlib's topology on the `p`-adic integers, its Borel
σ-algebra and normalized Haar measure, the type densities of monic polynomials and of primitive
binary forms over `ℤ_[p]` are the universal expressions evaluated at `q = p`. -/
theorem main_dvr_padicInt (n : ℕ) (σ : FactorType) :
    monicDensity ℤ_[p] n σ = densityValue (monicExpr n σ) p ∧
      projectiveDensity ℤ_[p] n σ = densityValue (projectiveExpr n σ) p := by
  have h := main_dvr ℤ_[p] (isAdic_maximalIdeal_padicInt p) n σ
  rwa [card_residueField_padicInt] at h

/-- **Theorem 1.1 over `ℤ_[p]`, in terms of rational functions.** The values at `p` of the
rational functions of `monicExpr n σ`, `clusterExpr n σ`, `projectiveExpr n σ` are nonnegative, and
they are the monic, cluster and projective probabilities of type `σ` over `ℤ_[p]`. -/
theorem universal_type_laws_padicInt (n : ℕ) (σ : FactorType) :
    (0 ≤ RatFunc.eval (RingHom.id ℚ) (p : ℚ) (monicExpr n σ).rational ∧
      monicDensity ℤ_[p] n σ = ENNReal.ofReal
        ((RatFunc.eval (RingHom.id ℚ) (p : ℚ) (monicExpr n σ).rational : ℚ) : ℝ)) ∧
    (0 ≤ RatFunc.eval (RingHom.id ℚ) (p : ℚ) (clusterExpr n σ).rational ∧
      clusterDensity ℤ_[p] n σ = ENNReal.ofReal
        ((RatFunc.eval (RingHom.id ℚ) (p : ℚ) (clusterExpr n σ).rational : ℚ) : ℝ)) ∧
    (0 ≤ RatFunc.eval (RingHom.id ℚ) (p : ℚ) (projectiveExpr n σ).rational ∧
      projectiveDensity ℤ_[p] n σ = ENNReal.ofReal
        ((RatFunc.eval (RingHom.id ℚ) (p : ℚ) (projectiveExpr n σ).rational : ℚ) : ℝ)) := by
  obtain ⟨A, B, R, rfl, rfl, rfl, -, -, h⟩ := universal_type_laws n σ
  have h' := h ℤ_[p] (isAdic_maximalIdeal_padicInt p)
  rwa [card_residueField_padicInt] at h'

/-- A random monic quadratic over `ℤ_[p]` is ramified (type `(2,1)`) with probability
`1 / (p + 1)`, for every prime `p`. -/
theorem monicDensity_padicInt_two_ramified :
    monicDensity ℤ_[p] 2 {(2,1)} = ENNReal.ofReal (1 / ((p : ℝ) + 1)) := by
  have h := monicDensity_two_ramified ℤ_[p] (isAdic_maximalIdeal_padicInt p)
  rwa [card_residueField_padicInt] at h

end PadicInt

end SurfaceBlowup.Tests

#print axioms SurfaceBlowup.Tests.main_dvr_padicInt
#print axioms SurfaceBlowup.Tests.universal_type_laws_padicInt
