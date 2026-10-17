/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Basic

/-!
# The cluster density

Definitions for the cluster clause of Theorem 1.1: the cluster cell `(πO)^n` (coefficient vectors
whose monic polynomial reduces to `X^n`), the universal cluster expression `B_{n,σ}` (the
coefficient of `σ` in the root law, the law of the state `S(1;n)`), and the cluster probability
`clusterDensity O n σ` (the normalized restriction of the coefficient measure to the cluster cell,
with the reduced-algebra type predicate `HasPolynomialType`).
-/

noncomputable section

namespace SurfaceBlowup

open scoped ENNReal

section Classical

variable (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]

/-- The cluster cell `(πO)^n`: coefficient vectors whose monic polynomial reduces to `X^n`
(paper display (1.1), measure `μ_cluster`). -/
def clusterCell (n : ℕ) : Set (Fin n → O) := {a | ∀ i, a i ∈ IsLocalRing.maximalIdeal O}

end Classical

/-- `B_{n,σ}`: the coefficient of `σ` in the root law, the law of the state `S(1;n)`
(paper display (7.1)). -/
noncomputable def clusterExpr (n : ℕ) (σ : FactorType) : Expr := lawCoeff (rootLaw n) σ

section Measure

variable (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [SecondCountableTopology O]
  [MeasurableSpace O] [BorelSpace O]

/-- The cluster probability of type `σ` (paper display (1.1)): the normalized restriction of
the coefficient measure to the cluster cell. The event uses `HasPolynomialType` (the
reduced-algebra convention: a factorization into distinct monic irreducible factors, inseparable
factors allowed); the inseparable locus is Haar-null, so the étale convention gives the same
value (`clusterDensity_eq_etale`). -/
noncomputable def clusterDensity (n : ℕ) (σ : FactorType) : ℝ≥0∞ :=
  coefficientMeasure O n (clusterCell O n ∩ {a | HasPolynomialType O (monicPolynomial O a) σ}) /
    coefficientMeasure O n (clusterCell O n)

end Measure

end SurfaceBlowup
