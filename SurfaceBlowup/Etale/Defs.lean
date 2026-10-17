/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Basic

/-!
# The étale convention for the type densities

The published densities `monicDensity`, `projectiveDensity` (in `SurfaceBlowup.Basic`) define the
type of a polynomial through finite integral closures (the reduced-algebra convention). This file
defines the densities under the étale convention, where the event is restricted to separable
polynomials (étale algebras `K[X]/(f_a)`), resp. to binary forms with finite étale zero scheme.

## Main definitions

* `SurfaceBlowup.IsEtaleForm`
* `SurfaceBlowup.etaleMonicDensity`, `SurfaceBlowup.etaleProjectiveDensity`
-/

open MeasureTheory
open scoped ENNReal

namespace SurfaceBlowup

section EtaleForm

variable (O : Type) [CommRing O] [IsDomain O]

/-- The binary form `F_a` is étale of degree `n` (its zero scheme in `ℙ¹_K` is finite étale of
degree `n`): nonzero, degree drop at most one (so the point at infinity has multiplicity at most
one), and separable dehomogenization `F_a(X,1)`. -/
def IsEtaleForm {n : ℕ} (a : Fin (n + 1) → O) : Prop :=
  affinePolynomial O a ≠ 0 ∧ n - (affinePolynomial O a).natDegree ≤ 1 ∧
    (affinePolynomial O a).Separable

end EtaleForm

section EtaleMeasure

variable (O : Type) [CommRing O] [IsDomain O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [SecondCountableTopology O]
  [MeasurableSpace O] [BorelSpace O]

/-- The monic probability of type `σ` under the étale convention: the event is restricted to
separable polynomials, i.e. to étale algebras `K[X]/(f_a)`. -/
noncomputable def etaleMonicDensity (n : ℕ) (σ : FactorType) : ℝ≥0∞ :=
  coefficientMeasure O n
    {a | (monicPolynomial O a).Separable ∧ HasPolynomialType O (monicPolynomial O a) σ}

/-- The projective probability of type `σ` under the étale convention. -/
noncomputable def etaleProjectiveDensity (n : ℕ) (σ : FactorType) : ℝ≥0∞ :=
  coefficientMeasure O (n+1) {a | primitive O a ∧ IsEtaleForm O a ∧ HasBinaryType O a σ} /
    coefficientMeasure O (n+1) {a | primitive O a}

end EtaleMeasure

end SurfaceBlowup
