/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Cluster.Main
import Tests.Regression

/-!
# Regression guard for the cluster density

The quadratic cluster law: over every complete DVR with finite residue field of cardinality `q`,
a random monic quadratic reducing to `X²` is ramified (type `(2,1)`) with probability
`q / (q + 1)`, split or inert each with probability `1 / (2(q + 1))`. Derived from
`SurfaceBlowup.main_dvr_cluster` and the law of `S(1;2)` (`SurfaceBlowup.Tests.single_two_law`).
-/

namespace SurfaceBlowup.Tests

open IsLocalRing

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
  [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
  [MeasurableSpace O] [BorelSpace O]

/-- The value at `q = |k|` of the quadratic cluster law. -/
private theorem clusterDensity_two (htop : IsAdic (maximalIdeal O)) (σ : FactorType) :
    clusterDensity O 2 σ = ENNReal.ofReal (
      (if σ = {(2,1)} then (Nat.card (ResidueField O) : ℚ) / (Nat.card (ResidueField O) + 1)
        else 0) +
      (if σ = {(1,1),(1,1)} then 1 / (2 * ((Nat.card (ResidueField O) : ℚ) + 1)) else 0) +
      (if σ = {(1,2)} then 1 / (2 * ((Nat.card (ResidueField O) : ℚ) + 1)) else 0) : ℚ) := by
  have hq : 1 < (Nat.card (ResidueField O) : ℚ) := by exact_mod_cast Finite.one_lt_card
  rw [main_dvr_cluster O htop, clusterExpr, rootLaw, if_neg two_ne_zero, densityValue,
    single_two_law 1 one_pos _ hq]

/-- Quadratic cluster, ramified: probability `q / (q + 1)`. -/
theorem clusterDensity_two_ramified (htop : IsAdic (maximalIdeal O)) :
    clusterDensity O 2 {(2,1)} =
      ENNReal.ofReal (Nat.card (ResidueField O) / (Nat.card (ResidueField O) + 1)) := by
  rw [clusterDensity_two O htop]
  simp +decide

/-- Quadratic cluster, split: probability `1 / (2(q + 1))`. -/
theorem clusterDensity_two_split (htop : IsAdic (maximalIdeal O)) :
    clusterDensity O 2 {(1,1),(1,1)} =
      ENNReal.ofReal (1 / (2 * (Nat.card (ResidueField O) + 1))) := by
  rw [clusterDensity_two O htop]
  simp +decide

/-- Quadratic cluster, inert: probability `1 / (2(q + 1))`. -/
theorem clusterDensity_two_inert (htop : IsAdic (maximalIdeal O)) :
    clusterDensity O 2 {(1,2)} =
      ENNReal.ofReal (1 / (2 * (Nat.card (ResidueField O) + 1))) := by
  rw [clusterDensity_two O htop]
  simp +decide

end SurfaceBlowup.Tests
