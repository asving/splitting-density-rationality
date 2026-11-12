/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Main
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Topology.Metrizable.Uniformity

/-!
# The adic topology of a complete DVR with finite residue field

`main_dvr` takes the topology of `O` as hypotheses: a topology that is `𝔪`-adic (`IsAdic`), together
with the instances `IsTopologicalRing`, `CompactSpace`, `T2Space` and `SecondCountableTopology`.
This file proves that the last four follow from the first when `O` is a complete DVR with finite
residue field, so they are never an extra assumption. In particular the `𝔪`-adic topology itself
satisfies all of them.

## Main results

* `isTopologicalRing_of_isAdic`, `compactSpace_of_isAdic`, `t2Space_of_isAdic`,
  `secondCountableTopology_of_isAdic`: the instances, from `IsAdic 𝔪`.
* `main_dvr_of_isAdic`: `main_dvr` with only `IsAdic 𝔪` and a Borel σ-algebra as topological input.
* `main_dvr_adic`: `main_dvr` for the `𝔪`-adic topology itself and its Borel σ-algebra; no
  topological hypothesis is left.
* `main_field_form_ramified_adic`: the same for the ring of integers of every finite extension
  `K/ℚ_p`, ramified or not.

Compactness is completeness plus total boundedness: Mathlib's `IsAdic.isAdicComplete_iff` gives
completeness and the Hausdorff property from `IsAdicComplete`, and total boundedness holds because
every `O/𝔪ⁿ` is finite (`residue_quotient_card`).
-/

open IsLocalRing Topology Filter

namespace SurfaceBlowup

section General

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]

/-- An `I`-adic topology is a ring topology. -/
theorem isTopologicalRing_of_isAdic {R : Type*} [CommRing R] [t : TopologicalSpace R] {I : Ideal R}
    (h : IsAdic I) : IsTopologicalRing R := by
  have : t = I.adicTopology := h
  subst this
  exact I.ringFilterBasis.isTopologicalRing

omit [IsAdicComplete (maximalIdeal O) O] [TopologicalSpace O] in
/-- Every `O/𝔪ⁿ` is finite. -/
theorem finite_quotient_maximalIdeal_pow (n : ℕ) : Finite (O ⧸ maximalIdeal O ^ n) := by
  apply Nat.finite_of_card_ne_zero
  rw [residue_quotient_card]
  exact pow_ne_zero _ (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)

variable (htop : IsAdic (maximalIdeal O))
include htop

omit [Finite (ResidueField O)] in
/-- The `𝔪`-adic topology is Hausdorff. -/
theorem t2Space_of_isAdic : T2Space O := by
  have := isTopologicalRing_of_isAdic htop
  let := IsTopologicalAddGroup.rightUniformSpace O
  have := isUniformAddGroup_of_addCommGroup (G := O)
  exact ((IsAdic.isAdicComplete_iff htop).mp inferInstance).2

/-- The `𝔪`-adic topology of a complete DVR with finite residue field is compact. -/
theorem compactSpace_of_isAdic : CompactSpace O := by
  have := isTopologicalRing_of_isAdic htop
  let := IsTopologicalAddGroup.rightUniformSpace O
  have := isUniformAddGroup_of_addCommGroup (G := O)
  have hc : CompleteSpace O := ((IsAdic.isAdicComplete_iff htop).mp inferInstance).1
  refine ⟨isCompact_iff_totallyBounded_isComplete.mpr ⟨?_, isComplete_univ⟩⟩
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  obtain ⟨n, -, hn⟩ := (IsAdic.hasBasis_nhds_zero htop).mem_iff.mp hU
  have := finite_quotient_maximalIdeal_pow (O := O) n
  refine ⟨Set.range (fun c : O ⧸ maximalIdeal O ^ n => c.out), Set.finite_range _, ?_⟩
  intro x _
  simp only [Set.mem_iUnion, Set.mem_range, exists_prop, exists_exists_eq_and]
  set c := (Ideal.Quotient.mk (maximalIdeal O ^ n) x).out
  refine ⟨Ideal.Quotient.mk _ x, Set.mem_vadd_set.mpr ⟨x - c, hn ?_, by simp [vadd_eq_add, c]⟩⟩
  rw [SetLike.mem_coe, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp [c]

/-- The `𝔪`-adic topology is second countable. -/
theorem secondCountableTopology_of_isAdic : SecondCountableTopology O := by
  have := isTopologicalRing_of_isAdic htop
  have := compactSpace_of_isAdic htop
  have := t2Space_of_isAdic htop
  let := IsTopologicalAddGroup.rightUniformSpace O
  have := isUniformAddGroup_of_addCommGroup (G := O)
  have : (𝓝 (0 : O)).IsCountablyGenerated := (IsAdic.hasBasis_nhds_zero htop).isCountablyGenerated
  have : (uniformity O).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have := UniformSpace.metrizableSpace (X := O)
  infer_instance

omit htop in
/-- **Main theorem, adic form.** `main_dvr` with only the `𝔪`-adic hypothesis and a Borel
σ-algebra: the ring topology, compactness, Hausdorffness and second countability are proved. -/
theorem main_dvr_of_isAdic (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
    [MeasurableSpace O] [BorelSpace O] (htop : IsAdic (maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    haveI := isTopologicalRing_of_isAdic htop
    haveI := compactSpace_of_isAdic htop
    haveI := t2Space_of_isAdic htop
    haveI := secondCountableTopology_of_isAdic htop
    monicDensity O n σ = densityValue (monicExpr n σ) (Nat.card (ResidueField O)) ∧
      projectiveDensity O n σ = densityValue (projectiveExpr n σ) (Nat.card (ResidueField O)) :=
  haveI := isTopologicalRing_of_isAdic htop
  haveI := compactSpace_of_isAdic htop
  haveI := t2Space_of_isAdic htop
  haveI := secondCountableTopology_of_isAdic htop
  main_dvr O htop n σ

end General

/-- **Main theorem for the `𝔪`-adic topology.** For every complete DVR `O` with finite residue
field, give `O` its `𝔪`-adic topology and the Borel σ-algebra. Then the monic and projective type
densities are the values at `q = |k|` of `monicExpr n σ` and `projectiveExpr n σ`. No topological
hypothesis remains. -/
theorem main_dvr_adic (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (n : ℕ) (σ : FactorType) :
    letI := (maximalIdeal O).adicTopology
    letI : MeasurableSpace O := borel O
    haveI : BorelSpace O := ⟨rfl⟩
    haveI := isTopologicalRing_of_isAdic (I := maximalIdeal O) rfl
    haveI := compactSpace_of_isAdic (O := O) rfl
    haveI := t2Space_of_isAdic (O := O) rfl
    haveI := secondCountableTopology_of_isAdic (O := O) rfl
    monicDensity O n σ = densityValue (monicExpr n σ) (Nat.card (ResidueField O)) ∧
      projectiveDensity O n σ = densityValue (projectiveExpr n σ) (Nat.card (ResidueField O)) :=
  letI := (maximalIdeal O).adicTopology
  letI : MeasurableSpace O := borel O
  haveI : BorelSpace O := ⟨rfl⟩
  main_dvr_of_isAdic O rfl n σ

/-- **Field form for every finite `K/ℚ_p`, ramified or not, with no topological hypothesis.** Give
the ring of integers `𝒪_K = padicIntegers p K` its `𝔪`-adic topology and Borel σ-algebra. Then the
monic and projective type densities over `𝒪_K` are the values at `q = |𝒪_K/𝔪|` of the rational
functions `(monicExpr n σ).rational` and `(projectiveExpr n σ).rational`. This discharges the
topological hypotheses of `main_field_form_ramified`. -/
theorem main_field_form_ramified_adic (n : ℕ) (σ : FactorType) (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] :
    letI := padicIntegers_isDVR p K
    haveI := padicIntegers_maximal_adic_complete p K this
    haveI := padicIntegers_residueField_finite p K (padicIntegers_isDVR p K)
    letI := (maximalIdeal (padicIntegers p K)).adicTopology
    letI : MeasurableSpace (padicIntegers p K) := borel _
    haveI : BorelSpace (padicIntegers p K) := ⟨rfl⟩
    haveI := isTopologicalRing_of_isAdic (I := maximalIdeal (padicIntegers p K)) rfl
    haveI := compactSpace_of_isAdic (O := padicIntegers p K) rfl
    haveI := t2Space_of_isAdic (O := padicIntegers p K) rfl
    haveI := secondCountableTopology_of_isAdic (O := padicIntegers p K) rfl
    monicDensity (padicIntegers p K) n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
        (Nat.card (ResidueField (padicIntegers p K)) : ℚ) (monicExpr n σ).rational : ℚ) : ℝ) ∧
      projectiveDensity (padicIntegers p K) n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
        (Nat.card (ResidueField (padicIntegers p K)) : ℚ) (projectiveExpr n σ).rational : ℚ) : ℝ) :=
  letI := padicIntegers_isDVR p K
  haveI := padicIntegers_maximal_adic_complete p K this
  haveI := padicIntegers_residueField_finite p K (padicIntegers_isDVR p K)
  letI := (maximalIdeal (padicIntegers p K)).adicTopology
  letI : MeasurableSpace (padicIntegers p K) := borel _
  haveI : BorelSpace (padicIntegers p K) := ⟨rfl⟩
  haveI := isTopologicalRing_of_isAdic (I := maximalIdeal (padicIntegers p K)) rfl
  haveI := compactSpace_of_isAdic (O := padicIntegers p K) rfl
  haveI := t2Space_of_isAdic (O := padicIntegers p K) rfl
  haveI := secondCountableTopology_of_isAdic (O := padicIntegers p K) rfl
  main_field_form_ramified n σ p K rfl

end SurfaceBlowup
