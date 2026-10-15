/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Assembly.MonicCells
import SurfaceBlowup.Assembly.NullBridges
import SurfaceBlowup.Assembly.TypeEvents
import SurfaceBlowup.Formula.PatternCounts
import SurfaceBlowup.Formula.StateCombinatorics
import SurfaceBlowup.Formula.TypeTransport
import SurfaceBlowup.Measure.MemberCharts
import SurfaceBlowup.Measure.PrimitiveLocus
import SurfaceBlowup.Recursion.RootCellLaw
import SurfaceBlowup.Unramified.FrobeniusDescent

/-!
# The density formulas for the route-F densities

For every complete DVR `O` with finite residue field `k` (any characteristic), the route-F
densities `monicDensityF`, `projectiveDensityF` (type predicates carrying the integral-closure
finiteness conjunct) are the values at `q = |k|` of `monicExpr n σ` and `projectiveExpr n σ`.

## Main results

* `SurfaceBlowup.monicDensityF_eq_densityValue`: the monic density formula.
* `SurfaceBlowup.projectiveDensityF_eq_densityValue`: the projective density formula.

## Implementation notes

The monic formula sums the root-cell law `root_cell_law` over the residue-divisor partition of the
coefficient space; the projective formula reduces to the affine one off the Haar-null hyperplane
`{a_n = 0}`. `Main.lean` transfers both to the original densities.

Provenance: `Thm_Gen_MainDvr` (`SurfaceBlowupV2Gen.{monic,projective}_formula_dvr`, route-F copies
of the accepted `Thm_SurfaceBlowupV2_{monic,projective}_formula_of_root_cell_law`).
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]

/-- **Monic formula** for the route-F density: `monicDensityF O n σ = monicExpr n σ` evaluated at
`q = |k|`. -/
theorem monicDensityF_eq_densityValue (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (σ : FactorType) :
    monicDensityF O n σ = densityValue (monicExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) := by
  classical
  set k := IsLocalRing.ResidueField O
  set q := Nat.card k
  have hq2 : 2 ≤ q := Finite.one_lt_card
  set μ := coefficientMeasure O n
  set E := typeEvent O n σ
  have hE : MeasurableSet E :=
    monic_type_event_measurable_of_root_cell_law root_cell_law O htop n σ
  obtain ⟨⟨S, hS⟩, _, hcell, hsum⟩ := monic_cells_partition O htop n
  -- nonnegativity of array laws
  have hA : ∀ m : Pattern n, 0 ≤ (lawCoeff (arrayLaw m) σ).eval (q : ℚ) := by
    refine fun m ↦ (law_coeff_nonneg_closure (q : ℚ)).2.2.1 _ (fun L hL τ ↦ ?_) σ
    simp only [List.mem_map, otherChildren, List.mem_flatMap, List.mem_replicate] at hL
    obtain ⟨z, ⟨ij, -, -, rfl⟩, rfl⟩ := hL
    exact (state_law_coeff_nonneg q (finite_field_card_primePower k) _
      (show State.Valid (.single 1 _) from ⟨Nat.one_pos, Nat.succ_pos _⟩) τ).2 _ (Nat.succ_pos _)
  -- count
  have hC : ∀ m ∈ residuePatterns n, ((divisorCount 0 m).eval (q : ℚ) : ℝ)
      = ((S.filter fun D => HasArray k n D m).card : ℝ) := by
    intro m hm
    rw [← (affine_divisor_count k n m hm).2, Nat.subtype_card (S.filter fun D ↦ HasArray k n D m)
      fun D ↦ by simp only [Finset.mem_filter, hS]; exact Iff.rfl]
    simp
  -- measure side
  have hmeas : μ E = ∑ m ∈ residuePatterns n, ((S.filter fun D => HasArray k n D m).card : ℝ≥0∞) *
      ((q : ℝ≥0∞)⁻¹ ^ n * densityValue (lawCoeff (arrayLaw m) σ) q) := by
    rw [hsum S hS E hE]
    have h1 : ∀ D ∈ S, μ (E ∩ residueCell O n (divisorAffinePolynomial k D)) =
        ∑ m ∈ residuePatterns n, if HasArray k n D m then
          (q : ℝ≥0∞)⁻¹ ^ n * densityValue (lawCoeff (arrayLaw m) σ) q else 0 := by
      intro D hD
      have hD' := (hS D).1 hD
      obtain ⟨⟨m0, hm0, hm0R⟩, huniq⟩ := divisor_array_exists_unique k n D hD'.2
      rw [Finset.sum_eq_single_of_mem m0 hm0R fun m _ hne ↦ if_neg fun h ↦ hne (huniq _ _ h hm0),
        if_pos hm0, (hcell D hD').2.2 E,
        (monic_cell_law root_cell_law O htop n D hD' m0 hm0 σ).2]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- law side
  have hlaw : densityValue (monicExpr n σ) q = ∑ m ∈ residuePatterns n,
      ENNReal.ofReal ((divisorCount 0 m).eval (q : ℚ) : ℝ) *
      ((q : ℝ≥0∞)⁻¹ ^ n * densityValue (lawCoeff (arrayLaw m) σ) q) := by
    have hev : (monicExpr n σ).eval (q : ℚ) = (Expr.inv (.pow .var n)).eval (q : ℚ) *
        ∑ m ∈ residuePatterns n, (divisorCount 0 m).eval (q : ℚ) *
          (lawCoeff (arrayLaw m) σ).eval (q : ℚ) := by
      rw [monicExpr, globalLaw, law_coeff_scale, (law_coeff_flatMap _ _ _ [] [] σ _).2.2,
        ← Finset.sum_map_toList]
      simp only [Bool.false_eq_true, if_false]
      congr 2
      exact List.map_congr_left fun m _ ↦ by rw [law_coeff_scale]; rfl
    have hinv0 : 0 ≤ (Expr.inv (.pow .var n)).eval ((q : ℕ) : ℚ) := by
      have : ∀ j : ℕ, (Expr.pow .var j).eval ((q : ℕ) : ℚ) = (q : ℚ) ^ j := by
        intro j; induction j with
        | zero => rfl
        | succ j ih => simp [Expr.pow, Expr.eval, ih, pow_succ]
      simp only [Expr.eval, this]; positivity
    have hc0 : ∀ m ∈ residuePatterns n, 0 ≤ (divisorCount 0 m).eval (q : ℚ) := fun m hm ↦ by
      rw [← (affine_divisor_count k n m hm).2]; positivity
    have hinv := (density_value_arith q hq2 _ _ hinv0 hinv0 n (.single 1 1)
      ⟨Nat.one_pos, Nat.one_pos⟩).2.2.1
    rw [← hinv, densityValue, densityValue, hev, Rat.cast_mul, Rat.cast_sum,
      ENNReal.ofReal_mul (by exact_mod_cast hinv0),
      ENNReal.ofReal_sum_of_nonneg (fun m hm => by
        have := hc0 m hm; have := hA m; push_cast; positivity), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Rat.cast_mul, ENNReal.ofReal_mul (by exact_mod_cast hc0 m hm)]
    ring
  change μ E = _
  rw [hmeas, hlaw]
  exact Finset.sum_congr rfl fun m hm ↦ by rw [hC m hm, ENNReal.ofReal_natCast]

/-- **Projective formula** for the route-F density: `projectiveDensityF O n σ = projectiveExpr n σ`
at `q = |k|`. -/
theorem projectiveDensityF_eq_densityValue (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (σ : FactorType) :
    projectiveDensityF O n σ =
      densityValue (projectiveExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) := by
  obtain ⟨hHm, hH0⟩ := coordinate_hyperplane_null O htop (n+1) (Fin.last n)
  rw [projectiveDensityF, ← (affine_type_event_primitive_density root_cell_law O htop n σ).2,
    ← (binary_type_event_decomposition O σ).1 n]
  congr 1
  change coefficientMeasure O (n+1) (binaryTypeEvent O n σ) = _
  rw [← MeasureTheory.measure_inter_add_sdiff _ hHm,
    MeasureTheory.measure_mono_null Set.inter_subset_right hH0, zero_add, Set.sdiff_eq]
  rfl

end SurfaceBlowup
