/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Cluster.Main

/-!
# Nonnegativity of the universal expressions, and real-valued forms of the main theorems

The main theorems `main_dvr` and `main_dvr_cluster` state a density as
`densityValue x q = ENNReal.ofReal (x.eval q)`. Since `ENNReal.ofReal` sends negative reals to `0`,
that statement alone does not say that the density equals the rational number `x.eval q`: it says
that the density equals `max (x.eval q) 0`. This file closes that gap. It proves that the universal
expressions take nonnegative values at every prime power, and restates the main theorems as
equalities of real numbers.

## Main results

* `SurfaceBlowup.monicExpr_eval_nonneg`, `SurfaceBlowup.projectiveExpr_eval_nonneg`,
  `SurfaceBlowup.clusterExpr_eval_nonneg`: the values at a prime power are nonnegative.
* `SurfaceBlowup.main_dvr_toReal`: the monic and projective densities, as real numbers, are the
  values of `monicExpr n σ` and `projectiveExpr n σ` at `q = |k|`.
* `SurfaceBlowup.main_dvr_cluster_toReal`: the same for the cluster density.

No existing declaration is modified; the statements use only the definitions of
`SurfaceBlowup.Basic` and `SurfaceBlowup.Cluster.Defs`.
-/

open scoped ENNReal

namespace SurfaceBlowup

/-! ### Divisor counts are nonnegative at prime powers -/

/-- `∏_{j < M} (N - j) ≥ 0` for natural numbers `N`, `M`: every factor is positive when `M ≤ N`,
and the factor `j = N` vanishes otherwise. -/
private theorem list_prod_falling_nonneg (N M : ℕ) (f : ℕ → ℚ)
    (hf : ∀ j, f j = (N : ℚ) - (j : ℚ)) : 0 ≤ ((List.range M).map f).prod := by
  obtain rfl : f = fun j : ℕ => (N : ℚ) - (j : ℚ) := funext hf
  have key : ∀ M : ℕ,
      (M ≤ N → 0 < ((List.range M).map fun j : ℕ => (N : ℚ) - (j : ℚ)).prod) ∧
      (N < M → ((List.range M).map fun j : ℕ => (N : ℚ) - (j : ℚ)).prod = 0) := by
    intro M
    induction M with
    | zero => exact ⟨fun _ => by simp, fun h => absurd h (Nat.not_lt_zero _)⟩
    | succ M ih =>
      rw [List.range_succ, List.map_append, List.prod_append]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      refine ⟨fun h => mul_pos (ih.1 (by omega)) ?_, fun h => ?_⟩
      · have : (M : ℚ) < (N : ℚ) := by exact_mod_cast (by omega : M < N)
        linarith
      · rcases Nat.lt_or_ge N M with h' | h'
        · rw [ih.2 h', zero_mul]
        · obtain rfl : N = M := by omega
          rw [sub_self, mul_zero]
  rcases Nat.lt_or_ge N M with h | h
  · exact ((key M).2 h).ge
  · exact ((key M).1 h).le

/-- At a prime power `Q`, the number of available points of degree `δ > 0` is a natural number:
`Q + offset` in degree one, and the number of monic irreducible polynomials of degree `δ` over the
field with `Q` elements otherwise. -/
private theorem availablePoints_eval_natCast (Q : ℕ) (hQ : PrimePower Q) (offset : ℤ)
    (hoff : 0 ≤ offset) (δ : ℕ) (hδ : 0 < δ) :
    ∃ N : ℕ, (availablePoints offset δ).eval (Q : ℚ) = (N : ℚ) := by
  unfold availablePoints
  split_ifs with h
  · refine ⟨Q + offset.toNat, ?_⟩
    have h2 : ((offset.toNat : ℕ) : ℚ) = (offset : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hoff]
    simp only [Expr.eval, Nat.cast_add, h2]
  · obtain ⟨p, e, hp, he, rfl⟩ := hQ
    have : Fact p.Prime := ⟨hp⟩
    have : Finite (GaloisField p e) := Module.finite_of_finite (ZMod p)
    have hc := finite_field_irreducible_count (GaloisField p e) δ hδ
    rw [GaloisField.card p e he.ne'] at hc
    exact ⟨_, hc.symm⟩

/-- The evaluation of a falling factorial expression. (In the definition of `falling` the list
`List.range M` is coerced to a list of rationals; the first two steps turn that coercion into
`List.map Nat.cast`.) -/
private theorem falling_eval (x : Expr) (M : ℕ) (q : ℚ) :
    (falling x M).eval q = ((List.range M).map fun j : ℕ => x.eval q - (j : ℚ)).prod := by
  unfold falling
  simp only [List.pure_def, List.bind_eq_flatMap]
  rw [← List.map_eq_flatMap, expression_prod_eval, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, Expr.sub, Expr.neg, Expr.eval]
  ring

/-- **Divisor counts are nonnegative.** At a prime power `Q` and for a nonnegative offset (`0` on
the affine line, `1` on the projective line), the expression `divisorCount offset m` takes a
nonnegative value: it is a product of falling factorials of natural numbers divided by
factorials. -/
theorem divisorCount_eval_nonneg (Q : ℕ) (hQ : PrimePower Q) (offset : ℤ) (hoff : 0 ≤ offset)
    {n : ℕ} (m : Pattern n) : 0 ≤ (divisorCount offset m).eval (Q : ℚ) := by
  unfold divisorCount
  rw [expression_prod_eval]
  refine List.prod_nonneg fun y hy => ?_
  rw [List.map_map] at hy
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
  obtain ⟨N, hN⟩ :=
    availablePoints_eval_natCast Q hQ offset hoff (i.val + 1) (Nat.succ_pos _)
  simp only [Function.comp, Expr.eval]
  rw [falling_eval, hN]
  exact mul_nonneg (list_prod_falling_nonneg N _ _ fun _ => rfl)
    (one_div_nonneg.2 (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _))

/-! ### The universal expressions are nonnegative at prime powers -/

/-- Every coefficient of the global law (monic or projective) is nonnegative at a prime power. -/
theorem globalLaw_coeff_eval_nonneg (projective : Bool) (n : ℕ) (Q : ℕ) (hQ : PrimePower Q)
    (σ : FactorType) : 0 ≤ (lawCoeff (globalLaw projective n) σ).eval (Q : ℚ) := by
  have hC := law_coeff_nonneg_closure (Q : ℚ)
  have hQ0 : (0 : ℚ) ≤ (Q : ℚ) := Nat.cast_nonneg Q
  unfold globalLaw
  refine hC.1 _ _ ?_ (hC.2.2.2.1 _ _ _ fun m _ =>
    hC.1 _ _ ?_ (hC.2.2.1 _ fun L hL τ => ?_)) σ
  · -- the normaliser `q⁻ⁿ`, resp. `[n+1]_q⁻¹`
    simp only [Expr.eval]
    refine inv_nonneg.2 ?_
    cases projective
    · rw [ite_eq_right Bool.false_ne_true, expression_pow_eval]
      simp only [Expr.eval]
      positivity
    · rw [ite_eq_left rfl]
      exact (projective_normalizer_positive n _ hQ0).le
  · -- the number of residue divisors with the pattern `m`
    exact divisorCount_eval_nonneg Q hQ _ (by cases projective <;> simp) m
  · -- the descended root laws of the points of the pattern
    simp only [List.mem_map, otherChildren, List.mem_flatMap, List.mem_replicate] at hL
    obtain ⟨z, ⟨ij, -, -, rfl⟩, rfl⟩ := hL
    exact (state_law_coeff_nonneg Q hQ _
      (show State.Valid (.single 1 _) from ⟨Nat.one_pos, Nat.succ_pos _⟩) τ).2 _ (Nat.succ_pos _)

/-- **Nonnegativity of `A_{n,σ}`.** The universal monic expression takes a nonnegative value at
every prime power. -/
theorem monicExpr_eval_nonneg (n : ℕ) (σ : FactorType) (Q : ℕ) (hQ : PrimePower Q) :
    0 ≤ (monicExpr n σ).eval (Q : ℚ) :=
  globalLaw_coeff_eval_nonneg false n Q hQ σ

/-- **Nonnegativity of `R_{n,σ}`.** The universal projective expression takes a nonnegative value
at every prime power. -/
theorem projectiveExpr_eval_nonneg (n : ℕ) (σ : FactorType) (Q : ℕ) (hQ : PrimePower Q) :
    0 ≤ (projectiveExpr n σ).eval (Q : ℚ) :=
  globalLaw_coeff_eval_nonneg true n Q hQ σ

/-- **Nonnegativity of `B_{n,σ}`.** The universal cluster expression takes a nonnegative value at
every prime power. -/
theorem clusterExpr_eval_nonneg (n : ℕ) (σ : FactorType) (Q : ℕ) (hQ : PrimePower Q) :
    0 ≤ (clusterExpr n σ).eval (Q : ℚ) := by
  unfold clusterExpr rootLaw
  split_ifs with h
  · exact (law_coeff_nonneg_closure (Q : ℚ)).2.2.2.2.2.2.1 σ
  · exact (state_law_coeff_nonneg Q hQ (State.single 1 n)
      (show State.Valid (.single 1 n) from ⟨Nat.one_pos, Nat.pos_of_ne_zero h⟩) σ).1

/-! ### Real-valued forms of the main theorems -/

/-- **Theorem 1.1, monic and projective laws, as real numbers.** Over every complete discrete
valuation ring `O` with finite residue field `k`, the probability that a random monic polynomial of
degree `n` (resp. a random primitive binary form of degree `n`) has type `σ` is, as a real number,
the value at `q = |k|` of `monicExpr n σ` (resp. `projectiveExpr n σ`). Unlike `main_dvr`, the right
side is not passed through `ENNReal.ofReal`, so no clamping at `0` can occur. (`ENNReal.toReal`
sends `⊤` to `0`; the densities are finite by `main_dvr`. The statement
`universal_type_laws` of `Corollaries.RationalForm` avoids both conventions.) -/
theorem main_dvr_toReal (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    (monicDensity O n σ).toReal =
        (((monicExpr n σ).eval (Nat.card (IsLocalRing.ResidueField O)) : ℚ) : ℝ) ∧
    (projectiveDensity O n σ).toReal =
        (((projectiveExpr n σ).eval (Nat.card (IsLocalRing.ResidueField O)) : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := main_dvr O htop n σ
  have hq := finite_field_card_primePower (IsLocalRing.ResidueField O)
  rw [h1, h2]
  exact ⟨ENNReal.toReal_ofReal (by exact_mod_cast monicExpr_eval_nonneg n σ _ hq),
    ENNReal.toReal_ofReal (by exact_mod_cast projectiveExpr_eval_nonneg n σ _ hq)⟩

/-- **Theorem 1.1, cluster law, as a real number.** Over every complete discrete valuation ring
`O` with finite residue field `k`, the cluster probability of type `σ` is, as a real number, the
value at `q = |k|` of `clusterExpr n σ`. -/
theorem main_dvr_cluster_toReal (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    (clusterDensity O n σ).toReal =
        (((clusterExpr n σ).eval (Nat.card (IsLocalRing.ResidueField O)) : ℚ) : ℝ) := by
  rw [main_dvr_cluster O htop n σ]
  exact ENNReal.toReal_ofReal (by
    exact_mod_cast clusterExpr_eval_nonneg n σ _
      (finite_field_card_primePower (IsLocalRing.ResidueField O)))

end SurfaceBlowup
