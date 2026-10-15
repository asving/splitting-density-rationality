/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Reciprocity.Patterns

/-!
# The reciprocity law (Theorem R)

This file assembles the proof of Theorem R: the universal monic density `monicExpr n σ` is the
`σ`-coefficient of the root law `rootLaw n` with `q ↦ 1/q` substituted (`A_n(q) = B_n(1/q)`),
and the universal projective density `projectiveExpr n σ` is self-reciprocal
(`R_n(1/q) = R_n(q)`).

The single-boundary cluster series `B_a = clusterSer a` satisfies an operator equation
`B_a = ρ(U_{a,a}) Φ(G_a)` for the contact series `U_{a,a} = crossingQ a a`, where
`G_a = eulerSer 0 a` is its Euler transform. Conjugating by reciprocal substitution `q ↦ q⁻¹`
and using the unitarity of `U_{a,a}` through a given degree, an induction on the cluster degree
shows `G_a = S(B_aᵛ)` (`S` the dilation `x ↦ qx`, `ᵛ` the reciprocal substitution). Reading off
coefficients for `a = 1` gives both statements.

## Main results

* `coeff_clusterSer_eq_coeff_qact`: `B_a = ρ(U_{a,a}) Φ(G_a)` coefficientwise.
* `cluster_reciprocity`: `G_a ≡ S(B_aᵛ)` in every degree.
* `lawCoef_globalLaw_false_eq_recipCoef`, `recipCoef_lawCoef_globalLaw_true`: the coefficient
  forms.
* `recip_main`: Theorem R.

Provenance: `Thm_SurfaceBlowupV2_recip_{single_exit_regroup, single_operator_equation,
reciprocal_operator_equation, second_operator_equation, cluster_step, cluster_all, affine_coef,
projective_coef, main}`.
-/

namespace SurfaceBlowup

/-! ### The operator equation for single-boundary clusters -/

/-- The exit part of the recursion of `S(a;n)` (`n ≥ 2`), plus the self-return term
`q^{-tri n} q F_{S(a;n)}`, regroups by divisor degree `d` and crossing depth `r` into the
pattern sums `patternSum 0 a (a n) (d - r)`, weighted by the divisor probabilities and the laws
of the crossing children `T(a,a;r,n-d)`. -/
private theorem lawCoef_exitLaw_single_add_self (a n : ℕ) (ha : 0 < a) (hn : 2 ≤ n) :
    lawCoef (exitLaw (State.single a n)) +
        qpow (-(tri n : ℤ)) * (qpow 1 * lawCoef (stateLaw (State.single a n))) =
      ∑ d ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (d + 1),
        (if ((0 < r ↔ d < n) ∧ r ≤ d) then
          scalar (divisorProbability (State.single a n) d).rational *
            ((if r = 0 then 1 else lawCoef (stateLaw (State.crossing a a r (n - d)))) *
              patternSum 0 a (a * n) (d - r))
        else 0) := by
  classical
  have hn0 : 0 < n := by omega
  have hA : ∀ P ∈ allowedPatterns (State.single a n), Allowed (State.single a n) P :=
    fun P hP ↦ (Finset.mem_filter.mp hP).2
  set T : TangentPattern (State.single a n).degree → Coef := fun P ↦
    lawCoef (lawScale (.mul (tangentCount (State.single a n) P)
      (divisorProbability (State.single a n) P.d.val))
        (lawProd ((children (State.single a n) P).map fun z ↦ lawDescend z.1 (stateLaw z.2))))
    with hT
  have hexit : lawCoef (exitLaw (State.single a n)) = ∑ P ∈ allowedPatterns (State.single a n),
      (if SelfPattern (State.single a n) P then 0 else T P) := by
    unfold exitLaw
    rw [lawCoef_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    split_ifs <;> simp [lawCoef_nil, hT]
  obtain ⟨P₀, hA₀, hS₀, huniq⟩ := exists_unique_selfPattern_single a n ha hn
  have hself : ∑ P ∈ allowedPatterns (State.single a n),
      (if SelfPattern (State.single a n) P then T P else 0) = T P₀ := by
    rw [Finset.sum_eq_single P₀ (fun Q hQ hne ↦ if_neg fun hSQ ↦ hne (huniq Q (hA Q hQ) hSQ))
      (fun h ↦ absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA₀⟩) h), if_pos hS₀]
  have hsplit : lawCoef (exitLaw (State.single a n)) + T P₀ =
      ∑ P ∈ allowedPatterns (State.single a n), T P := by
    rw [hexit, ← hself, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    split_ifs <;> simp
  rw [← lawCoef_single_self_term a n ha hn P₀ hA₀ hS₀]
  refine hsplit.trans <| (Finset.sum_congr rfl fun P hP ↦
    lawCoef_single_term a n ha hn0 P (hA P hP)).trans ?_
  rw [sum_allowedPatterns_single a n ha (fun d r m ↦
    scalar ((divisorCount 0 m).rational * (divisorProbability (State.single a n) d).rational) *
      ((if r = 0 then 1 else lawCoef (stateLaw (State.crossing a a r (n - d)))) *
        ∏ ij : Fin (State.single a n).degree × Fin (State.single a n).degree,
          (adamsCoef (ij.1.val + 1) (lawCoef (stateLaw (State.single a (ij.2.val + 1))))) ^
            (m ij).val))]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun r _ ↦ ?_
  by_cases hcond : ((0 < r ↔ d < n) ∧ r ≤ d)
  · rw [if_pos hcond, if_pos hcond]; exact sum_patterns_scalar_mul_eq_patternSum _ _ _ _ _ _
  · rw [if_neg hcond, if_neg hcond]

/-- **Operator equation.** The cluster series is obtained from its Euler transform by the
Gaussian twist and the contact representation: `B_a = ρ(U_{a,a}) Φ(G_a)`, coefficientwise. -/
theorem coeff_clusterSer_eq_coeff_qact (a n : ℕ) (ha : 0 < a) :
    PowerSeries.coeff n (clusterSer a) =
      PowerSeries.coeff n (qact (crossingQ a a) (gaussPhi (eulerSer 0 a))) := by
  have hqp : ∀ k : ℤ, qpow k = algebraMap (RatFunc ℚ) Coef ((RatFunc.X : RatFunc ℚ) ^ k) :=
    fun k ↦ scalar_eq_algebraMap _
  rw [coeff_qact_crossingQ_gaussPhi_eulerSer a n ha]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [(coeff_zero_clusterSer a)]
    · rw [(coeff_one_clusterSer a)]
      simp only [Finset.Icc_self, Finset.sum_singleton, Finset.sum_range_succ, Finset.range_one]
      have hp : patternSum 0 a (a * 1) 1 =
          qpow 1 * AddMonoidAlgebra.single ({(a, 1)} : FactorType) 1 := by
        rw [patternSum_eq_of_le 0 a (a * 1) 1 1 (by omega) le_rfl, ← coeff_eulerSer,
          coeff_one_eulerSer_zero a]
      have hd : (divisorProbability (State.single a 1) 1).rational =
          (RatFunc.X : RatFunc ℚ)⁻¹ := by
        rw [rational_divisorProbability_single a 1 1]; simp [tri]
      simp only [hp, hd, lt_irrefl, iff_self, zero_le, and_self, if_true, one_ne_zero, if_false,
        one_mul, Nat.sub_zero, zero_lt_one, iff_false, not_true, false_and, add_zero]
      rw [scalar_eq_algebraMap, hqp, ← mul_assoc, ← map_mul, zpow_one,
        inv_mul_cancel₀ RatFunc.X_ne_zero, map_one,
        one_mul]
  · have hB := (coeff_succ_clusterSer a (n - 1))
    rw [show n - 1 + 1 = n by omega] at hB
    have hreg := lawCoef_exitLaw_single_add_self a n ha hn
    have hnt : (State.single a n).terminal = false := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      rfl
    have hs : (State.single a n).Valid := ⟨ha, by omega⟩
    have hlaw := (state_law_unfold _ hs hnt).1 a n rfl
    rw [hB, hlaw]; rw [hlaw] at hreg
    have hsub : (Expr.sub (Expr.const 1) (returnWeight n)).rational =
        1 - (returnWeight n).rational := by
      rw [Expr.rational_sub (x := Expr.const 1) trivial (wf_returnWeight n), Expr.rational_const]
      simp
    rw [lawCoef_lawScale, Expr.rational_inv, hsub] at hreg ⊢
    have hne := one_sub_rational_returnWeight_ne_zero n hn
    have hlam : (returnWeight n).rational =
        (RatFunc.X : RatFunc ℚ) ^ (-(tri n : ℤ)) * RatFunc.X ^ (1 : ℤ) := by
      rw [rational_returnWeight n, zpow_neg, zpow_natCast, zpow_one,
        mul_comm]
    rw [← hreg, if_neg (by omega), add_zero, ← mul_assoc, hqp, hqp, ← map_mul, ← hlam,
      scalar_eq_algebraMap,
      ← mul_assoc, ← map_mul, ← one_add_mul, ← map_one (algebraMap (RatFunc ℚ) Coef), ← map_add]
    congr 2
    field_simp
    ring

/-- **Reciprocal operator equation.** Applying reciprocal substitution and the dilation to the
operator equation: `Φ(S(B_aᵛ)) = ρ(U_{a,a}†) S(G_aᵛ)`. -/
private theorem gaussPhi_dilate_recipSer_clusterSer (a : ℕ) (ha : 0 < a) :
    gaussPhi (dilate (recipSer (clusterSer a))) =
      qact (qdagger (crossingQ a a)) (dilate (recipSer (eulerSer 0 a))) := by
  have hB : clusterSer a = qact (crossingQ a a) (gaussPhi (eulerSer 0 a)) :=
    PowerSeries.ext fun n ↦ coeff_clusterSer_eq_coeff_qact a n ha
  have hv : recipSer (clusterSer a) =
      qactRecip (qrecip (crossingQ a a)) (gaussPhiInv (recipSer (eulerSer 0 a))) := by
    rw [hB, (recipSer_qact _ _), (recipSer_gaussPhi (eulerSer 0 a))]
  have hconj := gaussPhi_qactRecip_gaussPhiInv (crossingQ a a)
    (fun c h ↦ crossingQ_symm a a c h ha ha) (recipSer (eulerSer 0 a))
  rw [← hv] at hconj
  rw [(gaussPhi_dilate (recipSer (clusterSer a))), hconj,
    (dilate_codilate (qact (qdagger (crossingQ a a))
      (dilate (recipSer (eulerSer 0 a)))))]

/-- If `U_{a,a} U_{a,a}† ≡ 1` through degree `n`, then `ρ(U_{a,a}) Φ(S(B_aᵛ)) ≡ S(G_aᵛ)`
through degree `n`. -/
private theorem qact_gaussPhi_dilate_recipSer_scongr (a n : ℕ) (ha : 0 < a)
    (hU : QCongr n (qmul (crossingQ a a) (qdagger (crossingQ a a))) qone) :
    SCongr n (qact (crossingQ a a) (gaussPhi (dilate (recipSer (clusterSer a)))))
      (dilate (recipSer (eulerSer 0 a))) := by
  rw [gaussPhi_dilate_recipSer_clusterSer a ha, ← qact_qmul]
  simpa only [qact_qone] using hU.qact_scongr (dilate (recipSer (eulerSer 0 a)))

/-! ### The induction on cluster degree -/

/-- Inductive step: if `G_b ≡ S(B_bᵛ)` through degree `n - 1` for all `b > 0`, then
`G_a ≡ S(B_aᵛ)` through degree `n` (`n ≥ 2`). -/
private theorem cluster_reciprocity_step (n : ℕ) (hn : 2 ≤ n)
    (ih : ∀ a : ℕ, 0 < a → SCongr (n - 1) (eulerSer 0 a) (dilate (recipSer (clusterSer a))))
    (a : ℕ) (ha : 0 < a) :
    SCongr n (eulerSer 0 a) (dilate (recipSer (clusterSer a))) := by
  have hQ := qcongr_crossingQ_mul_qdagger (n / 2) (fun b hb ↦
    (SCongr.mono (ih b hb) (by omega)))
    n (by omega) a a ha ha
  have h2 := qact_gaussPhi_dilate_recipSer_scongr a n ha hQ n le_rfl
  have hD : ∀ m : ℕ, m < n → PowerSeries.coeff m
      (eulerSer 0 a - dilate (recipSer (clusterSer a))) = 0 := fun m hm ↦ by
    rw [map_sub, sub_eq_zero]
    exact ih a ha m (by omega)
  have lead := coeff_qact_gaussPhi_of_lt (crossingQ a a) (crossingQ_zero_zero a a) _ n hD
  rw [(gaussPhi_sub (eulerSer 0 a) (dilate (recipSer (clusterSer a)))),
    (qact_sub (crossingQ a a) _ _), map_sub, map_sub,
    ← coeff_clusterSer_eq_coeff_qact a n ha, h2] at lead
  have h4 := coeff_pPow_sub_of_scongr n (by omega) (RatFunc.X : RatFunc ℚ)⁻¹ _ _
    (constantCoeff_eulerSer 0 a)
    (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_zero_dilate_recipSer_clusterSer]) (ih a ha)
  rw [← clusterSer_eq_pPow, ← dilate_recipSer_eulerSer_eq_pPow] at h4
  set δ := PowerSeries.coeff n (eulerSer 0 a) -
    PowerSeries.coeff n (dilate (recipSer (clusterSer a)))
  have key : scalar ((RatFunc.X : RatFunc ℚ)⁻¹ - (RatFunc.X : RatFunc ℚ) ^ (-(tri n : ℤ))) * δ =
      0 := by
    have : scalar ((RatFunc.X : RatFunc ℚ)⁻¹ - (RatFunc.X : RatFunc ℚ) ^ (-(tri n : ℤ)))
        = scalar (RatFunc.X : RatFunc ℚ)⁻¹ - qpow (-(tri n : ℤ)) :=
      AddMonoidAlgebra.single_sub (R := RatFunc ℚ) _ _ _
    rw [this, sub_mul, ← h4, ← lead, sub_self]
  have hδ := eq_zero_of_scalar_mul_eq_zero (X_inv_sub_X_zpow_neg_tri_ne_zero n hn) key
  intro m hm
  rcases Nat.lt_or_ge m n with h | h
  · exact ih a ha m (by omega)
  · obtain rfl : m = n := by omega
    exact sub_eq_zero.mp hδ

/-- **Cluster reciprocity.** For every `a > 0`, the Euler transform `G_a` agrees with the
dilated reciprocal cluster series `S(B_aᵛ)` in every degree `≤ n`. -/
theorem cluster_reciprocity (n a : ℕ) (ha : 0 < a) :
    SCongr n (eulerSer 0 a) (dilate (recipSer (clusterSer a))) := by
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases h : n ≤ 1
    · exact (SCongr.mono (cluster_reciprocity_one a) h)
    · exact cluster_reciprocity_step n (by omega) (fun a ha ↦ ih (n - 1) (by omega) a ha) a ha

/-! ### Coefficient forms and Theorem R -/

/-- **Affine reciprocity.** The global monic law is the reciprocal of the root law:
`F_global(q) = F_{S(1;n)}(1/q)` as elements of `Coef`. -/
theorem lawCoef_globalLaw_false_eq_recipCoef (n : ℕ) (hn : 0 < n) :
    lawCoef (globalLaw false n) = recipCoef (lawCoef (rootLaw n)) := by
  have h1 := (cluster_reciprocity n 1 one_pos) n le_rfl
  rw [coeff_eulerSer,
    (coeff_dilate (recipSer (clusterSer 1)) n),
    (coeff_recipSer (clusterSer 1) n)] at h1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(coeff_succ_clusterSer 1 m)] at h1
  rw [show rootLaw (m + 1) = stateLaw (.single 1 (m + 1)) by simp [rootLaw]]
  refine scalar_mul_left_cancel (pow_ne_zero (m + 1) (RatFunc.X_ne_zero (K := ℚ))) ?_
  rw [← qpow_natCast, ← h1, lawCoef_globalLaw_false, ← mul_assoc, mul_comm (qpow _),
    qpow_neg_mul_qpow, one_mul]

/-- **Projective self-reciprocity.** The normalised global projective law `R_n` is invariant
under reciprocal substitution: `R_n(1/q) = R_n(q)` as elements of `Coef`. -/
theorem recipCoef_lawCoef_globalLaw_true (n : ℕ) :
    recipCoef (lawCoef (globalLaw true n)) = lawCoef (globalLaw true n) := by
  set B := clusterSer 1 with hBdef
  have hB1 : PowerSeries.constantCoeff B = 1 := (constantCoeff_clusterSer 1)
  have hG : eulerSer 0 1 = pPow RatFunc.X B := by simp [eulerSer, hBdef]
  have hQ : eulerSer 1 1 = pPow (RatFunc.X + 1) B := by simp [eulerSer, hBdef]
  -- Step 1: `B ᵛ = S⁻¹ G_1`.
  have hGd : eulerSer 0 1 = dilate (recipSer B) :=
    PowerSeries.ext fun m ↦ cluster_reciprocity m 1 one_pos m le_rfl
  have hrB : recipSer B = codilate (pPow RatFunc.X B) := by
    rw [← hG, hGd, (codilate_dilate (recipSer B))]
  -- Step 2: `Q_1 ᵛ = S⁻¹ Q_1`.
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hrQ : recipSer (pPow (RatFunc.X + 1) B) = codilate (pPow (RatFunc.X + 1) B) := by
    rw [(recipSer_pPow (RatFunc.X + 1) B hB1), map_add,
      recipRat_X, map_one, hrB,
      ← (codilate_pPow ((RatFunc.X)⁻¹ + 1) (pPow RatFunc.X B) (constantCoeff_pPow RatFunc.X B)),
      (pPow_pPow ((RatFunc.X)⁻¹ + 1) RatFunc.X B)]
    congr 2
    field_simp
    ring
  -- Step 3: read off the coefficient of `xⁿ`.
  have hcQ := congrArg (PowerSeries.coeff n) hrQ
  rw [(coeff_recipSer (pPow (RatFunc.X + 1) B) n),
    (coeff_codilate (pPow (RatFunc.X + 1) B) n),
    ← hQ, coeff_eulerSer] at hcQ
  have hNrec := recipRat_projectiveNormalizer n
  have hDne := projectiveNormalizer_rational_ne_zero n
  set D := (projectiveNormalizer n).rational
  set R := lawCoef (globalLaw true n)
  have hP : patternSum 1 1 n n = scalar D * R := by
    rw [show R = _ from lawCoef_globalLaw_true n, ← mul_assoc,
      ← (scalar_mul D D⁻¹), mul_inv_cancel₀ hDne,
      scalar_one, one_mul]
  have hqp : qpow (-(n : ℤ)) = scalar ((RatFunc.X ^ n)⁻¹) := by
    simp [qpow, zpow_neg, zpow_natCast]
  rw [hP, map_mul, (recipCoef_scalar D), hNrec,
    hqp, ← mul_assoc, ← (scalar_mul _ D)] at hcQ
  exact (scalar_mul_left_cancel (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX)) hDne)) hcQ

/-- **Theorem R (reciprocity).** For `n > 0` and every factorization type `σ`:
the universal monic density is the root-law coefficient with `q ↦ 1/q` substituted,
`A_{n,σ}(q) = B_{n,σ}(1/q)` (where `B_{n,σ}` is the coefficient of `σ` in the root law
`rootLaw n`), and the universal projective density is self-reciprocal,
`R_{n,σ}(1/q) = R_{n,σ}(q)`; both as identities of rational functions in `q`.

The certified form also assumed `ValidType σ` and `typeDegree σ = n`, which the proof does not use.
The hypothesis `0 < n` is used (`rootLaw 0` is defined separately). -/
theorem recip_main (n : ℕ) (hn : 0 < n) (σ : FactorType) :
    (monicExpr n σ).rational =
      ((lawCoeff (rootLaw n) σ).subst (.inv .var)).rational ∧
    (projectiveExpr n σ).rational =
      ((projectiveExpr n σ).subst (.inv .var)).rational := by
  have hv : (State.single 1 n).Valid := ⟨Nat.one_pos, hn⟩
  have hr : rootLaw n = stateLaw (State.single 1 n) := by
    unfold rootLaw; rw [if_neg hn.ne']
  refine ⟨?_, ?_⟩
  · rw [← coeff_lawCoef_globalLaw_false, lawCoef_globalLaw_false_eq_recipCoef n hn, hr,
      coeff_recipCoef_lawCoef _ (lawWf_stateLaw (State.single 1 n) hv) σ]
  · rw [← coeff_lawCoef_globalLaw_true, ← recipCoef_lawCoef_globalLaw_true n,
      coeff_recipCoef_lawCoef _ (lawWf_globalLaw true n) σ]
    rfl

end SurfaceBlowup
