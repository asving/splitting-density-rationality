/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Formula.StateCombinatorics
import SurfaceBlowup.Reciprocity.Quantum

/-!
# Plethystic calculus for the reciprocity law

Formal-power-series tools over the coefficient ring `Coef = ℚ(q)[Z_{e,f}]` used in the proof of
the reciprocity law: truncated congruences, `exp`/`log` and formal powers, the plethystic
exponential, logarithm and powers `P_w`, multinomial expansions of Euler products into pattern
sums, the combinatorics of the tangent patterns of single-boundary states `S(a;n)`, and the
well-formedness and rational-function calculus of the weight expressions.

## Main results

* `eq_of_mul_derivative_eq_mul`: uniqueness for the ODE `g E' = w E`.
* `expSer_add`, `expSer_logSer`, `logSer_expSer`, `coeff_formalPow`: `exp`, `log` and powers.
* `pPow_pPow`, `pPow_mul_pPow`, `coeff_pPow_sub_of_scongr`: plethystic powers.
* `prod_formalPow_adamsSer_clusterSer_scongr`, `coeff_euler_families_eq_patternSum`: Euler
  products as pattern sums.
* `exists_unique_selfPattern_single`: the unique self pattern of `S(a;n)`.
* `Expr.rational_add`, `Expr.rational_sum`, `lawCoef_lawScale`, `lawCoef_lawProd`: the expression
  and law calculus.
* `clusterSer_eq_pPow`, `dilate_recipSer_eulerSer_mul_scongr_one`.

Provenance: `Thm_SurfaceBlowupV2_recip_{scongr_pleth, scongr_pleth_lead, ser_ode_unique,
expSer_add, expSer_logSer, logSer_mul, formalPow_basic, formalPow_coeff, formalPow_adams_series,
euler_product_families, pExp_add, pExp_pLog, pPow_comp, scongr_pPow, single_pattern_reindex,
single_self_pattern, single_self_pattern_unique, sum_triple_reindex, weights_wf,
wf_fraction_ne_zero, rational_hom, lawCoef_append_scale, clusterSer_coeff, central_inverse,
lawCoef_mul_prod, power_identities, rational_sum_prod, divisorCount_rational,
families_to_pattern, lawCoef_coeff, lawWf_safe, safe_wf}`.
-/

namespace SurfaceBlowup

/-- Truncated agreement `f ≡ g mod x^{n+1}` is preserved by `plethSum = Σ ψ_k/k`. -/
theorem SCongr.plethSum {n : ℕ} {f g : Ser} (h : SCongr n f g) :
    SCongr n (SurfaceBlowup.plethSum f) (SurfaceBlowup.plethSum g) := fun m hm ↦ by
  simp only [SurfaceBlowup.plethSum, PowerSeries.coeff_mk,
    fun k ↦ h (m / k) ((Nat.div_le_self m k).trans hm)]

/-- Truncated agreement `f ≡ g mod x^{n+1}` is preserved by `moebiusSum = Σ μ(k) ψ_k/k`. -/
theorem SCongr.moebiusSum {n : ℕ} {f g : Ser} (h : SCongr n f g) :
    SCongr n (SurfaceBlowup.moebiusSum f) (SurfaceBlowup.moebiusSum g) := fun m hm ↦ by
  simp only [SurfaceBlowup.moebiusSum, PowerSeries.coeff_mk,
    fun k ↦ h (m / k) ((Nat.div_le_self m k).trans hm)]

/-- A divisor sum `Σ_{k ∣ n} w_k ψ_k(f_{n/k})` with `w_1 = 1` sees only the top coefficient of `f`
modulo agreement in lower degrees. -/
private theorem divisorSum_sub_of_scongr (n : ℕ) (hn : 0 < n) (f g : Ser)
    (h : SCongr (n - 1) f g) (w : ℕ → ℚ) (hw : w 1 = 1) :
    (∑ k ∈ n.divisors, w k • adamsCoef k (PowerSeries.coeff (n / k) f)) -
      (∑ k ∈ n.divisors, w k • adamsCoef k (PowerSeries.coeff (n / k) g)) =
      PowerSeries.coeff n f - PowerSeries.coeff n g := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single 1]
  · rw [Nat.div_one, hw, one_smul, one_smul, adamsCoef_one, adamsCoef_one]
  · intro k hk hk1
    have := Nat.div_lt_self hn (by have := Nat.pos_of_mem_divisors hk; omega : 1 < k)
    rw [h _ (by omega), sub_self]
  · exact fun h1 ↦ absurd (Nat.one_mem_divisors.2 hn.ne') h1

/-- If `f ≡ g` below degree `n`, then the degree-`n` coefficients of `Σ ψ_k f/k` and
`Σ ψ_k g/k` differ exactly as those of `f` and `g`. -/
private theorem coeff_plethSum_sub_of_scongr (n : ℕ) (hn : 0 < n) (f g : Ser)
    (h : SCongr (n - 1) f g) :
    PowerSeries.coeff n (plethSum f) - PowerSeries.coeff n (plethSum g) =
      PowerSeries.coeff n f - PowerSeries.coeff n g := by
  simp only [plethSum, PowerSeries.coeff_mk]
  exact divisorSum_sub_of_scongr n hn f g h (fun k ↦ ((k : ℚ)⁻¹)) (by simp)

/-- If `f ≡ g` below degree `n`, then the degree-`n` coefficients of `Σ μ(k) ψ_k f/k` and
`Σ μ(k) ψ_k g/k` differ exactly as those of `f` and `g`. -/
private theorem coeff_moebiusSum_sub_of_scongr (n : ℕ) (hn : 0 < n) (f g : Ser)
    (h : SCongr (n - 1) f g) :
    PowerSeries.coeff n (moebiusSum f) - PowerSeries.coeff n (moebiusSum g) =
      PowerSeries.coeff n f - PowerSeries.coeff n g := by
  simp only [moebiusSum, PowerSeries.coeff_mk]
  exact divisorSum_sub_of_scongr n hn f g h
    (fun k ↦ (((ArithmeticFunction.moebius k : ℤ) : ℚ)) / (k : ℚ)) (by simp)

/-- Uniqueness for the linear ODE `g E' = w E` with `g(0) = 1`: a solution is determined by its
constant term. -/
theorem eq_of_mul_derivative_eq_mul (g w E F : Ser) (hg : PowerSeries.constantCoeff g = 1)
    (hE : g * PowerSeries.derivative Coef E = w * E)
    (hF : g * PowerSeries.derivative Coef F = w * F)
    (h0 : PowerSeries.constantCoeff E = PowerSeries.constantCoeff F) :
    E = F := by
  have := IsAddTorsionFree.of_module_rat (M := Coef)
  set D : Ser := E - F with hDdef
  have hD : g * PowerSeries.derivative Coef D = w * D := by
    simp only [hDdef, map_sub, mul_sub, hE, hF]
  have key : ∀ n, ∀ m ≤ n, PowerSeries.coeff m D = 0 := by
    intro n
    induction n with
    | zero =>
      intro m hm
      rw [Nat.le_zero.mp hm, PowerSeries.coeff_zero_eq_constantCoeff_apply, hDdef, map_sub, h0,
        sub_self]
    | succ n ih =>
      intro m hm
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact ih m (by omega)
      have hc := congrArg (PowerSeries.coeff n) hD
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul] at hc
      have hR : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          PowerSeries.coeff p.1 w * PowerSeries.coeff p.2 D = 0 :=
        Finset.sum_eq_zero fun p hp ↦ by
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
          rw [ih p.2 (by omega), mul_zero]
      have hmem : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
      rw [hR, ← Finset.add_sum_erase _ _ hmem] at hc
      have hL : ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
          PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 (PowerSeries.derivative Coef D) = 0 :=
        Finset.sum_eq_zero fun p hp ↦ by
          rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
          have : p.1 ≠ 0 := fun h0' ↦ hp.1 (by ext <;> simp <;> omega)
          rw [PowerSeries.coeff_derivative, ih (p.2 + 1) (by omega), zero_mul, mul_zero]
      rw [hL, add_zero, PowerSeries.coeff_derivative, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        hg, one_mul] at hc
      refine nsmul_right_injective (Nat.succ_ne_zero n) (?_ : (n + 1) • _ = (n + 1) • (0 : Coef))
      rw [nsmul_eq_mul, smul_zero, mul_comm]
      push_cast
      exact hc
  exact sub_eq_zero.mp (show D = 0 from PowerSeries.ext fun n ↦ by simpa using key n n le_rfl)

/-- The exponential is additive-to-multiplicative on series with zero constant term. -/
theorem expSer_add (f g : Ser) (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) :
    expSer (f + g) = expSer f * expSer g := by
  have hfg : PowerSeries.constantCoeff (f + g) = 0 := by rw [map_add, hf, hg, add_zero]
  apply eq_of_mul_derivative_eq_mul 1 (PowerSeries.derivative Coef (f + g)) _ _
    PowerSeries.constantCoeff_one
  · rw [one_mul, derivative_expSer _ hfg]
  · rw [one_mul, Derivation.leibniz, derivative_expSer f hf, derivative_expSer g hg, map_add]
    simp only [smul_eq_mul]
    ring
  · rw [constantCoeff_expSer _ hfg, map_mul, constantCoeff_expSer f hf, constantCoeff_expSer g hg,
      mul_one]

/-- `exp ∘ log = id` on series with constant term `1`. -/
theorem expSer_logSer (g : Ser) (hg : PowerSeries.constantCoeff g = 1) : expSer (logSer g) = g := by
  have hL0 := constantCoeff_logSer g hg
  apply eq_of_mul_derivative_eq_mul g (PowerSeries.derivative Coef g) _ _ hg
  · rw [derivative_expSer _ hL0, ← mul_assoc, mul_derivative_logSer g hg]
  · exact mul_comm _ _
  · rw [constantCoeff_expSer _ hL0, hg]

/-- `log ∘ exp = id` on series with constant term `0`. -/
theorem logSer_expSer (f : Ser) (hf : PowerSeries.constantCoeff f = 0) : logSer (expSer f) = f := by
  have hE0 := constantCoeff_expSer f hf
  have hu : IsUnit (expSer f) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hE0]; exact isUnit_one
  have hd : PowerSeries.derivative Coef (logSer (expSer f)) = PowerSeries.derivative Coef f :=
    hu.mul_left_cancel (by rw [mul_derivative_logSer _ hE0, derivative_expSer f hf, mul_comm])
  have := IsAddTorsionFree.of_module_rat (M := Coef)
  exact PowerSeries.derivative.ext hd (by rw [constantCoeff_logSer _ hE0, hf])

/-- The formal power `g^c = exp(c log g)` has constant term `1` (for `g(0) = 1`). -/
private theorem constantCoeff_formalPow (c : RatFunc ℚ) (g : Ser)
    (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.constantCoeff (formalPow c g) = 1 :=
  constantCoeff_expSer _ (by rw [map_mul, PowerSeries.constantCoeff_C, constantCoeff_logSer g hg,
    mul_zero])

/-- The formal power solves the ODE `g (g^c)' = c g' g^c` (for `g(0) = 1`). -/
private theorem mul_derivative_formalPow (c : RatFunc ℚ) (g : Ser)
    (hg : PowerSeries.constantCoeff g = 1) :
    g * PowerSeries.derivative Coef (formalPow c g) =
      PowerSeries.C (scalar c) * PowerSeries.derivative Coef g * formalPow c g := by
  have hl : PowerSeries.derivative Coef (PowerSeries.C (scalar c) * logSer g) =
      PowerSeries.C (scalar c) * PowerSeries.derivative Coef (logSer g) := by
    rw [Derivation.leibniz, PowerSeries.derivative_C]; simp
  rw [formalPow, derivative_expSer _ (by rw [map_mul, PowerSeries.constantCoeff_C,
    constantCoeff_logSer g hg, mul_zero]), hl, ← mul_derivative_logSer g hg]
  ring

/-- Binomial expansion of the formal power: the `n`-th coefficient of `g^c` is
`Σ_{k ≤ n} (1/k!) c(c-1)⋯(c-k+1) [xⁿ](g-1)^k`. -/
theorem coeff_formalPow (c : RatFunc ℚ) (g : Ser) (hg : PowerSeries.constantCoeff g = 1)
    (n : ℕ) :
    PowerSeries.coeff n (formalPow c g) = ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℚ)⁻¹) •
      ((∏ j ∈ Finset.range k, (scalar c - (j : ℚ) • (1 : Coef))) *
        PowerSeries.coeff n ((g - 1) ^ k)) := by
  set B : Ser := PowerSeries.mk fun n ↦
    ((n.factorial : ℚ)⁻¹) • ∏ j ∈ Finset.range n, (scalar c - (j : ℚ) • (1 : Coef)) with hB
  set y : Ser := g - 1 with hy_def
  have hy0 : PowerSeries.constantCoeff y = 0 := by simp [y, hg]
  have hy : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero' hy0
  have hODE := binomial_series_ode c
  rw [← hB] at hODE
  have hEq : B.subst y = formalPow c g := by
    refine eq_of_mul_derivative_eq_mul g (PowerSeries.C (scalar c) * PowerSeries.derivative Coef g)
      _ _ hg ?_ (mul_derivative_formalPow c g hg) ?_
    · have hs := congrArg (fun f : Ser ↦ f.subst y) hODE
      rw [PowerSeries.subst_mul hy, PowerSeries.subst_mul hy, PowerSeries.subst_add hy,
        PowerSeries.subst_X hy] at hs
      have hone : (1 : Ser).subst y = 1 := by
        simpa using (PowerSeries.subst_C (a := y) (1 : Coef))
      have hC : (PowerSeries.C (scalar c)).subst y = PowerSeries.C (scalar c) :=
        PowerSeries.subst_C _
      rw [hone, hC, show (1 : Ser) + y = g by simp [y]] at hs
      rw [PowerSeries.derivative_subst hy, show PowerSeries.derivative Coef y =
        PowerSeries.derivative Coef g by simp [y], ← mul_assoc, hs]
      ring
    · rw [constantCoeff_formalPow c g hg, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        coeff_subst_eq_sum 0 B y hy0]
      simp [B]
  rw [← hEq, coeff_subst_eq_sum n B y hy0]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [B, PowerSeries.coeff_mk, y]
  rw [smul_eq_mul, smul_mul_assoc]

/-- For `κ` with total `k`, `(k!)⁻¹ · multinomial(κ) = (Π_r κ_r!)⁻¹`. -/
private theorem inv_factorial_mul_multinomial {n k : ℕ} (κ : Fin n → ℕ) (hk : ∑ r, κ r = k) :
    ((k.factorial : ℚ))⁻¹ * (Nat.multinomial Finset.univ κ : ℚ) =
      (∏ r : Fin n, ((Nat.factorial (κ r) : ℕ) : ℚ))⁻¹ := by
  have hspec := Nat.multinomial_spec Finset.univ κ
  rw [hk] at hspec
  have hpos : (∏ r : Fin n, ((Nat.factorial (κ r) : ℕ) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun r _ ↦ by exact_mod_cast Nat.factorial_ne_zero _)
  have hk0 : ((k.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [← hspec] at hk0 ⊢
  push_cast at hk0 ⊢
  have hmn : (Nat.multinomial Finset.univ κ : ℚ) ≠ 0 := right_ne_zero_of_mul hk0
  field_simp

/-- A sum over all `κ : Fin n → ℕ` of total `≤ n`, grouped by the total, equals the sum over
`Fin (n + 1)`-valued vectors, provided the summand vanishes on vectors of total `> n`. -/
private theorem sum_range_sum_piAntidiag_eq_sum_fin {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : (Fin n → ℕ) → M) (hF : ∀ κ, n < ∑ r, κ r → F κ = 0) :
    ∑ k ∈ Finset.range (n + 1), ∑ κ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k, F κ =
      ∑ κ : Fin n → Fin (n + 1), F (fun r ↦ (κ r).val) := by
  set E : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ ↦ Finset.range (n + 1)) with hE
  set D : Finset (Fin n → ℕ) := E.filter (fun κ ↦ ∑ r, κ r ≤ n) with hD
  -- merge into the sum over `D`
  have h3 : ∑ k ∈ Finset.range (n + 1), ∑ κ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k,
      F κ = ∑ κ ∈ D, F κ := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := D) (t := Finset.range (n + 1))
        (g := fun κ ↦ ∑ r, κ r)]
    · refine Finset.sum_congr rfl (fun k hk ↦ ?_)
      rw [Finset.mem_range] at hk
      congr 1
      ext κ
      simp only [hD, hE, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
          Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true]
      constructor
      · intro h
        have h' : ∑ r, κ r = k := h
        refine ⟨⟨fun r ↦ ?_, by omega⟩, h⟩
        have : κ r ≤ ∑ r, κ r :=
          Finset.single_le_sum (f := κ) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r)
        omega
      · rintro ⟨_, h⟩; exact h
    · intro κ hκ
      simp only [hD, Finset.mem_filter] at hκ
      simp only [Finset.mem_range]; omega
  -- `D` to `E`
  have h4 : ∑ κ ∈ D, F κ = ∑ κ ∈ E, F κ :=
    Finset.sum_filter_of_ne fun κ _ hne ↦ by_contra fun h ↦ hne (hF κ (by omega))
  -- `E` to `Fin`-valued vectors
  rw [h3, h4]
  refine Finset.sum_nbij' (fun κ r ↦ ⟨κ r % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)
      (fun κ r ↦ (κ r).val) ?_ ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro κ _
    simp only [hE, Fintype.mem_piFinset, Finset.mem_range]
    exact fun r ↦ (κ r).isLt
  · intro κ hκ
    simp only [hE, Fintype.mem_piFinset, Finset.mem_range] at hκ
    funext r; exact Nat.mod_eq_of_lt (hκ r)
  · intro κ _
    funext r; exact Fin.ext (Nat.mod_eq_of_lt (κ r).isLt)
  · intro κ hκ
    simp only [hE, Fintype.mem_piFinset, Finset.mem_range] at hκ
    have : (fun r ↦ κ r % (n + 1)) = κ := funext fun r ↦ Nat.mod_eq_of_lt (hκ r)
    simp only [this]

/-- Multinomial expansion of `ψ_m(B_a)^{C_m}` (with `C_m = availablePoints ε m`) through degree
`n`: a sum over exponent vectors `κ` of generalized binomial coefficients times monomials in the
`ψ_m(F_{S(a;r+1)})`. -/
private theorem formalPow_adamsSer_clusterSer_scongr (ε : ℤ) (a m n : ℕ) (hm : 0 < m) :
    SCongr n (formalPow (availablePoints ε m).rational (adamsSer m (clusterSer a)))
        (∑ κ : Fin n → Fin (n + 1), PowerSeries.C (scalar
        ((∏ j ∈ Finset.range (∑ r : Fin n, (κ r).val), ((availablePoints ε m).rational - RatFunc.C
        (j : ℚ))) * RatFunc.C ((∏ r : Fin n, ((Nat.factorial (κ r).val : ℕ) : ℚ))⁻¹))) *
        (PowerSeries.C (∏ r : Fin n, (adamsCoef m (lawCoef
        (stateLaw (State.single a (r.val + 1))))) ^ (κ r).val) *
        (PowerSeries.X : Ser) ^ (m * ∑ r : Fin n, (r.val + 1) * (κ r).val))) := by
  -- Expand `g^c` binomially (`coeff_formalPow`), replace `g - 1` by its truncation `S`, expand
  -- each `S^k` multinomially, and regroup the exponent vectors.
  intro d hd
  set c := (availablePoints ε m).rational with hc
  set g := adamsSer m (clusterSer a) with hgdef
  set b : ℕ → Coef := fun s ↦ adamsCoef m (lawCoef (stateLaw (State.single a s))) with hb
  set S : Ser := ∑ r : Fin n, PowerSeries.C (b (r.val + 1)) *
      (PowerSeries.X : Ser) ^ (m * (r.val + 1)) with hSdef
  set T : (Fin n → ℕ) → Ser := fun κ ↦ PowerSeries.C (scalar
      ((∏ j ∈ Finset.range (∑ r : Fin n, κ r), (c - RatFunc.C (j : ℚ))) *
      RatFunc.C ((∏ r : Fin n, ((Nat.factorial (κ r) : ℕ) : ℚ))⁻¹))) *
      (PowerSeries.C (∏ r : Fin n, b (r.val + 1) ^ κ r) *
      (PowerSeries.X : Ser) ^ (m * ∑ r : Fin n, (r.val + 1) * κ r)) with hTdef
  have hg : PowerSeries.constantCoeff g = 1 := by
    rw [hgdef, constantCoeff_adamsSer m hm.ne', ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [clusterSer]
  have hpow : ∀ k : ℕ, SCongr n ((g - 1) ^ k) (S ^ k) :=
    (adamsSer_clusterSer_sub_one_scongr a m n hm).pow
  -- the summands of the target are T applied to ℕ-vectors
  have hR : (∑ κ : Fin n → Fin (n + 1), PowerSeries.C (scalar
      ((∏ j ∈ Finset.range (∑ r : Fin n, (κ r).val), ((availablePoints ε m).rational - RatFunc.C
      (j : ℚ))) * RatFunc.C ((∏ r : Fin n, ((Nat.factorial (κ r).val : ℕ) : ℚ))⁻¹))) *
      (PowerSeries.C (∏ r : Fin n, (adamsCoef m (lawCoef (stateLaw (State.single a (r.val + 1)))))
      ^ (κ r).val) * (PowerSeries.X : Ser) ^ (m * ∑ r : Fin n, (r.val + 1) * (κ r).val)))
      = ∑ κ : Fin n → Fin (n + 1), T (fun r ↦ (κ r).val) := rfl
  rw [hR, coeff_formalPow c g hg d]
  have hsum_le : ∀ κ : Fin n → ℕ, ∑ r, κ r ≤ m * ∑ r : Fin n, (r.val + 1) * κ r := by
    intro κ
    calc ∑ r, κ r ≤ ∑ r : Fin n, (r.val + 1) * κ r :=
          Finset.sum_le_sum (fun r _ ↦ Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      _ ≤ _ := Nat.le_mul_of_pos_left _ hm
  have hTcoeff : ∀ κ : Fin n → ℕ, PowerSeries.coeff d (T κ) = if d = m * ∑ r : Fin n, (r.val + 1) *
      κ r then scalar ((∏ j ∈ Finset.range (∑ r : Fin n, κ r), (c - RatFunc.C (j : ℚ))) *
      RatFunc.C ((∏ r : Fin n, ((Nat.factorial (κ r) : ℕ) : ℚ))⁻¹)) * ∏ r : Fin n,
      b (r.val + 1) ^ κ r else 0 := by
    intro κ
    rw [hTdef]; dsimp only
    rw [← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul_X_pow]
  have hTzero : ∀ κ : Fin n → ℕ, n < ∑ r, κ r → PowerSeries.coeff d (T κ) = 0 := by
    intro κ hκ
    rw [hTcoeff, if_neg]
    have := hsum_le κ
    omega
  -- step 1: extend the k-range and replace g - 1 by S
  have h1 : ∑ k ∈ Finset.range (d + 1), ((k.factorial : ℚ)⁻¹) •
      ((∏ j ∈ Finset.range k, (scalar c - (j : ℚ) • (1 : Coef))) *
      PowerSeries.coeff d ((g - 1) ^ k))
      = ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℚ)⁻¹) •
          ((∏ j ∈ Finset.range k, (scalar c - (j : ℚ) • (1 : Coef))) *
          PowerSeries.coeff d (S ^ k)) := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : d + 1 ≤ n + 1))]
    · refine Finset.sum_congr rfl (fun k _ ↦ ?_)
      rw [hpow k d hd]
    · intro k _ hk
      rw [Finset.mem_range] at hk
      have hX : (PowerSeries.X : Ser) ^ k ∣ S ^ k := by
        apply pow_dvd_pow_of_dvd
        rw [PowerSeries.X_dvd_iff, hSdef, map_sum]
        refine Finset.sum_eq_zero (fun r _ ↦ ?_)
        rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by positivity), mul_zero]
      obtain ⟨u, hu⟩ := hX
      rw [hu, PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero, smul_zero]
  -- step 2: multinomial expansion per k
  have h2 : ∀ k ∈ Finset.range (n + 1), ((k.factorial : ℚ)⁻¹) •
      ((∏ j ∈ Finset.range k, (scalar c - (j : ℚ) • (1 : Coef))) * PowerSeries.coeff d (S ^ k))
      = ∑ κ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k, PowerSeries.coeff d (T κ) := by
    intro k _
    rw [hSdef, sum_C_mul_X_pow_pow m n k b, map_sum, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun κ hκ ↦ ?_)
    rw [Finset.mem_piAntidiag] at hκ
    rw [PowerSeries.coeff_C_mul_X_pow, hTcoeff]
    split_ifs
    · have hk : ∑ r, κ r = k := hκ.1
      rw [hk]
      have hq := inv_factorial_mul_multinomial κ hk
      have hM : ((Nat.multinomial Finset.univ κ : ℕ) : Coef) =
          scalar (RatFunc.C (Nat.multinomial Finset.univ κ : ℚ)) := by
        rw [scalar_eq_algebraMap, map_natCast, map_natCast]
      have hP : (∏ j ∈ Finset.range k, (scalar c - (j : ℚ) • (1 : Coef))) =
          scalar (∏ j ∈ Finset.range k, (c - RatFunc.C (j : ℚ))) := by
        simp only [rat_smul_eq_scalar_mul, mul_one, scalar_eq_algebraMap, map_prod, map_sub]
      rw [rat_smul_eq_scalar_mul, hM, hP, ← hq, map_mul]
      simp only [scalar_eq_algebraMap, map_mul]
      ring
    · rw [mul_zero, smul_zero]
  rw [h1, Finset.sum_congr rfl h2, sum_range_sum_piAntidiag_eq_sum_fin n _ hTzero, map_sum]

private theorem scalar_prod {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ) :
    scalar (∏ i ∈ s, f i) = ∏ i ∈ s, scalar (f i) := by
  simp only [scalar_eq_algebraMap, map_prod]

private theorem scongr_prod {ι : Type*} (n : ℕ) (s : Finset ι) (f g : ι → Ser)
    (h : ∀ i ∈ s, SCongr n (f i) (g i)) : SCongr n (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact SCongr.refl n _
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).mul (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Truncated product expansion of `Π_{m=1}^n ψ_m(B_a)^{C_m}` as a sum over exponent families
`K i r`, obtained by multiplying the expansions of `formalPow_adamsSer_clusterSer_scongr`. -/
theorem prod_formalPow_adamsSer_clusterSer_scongr (ε : ℤ) (a n : ℕ) :
    SCongr n (∏ m ∈ Finset.Icc 1 n, formalPow (availablePoints ε m).rational
        (adamsSer m (clusterSer a))) (∑ K : Fin n → Fin n → Fin (n + 1),
        PowerSeries.C (scalar (∏ i : Fin n, ((∏ j ∈ Finset.range (∑ r : Fin n, (K i r).val),
        ((availablePoints ε (i.val + 1)).rational - RatFunc.C (j : ℚ))) *
        RatFunc.C ((∏ r : Fin n, ((Nat.factorial (K i r).val : ℕ) : ℚ))⁻¹)))) *
        (PowerSeries.C (∏ i : Fin n, ∏ r : Fin n, (adamsCoef (i.val + 1)
        (lawCoef (stateLaw (State.single a (r.val + 1))))) ^ (K i r).val) *
        (PowerSeries.X : Ser) ^ (∑ i : Fin n, (i.val + 1) * ∑ r : Fin n, (r.val + 1) *
        (K i r).val))) := by
  have hre : ∏ m ∈ Finset.Icc 1 n, formalPow (availablePoints ε m).rational
      (adamsSer m (clusterSer a))
      = ∏ i : Fin n, formalPow (availablePoints ε (i.val + 1)).rational
          (adamsSer (i.val + 1) (clusterSer a)) := by
    rw [Fin.prod_univ_eq_prod_range (fun i ↦ formalPow (availablePoints ε (i + 1)).rational
      (adamsSer (i + 1) (clusterSer a))), ← Finset.Ico_add_one_right_eq_Icc,
      Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel, add_comm 1]
  rw [hre]
  have hprod := scongr_prod n Finset.univ _ _ (fun (i : Fin n) _ ↦
    formalPow_adamsSer_clusterSer_scongr ε a (i.val + 1) n (Nat.succ_pos _))
  refine hprod.trans ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine SCongr.of_eq (Finset.sum_congr rfl fun K _ ↦ ?_)
  simp only [Finset.prod_mul_distrib, ← map_prod, ← scalar_prod,
      Finset.prod_pow_eq_pow_sum, Finset.mul_sum]

/-- The plethystic exponential is additive-to-multiplicative: `Exp(f+g) = Exp f · Exp g`. -/
private theorem pExp_add (f g : Ser) : pExp (f + g) = pExp f * pExp g := by
  rw [pExp, pExp, pExp, plethSum_add]
  exact expSer_add _ _ (constantCoeff_plethSum f) (constantCoeff_plethSum g)

/-- `Exp f` has constant term `1`. -/
private theorem constantCoeff_pExp (f : Ser) : PowerSeries.constantCoeff (pExp f) = 1 :=
  constantCoeff_expSer _ (constantCoeff_plethSum f)

/-- `Log g` has constant term `0`. -/
private theorem constantCoeff_pLog (g : Ser) : PowerSeries.constantCoeff (pLog g) = 0 :=
  constantCoeff_moebiusSum _

/-- `Exp ∘ Log = id` on series with constant term `1`. -/
private theorem pExp_pLog (g : Ser) (hg : PowerSeries.constantCoeff g = 1) : pExp (pLog g) = g := by
  rw [pExp, pLog, plethSum_moebiusSum _ (constantCoeff_logSer g hg), expSer_logSer g hg]

/-- `Log ∘ Exp = id` on series with constant term `0`. -/
private theorem pLog_pExp (f : Ser) (hf : PowerSeries.constantCoeff f = 0) : pLog (pExp f) = f := by
  rw [pExp, pLog, logSer_expSer _ (constantCoeff_plethSum f), moebiusSum_plethSum f hf]

/-- The plethystic power `P_w(g)` has constant term `1`. -/
theorem constantCoeff_pPow (w : RatFunc ℚ) (g : Ser) : PowerSeries.constantCoeff (pPow w g) = 1 :=
  constantCoeff_pExp _

private theorem constantCoeff_C_mul_pLog (a : RatFunc ℚ) (g : Ser) :
    PowerSeries.constantCoeff (PowerSeries.C (scalar a) * pLog g) = 0 := by
  simp [constantCoeff_pLog]

/-- `P_w ∘ P_z = P_{wz}`. -/
theorem pPow_pPow (w z : RatFunc ℚ) (g : Ser) : pPow w (pPow z g) = pPow (w * z) g := by
  rw [pPow, pPow, pLog_pExp _ (constantCoeff_C_mul_pLog z g), ← mul_assoc, ← map_mul,
    ← scalar_mul, pPow]

/-- `P_w P_z = P_{w+z}`. -/
theorem pPow_mul_pPow (w z : RatFunc ℚ) (g : Ser) : pPow w g * pPow z g = pPow (w + z) g := by
  rw [pPow, pPow, pPow, ← pExp_add, scalar_add, map_add, add_mul]

/-- `P_1 = id` on series with constant term `1`. -/
private theorem pPow_one (g : Ser) (hg : PowerSeries.constantCoeff g = 1) : pPow 1 g = g := by
  rw [pPow, scalar_one, map_one, one_mul, pExp_pLog g hg]

/-- If `g ≡ h` below degree `n`, then the degree-`n` coefficients of `P_w(g)` and `P_w(h)` differ
by `w` times those of `g` and `h`. -/
theorem coeff_pPow_sub_of_scongr (n : ℕ) (hn : 0 < n) (w : RatFunc ℚ) (g h : Ser)
    (hg : PowerSeries.constantCoeff g = 1) (hh : PowerSeries.constantCoeff h = 1)
    (hgh : SCongr (n - 1) g h) :
    PowerSeries.coeff n (pPow w g) - PowerSeries.coeff n (pPow w h) =
      scalar w * (PowerSeries.coeff n g - PowerSeries.coeff n h) := by
  have hL : SCongr (n - 1) (logSer g) (logSer h) := hgh.logSer hg hh
  have hP : SCongr (n - 1) (PowerSeries.C (scalar w) * pLog g)
      (PowerSeries.C (scalar w) * pLog h) := hL.moebiusSum.C_mul _
  rw [pPow, pPow, pExp, pExp, coeff_expSer_sub_of_scongr n hn _ _ (constantCoeff_plethSum _)
    (constantCoeff_plethSum _) hP.plethSum, coeff_plethSum_sub_of_scongr n hn _ _ hP,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, ← mul_sub, pLog, pLog,
    coeff_moebiusSum_sub_of_scongr n hn _ _ hL, coeff_logSer_sub_of_scongr n hn g h hg hh hgh]

/-- A sum over the allowed tangent patterns of `S(a;n)` depending only on the divisor degree `d`,
the tangent depth `r`, and the off-boundary pattern, reindexed as a sum over `d`, `r` and patterns
of weight `d - r`. -/
theorem sum_allowedPatterns_single (a n : ℕ) (ha : 0 < a)
    (F : ℕ → ℕ → Pattern (State.single a n).degree → Coef) :
    ∑ P ∈ allowedPatterns (State.single a n), F P.d.val P.rt.val P.other =
      ∑ d ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (d + 1), (if ((0 < r ↔ d < n) ∧ r ≤ d) then
        ∑ m ∈ (Finset.univ : Finset (Pattern (State.single a n).degree)).filter
          (fun m ↦ patternWeight m = d - r), F d r m else 0) := by
  rw [sum_allowedPatterns_reindex (.single a n) n (Nat.le_mul_of_pos_left n ha)
    (fun d rt rx ↦ rx = 0 ∧ (0 < rt ↔ d < n)) (fun P ↦ by simp [allowedPatterns, Allowed])
    (fun d rt _ m ↦ F d rt m)]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Finset.sum_eq_single 0 (fun rx _ h0 ↦ if_neg fun h ↦ h0 h.1.1) (by simp)]
  simp only [true_and, add_zero, Nat.sub_zero]

private theorem otherChildren_length {N : ℕ} (a : ℕ) (m : Pattern N) :
    (otherChildren a m).length = ∑ ij, (m ij).val := by
  unfold otherChildren
  rw [List.length_flatMap]
  simp only [List.length_replicate]
  rw [Finset.sum_map_toList]

private theorem mem_otherChildren {N : ℕ} (a : ℕ) (m : Pattern N) (x : ℕ × State) :
    x ∈ otherChildren a m ↔ ∃ ij, (m ij).val ≠ 0 ∧ x = (ij.1.val+1, .single a (ij.2.val+1)) := by
  unfold otherChildren
  simp [List.mem_flatMap, List.mem_replicate, eq_comm]

private theorem otherChildren_eq_single_iff (a n N : ℕ) (hn : 1 ≤ n) (hnN : n - 1 < N)
    (m : Pattern N) :
    otherChildren a m = [(1, State.single a n)] ↔
      ∀ ij : Fin N × Fin N, (m ij).val = (if ij.1.val = 0 ∧ ij.2.val = n - 1 then 1 else 0) := by
  have h0 : 0 < N := by omega
  let ij0 : Fin N × Fin N := (⟨0, h0⟩, ⟨n-1, hnN⟩)
  have key : ∀ ij : Fin N × Fin N, (ij.1.val = 0 ∧ ij.2.val = n - 1) ↔ ij = ij0 := by
    intro ij
    constructor
    · rintro ⟨h1, h2⟩; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · rintro rfl; simp [ij0]
  have hrep : [(1, State.single a n)] = List.replicate 1 (1, State.single a n) := rfl
  rw [hrep, List.eq_replicate_iff, otherChildren_length]
  constructor
  · rintro ⟨hlen, hall⟩
    have hsupp : ∀ ij, (m ij).val ≠ 0 → ij = ij0 := by
      intro ij hij
      have := hall _ ((mem_otherChildren a m _).2 ⟨ij, hij, rfl⟩)
      simp only [Prod.mk.injEq, State.single.injEq] at this
      rw [← key]; omega
    have hs : ∑ ij, (m ij).val = (m ij0).val :=
      Finset.sum_eq_single ij0 (fun b _ hb ↦ by by_contra h; exact hb (hsupp b h)) (by simp)
    intro ij
    by_cases h : ij = ij0
    · subst h; rw [if_pos ((key _).2 rfl)]; omega
    · rw [if_neg (by rw [key]; exact h)]
      by_contra h'; exact h (hsupp ij h')
  · intro hm
    constructor
    · rw [Finset.sum_eq_single ij0]
      · rw [hm]; simp [ij0]
      · intro b _ hb; rw [hm, if_neg (by rw [key]; exact hb)]
      · simp
    · intro b hb
      obtain ⟨ij, hij, rfl⟩ := (mem_otherChildren a m b).1 hb
      rw [hm] at hij
      split_ifs at hij with h
      · simp only [Prod.mk.injEq, State.single.injEq]; exact ⟨by omega, trivial, by omega⟩
      · exact absurd rfl hij

/-- An allowed tangent pattern of `S(a;n)` (`n ≥ 2`) is the self pattern exactly when `d = n`,
there is no tangent part, and the off-boundary pattern is the single point of type `(1, n-1)`. -/
theorem selfPattern_single_iff (a n : ℕ) (ha : 0 < a) (hn : 2 ≤ n)
    (P : TangentPattern (State.single a n).degree) (hP : Allowed (State.single a n) P) :
    SelfPattern (State.single a n) P ↔ (P.d.val = n ∧ P.rt.val = 0 ∧ P.rx.val = 0 ∧
        ∀ ij : Fin (State.single a n).degree × Fin (State.single a n).degree, (P.other ij).val =
        (if ij.1.val = 0 ∧ ij.2.val = n - 1 then 1 else 0)) := by
  have hnN : n - 1 < (State.single a n).degree := by
    change n - 1 < a * n
    have : n ≤ a * n := Nat.le_mul_of_pos_left n ha
    omega
  have hO := otherChildren_eq_single_iff a n _ (by omega) hnN P.other
  obtain ⟨hd0, hsum, hdle, hrx, hrt⟩ := hP
  have hch : children (State.single a n) P =
      (if P.rt.val=0 then [] else [(1,State.crossing a a P.rt.val (n-P.d.val))]) ++
        otherChildren a P.other := rfl
  constructor
  · rintro ⟨a', c', _, hc⟩
    rw [hch] at hc
    have hrt0 : P.rt.val = 0 := by
      by_contra h
      rw [if_neg h] at hc
      simp at hc
    rw [if_pos hrt0, List.nil_append] at hc
    have hm := hO.1 hc
    refine ⟨?_, hrt0, hrx, hm⟩
    have hw : patternWeight P.other = n := by
      unfold patternWeight
      rw [Finset.sum_eq_single ((⟨0, by omega⟩, ⟨n-1, hnN⟩) : Fin (State.single a n).degree × Fin
          (State.single a n).degree)]
      · rw [hm]; simp; omega
      · intro b _ hb
        rw [hm, if_neg]
        · simp
        · rintro ⟨h1, h2⟩; exact hb (Prod.ext (Fin.ext h1) (Fin.ext h2))
      · simp
    omega
  · rintro ⟨hd, hrt0, _, hm⟩
    refine ⟨a, n, rfl, ?_⟩
    rw [hch, if_pos hrt0, List.nil_append]
    exact hO.2 hm

/-- For `n ≥ 2`, `S(a;n)` has exactly one allowed self pattern. -/
theorem exists_unique_selfPattern_single (a n : ℕ) (ha : 0 < a) (hn : 2 ≤ n) :
    ∃ P₀ : TangentPattern (State.single a n).degree, Allowed (State.single a n) P₀ ∧
        SelfPattern (State.single a n) P₀ ∧ ∀ Q : TangentPattern (State.single a n).degree,
        Allowed (State.single a n) Q → SelfPattern (State.single a n) Q → Q = P₀ := by
  have hdeg : (State.single a n).degree = a * n := rfl
  have hnN : n ≤ (State.single a n).degree := by
    rw [hdeg]; exact Nat.le_mul_of_pos_left n ha
  have hn0 : 0 < n := by omega
  let m₀ : Pattern (State.single a n).degree := fun ij ↦
    if ij.1.val = 0 ∧ ij.2.val = n - 1 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  let P₀ : TangentPattern (State.single a n).degree :=
    ⟨⟨n, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, m₀⟩
  have hm : ∀ ij, (P₀.other ij).val = (if ij.1.val = 0 ∧ ij.2.val = n - 1 then 1 else 0) := by
    intro ij
    change (m₀ ij).val = _
    simp only [m₀]
    split_ifs <;> rfl
  have hA : Allowed (State.single a n) P₀ := by
    refine ⟨hn0, ?_, ?_⟩
    · have : patternWeight P₀.other = n := by
        unfold patternWeight
        have hlt : n - 1 < (State.single a n).degree := by omega
        have hpos : 0 < (State.single a n).degree := by omega
        rw [Finset.sum_eq_single (⟨0, hpos⟩, ⟨n - 1, hlt⟩)]
        · rw [hm]; simp; omega
        · intro ij _ hne
          rw [hm]
          have : ¬ (ij.1.val = 0 ∧ ij.2.val = n - 1) := by
            rintro ⟨h1, h2⟩
            apply hne
            exact Prod.ext (Fin.ext h1) (Fin.ext h2)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      change 0 + 0 + _ = n
      omega
    · refine ⟨le_refl _, rfl, ?_⟩
      change 0 < 0 ↔ n < n
      simp
  have hS := (selfPattern_single_iff a n ha hn P₀ hA).2
    ⟨rfl, rfl, rfl, hm⟩
  refine ⟨P₀, hA, hS, ?_⟩
  intro Q hQ hQS
  obtain ⟨h1, h2, h3, h4⟩ := (selfPattern_single_iff a n ha hn Q hQ).1 hQS
  cases Q with
  | mk d rt rx other =>
    simp only at h1 h2 h3 h4
    have e1 : d = P₀.d := Fin.ext h1
    have e2 : rt = P₀.rt := Fin.ext h2
    have e3 : rx = P₀.rx := Fin.ext h3
    have e4 : other = P₀.other := by
      funext ij; apply Fin.ext; rw [h4, hm]
    rw [e1, e2, e3, e4]

/-- Reindexing a triple sum over `(rx, m, rt)` with `rx + m + rt ≤ K` by the total
`d = rx + m + rt`. -/
theorem sum_triple_reindex (c K : ℕ) (hK : K ≤ c) (G : ℕ → ℕ → ℕ → Coef) :
    ∑ rx ∈ Finset.range (c + 1), ∑ m ∈ Finset.range (c + 1), ∑ rt ∈ Finset.range (c + 1),
        (if rx + m + rt ≤ K then G rx m rt else 0) = ∑ d ∈ Finset.range (c + 1),
        ∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1),
        (if (rt + rx ≤ d ∧ d ≤ K) then G rx (d - rt - rx) rt else 0) := by
  rw [← Finset.sum_product', ← Finset.sum_product']
  have h : ∀ d : ℕ, ∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1),
      (if (rt + rx ≤ d ∧ d ≤ K) then G rx (d - rt - rx) rt else 0) =
      ∑ p ∈ Finset.range (d + 1) ×ˢ Finset.range (d + 1),
      (if (p.1 + p.2 ≤ d ∧ d ≤ K) then G p.2 (d - p.1 - p.2) p.1 else 0) := fun d ↦
      (Finset.sum_product' _ _ _).symm
  simp_rw [h]
  rw [Finset.sum_sigma']
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun p _ ↦ (⟨p.1.1 + p.1.2 + p.2, (p.2, p.1.1)⟩ : (_ : ℕ) × (ℕ × ℕ)))
    (fun q _ ↦ ((q.2.2, q.1 - q.2.1 - q.2.2), q.2.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨rx, m⟩, rt⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sigma, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨d, rt, rx⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sigma, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨⟨rx, m⟩, rt⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    refine Prod.ext (Prod.ext rfl ?_) rfl
    simp only; omega
  · rintro ⟨d, rt, rx⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sigma, Finset.mem_range] at h ⊢
    have : rx + (d - rt - rx) + rt = d := by omega
    simp [this]
  · rintro ⟨⟨rx, m⟩, rt⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    simp

/-! ### Well-formed expressions and their rational functions -/

/-- A safe expression is well formed. -/
private theorem Expr.wf_of_safe (x : Expr) (q : ℚ) (hx : x.safe q) : x.wf := by
  induction x with
  | const r => trivial
  | var => trivial
  | add a b iha ihb => exact ⟨iha hx.1, ihb hx.2⟩
  | mul a b iha ihb => exact ⟨iha hx.1, ihb hx.2⟩
  | inv a ih =>
    refine ⟨ih hx.1, fun h ↦ hx.2 ?_⟩
    obtain ⟨_, h2⟩ := expression_fraction a q hx.1
    rw [h2, h]; simp

/-- Powers of well-formed expressions are well formed. -/
theorem Expr.wf_pow {x : Expr} (hx : x.wf) (k : ℕ) : (Expr.pow x k).wf := by
  induction k with
  | zero => simp [Expr.pow, Expr.wf]
  | succ k ih => exact ⟨ih, hx⟩

private theorem fraction_pow_var_ne_zero (k : ℕ) : (Expr.pow Expr.var k).fraction.1 ≠ 0 := by
  induction k with
  | zero => simp [Expr.pow, Expr.fraction]
  | succ k ih =>
    simp only [Expr.pow, Expr.fraction]
    exact mul_ne_zero ih Polynomial.X_ne_zero

/-- A sum of well-formed expressions is well formed. -/
private theorem Expr.wf_sum {xs : List Expr} (h : ∀ z ∈ xs, z.wf) : (Expr.sum xs).wf := by
  induction xs with
  | nil => simp [Expr.sum, Expr.wf]
  | cons a t ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    exact ⟨h.1, ih h.2⟩

private theorem wf_pointCount (δ : ℕ) : (pointCount δ).wf := by
  refine ⟨trivial, Expr.wf_sum ?_⟩
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨j, -, rfl⟩ := hz
  exact ⟨trivial, Expr.wf_pow (x := Expr.var) trivial _⟩

/-- The available-point counts are well formed. -/
private theorem wf_availablePoints (ε : ℤ) (δ : ℕ) : (availablePoints ε δ).wf := by
  unfold availablePoints
  split_ifs
  · exact ⟨trivial, trivial⟩
  · exact wf_pointCount δ

/-- The return weights are well formed. -/
theorem wf_returnWeight (c : ℕ) : (returnWeight c).wf :=
  ⟨trivial, Expr.wf_pow (x := Expr.var) trivial _, fraction_pow_var_ne_zero _⟩

/-- A well-formed expression has nonzero denominator. -/
theorem Expr.fraction_snd_ne_zero {x : Expr} (hx : x.wf) : x.fraction.2 ≠ 0 := by
  induction x with
  | const r => simp [Expr.fraction]
  | var => simp [Expr.fraction]
  | add a b iha ihb | mul a b iha ihb => exact mul_ne_zero (iha hx.1) (ihb hx.2)
  | inv a _ => exact hx.2

/-- `Expr.rational` is additive on well-formed expressions. -/
theorem Expr.rational_add {x y : Expr} (hx : x.wf) (hy : y.wf) :
    (Expr.add x y).rational = x.rational + y.rational := by
  have h1' := RatFunc.algebraMap_ne_zero (Expr.fraction_snd_ne_zero hx)
  have h2' := RatFunc.algebraMap_ne_zero (Expr.fraction_snd_ne_zero hy)
  simp only [Expr.rational, Expr.fraction, map_mul, map_add]
  rw [div_add_div _ _ h1' h2', mul_comm (algebraMap (Polynomial ℚ) (RatFunc ℚ) x.fraction.2)
    (algebraMap (Polynomial ℚ) (RatFunc ℚ) y.fraction.1)]

/-- `Expr.rational` is multiplicative. -/
theorem Expr.rational_mul (x y : Expr) : (Expr.mul x y).rational = x.rational * y.rational := by
  simp only [Expr.rational, Expr.fraction, map_mul]
  rw [div_mul_div_comm]

/-- `Expr.rational` commutes with inversion. -/
theorem Expr.rational_inv (x : Expr) : (Expr.inv x).rational = x.rational⁻¹ := by
  simp only [Expr.rational, Expr.fraction]
  rw [inv_div]

/-- The rational function of a constant. -/
theorem Expr.rational_const (r : ℚ) : (Expr.const r).rational = RatFunc.C r := by
  simp [Expr.rational, Expr.fraction, RatFunc.algebraMap_C]

/-- The rational function of the variable is `q`. -/
theorem Expr.rational_var : Expr.var.rational = (RatFunc.X : RatFunc ℚ) := by
  simp [Expr.rational, Expr.fraction, RatFunc.algebraMap_X]

/-- `lawCoef` of the empty law is `0`. -/
theorem lawCoef_nil : lawCoef ([] : Law) = 0 := lawInterp_nil _

/-- `lawCoef` turns `lawScale x` into multiplication by the scalar `x.rational`. -/
theorem lawCoef_lawScale (x : Expr) (L : Law) :
    lawCoef (lawScale x L) = scalar x.rational * lawCoef L :=
  lawInterp_lawScale _ Expr.rational_mul x L

/-- `lawCoef` of an atom is its monomial `Z_{e,f}`. -/
private theorem lawCoef_lawAtom (e f : ℕ) :
    lawCoef (lawAtom e f) = AddMonoidAlgebra.single ({(e, f)} : FactorType) (1 : RatFunc ℚ) := by
  simp [lawCoef, lawAtom, Expr.rational_const]

/-- `lawCoef` sends `flatMap` to the sum of the pieces. -/
theorem lawCoef_flatMap {α : Type} (xs : List α) (g : α → Law) :
    lawCoef (xs.flatMap g) = (xs.map fun u ↦ lawCoef (g u)).sum :=
  lawInterp_flatMap _ xs g

/-! ### The cluster series -/

/-- The constant term of the cluster series `B_a` is `1`. -/
theorem coeff_zero_clusterSer (a : ℕ) : PowerSeries.coeff 0 (clusterSer a) = 1 := by
  simp [clusterSer, PowerSeries.coeff_mk]

/-- The constant term of the cluster series `B_a` is `1`. -/
theorem constantCoeff_clusterSer (a : ℕ) : PowerSeries.constantCoeff (clusterSer a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_clusterSer]

/-- The coefficient of `x^{n+1}` in `B_a` is the law of `S(a;n+1)`. -/
theorem coeff_succ_clusterSer (a n : ℕ) :
    PowerSeries.coeff (n + 1) (clusterSer a) = lawCoef (stateLaw (State.single a (n + 1))) := by
  simp [clusterSer, PowerSeries.coeff_mk]

/-- The degree-one coefficient of `B_a` is `Z_{a,1}`. -/
theorem coeff_one_clusterSer (a : ℕ) :
    PowerSeries.coeff 1 (clusterSer a) = AddMonoidAlgebra.single ({(a, 1)} : FactorType) 1 := by
  rw [coeff_succ_clusterSer a 0, zero_add, terminal_law, lawCoef_lawAtom]

/-- The Euler transforms `eulerSer ε a` have constant term `1`. -/
theorem constantCoeff_eulerSer (ε : ℤ) (a : ℕ) : PowerSeries.constantCoeff (eulerSer ε a) = 1 :=
  constantCoeff_pPow _ _

/-- The Euler transforms `eulerSer ε a` have constant term `1`. -/
theorem coeff_zero_eulerSer (ε : ℤ) (a : ℕ) : PowerSeries.coeff 0 (eulerSer ε a) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_eulerSer]

private theorem coeff_dilate_recipSer_clusterSer (a m : ℕ) :
    PowerSeries.coeff m (dilate (recipSer (clusterSer a))) =
      qpow (m : ℤ) * recipCoef (PowerSeries.coeff m (clusterSer a)) := by
  rw [coeff_dilate, coeff_recipSer]

/-- The constant term of `S(B_aᵛ)` is `1`. -/
theorem coeff_zero_dilate_recipSer_clusterSer (a : ℕ) :
    PowerSeries.coeff 0 (dilate (recipSer (clusterSer a))) = 1 := by
  rw [coeff_dilate_recipSer_clusterSer, coeff_zero_clusterSer, map_one, mul_one, Nat.cast_zero,
    qpow_zero]

/-- The degree-one coefficient of `S(B_aᵛ)` is `q Z_{a,1}`. -/
theorem coeff_one_dilate_recipSer_clusterSer (a : ℕ) :
    PowerSeries.coeff 1 (dilate (recipSer (clusterSer a))) =
      qpow 1 * AddMonoidAlgebra.single ({(a, 1)} : FactorType) 1 := by
  rw [coeff_dilate_recipSer_clusterSer, coeff_one_clusterSer, recipCoef_single, map_one]
  rfl

/-- If `G_b ≡ S(B_bᵛ)` through degree `M` for every `b > 0`, then `S(P_sᵛ) · P_s ≡ 1` through
degree `M`, where `P_s = eulerSer (-1) s`. -/
theorem dilate_recipSer_eulerSer_mul_scongr_one (M s : ℕ) (hs : 0 < s) (hS : ∀ a : ℕ, 0 < a →
    SCongr M (eulerSer 0 a) (dilate (recipSer (clusterSer a)))) :
    SCongr M (dilate (recipSer (eulerSer (-1) s)) * eulerSer (-1) s) 1 := by
  set B := clusterSer s with hBdef
  have hB : PowerSeries.constantCoeff B = 1 := constantCoeff_clusterSer s
  -- Step 1: `P_s B_s = G_s`.
  have h1 : eulerSer (-1) s * B = eulerSer 0 s := by
    unfold eulerSer
    rw [← hBdef]
    conv_lhs => arg 2; rw [← pPow_one B hB]
    rw [pPow_mul_pPow]
    congr 1
    push_cast; ring
  -- Step 2: apply `S ∘ v`.
  have h2 : dilate (recipSer (eulerSer (-1) s)) * dilate (recipSer B) =
      dilate (recipSer (eulerSer 0 s)) := by
    rw [← h1, recipSer_mul, dilate_mul]
  -- Step 3: `S(G_sᵛ) ≡ B_s`.
  have hG := hS s hs
  have h3a : SCongr M (recipSer (eulerSer 0 s)) (recipSer (dilate (recipSer B))) := by
    intro m hm
    rw [coeff_recipSer, coeff_recipSer, hG m hm]
  rw [recipSer_dilate, recipSer_recipSer] at h3a
  have h3 : SCongr M (dilate (recipSer (eulerSer 0 s))) B := by
    simpa only [dilate_codilate] using h3a.dilate
  -- Step 4: cancel `B_s`.
  set D := dilate (recipSer (eulerSer (-1) s))
  have h4' : SCongr M (dilate (recipSer (eulerSer 0 s))) (D * (eulerSer (-1) s * B)) := by
    rw [h1, ← h2]; exact (SCongr.refl M D).mul hG.symm
  refine SCongr.of_mul_right hB ?_
  rw [one_mul, mul_assoc]
  exact h4'.symm.trans h3

/-- `lawCoef` is multiplicative on finite products `lawProd`. -/
theorem lawCoef_lawProd (Ls : List Law) : lawCoef (lawProd Ls) = (Ls.map lawCoef).prod :=
  lawInterp_lawProd _ Expr.rational_mul (by simp [Expr.rational_const]) Ls

/-- `B_a = P_{1/q}(G_a)`: the Euler transform with parameter `q` is inverted by the plethystic
power `1/q`. -/
theorem clusterSer_eq_pPow (a : ℕ) :
    clusterSer a = pPow (RatFunc.X : RatFunc ℚ)⁻¹ (eulerSer 0 a) := by
  rw [eulerSer, Int.cast_zero, add_zero, pPow_pPow, inv_mul_cancel₀ RatFunc.X_ne_zero,
    pPow_one _ (constantCoeff_clusterSer a)]

/-- `S(G_aᵛ) = P_{1/q}(S(B_aᵛ))`. -/
theorem dilate_recipSer_eulerSer_eq_pPow (a : ℕ) :
    dilate (recipSer (eulerSer 0 a)) =
      pPow (RatFunc.X : RatFunc ℚ)⁻¹ (dilate (recipSer (clusterSer a))) := by
  have hR : PowerSeries.constantCoeff (recipSer (clusterSer a)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_recipSer,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_clusterSer, map_one]
  rw [eulerSer, Int.cast_zero, add_zero, recipSer_pPow _ _ (constantCoeff_clusterSer a),
    recipRat_X, dilate_pPow _ _ hR]

/-- `Expr.rational` is additive on sums of well-formed expressions. -/
theorem Expr.rational_sum {xs : List Expr} (h : ∀ z ∈ xs, z.wf) :
    (Expr.sum xs).rational = (xs.map Expr.rational).sum := by
  induction xs with
  | nil => simpa [Expr.sum] using Expr.rational_const 0
  | cons a t ih =>
    have ht : ∀ z ∈ t, z.wf := fun z hz ↦ h z (by simp [hz])
    change (Expr.add a (Expr.sum t)).rational = _
    rw [Expr.rational_add (h a (by simp)) (Expr.wf_sum ht), ih ht]; simp

/-- `Expr.rational` is multiplicative on products. -/
private theorem Expr.rational_prod (xs : List Expr) :
    (Expr.prod xs).rational = (xs.map Expr.rational).prod := by
  induction xs with
  | nil => simpa [Expr.prod] using Expr.rational_const 1
  | cons a t ih =>
    change (Expr.mul a (Expr.prod t)).rational = _
    rw [Expr.rational_mul, ih]; simp

/-- `Expr.rational` commutes with powers. -/
theorem Expr.rational_pow (x : Expr) (n : ℕ) : (Expr.pow x n).rational = x.rational ^ n := by
  induction n with
  | zero => simpa [Expr.pow] using Expr.rational_const 1
  | succ k ih =>
    change (Expr.mul (Expr.pow x k) x).rational = _
    rw [Expr.rational_mul, ih, pow_succ]

private theorem Expr.rational_neg (x : Expr) : (Expr.neg x).rational = - x.rational := by
  change (Expr.mul (Expr.const (-1)) x).rational = _
  rw [Expr.rational_mul, Expr.rational_const]; simp

/-- `Expr.rational` is additive on differences of well-formed expressions. -/
theorem Expr.rational_sub {x y : Expr} (hx : x.wf) (hy : y.wf) :
    (Expr.sub x y).rational = x.rational - y.rational := by
  change (Expr.add x y.neg).rational = _
  rw [Expr.rational_add hx (show (Expr.neg y).wf from ⟨trivial, hy⟩), Expr.rational_neg,
    sub_eq_add_neg]

/-- The rational function of `eminusOne` is `q - 1`. -/
theorem rational_eminusOne : eminusOne.rational = (RatFunc.X : RatFunc ℚ) - 1 := by
  change (Expr.sub Expr.var (Expr.const 1)).rational = _
  rw [Expr.rational_sub (x := Expr.var) (y := Expr.const 1) trivial trivial, Expr.rational_var,
    Expr.rational_const]
  simp

/-- The rational function of the divisor count of a pattern `m`: a product over rows `i` of
generalized binomial coefficients in `availablePoints ε (i+1)`. -/
theorem rational_divisorCount (N : ℕ) (ε : ℤ) (m : Pattern N) :
    (divisorCount ε m).rational = ∏ i : Fin N, ((∏ j ∈ Finset.range (∑ j : Fin N, (m (i, j)).val),
        ((availablePoints ε (i.val + 1)).rational - RatFunc.C (j : ℚ))) *
        RatFunc.C (1 / (∏ j : Fin N, ((Nat.factorial (m (i, j)).val : ℕ) : ℚ)))) := by
  have hfall : ∀ (x : Expr), x.wf → ∀ k : ℕ, (falling x k).rational =
      ∏ j ∈ Finset.range k, (x.rational - RatFunc.C (j : ℚ)) := by
    intro x hx k
    unfold falling
    have hl : (do let a ← List.range k; pure (a : ℚ) : List ℚ) =
        (List.range k).map (fun a : ℕ ↦ (a : ℚ)) := by
      simp only [bind, List.flatMap]
      induction List.range k <;> simp_all
    rw [hl, (Expr.rational_prod _), List.map_map, List.map_map]
    have hc : List.map ((Expr.rational ∘ fun j ↦ x.sub (Expr.const j)) ∘ fun a : ℕ ↦ (a : ℚ))
        (List.range k)
        = List.map (fun j : ℕ ↦ x.rational - RatFunc.C (j : ℚ)) (List.range k) := by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      rw [Expr.rational_sub hx (by simp [Expr.wf]),
        (Expr.rational_const (j:ℚ))]
    rw [hc]
    rw [Finset.prod_eq_multiset_prod, Finset.range_val]
    rfl
  unfold divisorCount
  rw [(Expr.rational_prod _), List.map_map]
  rw [← Finset.prod_map_toList]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  rw [Expr.rational_mul, hfall _ (wf_availablePoints _ _), Expr.rational_const]

/-- The degree-`n` coefficient of the family expansion of
`prod_formalPow_adamsSer_clusterSer_scongr` is the
pattern sum `patternSum ε a n n`. -/
theorem coeff_euler_families_eq_patternSum (ε : ℤ) (a n : ℕ) :
    PowerSeries.coeff n (∑ K : Fin n → Fin n → Fin (n + 1),
        PowerSeries.C (scalar (∏ i : Fin n, ((∏ j ∈ Finset.range (∑ r : Fin n, (K i r).val),
        ((availablePoints ε (i.val + 1)).rational - RatFunc.C (j : ℚ))) *
        RatFunc.C ((∏ r : Fin n, ((Nat.factorial (K i r).val : ℕ) : ℚ))⁻¹)))) *
        (PowerSeries.C (∏ i : Fin n, ∏ r : Fin n, (adamsCoef (i.val + 1)
        (lawCoef (stateLaw (State.single a (r.val + 1))))) ^ (K i r).val) *
        (PowerSeries.X : Ser) ^ (∑ i : Fin n, (i.val + 1) * ∑ r : Fin n, (r.val + 1) *
        (K i r).val))) = patternSum ε a n n := by
  rw [map_sum]
  simp_rw [← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul_X_pow]
  rw [← Finset.sum_filter, patternSum]
  refine Finset.sum_equiv (Equiv.curry _ _ _).symm ?_ ?_
  · intro K
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, patternWeight, Equiv.curry_symm_apply,
      Function.uncurry_apply_pair, Fintype.sum_prod_type, Finset.mul_sum]
    have e : (∑ x : Fin n, ∑ i : Fin n, (x.val + 1) * ((i.val + 1) * (K x i).val))
        = ∑ x : Fin n, ∑ i : Fin n, (x.val + 1) * (i.val + 1) * (K x i).val :=
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [e]; exact eq_comm
  · intro K _
    rw [scalar_mul_eq_smul, rational_divisorCount]
    simp only [Equiv.curry_symm_apply, Function.uncurry_apply_pair, Fintype.prod_prod_type, one_div]

/-- For a well-formed law, the `σ`-coefficient of `lawCoef L` is the rational function of
`lawCoeff L σ`. -/
theorem coeff_lawCoef (L : Law) (hL : LawWf L) (σ : FactorType) :
    (lawCoef L).coeff σ = (lawCoeff L σ).rational := by
  have hw : ∀ z ∈ L.map (fun z ↦ if z.1 = σ then z.2 else Expr.const 0), z.wf := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp he
    by_cases h : z.1 = σ
    · simp only [h, if_true]; exact hL z hz
    · simp only [h, if_false]; simp [Expr.wf]
  unfold lawCoeff
  rw [(Expr.rational_sum) hw]
  clear hw
  induction L with
  | nil => simp [lawCoef]
  | cons z L ih =>
    have := ih (fun w hw ↦ hL w (List.mem_cons_of_mem _ hw))
    simp only [lawCoef, List.map_cons, List.sum_cons] at this ⊢
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, this]
    congr 1
    by_cases h : z.1 = σ
    · subst h; simp [AddMonoidAlgebra.coeff_single]
    · simp only [h, if_false]
      rw [(Expr.rational_const 0)]
      simp [AddMonoidAlgebra.coeff_single, h]

/-- Safe laws are well formed. -/
theorem LawSafe.lawWf {L : Law} (h : LawSafe L) : LawWf L :=
  fun z hz ↦ Expr.wf_of_safe _ 2 (h z hz 2 le_rfl)

/-- The `σ`-coefficient of a well-formed law is well formed. -/
theorem LawWf.wf_lawCoeff {L : Law} (h : LawWf L) (σ : FactorType) : (lawCoeff L σ).wf := by
  unfold lawCoeff
  refine Expr.wf_sum fun x hx ↦ ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact h z hz
  · trivial

end SurfaceBlowup
