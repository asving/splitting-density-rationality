/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Expression and law algebra, children of tangent patterns

Basic algebra of the formal expressions `Expr` (evaluation and safety of sums, products,
powers, substitutions, rational fractions) and of the formal laws `Law` (coefficients of
products, scalings, descents and flat maps), together with the elementary combinatorics of
the children of a tangent pattern and a handful of algebraic and topological facts used
throughout (coordinate cylinders, coprimality of reductions, ramification of local
extensions, finiteness of types of bounded degree).

## Main results

* `SurfaceBlowup.children_degree_identity`: `∑ e · deg(child) = deg(s)` over the children.
* `SurfaceBlowup.children_valid`: children of a valid state are valid.
* `SurfaceBlowup.expression_fraction`: evaluating a safe expression via its fraction.
* `SurfaceBlowup.lawInterp_lawMul`, `SurfaceBlowup.lawInterp_lawProd`: the interpretation of a
  law in a monoid algebra (shared by the numerical and the rational-function readings) is
  multiplicative.
* `SurfaceBlowup.law_coeff_mul`, `SurfaceBlowup.law_coeff_prod_formula`,
  `SurfaceBlowup.law_coeff_prod_descend`: coefficient formulas for products of laws.
* `SurfaceBlowup.law_coeff_nonneg_closure`: nonnegativity of coefficients is preserved by
  the law operations.
* `SurfaceBlowup.coordinate_cylinder_clopen`: congruence cylinders are clopen.
* `SurfaceBlowup.finite_flat_local_ramification_degree`: `e · f = rank` for finite flat
  local extensions.

Provenance: `Def_SurfaceBlowupV2_StateContact` and `Thm_SurfaceBlowupV2_*` for
children_degree_identity, children_residue_degree_pos, child_degree_le, children_valid,
coordinate_cylinder_clopen, coprime_of_monic_reduction_one, density_value_arith,
divisor_count_safe, expression_{fraction, pow_eval, pow_safe, prod_eval, regular, subst_eval,
subst_safe, sum_eval, sum_safe}, divisor_probability_safe,
finite_flat_local_ramification_degree, finite_types_of_degree, geometric_exit_sum,
image_measurable_of_continuousOn_injOn_compact, integral_local_extension_unique_prime,
law_coeff_{descend, flatMap, mul, prod_descend, prod_formula, scale, nonneg_closure},
law_safe_{descend, mul, scale}, list_get_fiber_card, monic_polynomial_degree,
other_children_count, prime_power_ge_two, projective_normalizer_positive,
rank_lt_of_degree_lt.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-! ### The first contact of a state -/

namespace State

/-- The contact of a state with the old boundary t = 0 (paper: c in S(a;c) and T(a,b;c,h));
for a child produced by one blowup step this is its contact r_P with the exceptional divisor E,
equation (5.1). -/
def firstContact : State → ℕ
  | .single _ c => c
  | .crossing _ _ c _ => c

end State

/-! ### Evaluation and safety of expressions -/

/-- Evaluation of a formal power: `(x ^ n)(q) = x(q) ^ n`. -/
theorem expression_pow_eval (x : Expr) (q : ℚ) (n : ℕ) :
    (x.pow n).eval q = (x.eval q)^n := by
  induction n with
  | zero => simp [Expr.pow, Expr.eval]
  | succ n ih => simp [Expr.pow, Expr.eval, ih, pow_succ]

/-- A formal power of a safe expression is safe. -/
theorem expression_pow_safe (x : Expr) (q : ℚ) (n : ℕ) (hx : x.safe q) :
    (x.pow n).safe q := by
  induction n with
  | zero => simp [Expr.pow, Expr.safe]
  | succ n ih => exact ⟨ih, hx⟩

/-- Evaluation of a formal product is the product of the evaluations. -/
theorem expression_prod_eval (xs : List Expr) (q : ℚ) :
    (Expr.prod xs).eval q = (xs.map (Expr.eval q)).prod := by
  induction xs <;> simp_all [Expr.prod, Expr.eval]

/-- A formal product of safe expressions is safe. -/
private theorem expression_prod_safe (xs : List Expr) (q : ℚ) (h : ∀ x ∈ xs, x.safe q) :
    (Expr.prod xs).safe q := by
  induction xs <;> simp_all [Expr.prod, Expr.safe]

/-- Evaluation of a formal sum is the sum of the evaluations. -/
theorem expression_sum_eval (xs : List Expr) (q : ℚ) :
    (Expr.sum xs).eval q = (xs.map (Expr.eval q)).sum := by
  induction xs <;> simp_all [Expr.sum, Expr.eval]

/-- A formal sum of safe expressions is safe. -/
theorem expression_sum_safe (xs : List Expr) (q : ℚ) (h : ∀ x ∈ xs, x.safe q) :
    (Expr.sum xs).safe q := by
  induction xs <;> simp_all [Expr.sum, Expr.safe]

/-- Evaluation commutes with substitution: `(x ∘ y)(q) = x(y(q))`. -/
private theorem expression_subst_eval (x y : Expr) (q : ℚ) :
    (x.subst y).eval q = x.eval (y.eval q) := by
  induction x <;> simp_all [Expr.subst, Expr.eval]

/-- If `y` is safe at `q` and `x` is safe at `y(q)`, then `x ∘ y` is safe at `q`. -/
private theorem expression_subst_safe (x y : Expr) (q : ℚ) (hy : y.safe q)
    (hx : x.safe (y.eval q)) :
    (x.subst y).safe q := by
  induction x with
  | const r => trivial
  | var => exact hy
  | add a b iha ihb => exact ⟨iha hx.1, ihb hx.2⟩
  | mul a b iha ihb => exact ⟨iha hx.1, ihb hx.2⟩
  | inv a iha => exact ⟨iha hx.1, by rw [expression_subst_eval]; exact hx.2⟩

/-- At a point where `x` is safe, the denominator of `x.fraction` does not vanish and `x`
evaluates to numerator over denominator. -/
theorem expression_fraction (x : Expr) (q : ℚ) (hx : x.safe q) :
    x.fraction.2.eval q ≠ 0 ∧ x.eval q = x.fraction.1.eval q / x.fraction.2.eval q := by
  induction x with
  | const r => simp [Expr.fraction, Expr.eval]
  | var => simp [Expr.fraction, Expr.eval]
  | add x y ihx ihy =>
    obtain ⟨hx1, hx2⟩ := ihx hx.1
    obtain ⟨hy1, hy2⟩ := ihy hx.2
    simp only [Expr.fraction, Expr.eval, Polynomial.eval_mul, Polynomial.eval_add]
    refine ⟨mul_ne_zero hx1 hy1, ?_⟩
    rw [hx2, hy2]
    field_simp
  | mul x y ihx ihy =>
    obtain ⟨hx1, hx2⟩ := ihx hx.1
    obtain ⟨hy1, hy2⟩ := ihy hx.2
    simp only [Expr.fraction, Expr.eval, Polynomial.eval_mul]
    exact ⟨mul_ne_zero hx1 hy1, by rw [hx2, hy2, div_mul_div_comm]⟩
  | inv x ihx =>
    obtain ⟨hs, hne⟩ := hx
    obtain ⟨hx1, hx2⟩ := ihx hs
    simp only [Expr.fraction, Expr.eval]
    exact ⟨fun h ↦ hne (by rw [hx2, h, zero_div]), by rw [hx2, inv_div]⟩

/-- The rational function of an expression is regular at every point where it is safe. -/
theorem expression_regular (x : Expr) (q : ℚ) (hx : x.safe q) :
    RegularAt x.rational q :=
  ⟨x.fraction.1, x.fraction.2, (expression_fraction x q hx).1, rfl⟩

/-- Positivity of the projective normalizer `1 + q + ⋯ + qⁿ` at `q ≥ 0`. -/
theorem projective_normalizer_positive (n : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    0 < (projectiveNormalizer n).eval q := by
  simp only [projectiveNormalizer, expression_sum_eval, List.map_map, Function.comp_def,
    expression_pow_eval, Expr.eval, List.range_succ_eq_map, List.map_cons, List.sum_cons,
    pow_zero]
  have : 0 ≤ ((List.range n).map fun x ↦ q ^ x.succ).sum :=
    List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨_, _, rfl⟩; positivity)
  linarith

/-- A prime power is at least `2`. -/
theorem prime_power_ge_two (q : ℕ) (hq : PrimePower q) :
    2 ≤ q := by
  obtain ⟨p, r, hp, hr, rfl⟩ := hq
  exact hp.two_le.trans (Nat.le_self_pow hr.ne' p)

/-! ### Children of tangent patterns -/

/-- The degree-weighted size of the "other" children is `a` times the pattern weight. -/
private theorem otherChildren_degree_sum {n : ℕ} (a : ℕ) (m : Pattern n) :
    ((otherChildren a m).map fun z ↦ z.1 * z.2.degree).sum = a * patternWeight m := by
  unfold otherChildren patternWeight
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map, Finset.mul_sum,
    Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  simp [List.map_replicate, List.sum_replicate, State.degree]
  ring

/-- Degree identity for one blowup step: for an allowed pattern, `∑ e · deg(child) = deg(s)`
over the children `(e, child)`. -/
theorem children_degree_identity (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) :
    ((children s P).map fun z ↦ z.1 * z.2.degree).sum = s.degree := by
  obtain ⟨hd, hsum, hrest⟩ := hP
  cases s with
  | single a c =>
    obtain ⟨hdc, hrx, hrt⟩ := hrest
    obtain ⟨W, hW⟩ : ∃ W, patternWeight P.other = W := ⟨_, rfl⟩
    simp only [children, List.map_append, List.sum_append, otherChildren_degree_sum, hW]
    rw [hW] at hsum
    simp only [State.degree]
    generalize P.d.val = D at *
    generalize P.rt.val = R at *
    generalize P.rx.val = X at *
    subst hrx
    obtain ⟨k, rfl⟩ : ∃ k, c = D + k := ⟨c - D, by omega⟩
    subst hsum
    split_ifs with h0
    · obtain rfl : k = 0 := by omega
      subst h0; simp
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [Nat.add_sub_cancel_left]; ring
  | crossing a b c h =>
    obtain ⟨hdc, hdh, hrt, hrx⟩ := hrest
    obtain ⟨W, hW⟩ : ∃ W, patternWeight P.other = W := ⟨_, rfl⟩
    simp only [children, List.map_append, List.sum_append, otherChildren_degree_sum, hW]
    rw [hW] at hsum
    simp only [State.degree]
    generalize P.d.val = D at *
    generalize P.rt.val = R at *
    generalize P.rx.val = X at *
    obtain ⟨k, rfl⟩ : ∃ k, c = D + k := ⟨c - D, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l, h = D + l := ⟨h - D, by omega⟩
    subst hsum
    simp only [Nat.add_sub_cancel_left]
    have e1 : R = 0 → k = 0 := by omega
    have e2 : X = 0 → l = 0 := by omega
    split_ifs <;>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
      (try (obtain rfl := e1 ‹R = 0›; subst ‹R = 0›)) <;>
      (try (obtain rfl := e2 ‹X = 0›; subst ‹X = 0›)) <;> ring

/-- Every child of a tangent pattern has positive residue degree. -/
theorem children_residue_degree_pos (s : State) (P : TangentPattern s.degree) (z : ℕ × State)
    (hz : z ∈ children s P) :
    0 < z.1 := by
  have hO : ∀ (a : ℕ) (m : Pattern s.degree), z ∈ otherChildren a m → 0 < z.1 := by
    intro a m h
    simp only [otherChildren, List.mem_flatMap] at h
    obtain ⟨ij, _, h⟩ := h
    simp [List.eq_of_mem_replicate h]
  cases s <;> simp only [children, List.mem_append] at hz
  · exact hz.elim (fun hz ↦ by split_ifs at hz <;> simp_all) (hO _ _)
  · exact hz.elim (fun hz ↦ by rcases hz with hz | hz <;> split_ifs at hz <;> simp_all) (hO _ _)

/-- Each child of an allowed pattern has degree at most that of the parent state. -/
theorem child_degree_le (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) (z : ℕ × State) (hz : z ∈ children s P) :
    z.2.degree ≤ s.degree := by
  calc z.2.degree ≤ z.1*z.2.degree :=
        Nat.le_mul_of_pos_left _ (children_residue_degree_pos s P z hz)
    _ ≤ ((children s P).map fun z ↦ z.1*z.2.degree).sum :=
        List.single_le_sum (by simp) _ (List.mem_map.2 ⟨z, hz, rfl⟩)
    _ = _ := children_degree_identity s hs P hP

/-- Children of an allowed pattern on a valid state are valid states. -/
theorem children_valid (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) (z : ℕ × State) (hz : z ∈ children s P) :
    z.2.Valid := by
  have other : ∀ (a : ℕ) (m : Pattern s.degree), 0 < a → z ∈ otherChildren a m → z.2.Valid := by
    intro a m ha h
    simp only [otherChildren, List.mem_flatMap, List.mem_replicate] at h
    obtain ⟨ij, _, _, rfl⟩ := h
    exact ⟨ha, Nat.succ_pos _⟩
  obtain ⟨hd, hsum, hrest⟩ := hP
  cases s with
  | single a c =>
    obtain ⟨ha, hc⟩ := hs
    obtain ⟨hdc, hrx, hrt⟩ := hrest
    simp only [children, List.mem_append] at hz
    rcases hz with hz | hz
    · split_ifs at hz with h0
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        exact ⟨ha, ha, Nat.pos_of_ne_zero h0, by have := hrt.mp (Nat.pos_of_ne_zero h0); omega⟩
    · exact other a _ ha hz
  | crossing a b c h =>
    obtain ⟨ha, hb, hc, hh⟩ := hs
    obtain ⟨hdc, hdh, hrt, hrx⟩ := hrest
    simp only [children, List.mem_append] at hz
    rcases hz with (hz | hz) | hz
    · split_ifs at hz with h0
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        have := hrt.mp (Nat.pos_of_ne_zero h0)
        exact ⟨by omega, ha, Nat.pos_of_ne_zero h0, by omega⟩
    · split_ifs at hz with h0
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        have := hrx.mp (Nat.pos_of_ne_zero h0)
        exact ⟨by omega, hb, Nat.pos_of_ne_zero h0, by omega⟩
    · exact other (a+b) _ (by omega) hz

/-- Counting the "other" children of residue degree `δ` and contact `r` of a unit-weight
pattern, their shape, and their total number. -/
theorem other_children_count (n : ℕ) (m : Pattern n) (δ r : ℕ) :
    List.count (δ, State.single 1 r) (otherChildren 1 m) =
        (if h : 1 ≤ δ ∧ δ ≤ n ∧ 1 ≤ r ∧ r ≤ n then
          (m (⟨δ - 1, Nat.sub_one_lt_of_le h.1 h.2.1⟩,
            ⟨r - 1, Nat.sub_one_lt_of_le h.2.2.1 h.2.2.2⟩)).val else 0) ∧
      (∀ z ∈ otherChildren 1 m,
        ∃ ij : Fin n × Fin n, z = (ij.1.val + 1, State.single 1 (ij.2.val + 1))) ∧
      (otherChildren 1 m).length = ∑ ij : Fin n × Fin n, (m ij).val := by
  refine ⟨?_, fun z hz ↦ ?_, ?_⟩
  · unfold otherChildren
    rw [List.count_flatMap]
    simp only [Function.comp_def, List.count_replicate, beq_iff_eq]
    rw [Finset.sum_map_toList (Finset.univ : Finset (Fin n × Fin n))
      (fun ij ↦ if ((ij.1.val + 1, State.single 1 (ij.2.val + 1)) : ℕ × State) =
        (δ, State.single 1 r) then (m ij).val else 0)]
    split_ifs with h
    · rw [Finset.sum_eq_single (⟨δ - 1, by omega⟩, ⟨r - 1, by omega⟩)]
      · rw [if_pos]
        simp only [Prod.mk.injEq, State.single.injEq]
        exact ⟨by omega, trivial, by omega⟩
      · intro b _ hb
        rw [if_neg]
        simp only [Prod.mk.injEq, State.single.injEq]
        rintro ⟨h1, -, h2⟩
        apply hb
        ext <;> simp <;> omega
      · simp
    · refine Finset.sum_eq_zero fun ij _ ↦ if_neg ?_
      simp only [Prod.mk.injEq, State.single.injEq]
      have := ij.1.isLt
      have := ij.2.isLt
      omega
  · simp only [otherChildren, List.mem_flatMap] at hz
    obtain ⟨ij, _, h⟩ := hz
    exact ⟨ij, (List.mem_replicate.mp h).2⟩
  · simp [otherChildren, List.length_flatMap, Finset.sum_map_toList]

/-- Among valid states, smaller degree forces smaller rank. -/
theorem rank_lt_of_degree_lt (s u : State) (hu : u.Valid)
    (h : u.degree < s.degree) :
    u.rank < s.rank := by
  have ht : u.tag ≤ 1 := by cases u <;> simp [State.tag]
  have h1 : u.degree - u.weight ≤ u.degree := Nat.sub_le _ _
  unfold State.rank
  have h3 : (u.degree + 1) * (u.degree + 1) ≤ s.degree * s.degree := Nat.mul_le_mul h h
  nlinarith

/-! ### Density values and safety of divisor counts -/

/-- Arithmetic of `densityValue` (multiplicativity, additivity, values on `q⁻ⁿ` and `1`,
finiteness and positivity) and positivity of state volumes at an integer `q ≥ 2`. -/
theorem density_value_arith (q : ℕ) (hq : 2 ≤ q) (x y : Expr) (hx : 0 ≤ x.eval q)
    (hy : 0 ≤ y.eval q) (n : ℕ) (s : State) (hs : s.Valid) :
    densityValue (.mul x y) q = densityValue x q * densityValue y q ∧
      densityValue (.add x y) q = densityValue x q + densityValue y q ∧
      densityValue (.inv (.pow .var n)) q = (q : ℝ≥0∞)⁻¹ ^ n ∧
      densityValue (.const 1) q = 1 ∧ densityValue x q ≠ ⊤ ∧
      (0 < x.eval q → densityValue x q ≠ 0) ∧ 0 < (stateVolume s).eval q ∧
      (stateVolume s).eval q ≠ 0 := by
  have hqpos : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have hvol : 0 < (stateVolume s).eval (q : ℚ) := by
    cases s with
    | single a c =>
      simp only [stateVolume, Expr.eval, expression_pow_eval]
      positivity
    | crossing a b c h =>
      have h1 : (1 : ℚ) < q := by exact_mod_cast (by omega : 1 < q)
      simp only [stateVolume, Expr.eval, expression_pow_eval, eminusOne, Expr.sub, Expr.neg]
      exact mul_pos (by linarith) (inv_pos.2 (pow_pos hqpos _))
  refine ⟨?_, ?_, ?_, ?_, ENNReal.ofReal_ne_top,
    fun h ↦ (ENNReal.ofReal_pos.2 (by exact_mod_cast h)).ne', hvol, hvol.ne'⟩
  · simp only [densityValue, Expr.eval]
    push_cast
    exact ENNReal.ofReal_mul (by exact_mod_cast hx)
  · simp only [densityValue, Expr.eval]
    push_cast
    exact ENNReal.ofReal_add (by exact_mod_cast hx) (by exact_mod_cast hy)
  · simp only [densityValue, Expr.eval, expression_pow_eval]
    push_cast
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.inv_pow]
  · simp [densityValue, Expr.eval]

/-- Every divisor count expression is safe at every integer `q ≥ 2`. -/
theorem divisor_count_safe (n : ℕ) (offset : ℤ) (m : Pattern n) :
    (divisorCount offset m).allSafe := by
  intro q _
  have hav : ∀ δ, (availablePoints offset δ).safe q := by
    intro δ
    unfold availablePoints
    split_ifs
    · exact ⟨trivial, trivial⟩
    · refine ⟨trivial, expression_sum_safe _ _ ?_⟩
      simp only [List.mem_map]
      rintro _ ⟨j, _, rfl⟩
      exact ⟨trivial, expression_pow_safe _ _ _ trivial⟩
  refine expression_prod_safe _ _ ?_
  simp only [List.mem_map]
  rintro _ ⟨i, _, rfl⟩
  refine ⟨expression_prod_safe _ _ ?_, trivial⟩
  simp only [List.mem_map]
  rintro _ ⟨j, _, rfl⟩
  exact ⟨hav _, trivial, trivial⟩

/-- Every divisor probability expression is safe at every integer `q ≥ 2`. -/
theorem divisor_probability_safe (s : State) (d : ℕ) :
    (divisorProbability s d).allSafe := by
  intro q hq
  have hq' : (2:ℚ) ≤ q := by exact_mod_cast hq
  have hE : eminusOne.safe q := by
    simp [eminusOne, Expr.sub, Expr.neg, Expr.safe]
  have hEv : eminusOne.eval q = (q:ℚ) - 1 := by
    simp [eminusOne, Expr.sub, Expr.neg, Expr.eval]; ring
  have hV : ∀ n : ℕ, ((Expr.var).pow n).safe q ∧ ((Expr.var).pow n).eval q ≠ 0 := fun n ↦
    ⟨expression_pow_safe _ _ _ trivial, by
      simpa [expression_pow_eval, Expr.eval] using pow_ne_zero n (by linarith : (q:ℚ) ≠ 0)⟩
  have hP : ∀ n : ℕ, (eminusOne.pow n).safe q := fun n ↦ expression_pow_safe _ _ _ hE
  cases s with
  | single a c => exact ⟨hV _, hP _⟩
  | crossing a b c h =>
    simp only [divisorProbability, Expr.safe]
    refine ⟨hV _, ?_⟩
    split_ifs
    all_goals first
      | exact hP _
      | exact ⟨hE, by rw [hEv]; linarith⟩

/-! ### Coefficients of laws -/

/-- Scaling types by `δ > 0` is injective. -/
private theorem scaleType_injective {δ : ℕ} (hδ : 0 < δ) : Function.Injective (scaleType δ) := by
  apply Multiset.map_injective
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.injEq] at h ⊢
  exact ⟨h.1, Nat.eq_of_mul_eq_mul_left hδ h.2⟩

/-- The value of a law coefficient is the sum of the values of the matching entries. -/
private theorem lawCoeff_eval (L : Law) (σ : FactorType) (q : ℚ) :
    (lawCoeff L σ).eval q = (L.map fun z ↦ if z.1 = σ then z.2.eval q else 0).sum := by
  simp only [lawCoeff, expression_sum_eval, List.map_map]
  congr 1
  refine List.map_congr_left fun z _ ↦ ?_
  split_ifs <;> simp [Expr.eval, *]

/-- Coefficients of a descended law: `lawDescend δ L` has coefficient `L_τ(q^δ)` at
`scaleType δ τ` and vanishing coefficients at types not of this form. -/
theorem law_coeff_descend (δ : ℕ) (hδ : 0 < δ) (L : Law) (τ : FactorType) (q : ℚ) :
    (lawCoeff (lawDescend δ L) (scaleType δ τ)).eval q = (lawCoeff L τ).eval (q ^ δ) ∧
      ∀ σ : FactorType, (∀ τ' : FactorType, σ ≠ scaleType δ τ') →
        (lawCoeff (lawDescend δ L) σ).eval q = 0 := by
  refine ⟨?_, fun σ hσ ↦ ?_⟩
  · simp only [lawCoeff_eval, lawDescend, List.map_map]
    congr 1
    refine List.map_congr_left fun z _ ↦ ?_
    simp [(scaleType_injective hδ).eq_iff, expression_subst_eval, expression_pow_eval, Expr.eval]
  · rw [lawCoeff_eval]
    refine List.sum_eq_zero fun x hx ↦ ?_
    simp only [lawDescend, List.map_map, List.mem_map, Function.comp_def] at hx
    obtain ⟨z, -, rfl⟩ := hx
    exact if_neg fun e ↦ hσ z.1 e.symm

/-! ### Interpretation of laws in a monoid algebra -/

/-- The interpretation of a law along a valuation `v` of expressions, as the element
`Σ_{z ∈ L} v(z.2) · Z^{z.1}` of the monoid algebra `S[FactorType]`. Numerical evaluation at `q`
and the rational-function interpretation of the reciprocity branch are both of this form. -/
noncomputable def lawInterp {S : Type*} [Semiring S] (v : Expr → S) (L : Law) :
    AddMonoidAlgebra S FactorType :=
  (L.map fun z ↦ AddMonoidAlgebra.single z.1 (v z.2)).sum

section lawInterp

variable {S : Type*} [Semiring S] (v : Expr → S)

/-- The interpretation of the empty law is `0`. -/
theorem lawInterp_nil : lawInterp v [] = 0 := rfl

/-- The interpretation is additive on concatenation. -/
theorem lawInterp_append (L M : Law) : lawInterp v (L ++ M) = lawInterp v L + lawInterp v M := by
  simp [lawInterp]

/-- The interpretation sends a `flatMap` to the sum of the pieces. -/
theorem lawInterp_flatMap {α : Type} (xs : List α) (g : α → Law) :
    lawInterp v (xs.flatMap g) = (xs.map fun u ↦ lawInterp v (g u)).sum := by
  simp [lawInterp, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
    Function.comp_def]

/-- For a multiplicative valuation, the interpretation is multiplicative on `lawMul`. -/
theorem lawInterp_lawMul (hv : ∀ x y, v (.mul x y) = v x * v y) (L M : Law) :
    lawInterp v (lawMul L M) = lawInterp v L * lawInterp v M := by
  simp only [lawInterp, lawMul, List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_map, Function.comp_def, ← List.sum_map_mul_right]
  simp [← List.sum_map_mul_left, AddMonoidAlgebra.single_mul_single, hv]

/-- For a multiplicative valuation, the interpretation turns `lawScale x` into multiplication
by the scalar `v x`. -/
theorem lawInterp_lawScale (hv : ∀ x y, v (.mul x y) = v x * v y) (x : Expr) (L : Law) :
    lawInterp v (lawScale x L) = AddMonoidAlgebra.single 0 (v x) * lawInterp v L := by
  simp [lawInterp, lawScale, List.map_map, Function.comp_def, ← List.sum_map_mul_left,
    AddMonoidAlgebra.single_mul_single, hv]

/-- For a multiplicative valuation with `v 1 = 1`, the interpretation is multiplicative on
finite products `lawProd`. -/
theorem lawInterp_lawProd (hv : ∀ x y, v (.mul x y) = v x * v y) (h1 : v (.const 1) = 1)
    (Ls : List Law) : lawInterp v (lawProd Ls) = (Ls.map (lawInterp v)).prod := by
  induction Ls with
  | nil => simp [lawProd, lawOne, lawInterp, h1, AddMonoidAlgebra.one_def]
  | cons L Ls ih => rw [lawProd, List.foldr_cons, ← lawProd, lawInterp_lawMul v hv, ih]; rfl

/-- The coefficients of the interpretation: the sum of the values of the matching entries. -/
theorem lawInterp_coeff (L : Law) (σ : FactorType) :
    (lawInterp v L).coeff σ = (L.map fun z ↦ if z.1 = σ then v z.2 else 0).sum := by
  rw [lawInterp, ← AddMonoidAlgebra.coeffAddEquiv_apply, map_list_sum,
    ← Finsupp.applyAddHom_apply, map_list_sum]
  simp [List.map_map, Function.comp_def, Finsupp.single_apply]

/-- The interpretation has no coefficients at types that do not occur in the law. -/
private theorem lawInterp_coeff_eq_zero (L : Law) (τ : FactorType)
    (h : τ ∉ (L.map Prod.fst).toFinset) : (lawInterp v L).coeff τ = 0 := by
  rw [lawInterp_coeff]
  refine List.sum_eq_zero fun x hx ↦ ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  exact if_neg fun e ↦ h (List.mem_toFinset.2 (List.mem_map.2 ⟨z, hz, e⟩))

end lawInterp

/-- The value at `q` of a law coefficient is the coefficient of its numerical interpretation. -/
private theorem lawCoeff_eval_interp (L : Law) (σ : FactorType) (q : ℚ) :
    (lawCoeff L σ).eval q = (lawInterp (fun x ↦ x.eval q) L).coeff σ :=
  (lawCoeff_eval L σ q).trans (lawInterp_coeff _ L σ).symm

/-- Coefficients are additive under concatenation, vanish on the empty law, and sum over a
`flatMap`. -/
theorem law_coeff_flatMap (α : Type) (xs : List α) (f : α → Law) (L M : Law) (σ : FactorType)
    (q : ℚ) :
    (lawCoeff (L ++ M) σ).eval q = (lawCoeff L σ).eval q + (lawCoeff M σ).eval q ∧
      (lawCoeff ([] : Law) σ).eval q = 0 ∧
      (lawCoeff (xs.flatMap f) σ).eval q = (xs.map fun x ↦ (lawCoeff (f x) σ).eval q).sum := by
  simp only [lawCoeff_eval_interp, lawInterp_append, lawInterp_nil, lawInterp_flatMap,
    AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
    Finsupp.coe_add, Pi.add_apply, true_and]
  rw [← AddMonoidAlgebra.coeffAddEquiv_apply, map_list_sum, ← Finsupp.applyAddHom_apply,
    map_list_sum, List.map_map, List.map_map]
  rfl

/-- Coefficient formula for a product of two laws: a convolution over the types of `L`. -/
theorem law_coeff_mul (L M : Law) (σ : FactorType) (q : ℚ) :
    (lawCoeff (lawMul L M) σ).eval q = ∑ τ ∈ (L.map Prod.fst).toFinset,
      (if τ ≤ σ then (lawCoeff L τ).eval q * (lawCoeff M (σ - τ)).eval q else 0) := by
  simp only [lawCoeff_eval_interp]
  set f := lawInterp (fun x ↦ x.eval q) L with hf0
  have hf : f = ∑ τ ∈ (L.map Prod.fst).toFinset, AddMonoidAlgebra.single τ (f.coeff τ) := by
    ext τ
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finset.sum_ite_eq']
    split_ifs with h
    exacts [rfl, lawInterp_coeff_eq_zero _ L τ h]
  rw [lawInterp_lawMul (fun x ↦ x.eval q) (fun _ _ ↦ rfl), ← hf0]
  conv_lhs => rw [hf, Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  split_ifs with h
  · obtain ⟨ρ, rfl⟩ := exists_add_of_le h
    rw [AddMonoidAlgebra.coeff_single_mul_add, add_tsub_cancel_left]
  · exact AddMonoidAlgebra.coeff_single_mul_of_forall_add_ne _ _ fun d e ↦ h (e ▸ le_self_add)

/-- Splitting a sum over `piFinset t` on `Fin (n + 1)` into the first coordinate and the
tail. -/
private theorem sum_piFinset_succ (n : ℕ) (t : Fin (n + 1) → Finset FactorType)
    (F : (Fin (n + 1) → FactorType) → ℚ) :
    ∑ τ ∈ Fintype.piFinset t, F τ
      = ∑ τ₀ ∈ t 0, ∑ τ' ∈ Fintype.piFinset (fun i ↦ t i.succ), F (Fin.cons τ₀ τ') := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun τ ↦ (τ 0, Fin.tail τ)) (fun p ↦ Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hτ ⊢
    exact ⟨hτ 0, fun i ↦ hτ i.succ⟩
  · intro p hp
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hp ⊢
    exact fun i ↦ Fin.cases (by simpa using hp.1) (fun j ↦ by simpa using hp.2 j) i
  all_goals intros; simp

/-- Coefficient formula for a product of descended laws `∏ⱼ lawDescend δⱼ Lⱼ`. -/
theorem law_coeff_prod_descend (Ls : List (ℕ × Law)) (hδ : ∀ z ∈ Ls, 0 < z.1)
    (σ : FactorType) (q : ℚ) :
    (lawCoeff (lawProd (Ls.map fun z ↦ lawDescend z.1 z.2)) σ).eval q =
      ∑ τ ∈ Fintype.piFinset (fun j : Fin Ls.length ↦ ((Ls.get j).2.map Prod.fst).toFinset),
        (if σ = ∑ j, scaleType (Ls.get j).1 (τ j) then
          ∏ j, (lawCoeff (Ls.get j).2 (τ j)).eval (q ^ (Ls.get j).1) else 0) := by
  induction Ls generalizing σ with
  | nil =>
    simp [lawProd, lawOne, lawCoeff, expression_sum_eval, Fintype.piFinset_of_isEmpty,
      eq_comm, apply_ite, Expr.eval]
  | cons z Ls ih =>
    obtain ⟨δ, L⟩ := z
    have hδ0 : 0 < δ := hδ _ List.mem_cons_self
    have ih' := fun σ ↦ ih (fun w hw ↦ hδ w (List.mem_cons_of_mem _ hw)) σ
    rw [List.map_cons, lawProd, List.foldr_cons, ← lawProd, law_coeff_mul]
    have hmap : ((lawDescend δ L).map Prod.fst).toFinset
        = (L.map Prod.fst).toFinset.image (scaleType δ) := by
      ext x; simp [lawDescend]
    rw [hmap, Finset.sum_image fun x _ y _ h ↦ scaleType_injective hδ0 h]
    change _ = ∑ τ ∈ Fintype.piFinset (fun j : Fin (Ls.length + 1) ↦
      (((δ, L) :: Ls).get j).2.map Prod.fst |>.toFinset), _
    rw [sum_piFinset_succ]
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    rw [(law_coeff_descend δ hδ0 L ρ q).1]
    -- `Fin.sum_univ_succ` stated for `Fin (Ls.length + 1)`, to be used up to defeq
    have hs : ∀ f : Fin (Ls.length + 1) → FactorType,
        ∑ j, f j = f 0 + ∑ j : Fin Ls.length, f j.succ := Fin.sum_univ_succ
    have hp : ∀ f : Fin (Ls.length + 1) → ℚ, ∏ j, f j = f 0 * ∏ j : Fin Ls.length, f j.succ :=
      Fin.prod_univ_succ
    have hg : ∀ i : Fin Ls.length, ((δ, L) :: Ls).get i.succ = Ls.get i := fun i ↦ rfl
    split_ifs with hle
    · rw [ih', Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ' _ ↦ ?_
      erw [hs, hp]
      simp only [Fin.cons_zero, Fin.cons_succ, List.get_cons_zero, hg,
        tsub_eq_iff_eq_add_of_le hle, mul_ite, mul_zero, add_comm]
    · refine (Finset.sum_eq_zero fun τ' _ ↦ if_neg fun h ↦ ?_).symm
      erw [hs] at h
      simp only [Fin.cons_zero, List.get_cons_zero] at h
      exact hle (h ▸ le_self_add)

/-- Coefficient formula for a finite product of laws `∏ⱼ Dl j`, and vanishing of the
coefficients of a law at types that do not occur in it. -/
theorem law_coeff_prod_formula (L : ℕ) (Dl : Fin L → Law) (σ : FactorType) (q : ℚ) :
    ((lawCoeff (lawProd (List.ofFn Dl)) σ).eval q =
        ∑ τ ∈ Fintype.piFinset (fun j ↦ ((Dl j).map Prod.fst).toFinset),
          (if σ = ∑ j, τ j then ∏ j, (lawCoeff (Dl j) (τ j)).eval q else 0)) ∧
      ∀ (M : Law) (τ : FactorType), τ ∉ (M.map Prod.fst).toFinset →
        (lawCoeff M τ).eval q = 0 := by
  refine ⟨?_, fun M τ h ↦ ?_⟩
  · induction L generalizing σ with
    | zero =>
      simp [lawProd, lawOne, lawCoeff, expression_sum_eval, Fintype.piFinset_of_isEmpty,
        eq_comm, apply_ite, Expr.eval]
    | succ n ih =>
      rw [List.ofFn_succ, lawProd, List.foldr_cons, ← lawProd, law_coeff_mul, sum_piFinset_succ]
      refine Finset.sum_congr rfl fun τ₀ _ ↦ ?_
      rw [ih (fun i ↦ Dl i.succ)]
      split_ifs with hle
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ' _ ↦ ?_
        simp only [Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        simp only [tsub_eq_iff_eq_add_of_le hle, mul_ite, mul_zero, add_comm]
      · refine (Finset.sum_eq_zero fun τ' _ ↦ if_neg fun h ↦ hle ?_).symm
        rw [h, Fin.sum_univ_succ, Fin.cons_zero]
        exact le_self_add
  · rw [lawCoeff_eval_interp]
    exact lawInterp_coeff_eq_zero _ M τ h

/-- Coefficients of a scaled law: `(x · L)_σ = x · L_σ`. -/
theorem law_coeff_scale (x : Expr) (L : Law) (σ : FactorType) (q : ℚ) :
    (lawCoeff (lawScale x L) σ).eval q = x.eval q * (lawCoeff L σ).eval q := by
  rw [lawCoeff_eval_interp, lawCoeff_eval_interp,
    lawInterp_lawScale (fun x ↦ x.eval q) (fun _ _ ↦ rfl), AddMonoidAlgebra.coeff_single_zero_mul]

/-- Nonnegativity of law coefficients at `q` is preserved by scaling by nonnegative
expressions, products, finite products, flat maps and descents, and holds for atoms and the
unit law; the empty law has zero coefficients. -/
theorem law_coeff_nonneg_closure (q : ℚ) :
    (∀ (x : Expr) (L : Law), 0 ≤ x.eval q → (∀ σ : FactorType, 0 ≤ (lawCoeff L σ).eval q) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (lawScale x L) σ).eval q) ∧
    (∀ L M : Law, (∀ σ : FactorType, 0 ≤ (lawCoeff L σ).eval q) →
      (∀ σ : FactorType, 0 ≤ (lawCoeff M σ).eval q) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (lawMul L M) σ).eval q) ∧
    (∀ Ls : List Law, (∀ L ∈ Ls, (∀ σ : FactorType, 0 ≤ (lawCoeff L σ).eval q)) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (lawProd Ls) σ).eval q) ∧
    (∀ (α : Type) (xs : List α) (f : α → Law),
      (∀ x ∈ xs, ∀ σ : FactorType, 0 ≤ (lawCoeff (f x) σ).eval q) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (xs.flatMap f) σ).eval q) ∧
    (∀ (δ : ℕ), 0 < δ → ∀ L : Law, (∀ σ : FactorType, 0 ≤ (lawCoeff L σ).eval (q ^ δ)) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (lawDescend δ L) σ).eval q) ∧
    (∀ (a f : ℕ) (σ : FactorType), 0 ≤ (lawCoeff (lawAtom a f) σ).eval q) ∧
    (∀ σ : FactorType, 0 ≤ (lawCoeff lawOne σ).eval q) ∧
    (∀ σ : FactorType, (lawCoeff ([] : Law) σ).eval q = 0) := by
  have hmul : ∀ L M : Law, (∀ σ : FactorType, 0 ≤ (lawCoeff L σ).eval q) →
      (∀ σ : FactorType, 0 ≤ (lawCoeff M σ).eval q) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (lawMul L M) σ).eval q := by
    intro L M hL hM σ
    rw [law_coeff_mul]
    refine Finset.sum_nonneg fun τ _ ↦ ?_
    split_ifs
    · exact mul_nonneg (hL _) (hM _)
    · exact le_rfl
  have hone : ∀ σ : FactorType, 0 ≤ (lawCoeff lawOne σ).eval q := by
    intro σ
    simp only [lawCoeff_eval, lawOne, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> simp [Expr.eval]
  refine ⟨fun x L hx hL σ ↦ by rw [law_coeff_scale]; exact mul_nonneg hx (hL σ), hmul, ?_, ?_,
    ?_, ?_, hone, fun σ ↦ by simp [lawCoeff_eval]⟩
  · intro Ls
    induction Ls with
    | nil => exact fun _ ↦ hone
    | cons L Ls ih =>
      exact fun h ↦ hmul _ _ (h L (by simp)) (ih fun L' hL' ↦ h L' (by simp [hL']))
  · intro α xs f h σ
    rw [(law_coeff_flatMap α xs f [] [] σ q).2.2]
    refine List.sum_nonneg fun y hy ↦ ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact h x hx σ
  · intro δ hδ L h σ
    by_cases hs : ∃ τ, σ = scaleType δ τ
    · obtain ⟨τ, rfl⟩ := hs
      rw [(law_coeff_descend δ hδ L τ q).1]
      exact h τ
    · push Not at hs
      rw [(law_coeff_descend δ hδ L 0 q).2 σ hs]
  · intro a f σ
    simp only [lawCoeff_eval, lawAtom, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> simp [Expr.eval]

/-- Descents of safe laws are safe. -/
theorem law_safe_descend (δ : ℕ) (hδ : 0 < δ) (L : Law) (hL : LawSafe L) :
    LawSafe (lawDescend δ L) := by
  intro z hz
  simp only [lawDescend, List.mem_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  intro q hq
  refine expression_subst_safe _ _ _ (expression_pow_safe _ _ _ trivial) ?_
  rw [expression_pow_eval]
  have : ((q:ℚ))^δ = ((q^δ : ℕ) : ℚ) := by push_cast; rfl
  change w.2.safe _
  simp only [Expr.eval]
  rw [this]
  exact hL w hw _ (hq.trans (Nat.le_self_pow (by omega) q))

/-- Products of safe laws are safe. -/
theorem law_safe_mul (L M : Law) (hL : LawSafe L) (hM : LawSafe M) :
    LawSafe (lawMul L M) := by
  intro z hz
  simp only [lawMul, List.mem_flatMap, List.mem_map] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  exact fun q hq ↦ ⟨hL a ha q hq, hM b hb q hq⟩

/-- Scaling a safe law by an everywhere-safe expression gives a safe law. -/
theorem law_safe_scale (x : Expr) (L : Law) (hx : x.allSafe) (hL : LawSafe L) :
    LawSafe (lawScale x L) := by
  intro z hz
  simp only [lawScale, List.mem_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact fun q hq ↦ ⟨hx q hq, hL w hw q hq⟩

/-! ### Algebraic and topological facts -/

/-- For an `I`-adic topology, the congruence cylinders `{b | ∀ j, b j - a j ∈ I ^ L}` are
clopen (hence compact when `O` is compact), and their products are closed. -/
theorem coordinate_cylinder_clopen (O : Type) [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (I : Ideal O) (htop : IsAdic I) (L : ℕ) :
    (∀ (n : ℕ) (a : Fin n → O), IsOpen {b : Fin n → O | ∀ j, b j - a j ∈ I ^ L} ∧
        IsClosed {b : Fin n → O | ∀ j, b j - a j ∈ I ^ L}) ∧
      (∀ (n : ℕ) (a : Fin n → O), CompactSpace O →
        IsCompact {b : Fin n → O | ∀ j, b j - a j ∈ I ^ L}) ∧
      (∀ (ι : Type) (d : ι → ℕ) (c : ∀ i, Fin (d i) → O),
        IsClosed (Set.pi Set.univ fun i ↦ {b : Fin (d i) → O | ∀ j, b j - c i j ∈ I ^ L})) := by
  have hopen : IsOpen (((I ^ L : Ideal O).toAddSubgroup : AddSubgroup O) : Set O) :=
    AddSubgroup.isOpen_of_mem_nhds _ ((htop.hasBasis_nhds_zero).mem_of_mem (i := L) trivial)
  have hclosed := AddSubgroup.isClosed_of_isOpen _ hopen
  have hcyl : ∀ (n : ℕ) (a : Fin n → O), IsOpen {b : Fin n → O | ∀ j, b j - a j ∈ I ^ L} ∧
      IsClosed {b : Fin n → O | ∀ j, b j - a j ∈ I ^ L} := by
    intro n a
    have e : {b : Fin n → O | ∀ j, b j - a j ∈ I ^ L} = ⋂ j, (fun b : Fin n → O ↦ b j - a j) ⁻¹'
        (((I ^ L : Ideal O).toAddSubgroup : AddSubgroup O) : Set O) := by
      ext b; simp
    have hc : ∀ j, Continuous fun b : Fin n → O ↦ b j - a j := fun j ↦
      (continuous_apply j).sub continuous_const
    rw [e]
    exact ⟨isOpen_iInter_of_finite fun j ↦ hopen.preimage (hc j),
      isClosed_iInter fun j ↦ hclosed.preimage (hc j)⟩
  exact ⟨hcyl, fun n a _ ↦ (hcyl n a).2.isCompact,
    fun ι d c ↦ isClosed_set_pi fun i _ ↦ (hcyl (d i) (c i)).2⟩

open Polynomial in
/-- Over a discrete valuation ring `R` with fraction field `K`, a monic polynomial `A` and a
polynomial `B` reducing to `1` modulo the maximal ideal are coprime over `K`. -/
theorem coprime_of_monic_reduction_one (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A B : Polynomial R)
    (hA : A.Monic) (hB : B.map (IsLocalRing.residue R) = 1) :
    IsCoprime (A.map (algebraMap R K)) (B.map (algebraMap R K)) := by
  classical
  have hinj := IsFractionRing.injective R K
  by_contra hnc
  set A' := A.map (algebraMap R K)
  set B' := B.map (algebraMap R K)
  have hd : ¬ IsUnit (EuclideanDomain.gcd A' B') := by
    rwa [EuclideanDomain.gcd_isUnit_iff]
  have hd0 : EuclideanDomain.gcd A' B' ≠ 0 := fun h ↦
    (hA.map _).ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  obtain ⟨h, hirr, hdvd⟩ := WfDvdMonoid.exists_irreducible_factor hd hd0
  set g := C (h.leadingCoeff)⁻¹ * h
  have hlc : h.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hirr.ne_zero
  have hgm : g.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hgh : g ∣ h := ⟨C h.leadingCoeff, by
    rw [mul_comm, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]⟩
  have hgA : g ∣ A' := hgh.trans (hdvd.trans (EuclideanDomain.gcd_dvd_left _ _))
  have hgB : g ∣ B' := hgh.trans (hdvd.trans (EuclideanDomain.gcd_dvd_right _ _))
  have hgdeg : 0 < g.natDegree := by
    rw [natDegree_C_mul (inv_ne_zero hlc), natDegree_pos_iff_degree_pos]
    exact degree_pos_of_irreducible hirr
  obtain ⟨h₀, hh₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hA hgA
  rw [hgm.leadingCoeff, C_1, mul_one] at hh₀
  have hh₀m : h₀.Monic := monic_of_injective hinj (hh₀ ▸ hgm)
  have hdeg : h₀.natDegree = g.natDegree := by
    rw [← hh₀, natDegree_map_eq_of_injective hinj]
  have hh₀B : h₀ ∣ B := by
    rw [← map_dvd_map (algebraMap R K) hinj hh₀m, hh₀]; exact hgB
  have hu : IsUnit (h₀.map (IsLocalRing.residue R)) :=
    isUnit_of_dvd_one (hB ▸ Polynomial.map_dvd (IsLocalRing.residue R) hh₀B)
  rw [(hh₀m.map _).isUnit_iff] at hu
  have := congrArg natDegree hu
  rw [hh₀m.natDegree_map, natDegree_one] at this
  omega

/-- For an integral extension of local rings, the maximal ideal of `B` lies over that of `O`,
and it is the only prime of `B` lying over it. -/
theorem integral_local_extension_unique_prime (O B : Type) [CommRing O] [IsLocalRing O]
    [CommRing B] [IsLocalRing B] [Algebra O B] [Algebra.IsIntegral O B] :
    (IsLocalRing.maximalIdeal B).comap (algebraMap O B) = IsLocalRing.maximalIdeal O ∧
      ∀ Q : Ideal B, Q.IsPrime → Q.comap (algebraMap O B) = IsLocalRing.maximalIdeal O →
        Q = IsLocalRing.maximalIdeal B := by
  refine ⟨IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _),
    fun Q hQ hc ↦ ?_⟩
  have hm : (Q.comap (algebraMap O B)).IsMaximal := by rw [hc]; infer_instance
  exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q hm)

/-- For a finite flat extension of local rings `O → B`, `e · f = [B : O]`. -/
theorem finite_flat_local_ramification_degree (O B : Type) [CommRing O] [IsDomain O]
    [IsLocalRing O] [CommRing B] [IsLocalRing B] [Algebra O B] [Module.Finite O B]
    [Module.Flat O B] :
    (IsLocalRing.maximalIdeal B).ramificationIdx O * (IsLocalRing.maximalIdeal B).inertiaDeg O =
      Module.finrank O B := by
  have : Algebra.IsIntegral O B := Algebra.IsIntegral.of_finite O B
  obtain ⟨hcomap, huniq⟩ := integral_local_extension_unique_prime O B
  let m : (IsLocalRing.maximalIdeal O).primesOver B :=
    ⟨IsLocalRing.maximalIdeal B, inferInstance, ⟨(Ideal.under_def _ _).trans hcomap |>.symm⟩⟩
  let : Unique ((IsLocalRing.maximalIdeal O).primesOver B) :=
    { default := m
      uniq := fun q ↦ Subtype.ext (huniq q.1 q.2.1 (q.2.2.over.symm)) }
  have := Ideal.sum_ramification_inertia_eq_finrank (IsLocalRing.maximalIdeal O) (S := B)
  rwa [Fintype.sum_unique,
    show (default : (IsLocalRing.maximalIdeal O).primesOver B) = m from Subsingleton.elim _ _]
    at this

/-- There are finitely many valid factorization types of a given degree. -/
theorem finite_types_of_degree (n : ℕ) :
    Set.Finite {σ : FactorType | ValidType σ ∧ typeDegree σ = n} := by
  set s : Finset (ℕ × ℕ) := Finset.range (n+1) ×ˢ Finset.range (n+1)
  refine Set.Finite.subset ((n • s.val).powerset.toFinset.finite_toSet) ?_
  rintro σ ⟨hv, hd⟩
  simp only [Multiset.mem_toFinset, Multiset.mem_powerset, Finset.mem_coe]
  have hmem : ∀ z ∈ σ, z.1 * z.2 ≤ n := fun z hz ↦ hd ▸
    Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun z : ℕ × ℕ ↦ z.1 * z.2) hz)
  have hcard : Multiset.card σ ≤ n := by
    rw [← hd, typeDegree]
    have : Multiset.card (σ.map fun z ↦ z.1 * z.2) • 1 ≤ (σ.map fun z ↦ z.1 * z.2).sum :=
      Multiset.card_nsmul_le_sum fun x hx ↦ by
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
        exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (hv z hz).1.ne' (hv z hz).2.ne')
    simpa using this
  refine Multiset.le_iff_count.2 fun z ↦ ?_
  rw [Multiset.count_nsmul]
  by_cases hz : z ∈ σ
  · have h1 := hv z hz
    have h2 := hmem z hz
    have hzs : z ∈ s := by
      have := Nat.le_mul_of_pos_right z.1 h1.2
      have := Nat.le_mul_of_pos_left z.2 h1.1
      simp only [s, Finset.mem_product, Finset.mem_range]
      omega
    rw [Multiset.count_eq_one_of_mem s.nodup hzs, mul_one]
    exact (Multiset.count_le_card _ _).trans hcard
  · simp [Multiset.count_eq_zero_of_notMem hz]

/-- Geometric series with an exit weight: `∑ⱼ λʲ G = G / (1 - λ)` for `0 ≤ λ < 1`. -/
theorem geometric_exit_sum (lam G : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    HasSum (fun j : ℕ ↦ lam^j * G) (G / (1 - lam)) := by
  have h : ‖lam‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hlam]
  rw [div_eq_inv_mul]
  exact (hasSum_geometric_of_norm_lt_one h).mul_right G

/-- The image of a measurable set under a map that is continuous and injective on a closed
subset of a compact space (into a Hausdorff space) is measurable. -/
theorem image_measurable_of_continuousOn_injOn_compact (X Y : Type) [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (f : X → Y) (C : Set X) (hC : IsClosed C)
    (hf : ContinuousOn f C) (hinj : Set.InjOn f C) (U : Set X) (hU : MeasurableSet U) :
    MeasurableSet (f '' (U ∩ C)) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  have hemb := (hf.domRestrict.isClosedEmbedding
    (Set.injOn_iff_injective.mp hinj)).measurableEmbedding
  have h := hemb.measurableSet_image.mpr (measurable_subtype_coe hU)
  rwa [Set.domRestrict_eq, Set.image_comp, Subtype.image_preimage_coe, Set.inter_comm] at h

/-- The number of positions at which a list takes the value `x` is `l.count x`. -/
theorem list_get_fiber_card (α : Type) [DecidableEq α] (l : List α) (x : α) :
    Nat.card {j : Fin l.length // l.get j = x} = l.count x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have e : {j : Fin (a :: l).length // (a :: l).get j = x} ≃
        {_u : Unit // a = x} ⊕ {j : Fin l.length // l.get j = x} :=
      { toFun := fun j ↦ Fin.cases (motive := fun i ↦ (a :: l).get i = x → _)
          (fun h ↦ Sum.inl ⟨(), h⟩) (fun i h ↦ Sum.inr ⟨i, h⟩) j.1 j.2
        invFun := fun
          | Sum.inl h => ⟨0, h.2⟩
          | Sum.inr h => ⟨Fin.succ h.1, h.2⟩
        left_inv := by
          rintro ⟨j, hj⟩
          induction j using Fin.cases <;> rfl
        right_inv := by
          rintro (h | h) <;> rfl }
    rw [Nat.card_congr e, Nat.card_sum, ih, List.count_cons]
    by_cases h : a = x
    · subst h
      simp [Nat.add_comm]
    · have : IsEmpty {_u : Unit // a = x} := ⟨fun u ↦ h u.2⟩
      simp [h]

/-- The polynomial `Xⁿ + ∑ aᵢ Xⁱ` is monic of degree `n`. -/
theorem monic_polynomial_degree (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (a : Fin n → O) :
    (monicPolynomial O a).Monic ∧ (monicPolynomial O a).natDegree = n := by
  have hdeg : (∑ i : Fin n, Polynomial.C (algebraMap O (BaseField O) (a i)) *
      Polynomial.X^i.val).degree < (n : WithBot ℕ) := by
    refine (Polynomial.degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2
      fun i _ ↦ (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.2 i.isLt))
  refine ⟨Polynomial.monic_X_pow_add hdeg, ?_⟩
  unfold monicPolynomial
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by simpa using hdeg)]
  simp

end SurfaceBlowup
