/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Main
import Tests.NonVacuity

/-!
# Regression guards for the universal density expressions

Pins the statement-level definitions of `SurfaceBlowup.Basic` (the recursion `stateLaw`, the global
laws and the universal expressions `monicExpr n σ`, `projectiveExpr n σ`) to independently known
numbers, and turns them, via `SurfaceBlowup.main_dvr`, into explicit density statements. Any change
to the definitions that alters these values breaks this file.

## Main results

* `SurfaceBlowup.Tests.monicExpr_two_eval`, `SurfaceBlowup.Tests.projectiveExpr_two_eval`: the
  quadratic expressions as rational functions of `q > 1`.
* `SurfaceBlowup.Tests.monicExpr_three_eval`: the cubic monic expressions for `q > 1`.
* `SurfaceBlowup.Tests.monicExpr_four_eval_two`, `SurfaceBlowup.Tests.projectiveExpr_four_eval_two`:
  all quartic values at `q = 2`.
* Point values, e.g. `SurfaceBlowup.Tests.monicExpr_three_totally_ramified_eval_three`
  (`10/121`), `SurfaceBlowup.Tests.monicExpr_four_totally_ramified_eval_two` (`107/1533`),
  `SurfaceBlowup.Tests.projectiveExpr_four_totally_ramified_eval_two` (`856/15841`).
* Density corollaries, e.g. `SurfaceBlowup.Tests.monicDensity_two_ramified` (`1/(q+1)` over every
  complete DVR with residue field of order `q`),
  `SurfaceBlowup.Tests.monicDensity_four_totally_ramified_of_card_eq_two`, and the end-to-end
  `SurfaceBlowup.Tests.monicDensity_powerSeries_zmod_two_four_totally_ramified` over `𝔽₂⟦X⟧`.

## Implementation notes

The expressions are not computable by brute force (`allowedPatterns` filters a Fintype of size
about `5^19` with classical decidability), so the values are computed by unfolding the recursion
state by state: the coefficient algebra of laws, a one-step unfolding of `stateLaw` (re-derived
here: fuel stability and the rank decrease of children), explicit enumerations of the allowed
tangent and residue patterns (children lists are computed by `decide` through an explicit
enumeration of the cells), and the laws of the small states `S(a;1)`, `S(a;2)`, `T(a,b;1,h)`,
`T(a,b;c,1)`, `T(1,1;2,2)`, `S(1;3)` and (at `q = 2`) `S(1;4)`. Final identities are checked as
linear combinations of type indicators. All of this is private and depends only on
`SurfaceBlowup.Basic` (plus `main_dvr` for the corollaries).

Provenance: port of the certified Prove2Me theorems `SurfaceBlowupV2.{quadratic_monic_formula,
quadratic_projective_formula, cubic_monic_formula, quartic_monic_law_at_two,
quartic_projective_law_at_two}` and their point-value corollaries, with their helper closure.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace SurfaceBlowup.Tests

/-- `coeffAt q L σ` is the value at `q` of the coefficient of the type `σ` in the law `L`. -/
local notation "coeffAt " q:max L:max σ:max => Expr.eval q (lawCoeff L σ)

/-- Sorts the types `K` of the indicators `indicator σ K` into a canonical form. -/
local macro "sort_types" : tactic => `(tactic| simp only [Multiset.insert_eq_cons,
  Multiset.singleton_add, Multiset.cons_add, zero_add, ← Multiset.cons_zero, Multiset.cons_swap])

-- `hygiene false`: the macro names private lemmas of this file declared further below.
set_option hygiene false in
/-- Evaluates coefficients of products of laws of children, terminal ones first. -/
local macro "simp_children" : tactic => `(tactic| simp only [childProd, List.map_cons,
  List.map_nil, stateLaw_terminal, lawDescend_lawAtom, lawProd_cons, lawProd_nil, coeff_mul_lawOne,
  coeff_descend_one, coeff_mul_atom, coeff_lawAtom, coeff_lawOne, ite_mem_erase, ite_add_zero,
  Multiset.cons_zero])

/-! ### Evaluating expressions -/

section Eval

private theorem eval_sum (q : ℚ) (xs : List Expr) :
    (Expr.sum xs).eval q = (xs.map (Expr.eval q)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [Expr.sum, List.foldr_cons, Expr.eval, ← Expr.sum, ih]; rfl

private theorem eval_prod (q : ℚ) (xs : List Expr) :
    (Expr.prod xs).eval q = (xs.map (Expr.eval q)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [Expr.prod, List.foldr_cons, Expr.eval, ← Expr.prod, ih]; rfl

private theorem eval_pow (q : ℚ) (x : Expr) (n : ℕ) : (x.pow n).eval q = x.eval q ^ n := by
  induction n with
  | zero => simp [Expr.pow, Expr.eval]
  | succ n ih => rw [Expr.pow, Expr.eval, ih, pow_succ]

private theorem eval_subst (q : ℚ) (x y : Expr) : (x.subst y).eval q = x.eval (y.eval q) := by
  induction x with
  | const r => rfl
  | var => rfl
  | add x z hx hz => simp only [Expr.subst, Expr.eval, hx, hz]
  | mul x z hx hz => simp only [Expr.subst, Expr.eval, hx, hz]
  | inv x hx => simp only [Expr.subst, Expr.eval, hx]

private theorem pointCount_eval (q : ℚ) (n : ℕ) : (pointCount n).eval q =
    1 / n * ∑ j ∈ n.divisors, ((ArithmeticFunction.moebius j : ℤ) : ℚ) * q ^ (n / j) := by
  simp only [pointCount, Expr.eval, eval_sum, List.map_map]
  rw [Finset.sum_map_toList]
  simp [Function.comp_def, Expr.eval, eval_pow]

private theorem pointCount_two (q : ℚ) : (pointCount 2).eval q = (q ^ 2 - q) / 2 := by
  rw [pointCount_eval, show Nat.divisors 2 = {1, 2} by decide]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

private theorem pointCount_three (q : ℚ) : (pointCount 3).eval q = (q ^ 3 - q) / 3 := by
  rw [pointCount_eval, show Nat.divisors 3 = {1, 3} by decide]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  ring

private theorem pointCount_four (q : ℚ) : (pointCount 4).eval q = (q ^ 4 - q ^ 2) / 4 := by
  have h4 : ArithmeticFunction.moebius 4 = 0 :=
    ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (k := 2) (by norm_num)
  rw [pointCount_eval, show Nat.divisors 4 = {1, 2, 4} by decide]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two, h4]
  ring

end Eval

/-! ### Coefficients of laws -/

section Coefficients

private theorem coeff_nil (q : ℚ) (σ : FactorType) : coeffAt q [] σ = 0 := rfl

private theorem coeff_cons (q : ℚ) (z : FactorType × Expr) (L : Law) (σ : FactorType) :
    coeffAt q (z :: L) σ = (if z.1 = σ then z.2.eval q else 0) + coeffAt q L σ := by
  simp only [lawCoeff, List.map_cons, Expr.sum, List.foldr_cons, Expr.eval]
  split_ifs <;> rfl

private theorem coeff_append (q : ℚ) (L M : Law) (σ : FactorType) :
    coeffAt q (L ++ M) σ = coeffAt q L σ + coeffAt q M σ := by
  induction L with
  | nil => simp [coeff_nil]
  | cons z L ih => rw [List.cons_append, coeff_cons, coeff_cons, ih, add_assoc]

private theorem coeff_flatMap {α : Type} (q : ℚ) (l : List α) (f : α → Law) (σ : FactorType) :
    coeffAt q (l.flatMap f) σ = (l.map fun x ↦ coeffAt q (f x) σ).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, coeff_append, ih, List.map_cons, List.sum_cons]

private theorem coeff_scale (q : ℚ) (x : Expr) (L : Law) (σ : FactorType) :
    coeffAt q (lawScale x L) σ = x.eval q * coeffAt q L σ := by
  induction L with
  | nil => simp [coeff_nil, lawScale]
  | cons z L ih =>
    simp only [lawScale, List.map_cons] at *
    rw [coeff_cons, coeff_cons, ih]; simp only [Expr.eval]; split_ifs <;> ring

private theorem coeff_lawOne (q : ℚ) (σ : FactorType) :
    coeffAt q lawOne σ = if σ = 0 then 1 else 0 := by
  simp only [lawOne, coeff_cons, coeff_nil, Expr.eval, add_zero, eq_comm]

private theorem coeff_prod_singleton (q : ℚ) (L : Law) (σ : FactorType) :
    coeffAt q (lawProd [L]) σ = coeffAt q L σ := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    simp only [lawProd, List.foldr_cons, List.foldr_nil, lawMul, lawOne, List.flatMap_cons,
      List.map_cons, List.map_nil] at *
    rw [List.singleton_append, coeff_cons, coeff_cons, ih]; simp [Expr.eval]

private theorem lawProd_cons (L : Law) (Ls : List Law) :
    lawProd (L :: Ls) = lawMul L (lawProd Ls) := rfl

private theorem scaleType_injective {δ : ℕ} (hδ : 0 < δ) : Function.Injective (scaleType δ) :=
  Multiset.map_injective fun _ _ h ↦
    Prod.ext (Prod.mk.inj h).1 (Nat.eq_of_mul_eq_mul_left hδ (Prod.mk.inj h).2)

private theorem coeff_descend_scaleType (q : ℚ) {δ : ℕ} (hδ : 0 < δ) (L : Law) (τ : FactorType) :
    coeffAt q (lawDescend δ L) (scaleType δ τ) = coeffAt (q ^ δ) L τ := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    simp only [lawDescend, List.map_cons] at *
    rw [coeff_cons, coeff_cons, ih]
    simp only [(scaleType_injective hδ).eq_iff, eval_subst, eval_pow]
    rfl

private theorem coeff_descend_of_ne (q : ℚ) (δ : ℕ) (L : Law) (σ : FactorType)
    (h : ∀ τ, σ ≠ scaleType δ τ) : coeffAt q (lawDescend δ L) σ = 0 := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    simp only [lawDescend, List.map_cons] at *
    rw [coeff_cons, ih, if_neg fun e ↦ h _ e.symm, zero_add]

private theorem coeff_descend_one (q : ℚ) (L : Law) (σ : FactorType) :
    coeffAt q (lawDescend 1 L) σ = coeffAt q L σ := by
  simpa [scaleType] using coeff_descend_scaleType q one_pos L σ

private theorem lawDescend_lawAtom (δ a : ℕ) : lawDescend δ (lawAtom a 1) = lawAtom a δ := by
  simp [lawDescend, lawAtom, scaleType, Expr.subst]

private theorem lawProd_nil : lawProd [] = lawOne := rfl

private theorem coeff_mul_lawOne (q : ℚ) (L : Law) (σ : FactorType) :
    coeffAt q (lawMul L lawOne) σ = coeffAt q L σ :=
  coeff_prod_singleton q L σ

private theorem coeff_lawAtom (q : ℚ) (e f : ℕ) (σ : FactorType) :
    coeffAt q (lawAtom e f) σ = if σ = {(e, f)} then 1 else 0 := by
  simp [lawAtom, coeff_cons, coeff_nil, Expr.eval, eq_comm]

private theorem coeff_mul_atom (q : ℚ) (e f : ℕ) (M : Law) (σ : FactorType) :
    coeffAt q (lawMul (lawAtom e f) M) σ =
      if (e, f) ∈ σ then coeffAt q M (σ.erase (e, f)) else 0 := by
  have key : ∀ t : FactorType, {(e, f)} + t = σ ↔ (e, f) ∈ σ ∧ σ.erase (e, f) = t := fun t ↦
    ⟨by rintro rfl; simp [Multiset.singleton_add],
      by rintro ⟨h, rfl⟩; rw [Multiset.singleton_add, Multiset.cons_erase h]⟩
  simp only [lawAtom, lawMul, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  induction M with
  | nil => simp [coeff_nil]
  | cons w M ih =>
    rw [List.map_cons, coeff_cons, ih, coeff_cons]
    simp only [key, Expr.eval, one_mul]
    by_cases h : (e, f) ∈ σ <;> simp [h, eq_comm]

private theorem coeff_eq_zero_of_not_mem (q : ℚ) (L : Law) (τ : FactorType)
    (h : τ ∉ (L.map Prod.fst).toFinset) : coeffAt q L τ = 0 := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at h
    rw [coeff_cons, ih h.2, if_neg (Ne.symm h.1), add_zero]

private theorem coeff_map_add (q : ℚ) (z : FactorType × Expr) (M : Law) (σ : FactorType) :
    coeffAt q (M.map fun w ↦ (z.1 + w.1, Expr.mul z.2 w.2)) σ =
      if z.1 ≤ σ then z.2.eval q * coeffAt q M (σ - z.1) else 0 := by
  induction M with
  | nil => simp [coeff_nil]
  | cons w M ih =>
    rw [List.map_cons, coeff_cons, coeff_cons, ih]
    by_cases h : z.1 ≤ σ
    · have e : z.1 + w.1 = σ ↔ w.1 = σ - z.1 :=
        ⟨fun e ↦ by rw [← e, add_tsub_cancel_left], fun e ↦ by rw [e, add_tsub_cancel_of_le h]⟩
      simp only [e, if_pos h, Expr.eval]; split_ifs <;> ring
    · have e : ¬ z.1 + w.1 = σ := fun e ↦ h (e ▸ le_self_add)
      simp [h, e]

private theorem coeff_mul_of_mem (q : ℚ) (L M : Law) (σ : FactorType) (S : Finset FactorType)
    (hS : ∀ z ∈ L, z.1 ∈ S) : coeffAt q (lawMul L M) σ =
      ∑ τ ∈ S, if τ ≤ σ then coeffAt q L τ * coeffAt q M (σ - τ) else 0 := by
  induction L with
  | nil => simp [lawMul, coeff_nil]
  | cons z L ih =>
    have e : lawMul (z :: L) M = (M.map fun w ↦ (z.1 + w.1, Expr.mul z.2 w.2)) ++ lawMul L M := by
      simp [lawMul]
    rw [e, coeff_append, coeff_map_add, ih fun y hy ↦ hS y (List.mem_cons_of_mem _ hy)]
    have : ∀ τ ∈ S, (if τ ≤ σ then coeffAt q (z :: L) τ * coeffAt q M (σ - τ) else 0) =
        (if z.1 = τ then (if τ ≤ σ then z.2.eval q * coeffAt q M (σ - τ) else 0) else 0) +
          (if τ ≤ σ then coeffAt q L τ * coeffAt q M (σ - τ) else 0) := by
      intro τ _; rw [coeff_cons]; split_ifs <;> ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq,
      if_pos (hS z (by simp))]

/-- The coefficients of a product, summed over any finite set containing the support of the
first factor. -/
private theorem coeff_mul (q : ℚ) (L M : Law) (S : Finset FactorType)
    (hS : ∀ τ ∉ S, coeffAt q L τ = 0) (σ : FactorType) : coeffAt q (lawMul L M) σ =
      ∑ τ ∈ S, if τ ≤ σ then coeffAt q L τ * coeffAt q M (σ - τ) else 0 := by
  set T := (L.map Prod.fst).toFinset
  rw [coeff_mul_of_mem q L M σ T fun z hz ↦ List.mem_toFinset.2 (List.mem_map_of_mem hz)]
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := S)) fun τ _ hτ ↦ by
      simp [coeff_eq_zero_of_not_mem q L τ hτ],
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := T)) fun τ _ hτ ↦ by simp [hS τ hτ]]

/-- The coefficient of `σ` in the law `M` with all types shifted by `τ`. -/
private noncomputable def shiftedCoeff (q : ℚ) (M : Law) (τ σ : FactorType) : ℚ :=
  (M.map fun w ↦ if τ + w.1 = σ then w.2.eval q else 0).sum

private theorem shiftedCoeff_mul (q : ℚ) (L M : Law) (τ σ : FactorType) :
    shiftedCoeff q (lawMul L M) τ σ =
      (L.map fun z ↦ z.2.eval q * shiftedCoeff q M (τ + z.1) σ).sum := by
  induction L with
  | nil => simp [shiftedCoeff, lawMul]
  | cons z L ih =>
    have : lawMul (z :: L) M = (M.map fun w ↦ (z.1 + w.1, Expr.mul z.2 w.2)) ++ lawMul L M := by
      simp [lawMul]
    rw [this]
    unfold shiftedCoeff at ih ⊢
    rw [List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons, List.map_map,
      ← List.sum_map_mul_left]
    congr 2
    refine List.map_congr_left fun w _ ↦ ?_
    simp only [Function.comp, add_assoc]
    split_ifs <;> simp [Expr.eval]

private theorem list_sum_comm {α β : Type} (l : List α) (m : List β) (f : α → β → ℚ) :
    (l.map fun a ↦ (m.map fun b ↦ f a b).sum).sum =
      (m.map fun b ↦ (l.map fun a ↦ f a b).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    clear ih
    induction m with
    | nil => simp
    | cons b m ihm => simp only [List.map_cons, List.sum_cons]; rw [← ihm]; ring

private theorem shiftedCoeff_prod_perm (q : ℚ) {Ls Ls' : List Law} (hperm : Ls.Perm Ls') :
    ∀ τ σ, shiftedCoeff q (lawProd Ls) τ σ = shiftedCoeff q (lawProd Ls') τ σ := by
  induction hperm with
  | nil => intros; rfl
  | cons x _ ih =>
    intro τ σ
    simp only [lawProd_cons, shiftedCoeff_mul, ih]
  | swap x y l =>
    intro τ σ
    simp only [lawProd_cons, shiftedCoeff_mul, ← List.sum_map_mul_left]
    rw [list_sum_comm]
    refine congrArg _ (List.map_congr_left fun w _ ↦
      congrArg _ (List.map_congr_left fun z _ ↦ ?_))
    rw [add_right_comm τ w.1 z.1]
    ring
  | trans _ _ ih1 ih2 => intro τ σ; rw [ih1, ih2]

/-- Coefficients of products of laws do not depend on the order of the factors. -/
private theorem coeff_prod_perm {Ls Ls' : List Law} (hperm : Ls.Perm Ls') (q : ℚ)
    (σ : FactorType) : coeffAt q (lawProd Ls) σ = coeffAt q (lawProd Ls') σ := by
  have h : ∀ M : Law, coeffAt q M σ = shiftedCoeff q M 0 σ := fun M ↦ by
    unfold lawCoeff shiftedCoeff
    rw [eval_sum, List.map_map]
    exact congrArg _ (List.map_congr_left fun w _ ↦ by
      by_cases h : w.1 = σ <;> simp [h, Expr.eval])
  rw [h, h, shiftedCoeff_prod_perm q hperm]

/-- The indicator `[σ = K]`. -/
private def indicator (σ K : FactorType) : ℚ := if σ = K then 1 else 0

private theorem ite_eq_mul_indicator (σ K : FactorType) (c : ℚ) [Decidable (σ = K)] :
    (if σ = K then c else 0) = c * indicator σ K := by
  unfold indicator; split_ifs <;> simp

private theorem ite_mem_erase (p : ℕ × ℕ) (σ t : FactorType) (x : ℚ) :
    (if p ∈ σ then (if σ.erase p = t then x else 0) else 0) = if σ = p ::ₘ t then x else 0 := by
  by_cases h : p ∈ σ
  · rw [if_pos h]
    by_cases h2 : σ.erase p = t
    · rw [if_pos h2, if_pos]; rw [← h2, Multiset.cons_erase h]
    · rw [if_neg h2, if_neg]; rintro rfl; exact h2 (by simp)
  · rw [if_neg h, if_neg]; rintro rfl; exact h (by simp)

private theorem ite_add_zero (c : Prop) [Decidable c] (a b : ℚ) :
    (if c then a + b else 0) = (if c then a else 0) + (if c then b else 0) := by
  split_ifs <;> simp

private theorem ite_le_sub (t σ u : FactorType) (c d : ℚ) :
    (if t ≤ σ then c * (if σ - t = u then d else 0) else 0) = if σ = t + u then c * d else 0 := by
  by_cases h : σ = t + u
  · subst h; simp
  · rw [if_neg h]
    split_ifs with h1 h2
    · exact absurd (by rw [← h2, add_tsub_cancel_of_le h1]) h
    · simp
    · rfl

private theorem ite_le_sub_one (t σ u : FactorType) (d : ℚ) :
    (if t ≤ σ then (if σ - t = u then d else 0) else 0) = if σ = t + u then d else 0 := by
  simpa using ite_le_sub t σ u 1 d

end Coefficients

/-! ### Patterns -/

section Patterns

/-- The pattern with the single nonzero entry `v` at `ij₀`. -/
private def spat {n : ℕ} (ij₀ : Fin n × Fin n) (v : Fin (n + 1)) : Pattern n :=
  fun ij ↦ if ij = ij₀ then v else 0

private theorem spat_val {n : ℕ} (ij₀ : Fin n × Fin n) (v : Fin (n + 1)) (ij : Fin n × Fin n) :
    ((spat ij₀ v ij : Fin (n+1)) : ℕ) = if ij = ij₀ then (v : ℕ) else 0 := by
  unfold spat; split_ifs <;> simp

private theorem eq_spat {n : ℕ} (m : Pattern n) (ij₀ : Fin n × Fin n) (v : Fin (n + 1))
    (h₀ : (m ij₀).val = v.val) (h : ∀ ij, ij ≠ ij₀ → (m ij).val = 0) : m = spat ij₀ v := by
  funext ij; apply Fin.ext; rw [spat_val]
  split_ifs with hij
  · subst hij; exact h₀
  · exact h ij hij

private theorem flatMap_replicate_eq {α β : Type} (l : List α) (x₀ : α) (g : α → β) (f : α → ℕ)
    (hf : ∀ x, x ≠ x₀ → f x = 0) (hnd : l.Nodup) (hm : x₀ ∈ l) :
    l.flatMap (fun x ↦ List.replicate (f x) (g x)) = List.replicate (f x₀) (g x₀) := by
  induction l with
  | nil => simp at hm
  | cons y l ih =>
    rw [List.flatMap_cons]
    rw [List.nodup_cons] at hnd
    by_cases h : y = x₀
    · subst h
      rw [List.flatMap_eq_nil_iff.2]
      · simp
      · intro x hx; rw [hf x (fun e ↦ hnd.1 (e ▸ hx))]; rfl
    · rw [hf y h, ih hnd.2 ((List.mem_cons.1 hm).resolve_left (Ne.symm h))]; rfl

private theorem otherChildren_spat {n : ℕ} (a : ℕ) (ij₀ : Fin n × Fin n) (v : Fin (n + 1)) :
    otherChildren a (spat ij₀ v) = List.replicate v (ij₀.1.val+1, .single a (ij₀.2.val+1)) := by
  unfold otherChildren
  rw [flatMap_replicate_eq _ ij₀
    (fun ij : Fin n × Fin n ↦ (ij.1.val+1, State.single a (ij.2.val+1)))
    (fun ij ↦ (spat ij₀ v ij : ℕ)) (fun x hx ↦ by rw [spat_val, if_neg hx])
    (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _)), spat_val, if_pos rfl]

private theorem patternWeight_spat {n : ℕ} (ij₀ : Fin n × Fin n) (v : Fin (n + 1)) :
    patternWeight (spat ij₀ v) = (ij₀.1.val+1)*(ij₀.2.val+1)*v := by
  unfold patternWeight
  rw [Finset.sum_eq_single ij₀]
  · rw [spat_val, if_pos rfl]
  · intro ij _ h; rw [spat_val, if_neg h]; simp
  · simp

private theorem divisorCount_eval {n : ℕ} (q : ℚ) (off : ℤ) (m : Pattern n) :
    (divisorCount off m).eval q = ∏ i : Fin n,
      (falling (availablePoints off (i.val+1)) (∑ j, (m (i, j)).val)).eval q *
        (1 / ∏ j, ((m (i, j)).val.factorial : ℚ)) := by
  simp only [divisorCount, eval_prod, List.map_map, Finset.prod_map_toList]
  rfl

private theorem divisorCount_spat {n : ℕ} (q : ℚ) (off : ℤ) (ij₀ : Fin n × Fin n)
    (v : Fin (n + 1)) :
    (divisorCount off (spat ij₀ v)).eval q =
      (falling (availablePoints off (ij₀.1.val+1)) v).eval q / ((v : ℕ).factorial : ℚ) := by
  rw [divisorCount_eval, Finset.prod_eq_single ij₀.1 _ (by simp)]
  · have h1 : (∑ j, ((spat ij₀ v (ij₀.1, j)) : ℕ)) = v := by
      rw [Finset.sum_eq_single ij₀.2 (fun j _ hj ↦ by simp [spat_val, Prod.ext_iff, hj]) (by simp),
        spat_val, if_pos rfl]
    have h2 : (∏ j, (((spat ij₀ v (ij₀.1, j)) : ℕ).factorial : ℚ)) = ((v : ℕ).factorial : ℚ) := by
      rw [Finset.prod_eq_single ij₀.2 (fun j _ hj ↦ by simp [spat_val, Prod.ext_iff, hj])
        (by simp), spat_val, if_pos rfl]
    rw [h1, h2]; ring
  · intro i _ hi
    have h1 : (∑ j, ((spat ij₀ v (i, j)) : ℕ)) = 0 :=
      Finset.sum_eq_zero fun j _ ↦ by simp [spat_val, Prod.ext_iff, hi]
    have h2 : (∏ j, (((spat ij₀ v (i, j)) : ℕ).factorial : ℚ)) = 1 :=
      Finset.prod_eq_one fun j _ ↦ by simp [spat_val, Prod.ext_iff, hi]
    simp [h1, h2, falling, Expr.prod, Expr.eval]

private theorem divisorCount_zero {n : ℕ} (q : ℚ) (off : ℤ) :
    (divisorCount off fun _ : Fin n × Fin n ↦ (0 : Fin (n+1))).eval q = 1 := by
  simp [divisorCount_eval, falling, Expr.prod, Expr.eval]

private theorem divisorCount_cell {n : ℕ} (q : ℚ) (off : ℤ) (a b : ℕ) (ha : a < n) (hb : b < n)
    (v : Fin (n + 1)) :
    (divisorCount off fun ij : Fin n × Fin n ↦
      if ij.1.val = a ∧ ij.2.val = b then v else 0).eval q =
      (falling (availablePoints off (a+1)) v).eval q / ((v : ℕ).factorial : ℚ) := by
  rw [show (fun ij : Fin n × Fin n ↦ if ij.1.val = a ∧ ij.2.val = b then v else 0) =
      spat (⟨a, ha⟩, ⟨b, hb⟩) v from funext fun ij ↦ by simp [spat, Prod.ext_iff, Fin.ext_iff],
    divisorCount_spat]

/-- A cell whose weight `(i + 1)(j + 1)` exceeds the total weight is empty. -/
private theorem cell_eq_zero {n : ℕ} (m : Pattern n) (ij : Fin n × Fin n)
    (h : patternWeight m < (ij.1.val + 1) * (ij.2.val + 1)) : (m ij).val = 0 := by
  have hle : (ij.1.val+1)*(ij.2.val+1)*(m ij).val ≤ patternWeight m :=
    Finset.single_le_sum (f := fun ij : Fin n × Fin n ↦ (ij.1.val+1)*(ij.2.val+1)*(m ij).val)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ ij)
  by_contra hc
  exact absurd (hle.trans_lt h) (not_lt.2 (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hc)))

private theorem pattern_eq_zero {n : ℕ} (m : Pattern n) (h : patternWeight m = 0)
    (ij₀ : Fin n × Fin n) : m = spat ij₀ 0 :=
  eq_spat _ _ _ (cell_eq_zero m ij₀ (by rw [h]; positivity))
    fun ij _ ↦ cell_eq_zero m ij (by rw [h]; positivity)

private theorem pattern_eq_of_weight_one {n : ℕ} (hn : 0 < n) (m : Pattern n)
    (h : patternWeight m = 1) : m = spat (⟨0, hn⟩, ⟨0, hn⟩) ⟨1, by omega⟩ := by
  have hz : ∀ ij, ij ≠ (⟨0, hn⟩, ⟨0, hn⟩) → (m ij).val = 0 := by
    rintro ⟨i, j⟩ hij
    have : 0 < i.val ∨ 0 < j.val := by
      by_contra hc; push Not at hc
      exact hij (Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega)))
    refine cell_eq_zero m _ ?_
    rw [h]; change 1 < (i.val+1)*(j.val+1)
    rcases this with hi | hi <;> nlinarith
  refine eq_spat _ _ _ ?_ hz
  have : patternWeight m = (m (⟨0, hn⟩, ⟨0, hn⟩)).val := by
    rw [patternWeight, Finset.sum_eq_single (⟨0, hn⟩, ⟨0, hn⟩) (fun ij _ hij ↦ by simp [hz ij hij])
      (by simp)]
    simp
  simp only; omega

private theorem pattern_eq_of_weight_two {n : ℕ} (hn : 2 ≤ n) (m : Pattern n)
    (h : patternWeight m = 2) :
    m = spat (⟨0, Nat.lt_of_lt_of_le Nat.two_pos hn⟩, ⟨0, Nat.lt_of_lt_of_le Nat.two_pos hn⟩)
        ⟨2, Nat.lt_succ_of_le hn⟩ ∨
    m = spat (⟨0, Nat.lt_of_lt_of_le Nat.two_pos hn⟩, ⟨1, Nat.lt_of_lt_of_le Nat.one_lt_two hn⟩)
        ⟨1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le Nat.two_pos hn)⟩ ∨
    m = spat (⟨1, Nat.lt_of_lt_of_le Nat.one_lt_two hn⟩, ⟨0, Nat.lt_of_lt_of_le Nat.two_pos hn⟩)
        ⟨1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le Nat.two_pos hn)⟩ := by
  set x00 : Fin n × Fin n := (⟨0, by omega⟩, ⟨0, by omega⟩)
  set x01 : Fin n × Fin n := (⟨0, by omega⟩, ⟨1, by omega⟩)
  set x10 : Fin n × Fin n := (⟨1, by omega⟩, ⟨0, by omega⟩)
  have hz : ∀ ij, ij ≠ x00 → ij ≠ x01 → ij ≠ x10 → (m ij).val = 0 := by
    rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ h0 h1 h2
    refine cell_eq_zero m _ (h ▸ ?_)
    simp only [x00, x01, x10, ne_eq, Prod.mk.injEq, Fin.mk.injEq] at h0 h1 h2 ⊢
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp_all
    nlinarith
  have hsum : patternWeight m = (m x00).val + 2*(m x01).val + 2*(m x10).val := by
    unfold patternWeight
    rw [← Finset.sum_subset (Finset.subset_univ ({x00, x01, x10} : Finset (Fin n × Fin n)))]
    · rw [Finset.sum_insert (by simp [x00, x01, x10]), Finset.sum_insert (by simp [x01, x10]),
        Finset.sum_singleton]
      simp [x00, x01, x10]; ring
    · intro ij _ hij
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hij
      rw [hz ij hij.1 hij.2.1 hij.2.2]; simp
  rcases (by omega : ((m x00).val = 2 ∧ (m x01).val = 0 ∧ (m x10).val = 0) ∨
      ((m x00).val = 0 ∧ (m x01).val = 1 ∧ (m x10).val = 0) ∨
      ((m x00).val = 0 ∧ (m x01).val = 0 ∧ (m x10).val = 1))
    with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · refine .inl (eq_spat _ _ _ e0 fun ij hij ↦ ?_)
    by_cases h1 : ij = x01; · rw [h1, e1]
    by_cases h2 : ij = x10; · rw [h2, e2]
    exact hz ij hij h1 h2
  · refine .inr (.inl (eq_spat _ _ _ e1 fun ij hij ↦ ?_))
    by_cases h1 : ij = x00; · rw [h1, e0]
    by_cases h2 : ij = x10; · rw [h2, e2]
    exact hz ij h1 hij h2
  · refine .inr (.inr (eq_spat _ _ _ e2 fun ij hij ↦ ?_))
    by_cases h1 : ij = x00; · rw [h1, e0]
    by_cases h2 : ij = x01; · rw [h2, e1]
    exact hz ij h1 h2 hij

private theorem univ_toList_perm (n : ℕ) :
    (Finset.univ : Finset (Fin n × Fin n)).toList.Perm (List.finRange n ×ˢ List.finRange n) :=
  List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _)
    ((List.nodup_finRange n).product (List.nodup_finRange n))
    (by ext ⟨a, b⟩; simp [List.mem_product])

/-- `otherChildren` with an explicit enumeration of the cells (computable by `decide`). -/
private def otherChildrenList {n : ℕ} (a : ℕ) (m : Pattern n) : List (ℕ × State) :=
  (List.finRange n ×ˢ List.finRange n).flatMap fun ij ↦
    List.replicate (m ij).val (ij.1.val+1, State.single a (ij.2.val+1))

private theorem otherChildren_perm {n : ℕ} (a : ℕ) (m : Pattern n) {l : List (ℕ × State)}
    (h : (otherChildrenList a m).Perm l) : (otherChildren a m).Perm l :=
  ((univ_toList_perm n).flatMap_right _).trans h

/-- The product of the descended laws of a list of children. -/
private noncomputable def childProd (l : List (ℕ × State)) : Law :=
  lawProd (l.map fun z ↦ lawDescend z.1 (stateLaw z.2))

private theorem coeff_childProd_perm {l l' : List (ℕ × State)} (h : l.Perm l') (q : ℚ)
    (σ : FactorType) : coeffAt q (childProd l) σ = coeffAt q (childProd l') σ :=
  coeff_prod_perm (h.map _) q σ

private theorem coeff_otherChildren {n : ℕ} (m : Pattern n) (l : List (ℕ × State))
    (h : (otherChildrenList 1 m).Perm l) (q : ℚ) (σ : FactorType) :
    coeffAt q (childProd (otherChildren 1 m)) σ = coeffAt q (childProd l) σ :=
  coeff_childProd_perm (otherChildren_perm 1 m h) q σ

end Patterns

/-! ### Unfolding the recursion

These facts are re-derived here (and not imported from the development) so that this file depends
only on the definitions in `SurfaceBlowup.Basic`. -/

section Recursion

private theorem mem_otherChildren {n : ℕ} {a : ℕ} {m : Pattern n} {z : ℕ × State}
    (h : z ∈ otherChildren a m) :
    ∃ ij : Fin n × Fin n, z = (ij.1.val+1, .single a (ij.2.val+1)) := by
  simp only [otherChildren, List.mem_flatMap, List.mem_replicate] at h
  obtain ⟨ij, -, -, rfl⟩ := h
  exact ⟨ij, rfl⟩

private theorem children_valid (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) (z : ℕ × State) (hz : z ∈ children s P) : z.2.Valid := by
  have other : ∀ a (m : Pattern s.degree), 0 < a → z ∈ otherChildren a m → z.2.Valid :=
    fun a m ha h ↦ by obtain ⟨ij, rfl⟩ := mem_otherChildren h; exact ⟨ha, Nat.succ_pos _⟩
  obtain ⟨-, -, hrest⟩ := hP
  cases s with
  | single a c =>
    obtain ⟨ha, hc⟩ := hs
    obtain ⟨-, -, hrt⟩ := hrest
    rcases List.mem_append.1 hz with hz | hz
    · split_ifs at hz with h0
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        exact ⟨ha, ha, Nat.pos_of_ne_zero h0, by have := hrt.mp (Nat.pos_of_ne_zero h0); omega⟩
    · exact other a _ ha hz
  | crossing a b c h =>
    obtain ⟨ha, hb, hc, hh⟩ := hs
    obtain ⟨-, -, hrt, hrx⟩ := hrest
    simp only [children, List.mem_append] at hz
    rcases hz with (hz | hz) | hz
    · split_ifs at hz with h0
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        exact ⟨by omega, ha, Nat.pos_of_ne_zero h0,
          by have := hrt.mp (Nat.pos_of_ne_zero h0); omega⟩
    · split_ifs at hz with h0
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        exact ⟨by omega, hb, Nat.pos_of_ne_zero h0,
          by have := hrx.mp (Nat.pos_of_ne_zero h0); omega⟩
    · exact other (a+b) _ (by omega) hz

private theorem weight_le_degree (s : State) (hs : s.Valid) : s.weight ≤ s.degree := by
  cases s with
  | single a c => exact Nat.le_mul_of_pos_right a hs.2
  | crossing a b c h =>
    exact Nat.add_le_add (Nat.le_mul_of_pos_right a hs.2.2.1) (Nat.le_mul_of_pos_right b hs.2.2.2)

private theorem degree_pos (s : State) (hs : s.Valid) : 0 < s.degree := by
  cases s with
  | single a c => exact Nat.mul_pos hs.1 hs.2
  | crossing a b c h => exact Nat.add_pos_left (Nat.mul_pos hs.1 hs.2.2.1) _

private theorem tag_le_one (s : State) : s.tag ≤ 1 := by cases s <;> simp [State.tag]

private theorem rank_lt_of_degree_lt (s u : State) (h : u.degree < s.degree) : u.rank < s.rank := by
  have := tag_le_one u
  have h3 : (u.degree + 1) * (u.degree + 1) ≤ s.degree * s.degree := Nat.mul_le_mul h h
  unfold State.rank
  have := Nat.sub_le u.degree u.weight
  nlinarith

private theorem rank_lt_of_weight_lt (s u : State) (hs : s.Valid) (hu : u.Valid)
    (hN : u.degree = s.degree) (hw : s.weight < u.weight) : u.rank < s.rank := by
  have := weight_le_degree s hs
  have := weight_le_degree u hu
  have := tag_le_one u
  unfold State.rank
  rw [hN] at *
  omega

private theorem otherChildren_degree_sum {n : ℕ} (a : ℕ) (m : Pattern n) :
    ((otherChildren a m).map fun z ↦ z.1*z.2.degree).sum = a * patternWeight m := by
  unfold otherChildren patternWeight
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map, Finset.mul_sum,
    Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  simp [List.map_replicate, List.sum_replicate, State.degree]
  ring

private theorem children_degree_sum (s : State) (P : TangentPattern s.degree) (hP : Allowed s P) :
    ((children s P).map fun z ↦ z.1*z.2.degree).sum = s.degree := by
  obtain ⟨-, hsum, hrest⟩ := hP
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

private theorem children_fst_pos (s : State) (P : TangentPattern s.degree) (z : ℕ × State)
    (hz : z ∈ children s P) : 0 < z.1 := by
  cases s with
  | single a c =>
    rcases List.mem_append.1 hz with hz | hz
    · split_ifs at hz <;> simp at hz; simp [hz]
    · obtain ⟨ij, rfl⟩ := mem_otherChildren hz; simp
  | crossing a b c h =>
    simp only [children, List.mem_append] at hz
    rcases hz with (hz | hz) | hz
    · split_ifs at hz <;> simp at hz; simp [hz]
    · split_ifs at hz <;> simp at hz; simp [hz]
    · obtain ⟨ij, rfl⟩ := mem_otherChildren hz; simp

/-- A child of the same degree as its parent is the only child, with residue degree one. -/
private theorem children_eq_singleton (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) (z : ℕ × State) (hz : z ∈ children s P) (heq : z.2.degree = s.degree) :
    children s P = [z] ∧ z.1 = 1 := by
  have hsum := children_degree_sum s P hP
  have hD := degree_pos s hs
  have hpos : ∀ w ∈ children s P, 0 < w.1 * w.2.degree := fun w hw ↦
    Nat.mul_pos (children_fst_pos s P w hw) (degree_pos _ (children_valid s hs P hP w hw))
  have hz1 := children_fst_pos s P z hz
  obtain ⟨l1, l2, hL⟩ := List.append_of_mem hz
  have empty : ∀ l : List (ℕ × State), (∀ w ∈ l, w ∈ children s P) →
      (l.map fun z ↦ z.1*z.2.degree).sum = 0 → l = [] := by
    rintro (_ | ⟨a, t⟩) hl h0
    · rfl
    · have := hpos a (hl a (by simp))
      simp only [List.map_cons, List.sum_cons] at h0
      omega
  rw [hL] at hsum
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, heq] at hsum
  have hge : s.degree ≤ z.1 * s.degree := Nat.le_mul_of_pos_left _ hz1
  obtain rfl := empty l1 (fun w hw ↦ by rw [hL]; simp [hw]) (by omega)
  obtain rfl := empty l2 (fun w hw ↦ by rw [hL]; simp [hw]) (by omega)
  refine ⟨by simpa using hL, Nat.eq_of_mul_eq_mul_right hD ?_⟩
  simp at hsum
  omega

private theorem nonself_child_rank_lt (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) (hself : ¬ SelfPattern s P) (z : ℕ × State) (hz : z ∈ children s P) :
    z.2.rank < s.rank := by
  have hv := children_valid s hs P hP z hz
  have hle : z.2.degree ≤ s.degree := calc
    z.2.degree ≤ z.1 * z.2.degree := Nat.le_mul_of_pos_left _ (children_fst_pos s P z hz)
    _ ≤ ((children s P).map fun z ↦ z.1*z.2.degree).sum :=
      List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ (List.mem_map.2 ⟨z, hz, rfl⟩)
    _ = s.degree := children_degree_sum s P hP
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact rank_lt_of_degree_lt s z.2 hlt
  obtain ⟨hch, hz1⟩ := children_eq_singleton s hs P hP z hz heq
  have hw : ∀ u : State, s.weight < u.weight → z.2 = u → z.2.rank < s.rank := by
    rintro u hwu rfl
    exact rank_lt_of_weight_lt s z.2 hs hv heq hwu
  cases s with
  | single a c =>
    simp only [children, otherChildren, List.mem_append, List.mem_flatMap,
      List.mem_replicate] at hz
    rcases hz with hz | ⟨ij, -, -, rfl⟩
    · split_ifs at hz with h0
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        exact hw _ (by have := hs.1; simp [State.weight]; omega) rfl
    · refine absurd ⟨a, c, rfl, ?_⟩ hself
      have hj : ij.2.val + 1 = c :=
        Nat.eq_of_mul_eq_mul_left hs.1 (by simpa [State.degree] using heq)
      rw [hch]
      simp only at hz1
      rw [hz1, hj]
  | crossing a b c h =>
    simp only [children, otherChildren, List.mem_append, List.mem_flatMap,
      List.mem_replicate] at hz
    rcases hz with (hz | hz) | ⟨ij, -, -, rfl⟩
    · split_ifs at hz with h0
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        exact hw _ (by have := hs.1; simp [State.weight]; omega) rfl
    · split_ifs at hz with h0
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        exact hw _ (by have := hs.2.1; simp [State.weight]; omega) rfl
    · simp only [State.rank, State.weight, State.tag] at heq ⊢
      rw [heq]
      omega

open scoped Classical in
/-- The recursion sum of a state with fuel `k` for the children. -/
private noncomputable def exitLawFuel (k : ℕ) (s : State) : Law :=
  (allowedPatterns s).toList.flatMap fun P ↦
    if SelfPattern s P then [] else
      lawScale (.mul (tangentCount s P) (divisorProbability s P.d.val))
        (lawProd ((children s P).map fun z ↦ lawDescend z.1 (stateLawFuel k z.2)))

open scoped Classical in
/-- The non-self part of the recursion sum of a state, with the children's laws `stateLaw`. -/
private noncomputable def exitLaw (s : State) : Law :=
  (allowedPatterns s).toList.flatMap fun P ↦
    if SelfPattern s P then [] else
      lawScale (.mul (tangentCount s P) (divisorProbability s P.d.val))
        (lawProd ((children s P).map fun z ↦ lawDescend z.1 (stateLaw z.2)))

private theorem exitLawFuel_congr (s : State) (hs : s.Valid) (k₁ k₂ : ℕ)
    (h : ∀ z : ℕ × State, z.2.Valid → z.2.rank < s.rank →
      stateLawFuel k₁ z.2 = stateLawFuel k₂ z.2) :
    exitLawFuel k₁ s = exitLawFuel k₂ s := by
  refine List.flatMap_congr fun P hP ↦ ?_
  have hA : Allowed s P := by simpa [allowedPatterns] using hP
  split_ifs with hself
  · rfl
  · refine congrArg _ (congrArg _ (List.map_congr_left fun z hz ↦ ?_))
    rw [h z (children_valid s hs P hA z hz) (nonself_child_rank_lt s hs P hA hself z hz)]

/-- One step of the fuelled recursion at a non-terminal state `s`: the recursion sum
`exitLawFuel k s`, scaled by `(1 - returnWeight c)⁻¹` when `s` is a single state of contact `c`. -/
noncomputable def stateLawFuelStep (k : ℕ) (s : State) : Law :=
  match s with
  | .single _ c => lawScale (.inv (.sub (.const 1) (returnWeight c))) (exitLawFuel k s)
  | .crossing _ _ _ _ => exitLawFuel k s

private theorem stateLawFuel_succ (k : ℕ) (s : State) (hnt : s.terminal = false) :
    stateLawFuel (k+1) s = stateLawFuelStep k s := by
  rcases s with ⟨a, _ | _ | c⟩ | ⟨a, b, c, h⟩
  · rfl
  · simp [State.terminal] at hnt
  · rfl
  · rfl

private theorem stateLawFuel_eq (k : ℕ) (s : State) (hs : s.Valid) (hk : s.rank < k) :
    stateLawFuel k s = stateLaw s := by
  suffices ∀ n s, s.Valid → s.rank < n → ∀ k₁ k₂, s.rank < k₁ → s.rank < k₂ →
      stateLawFuel k₁ s = stateLawFuel k₂ s from this _ s hs (Nat.lt_succ_self _) _ _ hk
      (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro s _ h; omega
  | succ n ih =>
    intro s hs hn k₁ k₂ h₁ h₂
    obtain ⟨j₁, rfl⟩ : ∃ j, k₁ = j + 1 := ⟨k₁ - 1, by omega⟩
    obtain ⟨j₂, rfl⟩ : ∃ j, k₂ = j + 1 := ⟨k₂ - 1, by omega⟩
    have := exitLawFuel_congr s hs j₁ j₂ fun z hz hlt ↦
      ih z.2 hz (by omega) j₁ j₂ (by omega) (by omega)
    rcases s with ⟨a, _ | _ | c⟩ | ⟨a, b, c, h⟩ <;>
      first | rw [stateLawFuel_succ _ _ rfl, stateLawFuel_succ _ _ rfl, stateLawFuelStep,
        stateLawFuelStep, this] | rfl

private theorem exitLawFuel_rank (s : State) (hs : s.Valid) : exitLawFuel s.rank s = exitLaw s :=
  List.flatMap_congr fun P hP ↦ by
    have hA : Allowed s P := by simpa [allowedPatterns] using hP
    split_ifs with hself
    · rfl
    · refine congrArg _ (congrArg _ (List.map_congr_left fun z hz ↦ ?_))
      rw [stateLawFuel_eq _ _ (children_valid s hs P hA z hz)
        (nonself_child_rank_lt s hs P hA hself z hz)]

private theorem stateLaw_single (a c : ℕ) (hs : (State.single a c).Valid) (hc : c ≠ 1) :
    stateLaw (.single a c) =
      lawScale (.inv (.sub (.const 1) (returnWeight c))) (exitLaw (.single a c)) := by
  rw [stateLaw, stateLawFuel_succ _ _ (by rcases c with _ | _ | c <;> simp_all [State.terminal]),
    stateLawFuelStep, exitLawFuel_rank _ hs]

private theorem stateLaw_crossing (a b c h : ℕ) (hs : (State.crossing a b c h).Valid) :
    stateLaw (.crossing a b c h) = exitLaw (.crossing a b c h) := by
  rw [stateLaw, stateLawFuel_succ _ _ rfl, stateLawFuelStep, exitLawFuel_rank _ hs]

private theorem stateLaw_terminal (a : ℕ) : stateLaw (.single a 1) = lawAtom a 1 := by
  rw [stateLaw, State.rank, stateLawFuel]

open scoped Classical in
/-- The coefficients of `exitLaw s`, as a sum over the allowed patterns. -/
private theorem coeff_exitLaw (q : ℚ) (s : State) (σ : FactorType) : coeffAt q (exitLaw s) σ =
    ∑ P ∈ allowedPatterns s, if SelfPattern s P then 0 else
      ((tangentCount s P).mul (divisorProbability s P.d.val)).eval q *
        coeffAt q (childProd (children s P)) σ := by
  rw [exitLaw, coeff_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  split_ifs
  · rfl
  · rw [coeff_scale]; rfl

/-- The coefficients of the global law, as a sum over the residue patterns. -/
private theorem coeff_globalLaw (proj : Bool) (n : ℕ) (q : ℚ) (σ : FactorType) :
    coeffAt q (globalLaw proj n) σ =
      (Expr.inv (if proj then projectiveNormalizer n else .pow .var n)).eval q *
        ∑ m ∈ residuePatterns n, (divisorCount (if proj then 1 else 0) m).eval q *
          coeffAt q (childProd (otherChildren 1 m)) σ := by
  rw [globalLaw, coeff_scale, coeff_flatMap, Finset.sum_map_toList]
  simp only [coeff_scale]; rfl

end Recursion

/-! ### The laws of the crossing states `T(a,b;c,h)` with `c = 1` or `h = 1` -/

section Crossing

/-- A crossing state with a unique allowed pattern, of weight one, with a unique child of residue
degree one has the law of that child. -/
private theorem coeff_crossing_of_unique {a b c h : ℕ} (hv : (State.crossing a b c h).Valid)
    (P : TangentPattern (State.crossing a b c h).degree)
    (hA : allowedPatterns (.crossing a b c h) = {P}) (s' : State)
    (hch : children (.crossing a b c h) P = [(1, s')]) (q : ℚ)
    (hX : ((tangentCount (.crossing a b c h) P).mul
      (divisorProbability (.crossing a b c h) P.d.val)).eval q = 1) (σ : FactorType) :
    coeffAt q (stateLaw (.crossing a b c h)) σ = coeffAt q (stateLaw s') σ := by
  rw [stateLaw_crossing _ _ _ _ hv, coeff_exitLaw, hA, Finset.sum_singleton,
    if_neg (by rintro ⟨_, _, h, _⟩; cases h), hX, one_mul, hch, childProd, List.map_singleton,
    coeff_prod_singleton, coeff_descend_one]

/-- `T(a,b;1,1)` has the law of the terminal state `S(a+b;1)`. -/
private theorem crossing_one_one_law (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (q : ℚ) (hq : 1 < q)
    (σ : FactorType) :
    coeffAt q (stateLaw (.crossing a b 1 1)) σ = if σ = {(a+b, 1)} then 1 else 0 := by
  have hn : 0 < (State.crossing a b 1 1).degree := by simp [State.degree]; omega
  set D := (State.crossing a b 1 1).degree
  let x : Fin D × Fin D := (⟨0, hn⟩, ⟨0, hn⟩)
  let P : TangentPattern D := ⟨⟨1, by omega⟩, 0, 0, spat x ⟨1, by omega⟩⟩
  have hA : allowedPatterns (.crossing a b 1 1) = {P} := by
    ext Q
    simp only [allowedPatterns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · obtain ⟨d, rt, rx, other⟩ := Q
      rintro ⟨h0, hw, h1, h2, h3, h4⟩
      simp only at h0 hw h1 h2 h3 h4
      have hrt : rt.val = 0 := by by_contra h; have := h3.1 (by omega); omega
      have hrx : rx.val = 0 := by by_contra h; have := h4.1 (by omega); omega
      rw [pattern_eq_of_weight_one hn other (by omega)]
      simp only [P, x, TangentPattern.mk.injEq, Fin.ext_iff, Fin.val_zero, and_true]
      omega
    · rintro rfl
      exact ⟨by simp [P], by simp [P, patternWeight_spat, x], by simp [P]⟩
  rw [coeff_crossing_of_unique ⟨ha, hb, one_pos, one_pos⟩ P hA (.single (a+b) 1) ?_ q ?_ σ,
    stateLaw_terminal, coeff_lawAtom]
  · simp [children, P, otherChildren_spat, x]
  · have hq1 : q + -1 ≠ 0 := by linarith
    simp [P, tangentCount, divisorCount_spat, divisorProbability, chooseTwo, falling,
      availablePoints, x, Expr.eval, eminusOne, Expr.sub, Expr.neg, Expr.pow, Expr.prod, hq1]

/-- For `c = 1` or `h = 1` (not both) the unique allowed pattern of `T(a,b;c,h)` has weight one
and a unique child, of residue degree one. -/
private theorem crossing_unique_pattern (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h) (q : ℚ) (hone : c = 1 ∨ h = 1) (hnot : ¬ (c = 1 ∧ h = 1)) :
    ∃ P : TangentPattern (State.crossing a b c h).degree,
      allowedPatterns (State.crossing a b c h) = {P} ∧
      children (State.crossing a b c h) P =
        (if 1 < c then [(1, .crossing (a+b) a 1 (c-1))] else []) ++
        (if 1 < h then [(1, .crossing (a+b) b 1 (h-1))] else []) ∧
      ((tangentCount (State.crossing a b c h) P).mul
        (divisorProbability (State.crossing a b c h) P.d.val)).eval q = 1 := by
  have hn : 1 < (State.crossing a b c h).degree := by
    change 1 < a*c+b*h
    have := Nat.mul_pos ha hc; have := Nat.mul_pos hb hh; omega
  let P : TangentPattern (State.crossing a b c h).degree :=
    ⟨⟨1, by omega⟩, ⟨if 1 < c then 1 else 0, by split_ifs <;> omega⟩,
      ⟨if 1 < h then 1 else 0, by split_ifs <;> omega⟩, fun _ ↦ 0⟩
  have hpw0 : patternWeight P.other = 0 := by simp [patternWeight, P]
  refine ⟨P, ?_, ?_, ?_⟩
  · ext Q
    simp only [allowedPatterns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · obtain ⟨d, rt, rx, other⟩ := Q
      rintro ⟨h0, hw, h1, h2, h3, h4⟩
      simp only at h0 hw h1 h2 h3 h4
      have hrt : rt.val = if 1 < c then 1 else 0 := by
        split_ifs with hc1
        · have := h3.2 (by omega); omega
        · by_contra hne; have := h3.1 (by omega); omega
      have hrx : rx.val = if 1 < h then 1 else 0 := by
        split_ifs with hh1
        · have := h4.2 (by omega); omega
        · by_contra hne; have := h4.1 (by omega); omega
      have hpw : patternWeight other = 0 := by rw [hrt, hrx] at hw; split_ifs at hw <;> omega
      have := pattern_eq_zero other hpw (⟨0, by omega⟩, ⟨0, by omega⟩)
      simp only [P, TangentPattern.mk.injEq, Fin.ext_iff, hrt, hrx, true_and]
      refine ⟨by omega, this.trans (funext fun _ ↦ ?_)⟩
      simp [spat]
    · rintro rfl
      refine ⟨by simp [P], ?_, ?_⟩
      · rw [hpw0]; simp only [P]; split_ifs <;> omega
      · simp only [P]; refine ⟨by omega, by omega, ?_, ?_⟩ <;> split_ifs <;> omega
  · simp only [children, show otherChildren (a+b) P.other = [] by simp [otherChildren, P], P,
      List.append_nil]
    rcases hone with rfl | rfl
    · simp [show 1 < h by omega]
    · simp [show 1 < c by omega]
  · have hj : (if 1 < c then 1 else 0) + (if 1 < h then 1 else 0) = 1 := by split_ifs <;> omega
    simp only [Expr.eval, divisorProbability, P, chooseTwo, hj, tangentCount, divisorCount, falling,
      eval_prod]
    simp [Expr.prod, Expr.pow, Expr.eval]

/-- `T(a,b;1,h)` has the law of the terminal state `S(a+hb;1)`. -/
private theorem crossing_left_one_law (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (q : ℚ)
    (hq : 1 < q) (σ : FactorType) :
    coeffAt q (stateLaw (.crossing a b 1 h)) σ = if σ = {(a+h*b, 1)} then 1 else 0 := by
  induction h generalizing a with
  | zero => omega
  | succ h ih =>
    rcases Nat.eq_zero_or_pos h with rfl | h0
    · simpa using crossing_one_one_law a b ha hb q hq σ
    obtain ⟨P, hA, hch, hX⟩ :=
      crossing_unique_pattern a b 1 (h+1) ha hb one_pos (by omega) q (.inl rfl) (by omega)
    rw [if_neg (by omega), if_pos (by omega), List.nil_append, Nat.add_sub_cancel] at hch
    rw [coeff_crossing_of_unique ⟨ha, hb, one_pos, by omega⟩ P hA _ hch q hX,
      ih (a+b) (by omega) h0]
    congr 2; ring_nf

/-- `T(a,b;c,1)` has the law of the terminal state `S(ca+b;1)`. -/
private theorem crossing_right_one_law (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (q : ℚ)
    (hq : 1 < q) (σ : FactorType) :
    coeffAt q (stateLaw (.crossing a b c 1)) σ = if σ = {(c*a+b, 1)} then 1 else 0 := by
  rcases Nat.lt_or_ge 1 c with hc1 | hc1
  · obtain ⟨P, hA, hch, hX⟩ :=
      crossing_unique_pattern a b c 1 ha hb hc one_pos q (.inr rfl) (by omega)
    rw [if_pos hc1, if_neg (by omega), List.append_nil] at hch
    rw [coeff_crossing_of_unique ⟨ha, hb, hc, one_pos⟩ P hA _ hch q hX,
      crossing_left_one_law (a+b) a (c-1) (by omega) ha (by omega) q hq]
    obtain ⟨k, rfl⟩ : ∃ k, c = k+1 := ⟨c-1, by omega⟩
    simp only [Nat.add_sub_cancel]
    congr 2; ring_nf
  · obtain rfl : c = 1 := by omega
    simpa using crossing_one_one_law a b ha hb q hq σ

end Crossing

/-! ### The law of `S(a;2)` -/

section SingleTwo

private theorem returnWeight_eval (q : ℚ) (c : ℕ) :
    (Expr.inv (.sub (.const 1) (returnWeight c))).eval q = (1 - q / q ^ tri c)⁻¹ := by
  simp [returnWeight, Expr.eval, Expr.sub, Expr.neg, eval_pow, div_eq_mul_inv, sub_eq_add_neg]

/-- The tangent-point patterns of `S(a;2)`: a transverse tangent with a node, a double point, a
point of contact two (a self pattern) and a point of degree two. -/
private theorem single_two_law (a : ℕ) (ha : 0 < a) (q : ℚ) (hq : 1 < q) (σ : FactorType) :
    coeffAt q (stateLaw (.single a 2)) σ = (if σ = {(2*a,1)} then q/(q+1) else 0) +
      (if σ = {(a,1),(a,1)} then 1/(2*(q+1)) else 0) +
      (if σ = {(a,2)} then 1/(2*(q+1)) else 0) := by
  have hn : 2 ≤ (State.single a 2).degree := by simp [State.degree]; omega
  set D := (State.single a 2).degree
  let i0 : Fin D := ⟨0, by omega⟩
  let i1 : Fin D := ⟨1, by omega⟩
  let f1 : Fin (D+1) := ⟨1, by omega⟩
  let f2 : Fin (D+1) := ⟨2, by omega⟩
  let P1 : TangentPattern D := ⟨f1, f1, 0, spat (i0, i0) 0⟩
  let P2 : TangentPattern D := ⟨f2, 0, 0, spat (i0, i0) f2⟩
  let P3 : TangentPattern D := ⟨f2, 0, 0, spat (i0, i1) f1⟩
  let P4 : TangentPattern D := ⟨f2, 0, 0, spat (i1, i0) f1⟩
  have hA : allowedPatterns (.single a 2) = {P1, P2, P3, P4} := by
    ext P
    simp only [allowedPatterns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · obtain ⟨d, rt, rx, other⟩ := P
      rintro ⟨h0, hw, h1, h2, h3⟩
      simp only at h0 hw h1 h2 h3
      obtain rfl : rx = 0 := Fin.ext h2
      rcases (by omega : d.val = 1 ∨ d.val = 2) with hd | hd
      · have hrt : rt.val = 1 := by have := h3.1 (by omega); simp at hw; omega
        left
        rw [pattern_eq_zero other (by simp at hw; omega) (i0, i0)]
        simp only [P1, TangentPattern.mk.injEq, Fin.ext_iff, and_true]
        exact ⟨hd, hrt⟩
      · obtain rfl : rt = 0 := Fin.ext (by by_contra hc; have := h3.2 (by omega); omega)
        obtain rfl : d = f2 := Fin.ext hd
        right
        rcases pattern_eq_of_weight_two hn other (by simp at hw; omega) with ho | ho | ho <;>
          rw [ho]
        · left; rfl
        · right; left; rfl
        · right; right; rfl
    · rintro (rfl | rfl | rfl | rfl) <;> refine ⟨by simp [P1, P2, P3, P4, f1, f2], ?_, ?_⟩ <;>
        simp [P1, P2, P3, P4, patternWeight_spat, f1, f2, i0, i1]
  have hi01 : i0 ≠ i1 := by simp [i0, i1]
  have hne : P1 ≠ P2 ∧ P1 ≠ P3 ∧ P1 ≠ P4 ∧ P2 ≠ P3 ∧ P2 ≠ P4 ∧ P3 ≠ P4 := by
    refine ⟨by simp [P1, P2, f1, f2], by simp [P1, P3, f1, f2], by simp [P1, P4, f1, f2],
      ?_, ?_, ?_⟩
    all_goals intro h
    · simpa [P2, P3, spat, hi01, f2] using congrArg (fun P ↦ (P.other (i0, i0)).val) h
    · simpa [P2, P4, spat, hi01, f2] using congrArg (fun P ↦ (P.other (i0, i0)).val) h
    · simpa [P3, P4, spat, hi01, f1] using congrArg (fun P ↦ (P.other (i0, i1)).val) h
  rw [stateLaw_single _ _ ⟨ha, two_pos⟩ (by norm_num), coeff_scale, coeff_exitLaw, hA,
    Finset.sum_insert (by simp [hne]), Finset.sum_insert (by simp [hne]),
    Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  have hch1 : children (.single a 2) P1 = [(1, .crossing a a 1 1)] := by
    simp [children, P1, f1, otherChildren_spat]
  have hch2 : children (.single a 2) P2 = [(1, .single a 1), (1, .single a 1)] := by
    simp [children, P2, f2, otherChildren_spat, i0]
  have hch3 : children (.single a 2) P3 = [(1, .single a 2)] := by
    simp [children, P3, f1, otherChildren_spat, i0, i1]
  have hch4 : children (.single a 2) P4 = [(2, .single a 1)] := by
    simp [children, P4, f1, otherChildren_spat, i0, i1]
  have notSelf (P : TangentPattern D) (z : ℕ × State) (hz : children (.single a 2) P = [z])
      (h : z ≠ (1, .single a 2)) : ¬ SelfPattern (.single a 2) P := by
    rintro ⟨_, _, he, h'⟩; rw [hz] at h'; simp only [List.cons.injEq] at h'; exact h (he ▸ h'.1)
  have hS2 : ¬ SelfPattern (.single a 2) P2 := by
    rintro ⟨_, _, _, h⟩; rw [hch2] at h; simp at h
  rw [if_neg (notSelf P1 _ hch1 (by simp)), if_neg hS2,
    if_pos (show SelfPattern (.single a 2) P3 from ⟨a, 2, rfl, hch3⟩),
    if_neg (notSelf P4 _ hch4 (by simp)), hch1, hch2, hch4]
  simp only [childProd, List.map_cons, List.map_nil, stateLaw_terminal, lawDescend_lawAtom,
    lawProd_cons, lawProd_nil, coeff_mul_lawOne, coeff_descend_one,
    crossing_one_one_law a a ha ha q hq,
    coeff_mul_atom, coeff_lawAtom, ite_mem_erase]
  have hq0 : q ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := by linarith
  have hN1 : ((tangentCount (.single a 2) P1).mul
      (divisorProbability (.single a 2) P1.d.val)).eval q = (q - 1) / q := by
    simp [tangentCount, divisorCount_spat, P1, f1, divisorProbability, tri, Expr.eval, Expr.pow,
      eminusOne, Expr.sub, Expr.neg, falling, Expr.prod]
    field_simp; ring
  have hN2 : ((tangentCount (.single a 2) P2).mul
      (divisorProbability (.single a 2) P2.d.val)).eval q = q * (q - 1) / 2 / q ^ 3 := by
    simp [tangentCount, divisorCount_spat, P2, f2, divisorProbability, tri, Expr.eval, Expr.pow,
      Expr.sub, Expr.neg, falling, Expr.prod, availablePoints, i0, List.range_succ]
    ring
  have hN4 : ((tangentCount (.single a 2) P4).mul
      (divisorProbability (.single a 2) P4.d.val)).eval q = (q ^ 2 - q) / 2 / q ^ 3 := by
    simp [tangentCount, divisorCount_spat, P4, f1, f2, divisorProbability, tri, Expr.eval, Expr.pow,
      falling, Expr.prod, availablePoints, i1, pointCount_two, List.range_succ, Expr.sub, Expr.neg]
    ring
  have hR : (1 - q / q ^ tri 2)⁻¹ = q ^ 2 / ((q - 1) * (q + 1)) := by
    rw [show tri 2 = 3 from rfl, inv_eq_iff_eq_inv, inv_div]; field_simp; ring
  rw [hN1, hN2, hN4, returnWeight_eval, hR, ← two_mul]
  simp only [Multiset.insert_eq_cons, ite_eq_mul_indicator]
  have : q + 1 ≠ 0 := by linarith
  field_simp
  ring

end SingleTwo

/-! ### Quadratic expressions -/

section Quadratic

private theorem residuePatterns_two :
    residuePatterns 2 = {spat (0, 0) 2, spat (1, 0) 1, spat (0, 1) 1} := by
  unfold residuePatterns; decide

/-- The global law in degree two: two rational points, a point of degree two, or a point of
contact two (with the law of `S(1;2)`). -/
private theorem coeff_globalLaw_two (proj : Bool) (q : ℚ) (σ : FactorType) :
    coeffAt q (globalLaw proj 2) σ =
      (Expr.inv (if proj then projectiveNormalizer 2 else .pow .var 2)).eval q *
        ((divisorCount (if proj then 1 else 0) (spat (n := 2) (0, 0) 2)).eval q *
            (if σ = {(1,1), (1,1)} then 1 else 0) +
          ((divisorCount (if proj then 1 else 0) (spat (n := 2) (1, 0) 1)).eval q *
            (if σ = {(1,2)} then 1 else 0) +
          (divisorCount (if proj then 1 else 0) (spat (n := 2) (0, 1) 1)).eval q *
            coeffAt q (stateLaw (.single 1 2)) σ)) := by
  rw [globalLaw, coeff_scale, coeff_flatMap, Finset.sum_map_toList, residuePatterns_two,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [coeff_scale, otherChildren_spat]
  simp [List.replicate, stateLaw_terminal, lawDescend_lawAtom, lawProd_cons, lawProd_nil,
    coeff_mul_lawOne, coeff_descend_one, coeff_mul_atom, coeff_lawAtom, ite_mem_erase,
    Multiset.insert_eq_cons]

/-- **Quadratic monic densities.** For every `q > 1`, the universal monic expressions of degree `2`
take the values `q / (2(q + 1))` (split and inert types) and `1 / (q + 1)` (ramified type), and
vanish on every other type. -/
theorem monicExpr_two_eval (q : ℚ) (hq : 1 < q) (σ : FactorType) :
    (monicExpr 2 σ).eval q =
      (if σ = {(1,1), (1,1)} then q / (2 * (q + 1)) else 0) +
      (if σ = {(1,2)} then q / (2 * (q + 1)) else 0) +
      (if σ = {(2,1)} then 1 / (q + 1) else 0) := by
  rw [monicExpr, coeff_globalLaw_two, single_two_law 1 one_pos q hq]
  simp [divisorCount_spat, falling, availablePoints, Expr.eval, eval_prod, eval_pow, pointCount_two,
    Expr.sub, Expr.neg, List.range_succ, Multiset.insert_eq_cons, ite_eq_mul_indicator]
  have : q + 1 ≠ 0 := by positivity
  have : q ≠ 0 := by positivity
  field_simp
  ring

/-- **Quadratic projective densities.** For every `q > 1`, the universal projective expressions of
degree `2` take the values `1/2` (split), `(q² - q + 1) / (2(q² + q + 1))` (inert) and
`q / (q² + q + 1)` (ramified), and vanish on every other type. -/
theorem projectiveExpr_two_eval (q : ℚ) (hq : 1 < q) (σ : FactorType) :
    (projectiveExpr 2 σ).eval q =
      (if σ = {(1,1), (1,1)} then 1 / 2 else 0) +
      (if σ = {(1,2)} then (q ^ 2 - q + 1) / (2 * (q ^ 2 + q + 1)) else 0) +
      (if σ = {(2,1)} then q / (q ^ 2 + q + 1) else 0) := by
  rw [projectiveExpr, coeff_globalLaw_two, single_two_law 1 one_pos q hq]
  simp [divisorCount_spat, falling, availablePoints, Expr.eval, eval_prod, eval_pow, pointCount_two,
    Expr.sub, Expr.neg, List.range_succ, Multiset.insert_eq_cons, ite_eq_mul_indicator,
    projectiveNormalizer,
    eval_sum]
  have : q + 1 ≠ 0 := by positivity
  have : q ^ 2 + q + 1 ≠ 0 := by positivity
  field_simp
  ring

end Quadratic

/-! ### Children of single-boundary states -/

section SingleChildren

private theorem children_single_perm {a c : ℕ} (P : TangentPattern (State.single a c).degree)
    {l : List (ℕ × State)}
    (h : ((if P.rt.val = 0 then [] else [(1, State.crossing a a P.rt.val (c - P.d.val))]) ++
      otherChildrenList a P.other).Perm l) : (children (.single a c) P).Perm l :=
  (List.Perm.append_left _ ((univ_toList_perm _).flatMap_right _)).trans h

/-- Self patterns, decidably. -/
private theorem selfPattern_single_iff {a c : ℕ} (P : TangentPattern (State.single a c).degree) :
    SelfPattern (.single a c) P ↔
      ((if P.rt.val = 0 then [] else [(1, State.crossing a a P.rt.val (c - P.d.val))]) ++
        otherChildrenList a P.other).Perm [(1, .single a c)] := by
  have hp := children_single_perm P (List.Perm.refl _)
  constructor
  · rintro ⟨_, _, -, h⟩; exact hp.symm.trans (h ▸ List.Perm.refl _)
  · intro h; exact ⟨a, c, rfl, List.perm_singleton.1 (hp.trans h)⟩

end SingleChildren

/-! ### Degree three: patterns

Cells `(i, j)` of a pattern record points of degree `i + 1` and contact `j + 1`. -/

section DegreeThree

/-- One rational point of contact three (the self pattern of `S(1;3)`). -/
private abbrev m3Contact : Pattern 3 := fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 2 then 1 else 0
/-- One point of degree three. -/
private abbrev m3Inert : Pattern 3 := fun ij ↦ if ij.1.val = 2 ∧ ij.2.val = 0 then 1 else 0
/-- Two rational points, of contacts one and two. -/
private abbrev m3Tangent : Pattern 3 := fun ij ↦
  if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else if ij.1.val = 0 ∧ ij.2.val = 1 then 1 else 0
/-- A rational point and a point of degree two. -/
private abbrev m3Quadratic : Pattern 3 := fun ij ↦
  if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else if ij.1.val = 1 ∧ ij.2.val = 0 then 1 else 0
/-- Three rational points. -/
private abbrev m3Split : Pattern 3 := fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 3 else 0

private theorem allowed_single_one_three_iff (d rt rx : Fin 4) (m : Pattern 3) :
    Allowed (State.single 1 3) (⟨d, rt, rx, m⟩ : TangentPattern 3) ↔
      (⟨d, rt, rx, m⟩ : TangentPattern 3) ∈ ({⟨1, 1, 0, fun _ ↦ 0⟩, ⟨2, 2, 0, fun _ ↦ 0⟩,
        ⟨2, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩, ⟨3, 0, 0, m3Inert⟩,
        ⟨3, 0, 0, m3Quadratic⟩, ⟨3, 0, 0, m3Tangent⟩, ⟨3, 0, 0, m3Split⟩, ⟨3, 0, 0, m3Contact⟩} :
        Finset (TangentPattern 3)) := by
  change 0 < d.val ∧ rt.val + rx.val + patternWeight m = d.val ∧ d.val ≤ 3 ∧ rx.val = 0 ∧
    (0 < rt.val ↔ d.val < 3) ↔ _
  simp only [patternWeight, Fintype.sum_prod_type, Fin.sum_univ_three, Finset.mem_insert,
    Finset.mem_singleton, TangentPattern.mk.injEq, funext_iff, Prod.forall, Fin.forall_fin_succ,
    Fin.ext_iff, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true,
    m3Inert, m3Quadratic, m3Tangent, m3Split, m3Contact]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, and_self, and_true, and_false,
    ↓reduceIte, Nat.reduceEqDiff, show ((3 : Fin 4) : ℕ) = 3 from rfl]
  have := (m (0,0)).isLt; have := (m (0,1)).isLt; have := (m (0,2)).isLt
  have := (m (1,0)).isLt; have := (m (1,1)).isLt; have := (m (1,2)).isLt
  have := (m (2,0)).isLt; have := (m (2,1)).isLt; have := (m (2,2)).isLt
  have := d.isLt; have := rt.isLt; have := rx.isLt
  generalize (m (0,0)).val = a00 at *; generalize (m (0,1)).val = a01 at *
  generalize (m (0,2)).val = a02 at *; generalize (m (1,0)).val = a10 at *
  generalize (m (1,1)).val = a11 at *; generalize (m (1,2)).val = a12 at *
  generalize (m (2,0)).val = a20 at *; generalize (m (2,1)).val = a21 at *
  generalize (m (2,2)).val = a22 at *
  generalize d.val = dd at *; generalize rt.val = r at *; generalize rx.val = x at *
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a11 = 0 ∧ a12 = 0 ∧ a21 = 0 ∧ a22 = 0 ∧ x = 0 := by omega
    have : a01 ≤ 1 := by omega
    have : a10 ≤ 1 := by omega
    have : a02 ≤ 1 := by omega
    have : a20 ≤ 1 := by omega
    have : r ≤ 2 := by omega
    interval_cases dd <;> interval_cases r <;> (try (exfalso; omega)) <;>
      interval_cases a00 <;> (try (exfalso; omega)) <;> interval_cases a01 <;>
      (try (exfalso; omega)) <;> interval_cases a10 <;> (try (exfalso; omega)) <;>
      interval_cases a02 <;> (try (exfalso; omega)) <;> interval_cases a20 <;>
      (try (exfalso; omega)) <;> simp
  · rintro (h|h|h|h|h|h|h|h) <;> omega

open scoped Classical in
private def allowedThree : Finset (TangentPattern (State.single 1 3).degree) :=
  {⟨1, 1, 0, fun _ ↦ 0⟩, ⟨2, 2, 0, fun _ ↦ 0⟩,
    ⟨2, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩, ⟨3, 0, 0, m3Inert⟩,
    ⟨3, 0, 0, m3Quadratic⟩, ⟨3, 0, 0, m3Tangent⟩, ⟨3, 0, 0, m3Split⟩, ⟨3, 0, 0, m3Contact⟩}

private theorem allowedPatterns_single_one_three :
    allowedPatterns (.single 1 3) = allowedThree := by
  classical
  ext ⟨d, rt, rx, m⟩
  exact Finset.mem_filter.trans ((and_iff_right (Finset.mem_univ _)).trans
    (allowed_single_one_three_iff d rt rx m))

private theorem residuePatterns_three :
    residuePatterns 3 = {m3Inert, m3Quadratic, m3Tangent, m3Split, m3Contact} := by
  ext m
  have h := allowed_single_one_three_iff 3 0 0 m
  change 0 < 3 ∧ 0 + 0 + patternWeight m = 3 ∧ 3 ≤ 3 ∧ 0 = 0 ∧ (0 < 0 ↔ 3 < 3) ↔ _ at h
  simp only [residuePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa using h

open scoped Classical in
private theorem sum_allowed_single_one_three (f : TangentPattern (State.single 1 3).degree → ℚ) :
    ∑ P ∈ allowedPatterns (.single 1 3), (if SelfPattern (.single 1 3) P then 0 else f P) =
      f ⟨1, 1, 0, fun _ ↦ 0⟩ + f ⟨2, 2, 0, fun _ ↦ 0⟩ +
        f ⟨2, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩ +
        f ⟨3, 0, 0, m3Inert⟩ + f ⟨3, 0, 0, m3Quadratic⟩ + f ⟨3, 0, 0, m3Tangent⟩ +
        f ⟨3, 0, 0, m3Split⟩ := by
  rw [allowedPatterns_single_one_three, allowedThree]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp +decide only [selfPattern_single_iff, if_true, if_false, add_zero, add_assoc]

/-! ### Degree three: laws -/

private theorem coeff_m3Inert (q : ℚ) (σ : FactorType) :
    coeffAt q (childProd (otherChildren 1 m3Inert)) σ = if σ = {(1,3)} then 1 else 0 := by
  rw [coeff_otherChildren _ [(3, .single 1 1)] (by decide)]; simp_children

private theorem coeff_m3Quadratic (q : ℚ) (σ : FactorType) :
    coeffAt q (childProd (otherChildren 1 m3Quadratic)) σ =
      if σ = (1,1) ::ₘ {(1,2)} then 1 else 0 := by
  rw [coeff_otherChildren _ [(1, .single 1 1), (2, .single 1 1)] (by decide)]; simp_children

private theorem coeff_m3Split (q : ℚ) (σ : FactorType) :
    coeffAt q (childProd (otherChildren 1 m3Split)) σ =
      if σ = (1,1) ::ₘ (1,1) ::ₘ {(1,1)} then 1 else 0 := by
  rw [coeff_otherChildren _ [(1, .single 1 1), (1, .single 1 1), (1, .single 1 1)] (by decide)]
  simp_children

private theorem coeff_m3Tangent (q : ℚ) (hq : 1 < q) (σ : FactorType) :
    coeffAt q (childProd (otherChildren 1 m3Tangent)) σ =
      (if σ = (1,1) ::ₘ {(2,1)} then q/(q+1) else 0) +
        (if σ = (1,1) ::ₘ (1,1) ::ₘ {(1,1)} then 1/(2*(q+1)) else 0) +
        (if σ = (1,1) ::ₘ {(1,2)} then 1/(2*(q+1)) else 0) := by
  rw [coeff_otherChildren _ [(1, .single 1 1), (1, .single 1 2)] (by decide)]
  simp_children
  rw [single_two_law 1 one_pos q hq]
  simp only [ite_add_zero, ite_mem_erase, Multiset.insert_eq_cons]

private theorem divisorCount_m3 (q : ℚ) :
    (divisorCount 0 m3Inert).eval q = (q^3 - q) / 3 ∧
    (divisorCount 0 m3Quadratic).eval q = q * ((q^2 - q) / 2) ∧
    (divisorCount 0 m3Tangent).eval q = q * (q - 1) ∧
    (divisorCount 0 m3Split).eval q = q * (q - 1) * (q - 2) / 6 ∧
    (divisorCount 0 m3Contact).eval q = q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [divisorCount_eval, Fin.prod_univ_three, Fin.sum_univ_three, falling, eval_prod,
    availablePoints, Expr.eval, Expr.sub, Expr.neg, List.range_succ, pointCount_two,
    pointCount_three, m3Inert, m3Quadratic, m3Tangent, m3Split, m3Contact,
    -mul_eq_mul_left_iff] <;>
  ring_nf

private theorem children_single_one_three (m : Pattern 3) :
    children (.single 1 3) ⟨3, 0, 0, m⟩ = otherChildren (n := 3) 1 m := rfl

private theorem tangentCount_single_one_three (m : Pattern 3) :
    tangentCount (.single 1 3) ⟨3, 0, 0, m⟩ = divisorCount (n := 3) 0 m := rfl

private theorem single_three_law (q : ℚ) (hq : 1 < q) (σ : FactorType) :
    coeffAt q (stateLaw (.single 1 3)) σ =
      (if σ = {(3,1)} then q^2*(q^2+1)/(q^4+q^3+q^2+q+1) else 0) +
      (if σ = {(1,3)} then (q+1)/(3*(q^4+q^3+q^2+q+1)) else 0) +
      (if σ = {(1,1),(2,1)} then q*(q^3+q^2+1)/((q+1)*(q^4+q^3+q^2+q+1)) else 0) +
      (if σ = {(1,1),(1,2)} then (q^2+q+1)/(2*(q+1)*(q^4+q^3+q^2+q+1)) else 0) +
      (if σ = {(1,1),(1,1),(1,1)} then (q^2-q+1)/(6*(q+1)*(q^4+q^3+q^2+q+1)) else 0) := by
  obtain ⟨d1, d2, d3, d4, -⟩ := divisorCount_m3 q
  have hq0 : q ≠ 0 := by positivity
  have h5 : q ^ 5 - 1 ≠ 0 := by have : 1 < q ^ 5 := one_lt_pow₀ hq (by norm_num); linarith
  have hR : (Expr.inv (.sub (.const 1) (returnWeight 3))).eval q = q ^ 5 / (q ^ 5 - 1) := by
    rw [returnWeight_eval, show tri 3 = 6 from rfl, inv_eq_iff_eq_inv, inv_div]; field_simp
  rw [stateLaw_single 1 3 ⟨one_pos, by norm_num⟩ (by norm_num), coeff_scale, coeff_exitLaw,
    sum_allowed_single_one_three, hR]
  simp only [children_single_one_three, coeff_m3Inert, coeff_m3Quadratic, coeff_m3Split,
    coeff_m3Tangent q hq]
  rw [coeff_childProd_perm (children_single_perm _ (l := [(1, .crossing 1 1 1 2)]) (by decide)),
    coeff_childProd_perm (children_single_perm _ (l := [(1, .crossing 1 1 2 1)]) (by decide)),
    coeff_childProd_perm
      (children_single_perm _ (l := [(1, .single 1 1), (1, .crossing 1 1 1 1)]) (by decide))]
  simp_children
  rw [crossing_left_one_law 1 1 2 one_pos one_pos two_pos q hq,
    crossing_right_one_law 1 1 2 one_pos one_pos two_pos q hq,
    crossing_one_one_law 1 1 one_pos one_pos q hq]
  simp only [Expr.eval, tangentCount_single_one_three, d1, d2, d3, d4, ite_mem_erase]
  simp (disch := decide) only [tangentCount, divisorCount_zero, divisorCount_cell]
  simp [falling, availablePoints, Expr.prod, divisorProbability, tri, Expr.eval, eval_pow,
    eminusOne, Expr.sub, Expr.neg, State.degree, Multiset.insert_eq_cons, ite_eq_mul_indicator]
  have : q + 1 ≠ 0 := by positivity
  have : q ^ 4 + q ^ 3 + q ^ 2 + q + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **Cubic monic densities.** For every `q > 1`, the universal monic expressions of degree `3` on
the five valid cubic types, with `Φ₅(q) = q⁴ + q³ + q² + q + 1`; they vanish on every other type. -/
theorem monicExpr_three_eval (q : ℚ) (hq : 1 < q) (σ : FactorType) :
    (monicExpr 3 σ).eval q =
      (if σ = {(3,1)} then (q ^ 2 + 1) / (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) else 0) +
      (if σ = {(1,3)} then q ^ 3 * (q + 1) / (3 * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) else 0) +
      (if σ = {(1,1), (2,1)} then
        q * (q ^ 3 + q + 1) / ((q + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) else 0) +
      (if σ = {(1,1), (1,2)} then
        q ^ 3 * (q ^ 2 + q + 1) / (2 * (q + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) else 0) +
      (if σ = {(1,1), (1,1), (1,1)} then
        q ^ 3 * (q ^ 2 - q + 1) / (6 * (q + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) else 0) := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := divisorCount_m3 q
  rw [monicExpr, coeff_globalLaw, residuePatterns_three]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton, coeff_m3Inert, coeff_m3Quadratic, coeff_m3Tangent q hq, coeff_m3Split,
    coeff_otherChildren _ [(1, .single 1 3)] (by decide)]
  simp only [childProd, List.map_cons, List.map_nil, lawProd_cons, lawProd_nil, coeff_mul_lawOne,
    coeff_descend_one, single_three_law q hq, Bool.false_eq_true, if_false]
  simp [d1, d2, d3, d4, d5, Expr.eval, eval_pow, Multiset.insert_eq_cons, ite_eq_mul_indicator]
  have : q ≠ 0 := by positivity
  have : q + 1 ≠ 0 := by positivity
  have : q ^ 4 + q ^ 3 + q ^ 2 + q + 1 ≠ 0 := by positivity
  field_simp
  ring

end DegreeThree

/-! ### The law of `T(1,1;2,2)` -/

/-- The crossing state `T(1,1;2,2)` (tangent conic through the node): a point of degree two, a
rational point of contact two, or two rational points. -/
private theorem crossing_two_two_law (q : ℚ) (hq : 1 < q) (σ : FactorType) :
    coeffAt q (stateLaw (.crossing 1 1 2 2)) σ = (if σ = {(4,1)} then 1/(q+1) else 0) +
      (if σ = {(2,2)} then (q^2+q+1)/(2*q*(q+1)) else 0) +
      (if σ = {(2,1),(2,1)} then (q^2-q-1)/(2*q*(q+1)) else 0) := by
  have hn : 2 ≤ (State.crossing 1 1 2 2).degree := by decide
  set D := (State.crossing 1 1 2 2).degree
  let i0 : Fin D := ⟨0, by omega⟩
  let i1 : Fin D := ⟨1, by omega⟩
  let f1 : Fin (D+1) := ⟨1, by omega⟩
  let f2 : Fin (D+1) := ⟨2, by omega⟩
  let P1 : TangentPattern D := ⟨f2, 0, 0, spat (i1, i0) f1⟩
  let P2 : TangentPattern D := ⟨f2, 0, 0, spat (i0, i1) f1⟩
  let P3 : TangentPattern D := ⟨f2, 0, 0, spat (i0, i0) f2⟩
  have hA : allowedPatterns (.crossing 1 1 2 2) = {P1, P2, P3} := by
    ext P
    simp only [allowedPatterns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · obtain ⟨d, rt, rx, other⟩ := P
      rintro ⟨h0, hw, h1, h2, h3, h4⟩
      simp only at h0 hw h1 h2 h3 h4
      have hd : d.val = 2 := by
        by_contra hd; have := h3.2 (by omega); have := h4.2 (by omega); omega
      obtain rfl : rt = 0 :=
        Fin.ext (by rw [Fin.val_zero]; by_contra hc; have := h3.1 (by omega); omega)
      obtain rfl : rx = 0 :=
        Fin.ext (by rw [Fin.val_zero]; by_contra hc; have := h4.1 (by omega); omega)
      obtain rfl : d = f2 := Fin.ext hd
      rcases pattern_eq_of_weight_two hn other (by simp at hw; omega) with ho | ho | ho <;> rw [ho]
      · right; right; rfl
      · right; left; rfl
      · left; rfl
    · rintro (rfl | rfl | rfl) <;> refine ⟨by simp [P1, P2, P3, f2], ?_, ?_⟩ <;>
        simp [P1, P2, P3, patternWeight_spat, f1, f2, i0, i1]
  have hi01 : i0 ≠ i1 := by simp [i0, i1]
  have hne : P1 ≠ P2 ∧ P1 ≠ P3 ∧ P2 ≠ P3 := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
    · simpa [P1, P2, spat, hi01, hi01.symm, f1] using congrArg (fun P ↦ (P.other (i1, i0)).val) h
    · simpa [P1, P3, spat, hi01.symm, f1] using congrArg (fun P ↦ (P.other (i1, i0)).val) h
    · simpa [P2, P3, spat, hi01.symm, f1] using congrArg (fun P ↦ (P.other (i0, i1)).val) h
  have hS : ∀ P, ¬ SelfPattern (.crossing 1 1 2 2) P := by rintro P ⟨_, _, h, _⟩; cases h
  rw [stateLaw_crossing _ _ _ _ ⟨one_pos, one_pos, two_pos, two_pos⟩, coeff_exitLaw, hA,
    Finset.sum_insert (by simp [hne]), Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  simp only [if_neg (hS _)]
  have hch1 : children (.crossing 1 1 2 2) P1 = [(2, .single 2 1)] := by
    simp [children, P1, f1, otherChildren_spat, i0, i1]
  have hch2 : children (.crossing 1 1 2 2) P2 = [(1, .single 2 2)] := by
    simp [children, P2, f1, otherChildren_spat, i0, i1]
  have hch3 : children (.crossing 1 1 2 2) P3 = [(1, .single 2 1), (1, .single 2 1)] := by
    simp [children, P3, f2, otherChildren_spat, i0]
  rw [hch1, hch2, hch3]
  simp_children
  rw [single_two_law 2 two_pos q hq]
  have hq0 : q ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := by linarith
  have hDP : (divisorProbability (.crossing 1 1 2 2) 2).eval q = 1/(q*(q-1)) := by
    simp [divisorProbability, chooseTwo, Expr.eval, Expr.pow, eminusOne, Expr.sub, Expr.neg]
    ring
  simp only [Expr.eval, show P1.d.val = 2 from rfl, show P2.d.val = 2 from rfl,
    show P3.d.val = 2 from rfl, hDP]
  simp [tangentCount, divisorCount_spat, P1, P2, P3, f1, f2, falling, Expr.prod, availablePoints,
    i0, i1, pointCount_two, List.range_succ, Expr.sub, Expr.neg, Expr.eval, Multiset.insert_eq_cons,
    ite_eq_mul_indicator]
  have : q + 1 ≠ 0 := by positivity
  field_simp
  ring

/-! ### Degree four: patterns -/

section DegreeFour

/-- One rational point of contact four (the self pattern of `S(1;4)`). -/
private abbrev m4Contact : Pattern 4 := fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 3 then 1 else 0
/-- One point of degree two and contact two. -/
private abbrev m4QuadraticContact : Pattern 4 := fun ij ↦
  if ij.1.val = 1 ∧ ij.2.val = 1 then 1 else 0
/-- One point of degree four. -/
private abbrev m4Inert : Pattern 4 := fun ij ↦ if ij.1.val = 3 ∧ ij.2.val = 0 then 1 else 0
/-- A rational point of contact two and a point of degree two. -/
private abbrev m4TangentQuadratic : Pattern 4 := fun ij ↦
  if ij.1.val = 0 ∧ ij.2.val = 1 then 1 else if ij.1.val = 1 ∧ ij.2.val = 0 then 1 else 0
/-- Two rational points of contact two. -/
private abbrev m4TwoTangent : Pattern 4 := fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 1 then 2 else 0
/-- Two points of degree two. -/
private abbrev m4TwoQuadratic : Pattern 4 := fun ij ↦
  if ij.1.val = 1 ∧ ij.2.val = 0 then 2 else 0
/-- A rational point and a rational point of contact three. -/
private abbrev m4ContactThree : Pattern 4 := fun ij ↦
  if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else if ij.1.val = 0 ∧ ij.2.val = 2 then 1 else 0
/-- A rational point and a point of degree three. -/
private abbrev m4Cubic : Pattern 4 := fun ij ↦
  if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else if ij.1.val = 2 ∧ ij.2.val = 0 then 1 else 0
/-- Two rational points and a rational point of contact two. -/
private abbrev m4SplitTangent : Pattern 4 := fun ij ↦
  if ij.1.val = 0 ∧ ij.2.val = 0 then 2 else if ij.1.val = 0 ∧ ij.2.val = 1 then 1 else 0
/-- Two rational points and a point of degree two. -/
private abbrev m4SplitQuadratic : Pattern 4 := fun ij ↦
  if ij.1.val = 0 ∧ ij.2.val = 0 then 2 else if ij.1.val = 1 ∧ ij.2.val = 0 then 1 else 0
/-- Four rational points. -/
private abbrev m4Split : Pattern 4 := fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 4 else 0

open scoped Classical in
/-- The allowed patterns of `S(1;4)`. -/
private def allowedFour : Finset (TangentPattern (State.single 1 4).degree) :=
  {⟨1, 1, 0, fun _ ↦ 0⟩, ⟨2, 2, 0, fun _ ↦ 0⟩,
    ⟨2, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩, ⟨3, 3, 0, fun _ ↦ 0⟩,
    ⟨3, 2, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩,
    ⟨3, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 2 else 0⟩,
    ⟨3, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 1 then 1 else 0⟩,
    ⟨3, 1, 0, fun ij ↦ if ij.1.val = 1 ∧ ij.2.val = 0 then 1 else 0⟩,
    ⟨4, 0, 0, m4Split⟩, ⟨4, 0, 0, m4SplitTangent⟩, ⟨4, 0, 0, m4SplitQuadratic⟩,
    ⟨4, 0, 0, m4ContactThree⟩, ⟨4, 0, 0, m4Cubic⟩, ⟨4, 0, 0, m4TwoTangent⟩,
    ⟨4, 0, 0, m4TangentQuadratic⟩, ⟨4, 0, 0, m4TwoQuadratic⟩, ⟨4, 0, 0, m4QuadraticContact⟩,
    ⟨4, 0, 0, m4Inert⟩, ⟨4, 0, 0, m4Contact⟩}

private theorem allowed_single_one_four_iff (d rt rx : Fin 5) (m : Pattern 4) :
    Allowed (State.single 1 4) (⟨d, rt, rx, m⟩ : TangentPattern 4) ↔
      (⟨d, rt, rx, m⟩ : TangentPattern 4) ∈ ({⟨1, 1, 0, fun _ ↦ 0⟩, ⟨2, 2, 0, fun _ ↦ 0⟩,
    ⟨2, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩, ⟨3, 3, 0, fun _ ↦ 0⟩,
    ⟨3, 2, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩,
    ⟨3, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 2 else 0⟩,
    ⟨3, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 1 then 1 else 0⟩,
    ⟨3, 1, 0, fun ij ↦ if ij.1.val = 1 ∧ ij.2.val = 0 then 1 else 0⟩,
    ⟨4, 0, 0, m4Split⟩, ⟨4, 0, 0, m4SplitTangent⟩, ⟨4, 0, 0, m4SplitQuadratic⟩,
    ⟨4, 0, 0, m4ContactThree⟩, ⟨4, 0, 0, m4Cubic⟩, ⟨4, 0, 0, m4TwoTangent⟩,
    ⟨4, 0, 0, m4TangentQuadratic⟩, ⟨4, 0, 0, m4TwoQuadratic⟩, ⟨4, 0, 0, m4QuadraticContact⟩,
    ⟨4, 0, 0, m4Inert⟩, ⟨4, 0, 0, m4Contact⟩} : Finset (TangentPattern 4)) := by
  have fa4 (p : Fin 4 → Prop) : (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 :=
    ⟨fun h ↦ ⟨h 0, h 1, h 2, h 3⟩, fun ⟨h0, h1, h2, h3⟩ i ↦ by fin_cases i <;> assumption⟩
  change 0 < d.val ∧ rt.val + rx.val + patternWeight m = d.val ∧ d.val ≤ 4 ∧ rx.val = 0 ∧
    (0 < rt.val ↔ d.val < 4) ↔ _
  simp only [patternWeight, Fintype.sum_prod_type, Fin.sum_univ_four,
    Finset.mem_insert, Finset.mem_singleton, TangentPattern.mk.injEq, funext_iff, Prod.forall, fa4,
    Fin.ext_iff, m4Contact, m4QuadraticContact, m4Inert, m4TangentQuadratic, m4TwoTangent,
    m4TwoQuadratic, m4ContactThree, m4Cubic, m4SplitTangent, m4SplitQuadratic, m4Split]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, and_self, and_true, and_false,
    ↓reduceIte, Nat.reduceEqDiff, show ((3 : Fin 5) : ℕ) = 3 from rfl,
    show ((4 : Fin 5) : ℕ) = 4 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl]
  have := (m (0,0)).isLt; have := (m (0,1)).isLt; have := (m (0,2)).isLt; have := (m (0,3)).isLt
  have := (m (1,0)).isLt; have := (m (1,1)).isLt; have := (m (1,2)).isLt; have := (m (1,3)).isLt
  have := (m (2,0)).isLt; have := (m (2,1)).isLt; have := (m (2,2)).isLt; have := (m (2,3)).isLt
  have := (m (3,0)).isLt; have := (m (3,1)).isLt; have := (m (3,2)).isLt; have := (m (3,3)).isLt
  have := d.isLt; have := rt.isLt; have := rx.isLt
  generalize (m (0,0)).val = a00 at *; generalize (m (0,1)).val = a01 at *
  generalize (m (0,2)).val = a02 at *; generalize (m (0,3)).val = a03 at *
  generalize (m (1,0)).val = a10 at *; generalize (m (1,1)).val = a11 at *
  generalize (m (1,2)).val = a12 at *; generalize (m (1,3)).val = a13 at *
  generalize (m (2,0)).val = a20 at *; generalize (m (2,1)).val = a21 at *
  generalize (m (2,2)).val = a22 at *; generalize (m (2,3)).val = a23 at *
  generalize (m (3,0)).val = a30 at *; generalize (m (3,1)).val = a31 at *
  generalize (m (3,2)).val = a32 at *; generalize (m (3,3)).val = a33 at *
  generalize d.val = dd at *; generalize rt.val = r at *; generalize rx.val = x at *
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : a12 = 0 ∧ a13 = 0 ∧ a21 = 0 ∧ a22 = 0 ∧
      a23 = 0 ∧ a31 = 0 ∧ a32 = 0 ∧ a33 = 0 ∧ x = 0 := by omega
    have : a01 ≤ 2 := by omega
    have : a02 ≤ 1 := by omega
    have : a03 ≤ 1 := by omega
    have : a10 ≤ 2 := by omega
    have : a11 ≤ 1 := by omega
    have : a20 ≤ 1 := by omega
    have : a30 ≤ 1 := by omega
    have : r ≤ 3 := by omega
    interval_cases dd <;> interval_cases r <;> (try (exfalso; omega)) <;>
      interval_cases a00 <;> (try (exfalso; omega)) <;> interval_cases a01 <;>
      (try (exfalso; omega)) <;> interval_cases a02 <;> (try (exfalso; omega)) <;>
      interval_cases a03 <;> (try (exfalso; omega)) <;> interval_cases a10 <;>
      (try (exfalso; omega)) <;> interval_cases a11 <;> (try (exfalso; omega)) <;>
      interval_cases a20 <;> (try (exfalso; omega)) <;> interval_cases a30 <;>
      (try (exfalso; omega)) <;> simp
  · rintro (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h) <;> omega

private theorem allowedPatterns_single_one_four : allowedPatterns (.single 1 4) = allowedFour := by
  classical
  ext ⟨d, rt, rx, m⟩
  exact Finset.mem_filter.trans ((and_iff_right (Finset.mem_univ _)).trans
    (allowed_single_one_four_iff d rt rx m))

private theorem residuePatterns_four :
    residuePatterns 4 = {m4Split, m4SplitTangent, m4SplitQuadratic, m4ContactThree, m4Cubic,
      m4TwoTangent, m4TangentQuadratic, m4TwoQuadratic, m4QuadraticContact, m4Inert,
      m4Contact} := by
  ext m
  have h := allowed_single_one_four_iff 4 0 0 m
  change 0 < 4 ∧ 0 + 0 + patternWeight m = 4 ∧ 4 ≤ 4 ∧ 0 = 0 ∧ (0 < 0 ↔ 4 < 4) ↔ _ at h
  simp only [residuePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa using h

open scoped Classical in
private theorem sum_allowed_single_one_four (f : TangentPattern (State.single 1 4).degree → ℚ) :
    ∑ P ∈ allowedPatterns (.single 1 4), (if SelfPattern (.single 1 4) P then 0 else f P) =
      f ⟨1, 1, 0, fun _ ↦ 0⟩ + f ⟨2, 2, 0, fun _ ↦ 0⟩ +
        f ⟨2, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩ +
        f ⟨3, 3, 0, fun _ ↦ 0⟩ +
        f ⟨3, 2, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩ +
        f ⟨3, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 2 else 0⟩ +
        f ⟨3, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 1 then 1 else 0⟩ +
        f ⟨3, 1, 0, fun ij ↦ if ij.1.val = 1 ∧ ij.2.val = 0 then 1 else 0⟩ +
        f ⟨4, 0, 0, m4Split⟩ + f ⟨4, 0, 0, m4SplitTangent⟩ + f ⟨4, 0, 0, m4SplitQuadratic⟩ +
        f ⟨4, 0, 0, m4ContactThree⟩ + f ⟨4, 0, 0, m4Cubic⟩ + f ⟨4, 0, 0, m4TwoTangent⟩ +
        f ⟨4, 0, 0, m4TangentQuadratic⟩ + f ⟨4, 0, 0, m4TwoQuadratic⟩ +
        f ⟨4, 0, 0, m4QuadraticContact⟩ + f ⟨4, 0, 0, m4Inert⟩ := by
  rw [allowedPatterns_single_one_four, allowedFour]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp +decide only [selfPattern_single_iff, if_true, if_false, add_zero, add_assoc]

/-! ### Degree four: laws at `q = 2` -/

private theorem single_two_law_at_two (σ : FactorType) : coeffAt 2 (stateLaw (.single 1 2)) σ =
    (if σ = {(2,1)} then 2/3 else 0) + (if σ = (1,1) ::ₘ {(1,1)} then 1/6 else 0) +
      (if σ = {(1,2)} then 1/6 else 0) := by
  rw [single_two_law 1 one_pos 2 (by norm_num)]; norm_num [Multiset.insert_eq_cons]

private theorem single_two_law_at_four (σ : FactorType) :
    coeffAt (2^2) (stateLaw (.single 1 2)) σ =
      (if σ = {(2,1)} then 4/5 else 0) + (if σ = (1,1) ::ₘ {(1,1)} then 1/10 else 0) +
        (if σ = {(1,2)} then 1/10 else 0) := by
  rw [single_two_law 1 one_pos (2^2) (by norm_num)]; norm_num [Multiset.insert_eq_cons]

private theorem single_three_law_at_two (σ : FactorType) : coeffAt 2 (stateLaw (.single 1 3)) σ =
    (if σ = {(3,1)} then 20/31 else 0) + (if σ = {(1,3)} then 1/31 else 0) +
      (if σ = (1,1) ::ₘ {(2,1)} then 26/93 else 0) + (if σ = (1,1) ::ₘ {(1,2)} then 7/186 else 0) +
      (if σ = (1,1) ::ₘ (1,1) ::ₘ {(1,1)} then 1/186 else 0) := by
  rw [single_three_law 2 (by norm_num)]; norm_num [Multiset.insert_eq_cons]

private theorem crossing_two_two_law_at_two (σ : FactorType) :
    coeffAt 2 (stateLaw (.crossing 1 1 2 2)) σ = (if σ = {(4,1)} then 1/3 else 0) +
      (if σ = {(2,2)} then 7/12 else 0) + (if σ = (2,1) ::ₘ {(2,1)} then 1/12 else 0) := by
  rw [crossing_two_two_law 2 (by norm_num)]; norm_num [Multiset.insert_eq_cons]

private theorem coeff_m4Inert (q : ℚ) (σ : FactorType) :
    coeffAt q (childProd (otherChildren 1 m4Inert)) σ = if σ = {(1,4)} then 1 else 0 := by
  rw [coeff_otherChildren _ [(4, .single 1 1)] (by decide)]; simp_children

private theorem coeff_m4Cubic (q : ℚ) (σ : FactorType) :
    coeffAt q (childProd (otherChildren 1 m4Cubic)) σ = if σ = (1,1) ::ₘ {(1,3)} then 1 else 0 := by
  rw [coeff_otherChildren _ [(1, .single 1 1), (3, .single 1 1)] (by decide)]; simp_children

private theorem coeff_m4SplitQuadratic (q : ℚ) (σ : FactorType) :
    coeffAt q (childProd (otherChildren 1 m4SplitQuadratic)) σ =
      if σ = (1,1) ::ₘ (1,1) ::ₘ {(1,2)} then 1 else 0 := by
  rw [coeff_otherChildren _ [(1, .single 1 1), (1, .single 1 1), (2, .single 1 1)] (by decide)]
  simp_children

private theorem coeff_m4ContactThree (σ : FactorType) :
    coeffAt 2 (childProd (otherChildren 1 m4ContactThree)) σ =
      (if σ = (1,1) ::ₘ {(3,1)} then 20/31 else 0) + (if σ = (1,1) ::ₘ {(1,3)} then 1/31 else 0) +
      (if σ = (1,1) ::ₘ (1,1) ::ₘ {(2,1)} then 26/93 else 0) +
      (if σ = (1,1) ::ₘ (1,1) ::ₘ {(1,2)} then 7/186 else 0) +
      (if σ = (1,1) ::ₘ (1,1) ::ₘ (1,1) ::ₘ {(1,1)} then 1/186 else 0) := by
  rw [coeff_otherChildren _ [(1, .single 1 1), (1, .single 1 3)] (by decide)]
  simp_children
  rw [single_three_law_at_two]
  simp only [ite_add_zero, ite_mem_erase]

private theorem coeff_m4TangentQuadratic (σ : FactorType) :
    coeffAt 2 (childProd (otherChildren 1 m4TangentQuadratic)) σ =
      (if σ = (1,2) ::ₘ {(2,1)} then 2/3 else 0) +
      (if σ = (1,2) ::ₘ (1,1) ::ₘ {(1,1)} then 1/6 else 0) +
      (if σ = (1,2) ::ₘ {(1,2)} then 1/6 else 0) := by
  rw [coeff_otherChildren _ [(2, .single 1 1), (1, .single 1 2)] (by decide)]
  simp_children
  rw [single_two_law_at_two]
  simp only [ite_add_zero, ite_mem_erase]

private theorem coeff_m4SplitTangent (σ : FactorType) :
    coeffAt 2 (childProd (otherChildren 1 m4SplitTangent)) σ =
      (if σ = (1,1) ::ₘ (1,1) ::ₘ {(2,1)} then 2/3 else 0) +
      (if σ = (1,1) ::ₘ (1,1) ::ₘ (1,1) ::ₘ {(1,1)} then 1/6 else 0) +
      (if σ = (1,1) ::ₘ (1,1) ::ₘ {(1,2)} then 1/6 else 0) := by
  rw [coeff_otherChildren _ [(1, .single 1 1), (1, .single 1 1), (1, .single 1 2)] (by decide)]
  simp_children
  rw [single_two_law_at_two]
  simp only [ite_add_zero, ite_mem_erase]

private theorem coeff_m4QuadraticContact (σ : FactorType) :
    coeffAt 2 (childProd (otherChildren 1 m4QuadraticContact)) σ =
      (if σ = {(2,2)} then 4/5 else 0) + (if σ = (1,2) ::ₘ {(1,2)} then 1/10 else 0) +
        (if σ = {(1,4)} then 1/10 else 0) := by
  rw [coeff_otherChildren _ [(2, .single 1 2)] (by decide)]
  simp only [childProd, List.map_cons, List.map_nil, lawProd_cons, lawProd_nil, coeff_mul_lawOne]
  rw [show ({(2,2)} : FactorType) = scaleType 2 {(2,1)} by decide,
    show ((1,2) ::ₘ {(1,2)} : FactorType) = scaleType 2 ((1,1) ::ₘ {(1,1)}) by decide,
    show ({(1,4)} : FactorType) = scaleType 2 {(1,2)} by decide]
  by_cases h : ∃ τ, σ = scaleType 2 τ
  · obtain ⟨τ, rfl⟩ := h
    rw [coeff_descend_scaleType 2 two_pos, single_two_law_at_four]
    simp only [(scaleType_injective two_pos).eq_iff]
  · push Not at h
    rw [coeff_descend_of_ne 2 2 _ σ h, if_neg (h _), if_neg (h _), if_neg (h _)]
    norm_num

private theorem coeff_m4TwoTangent (σ : FactorType) :
    coeffAt 2 (childProd (otherChildren 1 m4TwoTangent)) σ =
      (if σ = {(2,1)} + {(2,1)} then 2/3 * (2/3) else 0) +
        (if σ = {(2,1)} + (1,1) ::ₘ {(1,1)} then 2/3 * (1/6) else 0) +
        (if σ = {(2,1)} + {(1,2)} then 2/3 * (1/6) else 0) +
      ((if σ = (1,1) ::ₘ {(1,1)} + {(2,1)} then 1/6 * (2/3) else 0) +
        (if σ = (1,1) ::ₘ {(1,1)} + (1,1) ::ₘ {(1,1)} then 1/6 * (1/6) else 0) +
        (if σ = (1,1) ::ₘ {(1,1)} + {(1,2)} then 1/6 * (1/6) else 0)) +
      ((if σ = {(1,2)} + {(2,1)} then 1/6 * (2/3) else 0) +
        (if σ = {(1,2)} + (1,1) ::ₘ {(1,1)} then 1/6 * (1/6) else 0) +
        (if σ = {(1,2)} + {(1,2)} then 1/6 * (1/6) else 0)) := by
  rw [coeff_otherChildren _ [(1, .single 1 2), (1, .single 1 2)] (by decide)]
  simp only [childProd, List.map_cons, List.map_nil, lawProd_cons]
  have hS : ∀ τ ∉ ({{(2,1)}, (1,1) ::ₘ {(1,1)}, {(1,2)}} : Finset FactorType),
      coeffAt 2 (lawDescend 1 (stateLaw (.single 1 2))) τ = 0 := by
    intro τ h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    rw [coeff_descend_one, single_two_law_at_two, if_neg h.1, if_neg h.2.1, if_neg h.2.2]; simp
  rw [coeff_mul 2 _ _ _ hS, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [lawProd_nil, coeff_mul_lawOne, coeff_descend_one, single_two_law_at_two]
  simp +decide only [if_true, if_false, add_zero, zero_add]
  simp only [mul_add, ite_add_zero, ite_le_sub]
  ring

private theorem children_single_one_four (m : Pattern 4) :
    children (.single 1 4) ⟨4, 0, 0, m⟩ = otherChildren (n := 4) 1 m := rfl

private theorem tangentCount_single_one_four (m : Pattern 4) :
    tangentCount (.single 1 4) ⟨4, 0, 0, m⟩ = divisorCount (n := 4) 0 m := rfl

private theorem divisorCount_m4_at_two :
    (divisorCount 0 m4Split).eval 2 = 0 ∧ (divisorCount 0 m4SplitTangent).eval 2 = 0 ∧
    (divisorCount 0 m4SplitQuadratic).eval 2 = 1 ∧ (divisorCount 0 m4ContactThree).eval 2 = 2 ∧
    (divisorCount 0 m4Cubic).eval 2 = 4 ∧ (divisorCount 0 m4TwoTangent).eval 2 = 1 ∧
    (divisorCount 0 m4TangentQuadratic).eval 2 = 2 ∧ (divisorCount 0 m4TwoQuadratic).eval 2 = 0 ∧
    (divisorCount 0 m4QuadraticContact).eval 2 = 1 ∧ (divisorCount 0 m4Inert).eval 2 = 3 ∧
    (divisorCount 0 m4Contact).eval 2 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [divisorCount_eval, Fin.prod_univ_four, Fin.sum_univ_four, falling, eval_prod,
    availablePoints, Expr.eval, Expr.sub, Expr.neg, List.range_succ, pointCount_two,
    pointCount_three, pointCount_four, m4Split, m4SplitTangent, m4SplitQuadratic, m4ContactThree,
    m4Cubic, m4TwoTangent, m4TangentQuadratic, m4TwoQuadratic, m4QuadraticContact, m4Inert,
    m4Contact] <;> norm_num [Nat.factorial]

/-- The children `T(1,1;1,1)` and `S(1;2)` (from the tangent pattern of `S(1;4)` with a point of
contact two). -/
private theorem coeff_crossing_one_one_single_two_at_two (σ : FactorType) :
    coeffAt 2 (childProd [(1, .crossing 1 1 1 1), (1, .single 1 2)]) σ =
      (if σ = {(2,1)} + {(2,1)} then 2/3 else 0) +
        (if σ = {(2,1)} + (1,1) ::ₘ {(1,1)} then 1/6 else 0) +
        (if σ = {(2,1)} + {(1,2)} then 1/6 else 0) := by
  have hS : ∀ τ ∉ ({{(2,1)}} : Finset FactorType),
      coeffAt 2 (lawDescend 1 (stateLaw (.crossing 1 1 1 1))) τ = 0 := fun τ h ↦ by
    rw [coeff_descend_one, crossing_one_one_law 1 1 one_pos one_pos 2 (by norm_num),
      if_neg (Finset.mem_singleton.not.1 h)]
  simp only [childProd, List.map_cons, List.map_nil, lawProd_cons]
  rw [coeff_mul 2 _ _ _ hS, Finset.sum_singleton, coeff_descend_one,
    crossing_one_one_law 1 1 one_pos one_pos 2 (by norm_num), if_pos rfl, lawProd_nil,
    coeff_mul_lawOne, coeff_descend_one, single_two_law_at_two]
  simp only [one_mul, ite_add_zero, ite_le_sub_one]

private theorem single_four_law_at_two (σ : FactorType) :
    coeffAt 2 (stateLaw (.single 1 4)) σ = (if σ = {(4,1)} then 856/1533 else 0) +
      (if σ = {(2,2)} then 566/7665 else 0) + (if σ = {(1,4)} then 31/10220 else 0) +
      (if σ = {(2,1),(2,1)} then 2/63 else 0) + (if σ = {(1,2),(1,2)} then 83/183960 else 0) +
      (if σ = {(1,2),(2,1)} then 103/4599 else 0) +
      (if σ = {(1,1),(3,1)} then 4484/15841 else 0) + (if σ = {(1,1),(1,3)} then 9/2263 else 0) +
      (if σ = {(1,1),(1,1),(2,1)} then 3085/142569 else 0) +
      (if σ = {(1,1),(1,1),(1,2)} then 817/570276 else 0) +
      (if σ = {(1,1),(1,1),(1,1),(1,1)} then 43/1140552 else 0) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, -⟩ := divisorCount_m4_at_two
  have hR : (Expr.inv (.sub (.const 1) (returnWeight 4))).eval 2 = 512/511 := by
    rw [returnWeight_eval, show tri 4 = 10 from rfl]; norm_num
  rw [stateLaw_single 1 4 ⟨one_pos, by norm_num⟩ (by norm_num), coeff_scale, coeff_exitLaw,
    sum_allowed_single_one_four, hR]
  simp only [children_single_one_four, coeff_m4Inert, coeff_m4Cubic, coeff_m4SplitQuadratic,
    coeff_m4ContactThree, coeff_m4TangentQuadratic, coeff_m4TwoTangent, coeff_m4QuadraticContact]
  rw [coeff_childProd_perm (children_single_perm _ (l := [(1, .crossing 1 1 1 3)]) (by decide)),
    coeff_childProd_perm (children_single_perm _ (l := [(1, .crossing 1 1 2 2)]) (by decide)),
    coeff_childProd_perm
      (children_single_perm _ (l := [(1, .single 1 1), (1, .crossing 1 1 1 2)]) (by decide)),
    coeff_childProd_perm (children_single_perm _ (l := [(1, .crossing 1 1 3 1)]) (by decide)),
    coeff_childProd_perm
      (children_single_perm _ (l := [(1, .single 1 1), (1, .crossing 1 1 2 1)]) (by decide)),
    coeff_childProd_perm (children_single_perm _
      (l := [(1, .single 1 1), (1, .single 1 1), (1, .crossing 1 1 1 1)]) (by decide)),
    coeff_childProd_perm
      (children_single_perm _ (l := [(1, .crossing 1 1 1 1), (1, .single 1 2)]) (by decide)),
    coeff_childProd_perm
      (children_single_perm _ (l := [(2, .single 1 1), (1, .crossing 1 1 1 1)]) (by decide)),
    coeff_crossing_one_one_single_two_at_two]
  simp_children
  simp only [crossing_left_one_law 1 1 3 one_pos one_pos (by norm_num) 2 (by norm_num),
    crossing_two_two_law_at_two,
    crossing_left_one_law 1 1 2 one_pos one_pos two_pos 2 (by norm_num),
    crossing_right_one_law 1 1 3 one_pos one_pos (by norm_num) 2 (by norm_num),
    crossing_right_one_law 1 1 2 one_pos one_pos two_pos 2 (by norm_num),
    crossing_one_one_law 1 1 one_pos one_pos 2 (by norm_num)]
  simp only [Expr.eval, tangentCount_single_one_four, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10,
    ite_mem_erase, zero_mul]
  simp only [ite_eq_mul_indicator]
  simp (disch := decide) only [tangentCount, divisorCount_zero, divisorCount_cell]
  simp only [divisorProbability, tri, State.degree, Nat.reduceMul, Nat.reduceAdd, Fin.isValue,
    Fin.coe_ofNat_eq_mod, one_mul, Nat.one_mod, Order.lt_two_iff, zero_le, Nat.div_self, eminusOne,
    Expr.sub, Expr.neg, Nat.one_lt_ofNat, ↓reduceIte, Expr.eval, eval_pow, pow_one, mul_one,
    Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, one_div, falling, availablePoints, zero_add,
    Int.cast_zero, List.range_succ, List.range_zero, List.nil_append, List.pure_def,
    List.bind_eq_flatMap, List.flatMap_cons, CharP.cast_eq_zero, List.flatMap_nil, List.append_nil,
    List.map_cons, List.map_nil, eval_prod, add_zero, mul_zero, List.prod_cons, List.prod_nil,
    Nat.factorial_one, Nat.cast_one, div_one, Nat.lt_add_one, List.cons_append, Nat.factorial_two,
    Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀,
    Multiset.singleton_add, Multiset.add_cons, OfNat.ofNat_ne_one, pointCount_two, Nat.mod_succ,
    lt_self_iff_false, pow_zero, Multiset.cons_add, Multiset.insert_eq_cons]
  sort_types
  ring

private theorem divisorCount_m4_projective_at_two :
    (divisorCount 1 m4Split).eval 2 = 0 ∧ (divisorCount 1 m4SplitTangent).eval 2 = 3 ∧
    (divisorCount 1 m4SplitQuadratic).eval 2 = 3 ∧ (divisorCount 1 m4ContactThree).eval 2 = 6 ∧
    (divisorCount 1 m4Cubic).eval 2 = 6 ∧ (divisorCount 1 m4TwoTangent).eval 2 = 3 ∧
    (divisorCount 1 m4TangentQuadratic).eval 2 = 3 ∧ (divisorCount 1 m4TwoQuadratic).eval 2 = 0 ∧
    (divisorCount 1 m4QuadraticContact).eval 2 = 1 ∧ (divisorCount 1 m4Inert).eval 2 = 3 ∧
    (divisorCount 1 m4Contact).eval 2 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [divisorCount_eval, Fin.prod_univ_four, Fin.sum_univ_four, falling, eval_prod,
    availablePoints, Expr.eval, Expr.sub, Expr.neg, List.range_succ, pointCount_two,
    pointCount_three, pointCount_four, m4Split, m4SplitTangent, m4SplitQuadratic, m4ContactThree,
    m4Cubic, m4TwoTangent, m4TangentQuadratic, m4TwoQuadratic, m4QuadraticContact, m4Inert,
    m4Contact] <;> norm_num [Nat.factorial]

private theorem coeff_m4Contact_at_two (σ : FactorType) :
    coeffAt 2 (childProd (otherChildren 1 m4Contact)) σ = coeffAt 2 (stateLaw (.single 1 4)) σ := by
  rw [coeff_otherChildren _ [(1, .single 1 4)] (by decide)]
  simp only [childProd, List.map_cons, List.map_nil, lawProd_cons, lawProd_nil, coeff_mul_lawOne,
    coeff_descend_one]

/-- **Quartic monic densities at `q = 2`.** The values at `q = 2` of the universal monic
expressions of degree `4` on all eleven valid quartic types (and `0` on every other type). -/
theorem monicExpr_four_eval_two (σ : FactorType) :
    (monicExpr 4 σ).eval 2 =
      (if σ = {(4,1)} then 107/1533 else 0) + (if σ = {(2,2)} then 454/7665 else 0) +
      (if σ = {(1,4)} then 496/2555 else 0) + (if σ = {(2,1), (2,1)} then 2/63 else 0) +
      (if σ = {(1,2), (1,2)} then 664/22995 else 0) +
      (if σ = {(1,2), (2,1)} then 460/4599 else 0) +
      (if σ = {(1,1), (3,1)} then 1838/15841 else 0) +
      (if σ = {(1,1), (1,3)} then 576/2263 else 0) +
      (if σ = {(1,1), (1,1), (2,1)} then 7348/142569 else 0) +
      (if σ = {(1,1), (1,1), (1,2)} then 13072/142569 else 0) +
      (if σ = {(1,1), (1,1), (1,1), (1,1)} then 344/142569 else 0) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := divisorCount_m4_at_two
  rw [monicExpr, coeff_globalLaw, residuePatterns_four]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [Bool.false_eq_true, if_false, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, zero_mul,
    zero_add, coeff_m4Inert, coeff_m4Cubic, coeff_m4SplitQuadratic, coeff_m4ContactThree,
    coeff_m4TangentQuadratic, coeff_m4TwoTangent, coeff_m4QuadraticContact, coeff_m4Contact_at_two,
    single_four_law_at_two]
  simp only [ite_eq_mul_indicator]
  simp only [Expr.eval, eval_pow]
  sort_types
  ring

/-- **Quartic projective densities at `q = 2`.** The values at `q = 2` of the universal projective
expressions of degree `4` on all eleven valid quartic types (and `0` on every other type). -/
theorem projectiveExpr_four_eval_two (σ : FactorType) :
    (projectiveExpr 4 σ).eval 2 =
      (if σ = {(4,1)} then 856/15841 else 0) + (if σ = {(2,2)} then 522/15841 else 0) +
      (if σ = {(1,4)} then 205/2044 else 0) + (if σ = {(2,1), (2,1)} then 10/217 else 0) +
      (if σ = {(1,2), (1,2)} then 2799/126728 else 0) +
      (if σ = {(1,2), (2,1)} then 1397/15841 else 0) +
      (if σ = {(1,1), (3,1)} then 2412/15841 else 0) +
      (if σ = {(1,1), (1,3)} then 453/2263 else 0) +
      (if σ = {(1,1), (1,1), (2,1)} then 2253/15841 else 0) +
      (if σ = {(1,1), (1,1), (1,2)} then 8987/63364 else 0) +
      (if σ = {(1,1), (1,1), (1,1), (1,1)} then 2517/126728 else 0) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := divisorCount_m4_projective_at_two
  rw [projectiveExpr, coeff_globalLaw, residuePatterns_four]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [if_true, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, zero_mul, zero_add,
    coeff_m4Inert, coeff_m4Cubic, coeff_m4SplitQuadratic, coeff_m4ContactThree,
    coeff_m4TangentQuadratic, coeff_m4TwoTangent, coeff_m4QuadraticContact, coeff_m4Contact_at_two,
    coeff_m4SplitTangent, single_four_law_at_two]
  simp only [ite_eq_mul_indicator]
  simp only [Expr.eval, projectiveNormalizer, eval_sum, List.range_succ, List.range_zero,
    List.map_append, List.map_cons, List.map_nil, eval_pow]
  sort_types
  norm_num
  ring

end DegreeFour

/-! ### Regression guards: point values of the universal expressions -/

/-- The three quadratic monic types are equidistributed at `q = 2`: split. -/
theorem monicExpr_two_split_eval_two : (monicExpr 2 {(1,1), (1,1)}).eval 2 = 1/3 := by
  rw [monicExpr_two_eval 2 one_lt_two]; simp +decide; norm_num

/-- The three quadratic monic types are equidistributed at `q = 2`: inert. -/
theorem monicExpr_two_inert_eval_two : (monicExpr 2 {(1,2)}).eval 2 = 1/3 := by
  rw [monicExpr_two_eval 2 one_lt_two]; simp +decide; norm_num

/-- The three quadratic monic types are equidistributed at `q = 2`: ramified. -/
theorem monicExpr_two_ramified_eval_two : (monicExpr 2 {(2,1)}).eval 2 = 1/3 := by
  rw [monicExpr_two_eval 2 one_lt_two]; simp +decide; norm_num

/-- Totally ramified cubics at `q = 3`: `A_{3,(3,1)}(3) = 10/121`. -/
theorem monicExpr_three_totally_ramified_eval_three : (monicExpr 3 {(3,1)}).eval 3 = 10/121 := by
  rw [monicExpr_three_eval 3 (by norm_num)]; simp +decide; norm_num

/-- Totally ramified quartics at `q = 2`: `A_{4,(4,1)}(2) = 107/1533`. -/
theorem monicExpr_four_totally_ramified_eval_two : (monicExpr 4 {(4,1)}).eval 2 = 107/1533 := by
  rw [monicExpr_four_eval_two]; simp +decide

/-- Totally ramified binary quartic forms at `q = 2`: `B_{4,(4,1)}(2) = 856/15841`. -/
theorem projectiveExpr_four_totally_ramified_eval_two :
    (projectiveExpr 4 {(4,1)}).eval 2 = 856/15841 := by
  rw [projectiveExpr_four_eval_two]; simp +decide

/-- Quartics generating a ramified quadratic extension of a quadratic one (type `(2,2)`) at
`q = 2`: `454/7665`. -/
theorem monicExpr_four_ramified_quadratic_eval_two : (monicExpr 4 {(2,2)}).eval 2 = 454/7665 := by
  rw [monicExpr_four_eval_two]; simp +decide

/-- Products of two distinct inert quadratics (type `(1,2),(1,2)`) at `q = 2`: `664/22995`. -/
theorem monicExpr_four_two_inert_quadratics_eval_two :
    (monicExpr 4 {(1,2), (1,2)}).eval 2 = 664/22995 := by
  rw [monicExpr_four_eval_two]; simp +decide

/-! ### Density corollaries of `main_dvr` -/

section Densities

open IsLocalRing

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
  [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
  [MeasurableSpace O] [BorelSpace O]

private theorem densityValue_eq {x : Expr} {q : ℕ} {r : ℚ} (h : x.eval q = r) :
    densityValue x q = ENNReal.ofReal r := by
  rw [densityValue, h]

omit [IsAdicComplete (maximalIdeal O) O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O]
  [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] in
private theorem one_lt_card_residueField : 1 < (Nat.card (ResidueField O) : ℚ) := by
  exact_mod_cast Finite.one_lt_card

/-- Over any complete DVR with finite residue field of cardinality `q`, a random monic quadratic
is ramified (type `(2,1)`) with probability `1 / (q + 1)`. -/
theorem monicDensity_two_ramified (htop : IsAdic (maximalIdeal O)) :
    monicDensity O 2 {(2,1)} = ENNReal.ofReal (1 / (Nat.card (ResidueField O) + 1)) := by
  rw [(main_dvr O htop 2 {(2,1)}).1, densityValue_eq
    (monicExpr_two_eval _ (one_lt_card_residueField O) _)]
  simp +decide

/-- Over any complete DVR with finite residue field of cardinality `q`, a random primitive binary
quadratic form is ramified (type `(2,1)`) with probability `q / (q² + q + 1)`. -/
theorem projectiveDensity_two_ramified (htop : IsAdic (maximalIdeal O)) :
    projectiveDensity O 2 {(2,1)} = ENNReal.ofReal (Nat.card (ResidueField O) /
      ((Nat.card (ResidueField O)) ^ 2 + Nat.card (ResidueField O) + 1)) := by
  rw [(main_dvr O htop 2 {(2,1)}).2, densityValue_eq
    (projectiveExpr_two_eval _ (one_lt_card_residueField O) _)]
  simp +decide

/-- Residue field `𝔽₃`: a random monic cubic is totally ramified with probability `10/121`. -/
theorem monicDensity_three_totally_ramified_of_card_eq_three (htop : IsAdic (maximalIdeal O))
    (hq : Nat.card (ResidueField O) = 3) : monicDensity O 3 {(3,1)} = ENNReal.ofReal (10/121) := by
  rw [(main_dvr O htop 3 {(3,1)}).1, hq,
    densityValue_eq monicExpr_three_totally_ramified_eval_three]
  norm_num

/-- Residue field `𝔽₂`: a random monic quartic is totally ramified with probability `107/1533`. -/
theorem monicDensity_four_totally_ramified_of_card_eq_two (htop : IsAdic (maximalIdeal O))
    (hq : Nat.card (ResidueField O) = 2) :
    monicDensity O 4 {(4,1)} = ENNReal.ofReal (107/1533) := by
  rw [(main_dvr O htop 4 {(4,1)}).1, hq,
    densityValue_eq monicExpr_four_totally_ramified_eval_two]
  norm_num

/-- Residue field `𝔽₂`: a random primitive binary quartic form is totally ramified with
probability `856/15841`. -/
theorem projectiveDensity_four_totally_ramified_of_card_eq_two (htop : IsAdic (maximalIdeal O))
    (hq : Nat.card (ResidueField O) = 2) :
    projectiveDensity O 4 {(4,1)} = ENNReal.ofReal (856/15841) := by
  rw [(main_dvr O htop 4 {(4,1)}).2, hq,
    densityValue_eq projectiveExpr_four_totally_ramified_eval_two]
  norm_num

/-- Residue field `𝔽₂`: a random monic quartic is irreducible of type `(2,2)` with probability
`454/7665`. -/
theorem monicDensity_four_ramified_quadratic_of_card_eq_two (htop : IsAdic (maximalIdeal O))
    (hq : Nat.card (ResidueField O) = 2) :
    monicDensity O 4 {(2,2)} = ENNReal.ofReal (454/7665) := by
  rw [(main_dvr O htop 4 {(2,2)}).1, hq,
    densityValue_eq monicExpr_four_ramified_quadratic_eval_two]
  norm_num

/-- Residue field `𝔽₂`: a random monic quartic is a product of two distinct inert quadratics with
probability `664/22995`. -/
theorem monicDensity_four_two_inert_quadratics_of_card_eq_two (htop : IsAdic (maximalIdeal O))
    (hq : Nat.card (ResidueField O) = 2) :
    monicDensity O 4 {(1,2), (1,2)} = ENNReal.ofReal (664/22995) := by
  rw [(main_dvr O htop 4 {(1,2), (1,2)}).1, hq,
    densityValue_eq monicExpr_four_two_inert_quadratics_eval_two]
  norm_num

end Densities

open PowerSeries in
open scoped PowerSeries.WithPiTopology in
/-- End-to-end test: over `𝔽₂⟦X⟧`, a random monic quartic is totally ramified with probability
`107/1533`. -/
theorem monicDensity_powerSeries_zmod_two_four_totally_ramified :
    monicDensity (ZMod 2)⟦X⟧ 4 {(4,1)} = ENNReal.ofReal (107/1533) := by
  rw [(main_dvr_zmod 2 4 {(4,1)}).1,
    densityValue_eq monicExpr_four_totally_ramified_eval_two]
  norm_num

end SurfaceBlowup.Tests

#print axioms SurfaceBlowup.Tests.monicExpr_four_eval_two
#print axioms SurfaceBlowup.Tests.projectiveExpr_four_eval_two
#print axioms SurfaceBlowup.Tests.monicExpr_three_eval
#print axioms SurfaceBlowup.Tests.projectiveExpr_two_eval
#print axioms SurfaceBlowup.Tests.monicDensity_two_ramified
#print axioms SurfaceBlowup.Tests.projectiveDensity_two_ramified
#print axioms SurfaceBlowup.Tests.monicDensity_three_totally_ramified_of_card_eq_three
#print axioms SurfaceBlowup.Tests.monicDensity_four_totally_ramified_of_card_eq_two
#print axioms SurfaceBlowup.Tests.projectiveDensity_four_totally_ramified_of_card_eq_two
#print axioms SurfaceBlowup.Tests.monicDensity_four_ramified_quadratic_of_card_eq_two
#print axioms SurfaceBlowup.Tests.monicDensity_four_two_inert_quadratics_of_card_eq_two
#print axioms SurfaceBlowup.Tests.monicDensity_powerSeries_zmod_two_four_totally_ramified
