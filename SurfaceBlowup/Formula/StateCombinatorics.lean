/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Formula.LawAlgebra

/-!
# Combinatorics of states, ranks and safety of the laws

Combinatorial facts about states and their children under one blowup step: positivity of
degrees, the unique self pattern of a single-branch state, strict decrease of the rank along
non-self children (which makes the fuel-based recursion `stateLawFuel` stable), and the
resulting safety (no division by zero at integers `q ≥ 2`) of the local and global laws, hence
regularity of the global formula. Also small arithmetic facts on `tri`, return weights,
divisor probabilities and scaled types.

## Main results

* `SurfaceBlowup.self_patterns_of_single_state`: `S(a; c)` has a unique self pattern.
* `SurfaceBlowup.nonself_child_rank_lt`: non-self children have strictly smaller rank.
* `SurfaceBlowup.state_fuel_stable`: `stateLawFuel k s = stateLaw s` once `rank s < k`.
* `SurfaceBlowup.state_law_unfold`: the law of a non-terminal state in terms of its exit law
  `exitLaw` (the non-self part of the recursion).
* `SurfaceBlowup.local_law_safe`, `SurfaceBlowup.global_law_safe`: safety of the laws.
* `SurfaceBlowup.global_formula_regular`: the global formula is regular at prime powers.
* `SurfaceBlowup.scale_type_valid_degree_iff`: scaling types by `δ` preserves validity and
  multiplies degrees by `δ`.

Provenance: `Thm_SurfaceBlowupV2_*` for self_patterns_of_single_state, state_degree_pos,
equal_degree_child_is_unique, state_weight_le_degree, rank_lt_of_weight_gt, nonself_child_rank_lt,
state_fuel_stable, exitLaw, state_law_unfold, tangent_weight_safe, terminal_law, tri_chooseTwo,
tri_ge_three, return_weight_bounds, divisor_probability_pos, local_law_safe, global_law_safe,
global_coefficients_safe, global_formula_regular, type_degree_scale,
scale_type_valid_degree_iff.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-! ### The self pattern of a single-branch state -/

/-- Multiplicity of a given "other" child in `otherChildren a m`. -/
private theorem count_otherChildren {n : ℕ} (a : ℕ) (m : Pattern n) (i j : Fin n) :
    (otherChildren a m).count (i.val + 1, State.single a (j.val + 1)) = (m (i, j)).val := by
  unfold otherChildren
  rw [List.count_flatMap, Finset.sum_map_toList]
  simp only [Function.comp, List.count_replicate]
  rw [Finset.sum_eq_single (i,j)]
  · simp
  · intro b _ hb
    refine if_neg fun h ↦ hb ?_
    simp only [beq_iff_eq, Prod.mk.injEq, State.single.injEq, add_left_inj, true_and] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  · simp

/-- The indicator pattern of the cell `(0, c - 1)`. -/
private abbrev IsSelfOther {n : ℕ} (c : ℕ) (m : Pattern n) : Prop :=
  ∀ ij, (m ij).val = if ij.1.val = 0 ∧ ij.2.val + 1 = c then 1 else 0

/-- Sums over `Fin n × Fin n` of the indicator of the cell `(0, c - 1)`. -/
private theorem sum_selfOther {n : ℕ} (c : ℕ) (hc : 0 < c) (hcn : c ≤ n) (f : Fin n × Fin n → ℕ)
    (hf : ∀ ij, ¬ (ij.1.val = 0 ∧ ij.2.val + 1 = c) → f ij = 0) :
    ∑ ij, f ij = f (⟨0, by omega⟩, ⟨c-1, by omega⟩) := by
  refine Finset.sum_eq_single _ (fun b _ hb ↦ hf b fun ⟨h1, h2⟩ ↦ hb ?_) (by simp)
  exact Prod.ext (Fin.ext h1) (Fin.ext (by simp; omega))

private theorem weight_selfOther {n : ℕ} (c : ℕ) (hc : 0 < c) (hcn : c ≤ n) (m : Pattern n)
    (hm : IsSelfOther c m) : patternWeight m = c := by
  unfold patternWeight
  rw [sum_selfOther c hc hcn _ fun ij h ↦ by rw [hm, if_neg h, mul_zero], hm,
    if_pos ⟨rfl, show c - 1 + 1 = c by omega⟩]
  change (0+1)*((c-1)+1)*1 = c; omega

private theorem otherChildren_selfOther {n : ℕ} (a c : ℕ) (hc : 0 < c) (hcn : c ≤ n)
    (m : Pattern n) (hm : IsSelfOther c m) :
    otherChildren a m = [(1, State.single a c)] := by
  have h1 : (otherChildren a m).length = 1 := by
    rw [otherChildren, List.length_flatMap, Finset.sum_map_toList]
    simp only [List.length_replicate]
    rw [sum_selfOther c hc hcn _ fun ij h ↦ by rw [hm, if_neg h], hm,
      if_pos ⟨rfl, show c - 1 + 1 = c by omega⟩]
  have h2 := count_otherChildren a m ⟨0, by omega⟩ ⟨c-1, by omega⟩
  rw [hm, if_pos ⟨rfl, show c - 1 + 1 = c by omega⟩] at h2
  simp only [show c - 1 + 1 = c by omega] at h2
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.1 h1
  rw [hy] at h2 ⊢
  by_cases e : y = (1, State.single a c)
  · rw [e]
  · simp [e] at h2

/-- The unique self pattern of `S(a; c)`. -/
private def selfPattern (a c : ℕ) (hc : 0 < c) (hca : c ≤ a * c) :
    TangentPattern (State.single a c).degree where
  d := ⟨c, by change c < a*c+1; omega⟩
  rt := ⟨0, by change 0 < a*c+1; omega⟩
  rx := ⟨0, by change 0 < a*c+1; omega⟩
  other := fun ij ↦ if ij.1.val = 0 ∧ ij.2.val + 1 = c then ⟨1, by change 1 < a*c+1; omega⟩
    else ⟨0, by change 0 < a*c+1; omega⟩

private theorem selfPattern_other (a c : ℕ) (hc : 0 < c) (hca : c ≤ a * c) :
    IsSelfOther c (selfPattern a c hc hca).other := fun ij ↦ by
  simp only [selfPattern]; split_ifs <;> rfl

/-- Every allowed self pattern of `S(a; c)` is `selfPattern a c`. -/
private theorem eq_selfPattern (a c : ℕ) (hc : 0 < c) (hca : c ≤ a * c)
    (P : TangentPattern (State.single a c).degree) (hA : Allowed (.single a c) P)
    (hS : SelfPattern (.single a c) P) : P = selfPattern a c hc hca := by
  obtain ⟨a', c', hs, hch⟩ := hS
  cases hs
  have hrt : P.rt.val = 0 := by
    by_contra h
    simp [children, h] at hch
  simp only [children, hrt, if_true, List.nil_append] at hch
  have hm : IsSelfOther c P.other := by
    intro ij
    rw [← count_otherChildren a P.other ij.1 ij.2, hch]
    simp [List.count_cons]
    split_ifs <;> omega
  have hw := weight_selfOther (n := (State.single a c).degree) c hc hca _ hm
  obtain ⟨hd0, hsum, hdc, hrx, hiff⟩ := hA
  obtain ⟨d, rt, rx, other⟩ := P
  simp only at hrt hrx hsum hm hw hd0 hdc hiff
  unfold selfPattern
  congr 1
  · ext; change d.val = c; omega
  · ext; change rt.val = 0; omega
  · ext; change rx.val = 0; omega
  · funext ij; ext; rw [hm]; split_ifs <;> rfl

open scoped Classical in
/-- The self patterns among the allowed patterns of `S(a; c)` are exactly `[selfPattern a c]`. -/
private theorem filter_selfPattern_eq (a c : ℕ) (hc : 0 < c) (hca : c ≤ a * c) :
    (allowedPatterns (.single a c)).toList.filter (SelfPattern (.single a c)) =
      [selfPattern a c hc hca] := by
  have hmem : selfPattern a c hc hca ∈
      (allowedPatterns (.single a c)).toList.filter (SelfPattern (.single a c)) := by
    simp only [List.mem_filter, Finset.mem_toList, allowedPatterns, Finset.mem_filter,
      Finset.mem_univ, true_and, decide_eq_true_eq]
    have hw := weight_selfOther (n := (State.single a c).degree) c hc hca _
      (selfPattern_other a c hc hca)
    have ho := otherChildren_selfOther (n := (State.single a c).degree) a c hc hca _
      (selfPattern_other a c hc hca)
    refine ⟨⟨hc, ?_, ?_⟩, a, c, rfl, by simp only [children, ho]; rfl⟩
    · rw [hw]; change 0 + 0 + c = c; omega
    · change c ≤ c ∧ 0 = 0 ∧ (0 < 0 ↔ c < c); omega
  refine ((List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).filter _)
    (List.nodup_singleton _)).2 fun b ↦ ⟨fun hb ↦ ?_, fun hb ↦ ?_⟩).eq_singleton
  · simp only [List.mem_filter, Finset.mem_toList, allowedPatterns, Finset.mem_filter,
      decide_eq_true_eq] at hb
    exact List.mem_singleton.2 (eq_selfPattern a c hc hca b hb.1.2 hb.2)
  · exact List.mem_singleton.1 hb ▸ hmem

/-- The tangent count of `selfPattern a c` evaluates to `q`. -/
private theorem tangentCount_selfPattern_eval (a c q : ℕ) (hc : 0 < c) (hca : c ≤ a * c) :
    (tangentCount (.single a c) (selfPattern a c hc hca)).eval (q:ℚ) = q := by
  simp only [tangentCount, divisorCount]
  rw [expression_prod_eval, List.map_map, Finset.prod_map_toList,
    Finset.prod_eq_single (⟨0, by change 0 < a*c; omega⟩ : Fin (State.single a c).degree)]
  · simp only [Function.comp, Expr.eval, selfPattern_other, true_and]
    have hs : (∑ x : Fin (State.single a c).degree, if x.val + 1 = c then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single (⟨c-1, by change c-1 < a*c; omega⟩ :
        Fin (State.single a c).degree)]
      · simp; omega
      · exact fun b _ hb ↦ if_neg fun h ↦ hb (Fin.ext (by simp; omega))
      · simp
    have hp : (∏ x : Fin (State.single a c).degree,
        (((if x.val + 1 = c then 1 else 0 : ℕ)).factorial : ℚ)) = 1 :=
      Finset.prod_eq_one fun j _ ↦ by split_ifs <;> simp
    rw [hs, hp]
    simp [falling, expression_prod_eval, availablePoints, Expr.sub, Expr.neg, Expr.eval]
  · intro b _ hb
    simp [selfPattern_other, Fin.val_ne_iff.2 hb, falling, expression_prod_eval, Expr.eval]
  · simp

open scoped Classical in
/-- A single-branch state `S(a; c)` with `c ≥ 2` has exactly one self pattern (of
multiplicity `d = c`, with the state itself as only child), whose tangent count at `q` is
`q`. -/
theorem self_patterns_of_single_state (a c q : ℕ) (ha : 0 < a) (hc : 2 ≤ c) :
    (∀ P : TangentPattern (State.single a c).degree, Allowed (State.single a c) P →
        SelfPattern (State.single a c) P →
          P.d.val = c ∧ children (State.single a c) P = [(1, State.single a c)]) ∧
      (((allowedPatterns (State.single a c)).toList.filter (SelfPattern (State.single a c))).map
        fun P ↦ (tangentCount (State.single a c) P).eval q).sum = q := by
  have hc : 0 < c := by omega
  have hca : c ≤ a*c := Nat.le_mul_of_pos_left c ha
  refine ⟨fun P hA hS ↦ ⟨by rw [eq_selfPattern a c hc hca P hA hS]; rfl,
    hS.choose_spec.choose_spec.2⟩, ?_⟩
  simpa [filter_selfPattern_eq a c hc hca] using tangentCount_selfPattern_eval a c q hc hca

/-! ### Degrees, weights and ranks -/

/-- A valid state has positive degree. -/
private theorem state_degree_pos (s : State) (hs : s.Valid) :
    0 < s.degree := by
  cases s with
  | single a c => exact Nat.mul_pos hs.1 hs.2
  | crossing a b c h =>
    have := Nat.mul_pos hs.1 hs.2.2.1
    change 0 < a*c+b*h
    omega

/-- If a child has the same degree as its parent, it is the only child and has residue
degree `1`. -/
private theorem equal_degree_child_is_unique (s : State) (hs : s.Valid)
    (P : TangentPattern s.degree)
    (hP : Allowed s P) (z : ℕ × State) (hz : z ∈ children s P) (heq : z.2.degree = s.degree) :
    children s P = [z] ∧ z.1 = 1 := by
  have hsum := children_degree_identity s hs P hP
  have hD := state_degree_pos s hs
  have hpos : ∀ w ∈ children s P, 0 < w.1 * w.2.degree := fun w hw ↦
    Nat.mul_pos (children_residue_degree_pos s P w hw)
      (state_degree_pos _ (children_valid s hs P hP w hw))
  have hz1 := children_residue_degree_pos s P z hz
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

/-- The weight of a valid state is at most its degree. -/
private theorem state_weight_le_degree (s : State) (hs : s.Valid) :
    s.weight ≤ s.degree := by
  cases s with
  | single a c => exact Nat.le_mul_of_pos_right a hs.2
  | crossing a b c h =>
    exact Nat.add_le_add (Nat.le_mul_of_pos_right a hs.2.2.1) (Nat.le_mul_of_pos_right b hs.2.2.2)

/-- Among valid states of equal degree, larger weight forces smaller rank. -/
private theorem rank_lt_of_weight_gt (s u : State) (hs : s.Valid) (hu : u.Valid)
    (hN : u.degree = s.degree)
    (hw : s.weight < u.weight) :
    u.rank < s.rank := by
  have h1 := state_weight_le_degree s hs
  have h2 := state_weight_le_degree u hu
  have ht : u.tag ≤ 1 := by cases u <;> simp [State.tag]
  unfold State.rank
  rw [hN] at h2 ⊢
  omega

/-- Every child of a non-self allowed pattern has strictly smaller rank than its parent. -/
theorem nonself_child_rank_lt (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) (hself : ¬ SelfPattern s P) (z : ℕ × State) (hz : z ∈ children s P) :
    z.2.rank < s.rank := by
  have hv := children_valid s hs P hP z hz
  rcases Nat.lt_or_eq_of_le (child_degree_le s hs P hP z hz) with hlt | heq
  · exact rank_lt_of_degree_lt s z.2 hv hlt
  obtain ⟨hch, hz1⟩ := equal_degree_child_is_unique s hs P hP z hz heq
  have hw : s.weight < z.2.weight → z.2.rank < s.rank :=
    rank_lt_of_weight_gt s z.2 hs hv heq
  cases s with
  | single a c =>
    obtain ⟨ha, hc⟩ := hs
    simp only [children, otherChildren, List.mem_append, List.mem_flatMap,
      List.mem_replicate] at hz
    rcases hz with hz | ⟨ij, -, -, rfl⟩
    · split_ifs at hz
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        exact hw (by simp [State.weight]; omega)
    · refine absurd ⟨a, c, rfl, ?_⟩ hself
      have hj : ij.2.val + 1 = c :=
        Nat.eq_of_mul_eq_mul_left ha (by simpa [State.degree] using heq)
      rw [hch]
      simp only at hz1
      rw [hz1, hj]
  | crossing a b c h =>
    obtain ⟨ha, hb, hc, hh⟩ := hs
    simp only [children, otherChildren, List.mem_append, List.mem_flatMap,
      List.mem_replicate] at hz
    rcases hz with (hz | hz) | ⟨ij, -, -, rfl⟩
    pick_goal 3
    · simp only [State.rank, State.weight, State.tag] at heq ⊢
      rw [heq]
      omega
    all_goals
      split_ifs at hz
      · simp at hz
      · obtain rfl := List.mem_singleton.1 hz
        exact hw (by simp [State.weight]; omega)

/-- Two fuel values above the rank give the same law (strong induction on a rank bound). -/
private theorem stateLawFuel_stable (n : ℕ) : ∀ (s : State), s.Valid → s.rank < n →
    ∀ k1 k2 : ℕ, s.rank < k1 → s.rank < k2 → stateLawFuel k1 s = stateLawFuel k2 s := by
  classical
  induction n with
  | zero => intro s _ h; omega
  | succ n ih =>
    intro s hs hn k1 k2 h1 h2
    obtain ⟨j1, rfl⟩ : ∃ j, k1 = j + 1 := ⟨k1 - 1, by omega⟩
    obtain ⟨j2, rfl⟩ : ∃ j, k2 = j + 1 := ⟨k2 - 1, by omega⟩
    have hterms : ((allowedPatterns s).toList.flatMap fun P ↦
        if SelfPattern s P then [] else
          lawScale (.mul (tangentCount s P) (divisorProbability s P.d.val))
            (lawProd ((children s P).map fun z ↦ lawDescend z.1 (stateLawFuel j1 z.2)))) =
        ((allowedPatterns s).toList.flatMap fun P ↦
        if SelfPattern s P then [] else
          lawScale (.mul (tangentCount s P) (divisorProbability s P.d.val))
            (lawProd ((children s P).map fun z ↦ lawDescend z.1 (stateLawFuel j2 z.2)))) := by
      simp only [List.flatMap]
      congr 1
      refine List.map_congr_left fun P hP ↦ ?_
      have hA : Allowed s P := by simpa [allowedPatterns] using hP
      split_ifs with hself
      · rfl
      · congr 2
        refine List.map_congr_left fun z hz ↦ ?_
        have hlt := nonself_child_rank_lt s hs P hA hself z hz
        rw [ih z.2 (children_valid s hs P hA z hz) (by omega) j1 j2 (by omega) (by omega)]
    cases s with
    | single a c =>
      rcases c with _ | _ | c
      · simp only [stateLawFuel]; rw [hterms]
      · simp only [stateLawFuel]
      · simp only [stateLawFuel]; rw [hterms]
    | crossing a b c h =>
      simp only [stateLawFuel]; rw [hterms]

/-- The fuel-based recursion is stable: any fuel `k > rank s` computes `stateLaw s`. -/
theorem state_fuel_stable (s : State) (hs : s.Valid) (k : ℕ) (hk : s.rank < k) :
    stateLawFuel k s = stateLaw s :=
  stateLawFuel_stable (s.rank + 1) s hs (by omega) k (s.rank + 1) hk (by omega)

/-! ### Unfolding the state law -/

open scoped Classical in
/-- The non-self part of the recursion of a state `s`: over the allowed tangent patterns `P` that
are not self patterns, the weight `tangentCount · divisorProbability` times the product of the
descended laws of the children of `P`. -/
noncomputable def exitLaw (s : State) : Law :=
  (allowedPatterns s).toList.flatMap fun P ↦
    if SelfPattern s P then [] else
      lawScale (.mul (tangentCount s P) (divisorProbability s P.d.val))
        (lawProd ((children s P).map fun z ↦ lawDescend z.1 (stateLaw z.2)))

open scoped Classical in
private theorem flatMap_terms_eq_exitLaw (s : State) (hs : s.Valid) :
    ((allowedPatterns s).toList.flatMap fun P ↦
        if SelfPattern s P then [] else
          lawScale (.mul (tangentCount s P) (divisorProbability s P.d.val))
            (lawProd ((children s P).map fun z ↦ lawDescend z.1 (stateLawFuel s.rank z.2))))
      = exitLaw s := by
  unfold exitLaw
  refine List.flatMap_congr fun P hP ↦ ?_
  have hA : Allowed s P := by simpa [allowedPatterns] using hP
  split_ifs with hself
  · rfl
  · congr 2
    refine List.map_congr_left fun z hz ↦ ?_
    rw [state_fuel_stable z.2 (children_valid s hs P hA z hz) s.rank
      (nonself_child_rank_lt s hs P hA hself z hz)]

/-- Unfolding of the state law: for a single state it is the exit law rescaled by
`1 / (1 - returnWeight c)`, and for a crossing state it is the exit law itself. -/
theorem state_law_unfold (s : State) (hs : s.Valid) (hnt : s.terminal = false) :
    (∀ a c : ℕ, s = State.single a c → stateLaw s =
      lawScale (.inv (.sub (.const 1) (returnWeight c))) (exitLaw s)) ∧
      (∀ a b c h : ℕ, s = State.crossing a b c h → stateLaw s = exitLaw s) := by
  refine ⟨?_, ?_⟩
  · rintro a c rfl
    obtain ⟨_, hc⟩ := id hs
    obtain _ | _ | c := c
    · omega
    · simp [State.terminal] at hnt
    · rw [← flatMap_terms_eq_exitLaw _ hs]
      rfl
  · rintro a b c h rfl
    rw [← flatMap_terms_eq_exitLaw _ hs]
    rfl

/-! ### Arithmetic of weights and probabilities -/

/-- The weight `tangentCount · divisorProbability` of a pattern is safe at all `q ≥ 2`. -/
private theorem tangent_weight_safe (s : State) (P : TangentPattern s.degree) :
    (Expr.mul (tangentCount s P) (divisorProbability s P.d.val)).allSafe := fun q hq ↦
  ⟨divisor_count_safe s.degree _ P.other q hq, divisor_probability_safe s P.d.val q hq⟩

/-- The law of the terminal state `S(a; 1)` is the atom `[(a, 1)]`. -/
theorem terminal_law (a : ℕ) :
    stateLaw (State.single a 1) = lawAtom a 1 := by
  rw [stateLaw, State.rank, stateLawFuel]

/-- `tri d = chooseTwo d + d`. -/
theorem tri_chooseTwo (d : ℕ) :
    tri d = chooseTwo d + d := by
  cases d with
  | zero => simp [tri, chooseTwo]
  | succ n =>
    unfold tri chooseTwo
    have h : (n+1)*(n+1+1) = (n+1)*(n+1-1) + 2*(n+1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

/-- `tri c ≥ 3` for `c ≥ 2`. -/
private theorem tri_ge_three (c : ℕ) (hc : 2 ≤ c) :
    3 ≤ tri c := by
  unfold tri
  have : 6 ≤ c*(c+1) := by nlinarith
  omega

/-- For `q, c ≥ 2`, the return weight `q · q^(-tri c)` lies in `(0, q⁻²]`, in particular
below `1`. -/
theorem return_weight_bounds (q c : ℕ) (hq : 2 ≤ q) (hc : 2 ≤ c) :
    0 < (returnWeight c).eval q ∧ (returnWeight c).eval q ≤ (q : ℚ)⁻¹^2 ∧
      (returnWeight c).eval q < 1 := by
  have hev : (returnWeight c).eval (q:ℚ) = (q:ℚ) * ((q:ℚ)^(tri c))⁻¹ := by
    simp [returnWeight, Expr.eval, expression_pow_eval]
  rw [hev]
  have hq2 : (2:ℚ) ≤ q := by exact_mod_cast hq
  have hqpos : (0:ℚ) < q := by linarith
  have hp3 : (q:ℚ)^3 ≤ (q:ℚ)^(tri c) := pow_le_pow_right₀ (by linarith) (tri_ge_three c hc)
  have hle : (q:ℚ) * ((q:ℚ)^(tri c))⁻¹ ≤ (q:ℚ)⁻¹^2 := by
    calc (q:ℚ) * ((q:ℚ)^(tri c))⁻¹ ≤ (q:ℚ) * ((q:ℚ)^3)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hp3) hqpos.le
      _ = (q:ℚ)⁻¹^2 := by field_simp
  refine ⟨by positivity, hle, lt_of_le_of_lt hle ?_⟩
  have : (q:ℚ)⁻¹ ≤ 1/2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) hq2
  have h0 : (0:ℚ) ≤ (q:ℚ)⁻¹ := by positivity
  nlinarith

/-- Divisor probabilities and the inverse `1 / (1 - returnWeight c)` are positive at `q ≥ 2`. -/
theorem divisor_probability_pos (q : ℕ) (hq : 2 ≤ q) (s : State) (d c : ℕ) (hc : 2 ≤ c) :
    0 < (divisorProbability s d).eval q ∧
      0 < (Expr.inv (.sub (.const 1) (returnWeight c))).eval q := by
  have hQ : (2:ℚ) ≤ (q:ℚ) := by exact_mod_cast hq
  have hE : (eminusOne).eval q = (q:ℚ) - 1 := by
    simp [eminusOne, Expr.sub, Expr.neg, Expr.eval]; ring
  have hE0 : 0 < (q:ℚ) - 1 := by linarith
  have hP : ∀ n : ℕ, 0 < ((Expr.pow .var n).eval q) := fun n ↦ by
    rw [expression_pow_eval]; simp only [Expr.eval]; positivity
  have hEp : ∀ n : ℕ, 0 < ((Expr.pow eminusOne n).eval q) := fun n ↦ by
    rw [expression_pow_eval, hE]; exact pow_pos hE0 _
  refine ⟨?_, ?_⟩
  · cases s with
    | single a c' => exact mul_pos (inv_pos.mpr (hP _)) (hEp _)
    | crossing a b c' h =>
      simp only [divisorProbability, Expr.eval]
      refine mul_pos (inv_pos.mpr (hP _)) ?_
      split_ifs
      all_goals first
        | exact hEp _
        | (simp only [Expr.eval]; rw [hE]; exact inv_pos.mpr hE0)
  · have := (return_weight_bounds q c hq hc).2.2
    simp only [Expr.sub, Expr.neg, Expr.eval]
    exact inv_pos.mpr (by linarith)

/-! ### Safety of the laws -/

/-- Products of safe laws are safe. -/
private theorem lawProd_safe (Ls : List Law) (h : ∀ L ∈ Ls, LawSafe L) :
    LawSafe (lawProd Ls) := by
  induction Ls with
  | nil =>
    intro z hz q _
    simp only [lawProd, lawOne, List.foldr_nil, List.mem_singleton] at hz
    subst hz
    trivial
  | cons L Ls ih =>
    exact law_safe_mul _ _ (h L (by simp)) (ih fun M hM ↦ h M (by simp [hM]))

open scoped Classical in
/-- The non-self part of the recursion for `stateLaw s` is safe, given safety for states of
smaller rank. -/
private theorem stateLaw_terms_safe (s : State) (hs : s.Valid)
    (ih : ∀ t : State, t.rank < s.rank → t.Valid → LawSafe (stateLaw t)) :
    LawSafe ((allowedPatterns s).toList.flatMap fun P ↦
        if SelfPattern s P then [] else
          lawScale (.mul (tangentCount s P) (divisorProbability s P.d.val))
            (lawProd ((children s P).map fun z ↦ lawDescend z.1 (stateLawFuel s.rank z.2)))) := by
  intro z hz
  rw [List.mem_flatMap] at hz
  obtain ⟨P, hP, hz⟩ := hz
  have hA : Allowed s P := by simpa [allowedPatterns] using hP
  by_cases hself : SelfPattern s P
  · simp [hself] at hz
  · rw [if_neg hself] at hz
    refine law_safe_scale _ _ (tangent_weight_safe s P) (lawProd_safe _ ?_) z hz
    simp only [List.mem_map]
    rintro _ ⟨w, hw, rfl⟩
    have hv := children_valid s hs P hA w hw
    have hr := nonself_child_rank_lt s hs P hA hself w hw
    rw [state_fuel_stable w.2 hv _ hr]
    exact law_safe_descend _ (children_residue_degree_pos s P w hw) _ (ih _ hr hv)

/-- The local law of every valid state is safe. -/
theorem local_law_safe (s : State) (hs : s.Valid) :
    LawSafe (stateLaw s) := by
  classical
  induction hn : s.rank using Nat.strong_induction_on generalizing s with
  | _ n IH =>
  have hT := stateLaw_terms_safe s hs fun t ht htv ↦ IH t.rank (hn ▸ ht) t htv rfl
  unfold stateLaw
  cases s with
  | single a c =>
    by_cases hc : c = 1
    · subst hc
      intro z hz q _
      simp only [stateLawFuel, lawAtom, List.mem_singleton] at hz
      subst hz
      trivial
    · have hc2 : 2 ≤ c := by have := hs.2; omega
      have hfuel : stateLawFuel ((State.single a c).rank + 1) (State.single a c) =
          lawScale (.inv (.sub (.const 1) (returnWeight c)))
            ((allowedPatterns (State.single a c)).toList.flatMap fun P ↦
              if SelfPattern (State.single a c) P then [] else
                lawScale (.mul (tangentCount (State.single a c) P)
                    (divisorProbability (State.single a c) P.d.val))
                  (lawProd ((children (State.single a c) P).map fun z ↦
                    lawDescend z.1 (stateLawFuel (State.single a c).rank z.2)))) := by
        rw [stateLawFuel]
        all_goals first | rfl | (intro a1 h; cases h; exact hc rfl)
      rw [hfuel]
      refine law_safe_scale _ _ (fun q hq ↦ ?_) hT
      obtain ⟨hpos, -, hlt⟩ := return_weight_bounds q c hq hc2
      have hne : (Expr.pow .var (tri c)).eval (q : ℚ) ≠ 0 := fun h0 ↦ by
        simp [returnWeight, Expr.eval, h0] at hpos
      refine ⟨⟨trivial, trivial, ⟨trivial, expression_pow_safe _ _ _ trivial, hne⟩⟩, ?_⟩
      simp only [Expr.sub, Expr.neg, Expr.eval]
      intro h0
      linarith
  | crossing a b c h =>
    rw [stateLawFuel]
    exact hT

/-- The global law (monic for `ε = false`, projective for `ε = true`) of degree `n` is safe. -/
theorem global_law_safe (n : ℕ) (ε : Bool) :
    LawSafe (globalLaw ε n) := by
  have normSafe : (Expr.inv (if ε then projectiveNormalizer n else .pow .var n)).allSafe := by
    intro q hq
    cases ε with
    | true =>
      refine ⟨?_, ne_of_gt (projective_normalizer_positive n q (by positivity))⟩
      refine expression_sum_safe _ _ ?_
      simp only [List.mem_map]
      rintro _ ⟨i, _, rfl⟩
      exact expression_pow_safe _ _ _ trivial
    | false =>
      refine ⟨expression_pow_safe _ _ _ trivial, ?_⟩
      have : (2:ℚ) ≤ q := by exact_mod_cast hq
      simpa [expression_pow_eval, Expr.eval] using pow_ne_zero n (by linarith : (q:ℚ) ≠ 0)
  refine law_safe_scale _ _ normSafe fun z hz ↦ ?_
  simp only [List.mem_flatMap] at hz
  obtain ⟨m, _, hz⟩ := hz
  refine law_safe_scale _ _ (divisor_count_safe _ _ m) (lawProd_safe _ ?_) z hz
  simp only [List.mem_map, otherChildren, List.mem_flatMap, List.mem_replicate]
  rintro _ ⟨w, ⟨ij, _, _, rfl⟩, rfl⟩
  exact law_safe_descend _ (Nat.succ_pos _) _ (local_law_safe _ ⟨Nat.one_pos, Nat.succ_pos _⟩)

/-- The coefficients of the monic and projective global laws are safe. -/
theorem global_coefficients_safe (n : ℕ) (σ : FactorType) :
    (monicExpr n σ).allSafe ∧ (projectiveExpr n σ).allSafe := by
  have hsafe : ∀ L : Law, LawSafe L → (lawCoeff L σ).allSafe := by
    intro L hL q hq
    refine expression_sum_safe _ _ fun x hx ↦ ?_
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    by_cases h : z.1 = σ
    · simp only [h, if_true]; exact hL z hz q hq
    · simp [h, Expr.safe]
  exact ⟨hsafe _ (global_law_safe n false), hsafe _ (global_law_safe n true)⟩

/-- The global formula is regular at every prime power. -/
theorem global_formula_regular (n : ℕ) (σ : FactorType) :
    FormulaRegular n σ := by
  intro q hq
  have h2 := prime_power_ge_two q hq
  obtain ⟨h1, h3⟩ := global_coefficients_safe n σ
  exact ⟨expression_regular _ _ (h1 q h2), expression_regular _ _ (h3 q h2)⟩

/-! ### Scaled types -/

/-- `typeDegree (scaleType δ σ) = δ · typeDegree σ`. -/
private theorem type_degree_scale (δ : ℕ) (σ : FactorType) :
    typeDegree (scaleType δ σ) = δ * typeDegree σ := by
  unfold typeDegree scaleType
  rw [Multiset.map_map, ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl fun z _ ↦ ?_
  simp only [Function.comp]
  ring

/-- Scaling by `δ > 0` is injective on types, preserves validity, and multiplies the degree
by `δ`. -/
theorem scale_type_valid_degree_iff (δ r : ℕ) (hδ : 0 < δ) (τ : FactorType) :
    ((ValidType (scaleType δ τ) ∧ typeDegree (scaleType δ τ) = δ * r) ↔
      (ValidType τ ∧ typeDegree τ = r)) ∧ Function.Injective (scaleType δ) := by
  refine ⟨?_, ?_⟩
  · have hv : ValidType (scaleType δ τ) ↔ ValidType τ := by
      unfold ValidType scaleType
      simp only [Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact forall₂_congr fun z _ ↦ by simp [hδ]
    rw [hv, type_degree_scale, Nat.mul_left_cancel_iff hδ]
  · apply Multiset.map_injective
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Nat.eq_of_mul_eq_mul_left hδ h.2)

end SurfaceBlowup
