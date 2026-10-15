/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Recursion.ChildMembers

/-!
# Return and exit events of the blowup recursion

For a surface universe, the recursion follows an ideal through successive blowups: at a
single state `single a c` it may return to the same state (self cells) `k` times before
exiting through a non-self cell. This file computes the masses of the exit events (in terms
of the exit law and the return weight), proves measurability of all recursion events, shows
that bad exits and never-returning ideals are null, and concludes by strong induction on the
state rank that the law statement holds for every member of a surface universe.

## Main results

* `exit_cell_type_mass`, `exit_cell_coeff_nonneg`: mass of the type box of an exit cell.
* `exit_event_zero_mass`, `exit_event_succ_mass`, `return_event_mass`: masses of exit and
  return events.
* `recursion_events_measurable`, `bad_exit_null`, `never_return_null`.
* `recursion_crossing_law`, `recursion_single_law`, `universal_law_statement`: the law.
* `type_event_null_difference`, `etale_type_event_measurable`,
  `unramified_generic_fibre_ascent`.

Provenance: `Thm_SurfaceBlowupV2_` nodes `exit_cell_type_mass`, `exit_event_succ_mass`,
`recursion_events_measurable`, `bad_exit_null`, `exit_event_zero_mass`,
`recursion_crossing_step`, `return_event_mass`, `never_return_null`, `recursion_single_step`,
`universal_law_statement`, `type_event_null_difference`, `etale_type_event_measurable`,
`unramified_generic_fibre_ascent`.
-/

open scoped BigOperators ENNReal TensorProduct

namespace SurfaceBlowup

/-! ### Exit cells -/

private theorem piFinset_sum_reindex (σ : FactorType) (q : ℚ) {m n : ℕ} (h : m = n)
    (a : Fin n → ℕ × Law) :
    (∑ τ ∈ Fintype.piFinset (fun j : Fin m => ((a (Fin.cast h j)).2.map Prod.fst).toFinset),
      (if σ = ∑ j, scaleType (a (Fin.cast h j)).1 (τ j) then
        ∏ j, (lawCoeff (a (Fin.cast h j)).2 (τ j)).eval (q ^ (a (Fin.cast h j)).1) else 0)) =
    ∑ τ ∈ Fintype.piFinset (fun j : Fin n => ((a j).2.map Prod.fst).toFinset),
      (if σ = ∑ j, scaleType (a j).1 (τ j) then
        ∏ j, (lawCoeff (a j).2 (τ j)).eval (q ^ (a j).1) else 0) := by
  subst h; rfl

private theorem lawCoeff_lawProd_descend_eval (l : List (ℕ × State)) (hδ : ∀ z ∈ l, 0 < z.1)
    (σ : FactorType) (q : ℚ) :
    (lawCoeff (lawProd (l.map fun z => lawDescend z.1 (stateLaw z.2))) σ).eval q =
    ∑ τ ∈ Fintype.piFinset (fun j : Fin l.length => ((stateLaw (l.get j).2).map Prod.fst).toFinset),
      (if σ = ∑ j, scaleType (l.get j).1 (τ j) then
        ∏ j, (lawCoeff (stateLaw (l.get j).2) (τ j)).eval (q ^ (l.get j).1) else 0) := by
  have h := law_coeff_prod_descend (l.map fun z => (z.1, stateLaw z.2))
    (by intro z hz; obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz; exact hδ w hw) σ q
  rw [List.map_map] at h
  rw [show ((fun z : ℕ × Law => lawDescend z.1 z.2) ∘ fun z : ℕ × State => (z.1, stateLaw z.2)) =
    (fun z => lawDescend z.1 (stateLaw z.2)) from rfl] at h
  have hl : (l.map fun z => (z.1, stateLaw z.2)).length = l.length := List.length_map _
  have hg : (l.map fun z => (z.1, stateLaw z.2)).get =
      fun j => ((l.get (Fin.cast hl j)).1, stateLaw (l.get (Fin.cast hl j)).2) := by
    funext j; simp
  rw [hg] at h
  rw [h]
  exact piFinset_sum_reindex σ q hl (fun j => ((l.get j).1, stateLaw (l.get j).2))

/-- The residue field of the `j`-th child of a cell has cardinality `q ^ δⱼ`. -/
private theorem child_q_eq_pow (U : SurfaceUniverse) (i : U.ι) (c : (U.M i).cellIndex)
    (j : (U.M i).childIdx c) :
    ((U.M (U.child i c j)).q : ℚ) = ((U.M i).q : ℚ) ^ (((U.M i).childList c).get j).1 := by
  rw [U.child_residue i c j]; push_cast; rfl

/-- The children of an exit cell have smaller rank, so they satisfy the law statement. -/
private theorem exit_child_law (U : SurfaceUniverse) (i : U.ι)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') (c : U.exitCells i)
    (j : (U.M i).childIdx c.1) : U.LawStatement (U.child i c.1 j) :=
  hIH _ (by
    rw [U.child_state i c.1 j]
    exact nonself_child_rank_lt _ (U.M i).valid _ c.1.1.2 c.2 _ (List.get_mem _ _))

/-- The law coefficients of the children of an exit cell, evaluated at `q ^ δⱼ`, are
nonnegative. -/
private theorem exit_child_coeff_nonneg (U : SurfaceUniverse) (i : U.ι)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') (c : U.exitCells i)
    (j : (U.M i).childIdx c.1) (t : FactorType) :
    0 ≤ (lawCoeff (stateLaw (((U.M i).childList c.1).get j).2) t).eval
      (((U.M i).q : ℚ) ^ (((U.M i).childList c.1).get j).1) := by
  have := ((exit_child_law U i hIH c j).1 t).2.1
  rwa [U.child_state i c.1 j, child_q_eq_pow] at this

/-- The `σ`-coefficient of the product of the descended children laws of an exit cell is
nonnegative. -/
theorem exit_cell_coeff_nonneg (U : SurfaceUniverse) (i : U.ι)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') (c : U.exitCells i)
    (σ : FactorType) :
    0 ≤ (lawCoeff (lawProd (((U.M i).childList c.1).map fun z ↦ lawDescend z.1 (stateLaw z.2)))
      σ).eval ((U.M i).q : ℚ) := by
  rw [lawCoeff_lawProd_descend_eval ((U.M i).childList c.1)
    (fun z hz ↦ children_residue_degree_pos _ _ _ hz)]
  refine Finset.sum_nonneg fun τ _ ↦ ?_
  split_ifs
  exacts [Finset.prod_nonneg fun j _ ↦ exit_child_coeff_nonneg U i hIH c j (τ j), le_rfl]

/-- The child box of an exit cell where the `j`-th child terminates with type `τ j` has mass
`P(d) · vol · ∏ⱼ Cⱼ(τ j)`, with `P(d)` the divisor probability of the cell and `Cⱼ` the law
coefficients of the children evaluated at `q ^ δⱼ`. -/
private theorem exit_child_box_mass (U : SurfaceUniverse) (i : U.ι)
    (hnt : (U.M i).s.terminal = false)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') (c : U.exitCells i)
    (τ : (U.M i).childIdx c.1 → FactorType) :
    (U.M i).μ (U.childBox i c.1 (fun j ↦ U.termTypeEvent (U.child i c.1 j) (τ j))) =
      ENNReal.ofReal ((((divisorProbability (U.M i).s ((U.M i).cellDegree c.1)).eval
        ((U.M i).q : ℚ) * (stateVolume (U.M i).s).eval ((U.M i).q : ℚ) *
        ∏ j, (lawCoeff (stateLaw (((U.M i).childList c.1).get j).2) (τ j)).eval
          (((U.M i).q : ℚ) ^ (((U.M i).childList c.1).get j).1) : ℚ)) : ℝ) := by
  have hq : 2 ≤ (U.M i).q := (universe_basic_facts U i).1
  have hL := exit_child_law U i hIH c
  have hsj : ∀ j, (U.M (U.child i c.1 j)).s = (((U.M i).childList c.1).get j).2 :=
    fun j ↦ U.child_state i c.1 j
  -- child volumes `V j` and child law coefficients `C j`, evaluated at `q ^ δⱼ`
  let V : (U.M i).childIdx c.1 → ℚ := fun j ↦ (stateVolume (((U.M i).childList c.1).get j).2).eval
    (((U.M i).q : ℚ) ^ (((U.M i).childList c.1).get j).1)
  let C : (U.M i).childIdx c.1 → ℚ := fun j ↦
    (lawCoeff (stateLaw (((U.M i).childList c.1).get j).2) (τ j)).eval
      (((U.M i).q : ℚ) ^ (((U.M i).childList c.1).get j).1)
  have hC : ∀ j, 0 ≤ C j := fun j ↦ exit_child_coeff_nonneg U i hIH c j (τ j)
  have hV : ∀ j, 0 < V j := by
    intro j
    have hqc : 2 ≤ (U.M (U.child i c.1 j)).q := U.child_residue i c.1 j ▸ hq.trans
      (Nat.le_self_pow (children_residue_degree_pos _ _ _ (List.get_mem _ _)).ne' _)
    have := (density_value_arith _ hqc (.const 1) (.const 1) (by simp [Expr.eval])
      (by simp [Expr.eval]) 0 _ (U.M (U.child i c.1 j)).valid).2.2.2.2.2.2.1
    rwa [hsj j, child_q_eq_pow] at this
  have hmeas : ∀ j, MeasurableSet (U.termTypeEvent (U.child i c.1 j) (τ j)) :=
    fun j ↦ ((hL j).1 (τ j)).1
  have hmu : ∀ j, (U.M (U.child i c.1 j)).μ (U.termTypeEvent (U.child i c.1 j) (τ j)) =
      ENNReal.ofReal (((C j * V j : ℚ)) : ℝ) := by
    intro j
    have e1 : (lawCoeff (stateLaw (U.M (U.child i c.1 j)).s) (τ j)).eval
        ((U.M (U.child i c.1 j)).q : ℚ) = C j := by rw [hsj j, child_q_eq_pow]
    have e2 : (stateVolume (U.M (U.child i c.1 j)).s).eval ((U.M (U.child i c.1 j)).q : ℚ) =
        V j := by rw [hsj j, child_q_eq_pow]
    rw [((hL j).1 (τ j)).2.2, U.volume]
    simp only [densityValue]
    rw [e1, e2, ← ENNReal.ofReal_mul (by exact_mod_cast hC j)]
    push_cast; rfl
  have hqpos : (0 : ℝ) < ((U.M i).q : ℝ) := by exact_mod_cast (show 0 < (U.M i).q by omega)
  -- the volume ratio `q^{-tri d} · ∏ V j / vol = P(d)`
  have hratio : ((U.M i).q : ℚ)⁻¹ ^ tri ((U.M i).cellDegree c.1) * (∏ j, V j) /
      (stateVolume (U.M i).s).eval ((U.M i).q : ℚ) =
      (divisorProbability (U.M i).s ((U.M i).cellDegree c.1)).eval ((U.M i).q : ℚ) := by
    have hprodV : (((U.M i).childList c.1).map fun z ↦
        (stateVolume z.2).eval (((U.M i).q : ℚ) ^ z.1)).prod = ∏ j, V j := by
      rw [← Fin.prod_univ_fun_getElem]; rfl
    rw [← hprodV]
    exact child_volume_ratio (U.M i).s (U.M i).valid c.1.1.1 c.1.1.2 _ hq
  have hVs := (density_value_arith _ hq (.const 1) (.const 1) (by simp [Expr.eval])
      (by simp [Expr.eval]) 0 _ (U.M i).valid).2.2.2.2.2.2.2
  change (U.M i).μ ((U.M i).cell c.1 ∩ U.Φ i c.1 ⁻¹' Set.pi Set.univ _) = _
  rw [U.Φ_measure i hnt c.1 _ hmeas, Finset.prod_congr rfl (fun j _ ↦ hmu j),
    ← ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ by have := hC j; have := hV j; positivity),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hqpos,
    ← ENNReal.ofReal_pow (inv_nonneg.2 hqpos.le), ← ENNReal.ofReal_mul (by positivity), ← hratio]
  congr 1
  push_cast
  rw [Finset.prod_mul_distrib]
  field_simp
  exact mul_comm _ _

/-- The type-`σ` box of a cell is the disjoint union, over the child types `τ` adding up to `σ`
(with residue scaling), of the child boxes where the `j`-th child terminates with type `τ j`. -/
private theorem typeBox_measure_eq_tsum (U : SurfaceUniverse) (i : U.ι)
    (hnt : (U.M i).s.terminal = false) (c : (U.M i).cellIndex) (σ : FactorType)
    (hmeas : ∀ j t, MeasurableSet (U.termTypeEvent (U.child i c j) t)) :
    (U.M i).μ (U.typeBox i c σ) = ∑' τ : (U.M i).childIdx c → FactorType,
      if σ = ∑ j, scaleType ((U.M i).childDelta c j) (τ j) then
        (U.M i).μ (U.childBox i c (fun j ↦ U.termTypeEvent (U.child i c j) (τ j))) else 0 := by
  unfold SurfaceUniverse.typeBox
  rw [MeasureTheory.measure_iUnion]
  · congr 1; funext τ
    rw [Set.iUnion_eq_if]
    split_ifs
    · rfl
    · exact MeasureTheory.measure_empty
  · intro τ τ' hne
    rw [Function.onFun, Set.disjoint_left]
    intro J hJ hJ'
    simp only [Set.mem_iUnion] at hJ hJ'
    obtain ⟨_, hJ⟩ := hJ
    obtain ⟨_, hJ'⟩ := hJ'
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have h1 := hJ.2 j (Set.mem_univ j)
    obtain ⟨σ0, -, huniq⟩ := terminates_type_unique U _ _ h1.2
    exact hj ((huniq _ h1.1.2).trans (huniq _ (hJ'.2 j (Set.mem_univ j)).1.2).symm)
  · exact fun τ ↦ MeasurableSet.iUnion fun _ ↦ U.Φ_measurable i hnt c _ fun j ↦ hmeas j (τ j)

/-- Mass of the type-`σ` box of a non-self (exit) cell: the divisor probability of the cell
times the `σ`-coefficient of the product of the descended children laws, times the volume of
the state set. -/
theorem exit_cell_type_mass (U : SurfaceUniverse) (i : U.ι) (hnt : (U.M i).s.terminal = false)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') (c : U.exitCells i)
    (σ : FactorType) :
    (U.M i).μ (U.typeBox i c.1 σ) =
      densityValue (.mul (divisorProbability (U.M i).s ((U.M i).cellDegree c.1))
        (lawCoeff (lawProd (((U.M i).childList c.1).map fun z ↦ lawDescend z.1 (stateLaw z.2))) σ))
        (U.M i).q * (U.M i).μ (U.M i).stateSet := by
  -- sum the child box masses over the finitely many child types with nonzero coefficient
  have hq : 2 ≤ (U.M i).q := (universe_basic_facts U i).1
  set A : ℚ := (divisorProbability (U.M i).s ((U.M i).cellDegree c.1)).eval ((U.M i).q : ℚ) *
    (stateVolume (U.M i).s).eval ((U.M i).q : ℚ) with hAdef
  let C : (U.M i).childIdx c.1 → FactorType → ℚ := fun j t ↦
    (lawCoeff (stateLaw (((U.M i).childList c.1).get j).2) t).eval
      (((U.M i).q : ℚ) ^ (((U.M i).childList c.1).get j).1)
  have hC : ∀ j t, 0 ≤ C j t := exit_child_coeff_nonneg U i hIH c
  have hA : 0 ≤ A := mul_nonneg (divisor_probability_pos _ hq _ _ 2 le_rfl).1.le
    (density_value_arith _ hq (.const 1) (.const 1) (by simp [Expr.eval])
      (by simp [Expr.eval]) 0 _ (U.M i).valid).2.2.2.2.2.2.1.le
  let g : ((U.M i).childIdx c.1 → FactorType) → ℚ := fun τ ↦
    if σ = ∑ j, scaleType ((U.M i).childDelta c.1 j) (τ j) then A * ∏ j, C j (τ j) else 0
  have hg : ∀ τ, 0 ≤ g τ := fun τ ↦ by
    simp only [g]; split_ifs
    exacts [mul_nonneg hA (Finset.prod_nonneg fun j _ ↦ hC j (τ j)), le_rfl]
  have hstep1 : (U.M i).μ (U.typeBox i c.1 σ) = ∑' τ, ENNReal.ofReal ((g τ : ℚ) : ℝ) := by
    rw [typeBox_measure_eq_tsum U i hnt c.1 σ fun j t ↦ ((exit_child_law U i hIH c j).1 t).1]
    congr 1; funext τ
    simp only [g]
    split_ifs
    · exact exit_child_box_mass U i hnt hIH c τ
    · simp
  have hstep2 : ∑' τ, ENNReal.ofReal ((g τ : ℚ) : ℝ) =
      ∑ τ ∈ Fintype.piFinset (fun j : (U.M i).childIdx c.1 ↦
        ((stateLaw (((U.M i).childList c.1).get j).2).map Prod.fst).toFinset),
        ENNReal.ofReal ((g τ : ℚ) : ℝ) := by
    refine tsum_eq_sum fun τ hτ ↦ ?_
    rw [Fintype.mem_piFinset] at hτ
    push Not at hτ
    obtain ⟨j, hj⟩ := hτ
    have h0 : ∏ j, C j (τ j) = 0 := Finset.prod_eq_zero (Finset.mem_univ j)
      ((law_coeff_prod_formula 0 Fin.elim0 (τ j) _).2 _ _ hj)
    simp [g, h0]
  have hVs := (density_value_arith _ hq (.const 1) (.const 1) (by simp [Expr.eval])
      (by simp [Expr.eval]) 0 _ (U.M i).valid).2.2.2.2.2.2.1
  rw [hstep1, hstep2, ← ENNReal.ofReal_sum_of_nonneg (fun τ _ ↦ by exact_mod_cast hg τ), U.volume]
  simp only [densityValue]
  rw [← ENNReal.ofReal_mul' (by exact_mod_cast hVs.le), ← Rat.cast_sum, ← Rat.cast_mul, Expr.eval,
    lawCoeff_lawProd_descend_eval ((U.M i).childList c.1)
      (fun z hz ↦ children_residue_degree_pos _ _ _ hz), Finset.mul_sum, Finset.sum_mul]
  congr 2
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  simp only [g]
  by_cases hσ : σ = ∑ j, scaleType ((U.M i).childDelta c.1 j) (τ j)
  · rw [if_pos hσ, if_pos (show σ = ∑ j, scaleType (((U.M i).childList c.1).get j).1 (τ j) from hσ)]
    ring
  · rw [if_neg hσ, if_neg (show ¬σ = ∑ j, scaleType (((U.M i).childList c.1).get j).1 (τ j) from
      hσ)]
    ring

/-! ### Return chains at single states -/

private theorem list_sum_filter {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℚ) :
    ((s.toList.filter (fun x => decide (p x))).map f).sum = ∑ x ∈ s.filter p, f x := by
  rw [Finset.sum_eq_multiset_sum, Finset.filter_val, ← Finset.coe_toList s]
  rw [Multiset.filter_coe, Multiset.map_coe, Multiset.sum_coe]

open scoped Classical in
private theorem self_facts (a c q : ℕ) (ha : 0 < a) (hc : 2 ≤ c) (s : State)
    (hs : s = State.single a c) :
    (∀ P : TangentPattern s.degree, Allowed s P → SelfPattern s P → P.d.val = c ∧ children s P =
        [(1, State.single a c)]) ∧
    (((allowedPatterns s).toList.filter (SelfPattern s)).map fun P => (tangentCount s P).eval q).sum
        = q := by
  subst hs; exact self_patterns_of_single_state a c q ha hc

private theorem list_get_of_eq_singleton {α : Type} (l : List α) (x : α) (h : l = [x])
    (j : Fin l.length) : l.get j = x := by
  subst h; simp

private theorem eval_pow_nonneg (x : Expr) (q : ℚ) (hx : 0 ≤ x.eval q) (n : ℕ) :
    0 ≤ (x.pow n).eval q :=
  expression_pow_eval x q n ▸ pow_nonneg hx n

open scoped Classical in
/-- The self cells of a measured surface are counted by the divisors of the self patterns. -/
private theorem natCard_selfCells (M : MeasuredSurface) (hfin : ∀ P : TangentPattern M.s.degree,
    Finite (patternDivisors (IsLocalRing.ResidueField M.R) M.s P)) :
    (Nat.card {c : M.cellIndex // M.IsSelfCell c} : ℚ) =
      ∑ P ∈ (allowedPatterns M.s).filter (SelfPattern M.s),
        (Nat.card (patternDivisors (IsLocalRing.ResidueField M.R) M.s P) : ℚ) := by
  let e : {c : M.cellIndex // M.IsSelfCell c} ≃
      Σ P : {P : TangentPattern M.s.degree // Allowed M.s P ∧ SelfPattern M.s P},
        patternDivisors (IsLocalRing.ResidueField M.R) M.s P.1 :=
    { toFun := fun c => ⟨⟨c.1.1.1, c.1.1.2, c.2⟩, c.1.2⟩
      invFun := fun c => ⟨⟨⟨c.1.1, c.1.2.1⟩, c.2⟩, c.1.2.2⟩
      left_inv := by rintro ⟨⟨⟨P, h⟩, d⟩, h'⟩; rfl
      right_inv := by rintro ⟨⟨P, h⟩, d⟩; rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  push_cast
  symm; apply Finset.sum_subtype
  intro x; simp [allowedPatterns]

/-- At a single state `single a c` (`a > 0`, `c ≥ 2`), every self cell has degree `c` and the
single child `(1, single a c)`, its child surfaces have the same state and residue
cardinality, and there are exactly `q` self cells. -/
private theorem self_cells_facts (U : SurfaceUniverse) {a c : ℕ} (ha : 0 < a) (hc : 2 ≤ c)
    (i : U.ι) (hs : (U.M i).s = State.single a c) :
    (∀ c' : U.selfCells i, (U.M i).cellDegree c'.1 = c ∧
      (U.M i).childList c'.1 = [(1, State.single a c)]) ∧
    (∀ (c' : U.selfCells i) (j : (U.M i).childIdx c'.1),
      (U.M (U.child i c'.1 j)).s = State.single a c ∧ (U.M (U.child i c'.1 j)).q = (U.M i).q) ∧
    Finite (U.selfCells i) ∧ (Nat.card (U.selfCells i) : ℚ) = (U.M i).q := by
  classical
  obtain ⟨hq, -, -, -, _⟩ := universe_basic_facts U i
  have hntM : (U.M i).s.terminal = false := by
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
    rw [hs]; rfl
  have hsf := self_facts a c (U.M i).q ha hc (U.M i).s hs
  have hcell : ∀ c' : U.selfCells i, (U.M i).cellDegree c'.1 = c ∧
      (U.M i).childList c'.1 = [(1, State.single a c)] :=
    fun c' => hsf.1 c'.1.1.1 c'.1.1.2 c'.2
  refine ⟨hcell, fun c' j => ?_, Subtype.finite, ?_⟩
  · have hg := list_get_of_eq_singleton _ _ (hcell c').2 j
    refine ⟨?_, ?_⟩
    · rw [U.child_state]; simp only [MeasuredSurface.childState, hg]
    · rw [U.child_residue]; simp only [MeasuredSurface.childDelta, hg, pow_one]
  · rw [show Nat.card (U.selfCells i) = Nat.card {c : (U.M i).cellIndex // (U.M i).IsSelfCell c}
      from rfl, natCard_selfCells (U.M i) (U.divisors_finite i), ← hsf.2, list_sum_filter]
    exact Finset.sum_congr rfl fun P hP =>
      U.divisor_count i hntM P (Finset.mem_filter.1 (Finset.mem_filter.1 hP).1).2

/-- The return weight `q · q^{-tri c}` as an extended nonnegative real. -/
private theorem densityValue_returnWeight (q : ℕ) (hq : 2 ≤ q) (c : ℕ) :
    densityValue (returnWeight c) q = (q : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ ^ tri c := by
  have h := density_value_arith q hq .var (.inv (.pow .var (tri c))) (by simp [Expr.eval])
    (by simp only [Expr.eval]; exact inv_nonneg.mpr (eval_pow_nonneg _ _ (by simp [Expr.eval]) _))
    (tri c) (State.single 1 1) ⟨Nat.one_pos, Nat.one_pos⟩
  rw [returnWeight, h.1, h.2.2.1]
  simp [densityValue, Expr.eval]

/-- One more return at `single a c`: if an event family `E` is measurable with mass `m · vol` at
every member in state `single a c` with the same residue cardinality, then the union over the
self cells of `i` of the child boxes of `E` is measurable with mass `λ · m · vol`, where `λ` is
the return weight. -/
private theorem self_cells_union_mass (U : SurfaceUniverse) {a c : ℕ} (ha : 0 < a) (hc : 2 ≤ c)
    (i : U.ι) (hs : (U.M i).s = State.single a c) (E : ∀ i' : U.ι, Set (Ideal (U.M i').R))
    (m : ℝ≥0∞)
    (hE : ∀ i' : U.ι, (U.M i').s = State.single a c → (U.M i').q = (U.M i).q →
      (U.M i').μ (E i') = m * (U.M i').μ (U.M i').stateSet ∧ MeasurableSet (E i')) :
    (U.M i).μ (⋃ c' : U.selfCells i, U.childBox i c'.1 (fun j ↦ E (U.child i c'.1 j))) =
      densityValue (returnWeight c) (U.M i).q * m * (U.M i).μ (U.M i).stateSet ∧
    MeasurableSet (⋃ c' : U.selfCells i, U.childBox i c'.1 (fun j ↦ E (U.child i c'.1 j))) := by
  obtain ⟨hq, -, -, -, -⟩ := universe_basic_facts U i
  have hntM : (U.M i).s.terminal = false := by
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
    rw [hs]; rfl
  obtain ⟨hcell, hchild, _, hcard⟩ := self_cells_facts U ha hc i hs
  -- each self cell has a single child, in the same state, with the same residue cardinality
  have hbox : ∀ c' : U.selfCells i,
      MeasurableSet (U.childBox i c'.1 (fun j ↦ E (U.child i c'.1 j))) ∧
      (U.M i).μ (U.childBox i c'.1 (fun j ↦ E (U.child i c'.1 j))) =
        ((U.M i).q : ℝ≥0∞)⁻¹ ^ tri c * (m * (U.M i).μ (U.M i).stateSet) := by
    intro c'
    have hG : ∀ j, MeasurableSet (E (U.child i c'.1 j)) :=
      fun j ↦ (hE _ (hchild c' j).1 (hchild c' j).2).2
    refine ⟨U.Φ_measurable i hntM c'.1 _ hG, ?_⟩
    unfold SurfaceUniverse.childBox
    rw [U.Φ_measure i hntM c'.1 _ hG, (hcell c').1]
    have j0 : (U.M i).childIdx c'.1 := ⟨0, by rw [(hcell c').2]; simp⟩
    have : Subsingleton ((U.M i).childIdx c'.1) := by
      change Subsingleton (Fin ((U.M i).childList c'.1).length)
      rw [(hcell c').2]; simp only [List.length_singleton]; infer_instance
    rw [Fintype.prod_subsingleton _ j0]
    congr 1
    rw [(hE _ (hchild c' j0).1 (hchild c' j0).2).1, U.volume, U.volume, (hchild c' j0).1, hs,
      (hchild c' j0).2]
  have hdisj : Pairwise (Function.onFun Disjoint fun c' : U.selfCells i ↦
      U.childBox i c'.1 (fun j ↦ E (U.child i c'.1 j))) := fun x y hxy ↦
    (U.cells_disjoint i hntM (fun h ↦ hxy (Subtype.ext h))).mono
      Set.inter_subset_left Set.inter_subset_left
  let : Fintype (U.selfCells i) := Fintype.ofFinite _
  refine ⟨?_, MeasurableSet.iUnion fun c' ↦ (hbox c').1⟩
  have hcardN : Fintype.card (U.selfCells i) = (U.M i).q := by
    rw [← Nat.card_eq_fintype_card]; exact_mod_cast hcard
  rw [MeasureTheory.measure_iUnion hdisj (fun c' ↦ (hbox c').1), tsum_fintype,
    Finset.sum_congr rfl (fun c' _ ↦ (hbox c').2), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hcardN, densityValue_returnWeight _ hq]
  ring

/-- If the immediate exit event at `single a c` has mass `G · vol`, then the exit event after
`k` returns has mass `λᵏ · G · vol`, where `λ` is the return weight; it is measurable. -/
theorem exit_event_succ_mass (U : SurfaceUniverse) (a c : ℕ) (ha : 0 < a) (hc : 2 ≤ c)
    (σ : FactorType) (q₀ : ℕ) (G : ℚ)
    (hexit : ∀ i : U.ι, (U.M i).s = State.single a c → (U.M i).q = q₀ → (U.M i).μ
        (U.exitEvent σ 0 i) = ENNReal.ofReal (G : ℝ) * (U.M i).μ (U.M i).stateSet ∧ MeasurableSet
        (U.exitEvent σ 0 i))
    (k : ℕ) :
    ∀ i : U.ι, (U.M i).s = State.single a c → (U.M i).q = q₀ →
    (U.M i).μ (U.exitEvent σ k i) = ENNReal.ofReal ((((returnWeight c).eval (q₀ : ℚ)) ^ k * G : ℚ) :
        ℝ) * (U.M i).μ (U.M i).stateSet ∧
    MeasurableSet (U.exitEvent σ k i) := by
  induction k with
  | zero =>
    intro i hs hq0
    simpa using hexit i hs hq0
  | succ k ih =>
    intro i hs hq0
    have hy : 0 ≤ (returnWeight c).eval (q₀ : ℚ) :=
      (return_weight_bounds _ c (hq0 ▸ (universe_basic_facts U i).1) hc).1.le
    obtain ⟨hmass, hmeas⟩ := self_cells_union_mass U ha hc i hs (U.exitEvent σ k) _
      fun i' hs' hq' ↦ ih i' hs' (hq'.trans hq0)
    refine ⟨hmass.trans ?_, hmeas⟩
    rw [hq0, densityValue, ← ENNReal.ofReal_mul (by exact_mod_cast hy)]
    congr 2; push_cast; ring

/-! ### Measurability and null sets -/

/-- At a nonterminal state (assuming the law for smaller ranks), all return, exit, terminating
exit and bad exit events of members in the same state are measurable. -/
theorem recursion_events_measurable (U : SurfaceUniverse) (i : U.ι)
    (hnt : (U.M i).s.terminal = false)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') :
    ∀ i' : U.ι, (U.M i').s = (U.M i).s → ∀ (k : ℕ) (σ : FactorType),
    MeasurableSet (U.returnEvent k i') ∧ MeasurableSet (U.exitEvent σ k i') ∧
    MeasurableSet (U.termExitEvent k i') ∧ MeasurableSet (U.badExitEvent k i') := by
  intro i₀ hs₀ k σ
  induction k generalizing i₀ with
  | zero =>
    have hnt' : (U.M i₀).s.terminal = false := by rw [hs₀]; exact hnt
    have : Finite (U.M i₀).cellIndex := (universe_basic_facts U i₀).2.2.2.2
    have : Countable (U.exitCells i₀) := by unfold SurfaceUniverse.exitCells; infer_instance
    have hrk : ∀ (c : U.exitCells i₀) j, (U.M (U.child i₀ c.1 j)).s.rank < (U.M i).s.rank := by
      intro c j
      rw [U.child_state, ← hs₀]
      exact nonself_child_rank_lt (U.M i₀).s (U.M i₀).valid c.1.1.1 c.1.1.2 c.2 _
        (List.get_mem _ _)
    refine ⟨U.stateSet_measurable i₀, ?_, ?_, ?_⟩
    · simp only [SurfaceUniverse.exitEvent]
      refine MeasurableSet.iUnion fun c => ?_
      unfold SurfaceUniverse.typeBox
      refine MeasurableSet.iUnion fun τ => MeasurableSet.iUnion fun _ => ?_
      exact U.Φ_measurable i₀ hnt' c.1 _ fun j => ((hIH _ (hrk c j)).1 (τ j)).1
    · simp only [SurfaceUniverse.termExitEvent]
      refine MeasurableSet.iUnion fun c => ?_
      exact U.Φ_measurable i₀ hnt' c.1 _ fun j => (hIH _ (hrk c j)).2.1
    · simp only [SurfaceUniverse.badExitEvent]
      refine MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun j₀ => ?_
      refine U.Φ_measurable i₀ hnt' c.1 _ fun j => ?_
      by_cases hj : j = j₀
      · subst hj
        rw [Function.update_self]
        exact (U.stateSet_measurable _).inter (hIH _ (hrk c j)).2.1.compl
      · rw [Function.update_of_ne hj]
        exact MeasurableSet.univ
  | succ k ih =>
    have hnt' : (U.M i₀).s.terminal = false := by rw [hs₀]; exact hnt
    have : Finite (U.M i₀).cellIndex := (universe_basic_facts U i₀).2.2.2.2
    have : Countable (U.selfCells i₀) := by unfold SurfaceUniverse.selfCells; infer_instance
    have hst : ∀ (c : U.selfCells i₀) j, (U.M (U.child i₀ c.1 j)).s = (U.M i).s := by
      intro c j
      rw [U.child_state, ← hs₀]
      obtain ⟨a, b, -, h⟩ := c.2
      have hm : ∀ z ∈ (U.M i₀).childList c.1, z = (1, (U.M i₀).s) := by
        intro z hz
        unfold MeasuredSurface.childList at hz
        rw [h] at hz
        simpa using hz
      exact congrArg Prod.snd (hm _ (List.get_mem _ _))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [SurfaceUniverse.returnEvent]
      exact MeasurableSet.iUnion fun c =>
        U.Φ_measurable i₀ hnt' c.1 _ fun j => (ih _ (hst c j)).1
    · simp only [SurfaceUniverse.exitEvent]
      exact MeasurableSet.iUnion fun c =>
        U.Φ_measurable i₀ hnt' c.1 _ fun j => (ih _ (hst c j)).2.1
    · simp only [SurfaceUniverse.termExitEvent]
      exact MeasurableSet.iUnion fun c =>
        U.Φ_measurable i₀ hnt' c.1 _ fun j => (ih _ (hst c j)).2.2.1
    · simp only [SurfaceUniverse.badExitEvent]
      exact MeasurableSet.iUnion fun c =>
        U.Φ_measurable i₀ hnt' c.1 _ fun j => (ih _ (hst c j)).2.2.2

/-- Bad exit events are null at a nonterminal state, assuming the law for smaller ranks. -/
theorem bad_exit_null (U : SurfaceUniverse) (i : U.ι) (hnt : (U.M i).s.terminal = false)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') (k : ℕ) :
    ∀ i' : U.ι, (U.M i').s = (U.M i).s → (U.M i').μ (U.badExitEvent k i') = 0 := by
  induction k with
  | zero =>
    intro i' hi'
    have hnt' : (U.M i').s.terminal = false := hi' ▸ hnt
    have : Finite (U.M i').cellIndex := (universe_basic_facts U i').2.2.2.2
    have : Countable (U.exitCells i') := by unfold SurfaceUniverse.exitCells; infer_instance
    simp only [SurfaceUniverse.badExitEvent]
    refine MeasureTheory.measure_iUnion_null fun c => MeasureTheory.measure_iUnion_null fun j₀ => ?_
    have hrank : ∀ j, (U.M (U.child i' c.1 j)).s.rank < (U.M i).s.rank := by
      intro j
      rw [U.child_state, ← hi']
      exact nonself_child_rank_lt (U.M i').s (U.M i').valid c.1.1.1 c.1.1.2 c.2
        _ (List.get_mem _ _)
    have hL := hIH _ (hrank j₀)
    have hmeas : ∀ j, MeasurableSet (Function.update (fun j =>
        (Set.univ : Set (Ideal (U.M (U.child i' c.1 j)).R))) j₀
        (U.nonterminatingSet (U.child i' c.1 j₀)) j) := by
      intro j
      by_cases h : j = j₀
      · subst h; rw [Function.update_self]
        exact (U.stateSet_measurable _).inter hL.2.1.compl
      · rw [Function.update_of_ne h]; exact MeasurableSet.univ
    unfold SurfaceUniverse.childBox
    rw [U.Φ_measure i' hnt' c.1 _ hmeas]
    rw [Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [Function.update_self]; exact hL.2.2),
        mul_zero]
  | succ k ih =>
    intro i' hi'
    have hnt' : (U.M i').s.terminal = false := hi' ▸ hnt
    have : Finite (U.M i').cellIndex := (universe_basic_facts U i').2.2.2.2
    have : Countable (U.selfCells i') := by unfold SurfaceUniverse.selfCells; infer_instance
    simp only [SurfaceUniverse.badExitEvent]
    refine MeasureTheory.measure_iUnion_null fun c => ?_
    have hs : ∀ j, (U.M (U.child i' c.1 j)).s = (U.M i).s := by
      intro j
      rw [U.child_state, ← hi']
      obtain ⟨a, b, _, hch⟩ := c.2
      have hm := List.get_mem ((U.M i').childList c.1) j
      have : (U.M i').childList c.1 = [(1, (U.M i').s)] := hch
      have key : ∀ z ∈ (U.M i').childList c.1, z = (1, (U.M i').s) := by
        rw [this]; simp
      have hm := key _ hm
      unfold MeasuredSurface.childState
      rw [hm]
    have hmeas : ∀ j, MeasurableSet (U.badExitEvent k (U.child i' c.1 j)) := fun j =>
      (recursion_events_measurable U i hnt hIH _ (hs j) k ∅).2.2.2
    unfold SurfaceUniverse.childBox
    rw [U.Φ_measure i' hnt' c.1 _ hmeas]
    have hpos : 0 < ((U.M i').childList c.1).length := by
      obtain ⟨a, b, _, hch⟩ := c.2
      have : (U.M i').childList c.1 = [(1, (U.M i').s)] := hch
      rw [this]; simp
    rw [Finset.prod_eq_zero_iff.mpr ⟨⟨0, hpos⟩, Finset.mem_univ _, ih _ (hs _)⟩, mul_zero]

/-- Summing the weight `P(d) · (σ-coefficient of the descended children laws)` over the exit
cells gives the `σ`-coefficient of the exit law. -/
private theorem exit_cell_weight_sum (U : SurfaceUniverse) (i : U.ι)
    (hnt : (U.M i).s.terminal = false) (σ : FactorType)
    [Fintype (U.exitCells i)] :
    ∑ c : U.exitCells i,
      (divisorProbability (U.M i).s ((U.M i).cellDegree c.1)).eval ((U.M i).q : ℚ) *
        (lawCoeff (lawProd (((U.M i).childList c.1).map fun z => lawDescend z.1 (stateLaw z.2)))
          σ).eval ((U.M i).q : ℚ) =
      (lawCoeff (exitLaw (U.M i).s) σ).eval ((U.M i).q : ℚ) := by
  classical
  let : ∀ P, Fintype (patternDivisors (IsLocalRing.ResidueField (U.M i).R) (U.M i).s P) :=
    fun P => @Fintype.ofFinite _ (U.divisors_finite i P)
  set M := U.M i with hM
  set s := M.s with hs
  set qq : ℚ := (M.q : ℚ) with hqq
  let F : M.cellIndex → ℚ := fun c =>
    (divisorProbability s (M.cellDegree c)).eval qq *
      (lawCoeff (lawProd ((M.childList c).map fun z => lawDescend z.1 (stateLaw z.2))) σ).eval qq
  let g : TangentPattern s.degree → ℚ := fun P => if SelfPattern s P then 0 else
    (tangentCount s P).eval qq * ((divisorProbability s P.d.val).eval qq *
      (lawCoeff (lawProd ((children s P).map fun z => lawDescend z.1 (stateLaw z.2))) σ).eval qq)
  have h1 : ∑ c : U.exitCells i, F c.1 =
      ∑ c : M.cellIndex, if M.IsSelfCell c then 0 else F c := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    exact (Finset.sum_subtype _ (fun x => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Iff.rfl) F).symm
  have h2 : (∑ c : M.cellIndex, if M.IsSelfCell c then 0 else F c) =
      ∑ P : M.allowedPattern, g P.1 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun P _ => ?_
    change ∑ D : patternDivisors (IsLocalRing.ResidueField M.R) s P.1,
        (if SelfPattern s P.1 then (0 : ℚ) else (divisorProbability s P.1.d.val).eval qq *
          (lawCoeff (lawProd ((children s P.1).map fun z => lawDescend z.1 (stateLaw z.2)))
              σ).eval qq)
        = g P.1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      U.divisor_count i hnt P.1 P.2]
    simp only [g]
    split_ifs
    · simp
    · simp only [mul_eq_mul_right_iff, mul_eq_zero]; left; rfl
  have h3 : ∑ P : M.allowedPattern, g P.1 = ∑ P ∈ allowedPatterns s, g P :=
    (Finset.sum_subtype _ (fun x => by
      simp only [allowedPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl) g).symm
  have h4 : (lawCoeff (exitLaw s) σ).eval qq = ∑ P ∈ allowedPatterns s, g P := by
    unfold exitLaw
    rw [(law_coeff_flatMap _ _ _ [] [] σ qq).2.2, Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun P _ => ?_
    simp only [g]
    split_ifs
    · exact (law_coeff_flatMap Unit [] (fun _ => []) [] [] σ qq).2.1
    · rw [law_coeff_scale]; change _ * _ * _ = _; ring
  exact h1.trans (h2.trans (h3.trans h4.symm))

/-- The immediate exit event of type `σ` has mass equal to the `σ`-coefficient of the exit law
times the volume of the state set; this coefficient is nonnegative and the event measurable. -/
theorem exit_event_zero_mass (U : SurfaceUniverse) (i : U.ι) (hnt : (U.M i).s.terminal = false)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') (σ : FactorType) :
    (U.M i).μ (U.exitEvent σ 0 i) = densityValue (lawCoeff (exitLaw (U.M i).s) σ) (U.M i).q *
        (U.M i).μ (U.M i).stateSet ∧
    0 ≤ (lawCoeff (exitLaw (U.M i).s) σ).eval ((U.M i).q : ℚ) ∧
      MeasurableSet (U.exitEvent σ 0 i) := by
  classical
  obtain ⟨hq, -, -, -, -⟩ := universe_basic_facts U i
  have hmeas : MeasurableSet (U.exitEvent σ 0 i) :=
    ((recursion_events_measurable U i hnt hIH) i rfl 0 σ).2.1
  set M := U.M i with hM
  set s := M.s with hs
  set qq : ℚ := (M.q : ℚ) with hqq
  -- the per-cell rational weight
  let F : M.cellIndex → ℚ := fun c =>
    (divisorProbability s (M.cellDegree c)).eval qq *
      (lawCoeff (lawProd ((M.childList c).map fun z => lawDescend z.1 (stateLaw z.2))) σ).eval qq
  have hFnn : ∀ c : U.exitCells i, 0 ≤ F c.1 := by
    intro c
    exact mul_nonneg ((divisor_probability_pos M.q hq s _ 2 le_rfl).1.le)
      (exit_cell_coeff_nonneg U i hIH c σ)
  have hbox_sub : ∀ c σ', U.typeBox i c σ' ⊆ M.cell c := by
    intro c σ' x hx
    simp only [SurfaceUniverse.typeBox, Set.mem_iUnion] at hx
    obtain ⟨τ, _, hx⟩ := hx
    exact hx.1
  have hbox_eq : ∀ c : U.exitCells i, U.typeBox i c.1 σ = U.exitEvent σ 0 i ∩ M.cell c.1 := by
    intro c
    ext x
    constructor
    · intro hx
      exact ⟨Set.mem_iUnion.2 ⟨c, hx⟩, hbox_sub _ _ hx⟩
    · rintro ⟨hE, hc⟩
      obtain ⟨c', hx'⟩ := Set.mem_iUnion.1 hE
      by_cases h : c'.1 = c.1
      · rw [← h]; exact hx'
      · exact absurd (U.cells_disjoint i hnt h) (Set.not_disjoint_iff.2 ⟨x, hbox_sub _ _ hx', hc⟩)
  let : ∀ P, Fintype (patternDivisors (IsLocalRing.ResidueField M.R) s P) :=
    fun P => @Fintype.ofFinite _ (U.divisors_finite i P)
  let : Fintype (U.exitCells i) := by unfold SurfaceUniverse.exitCells; infer_instance
  have hsum : (M.μ (U.exitEvent σ 0 i)) = ∑ c : U.exitCells i, ENNReal.ofReal ((F c.1 : ℚ) : ℝ) *
      M.μ M.stateSet := by
    rw [show U.exitEvent σ 0 i = ⋃ c : U.exitCells i, U.typeBox i c.1 σ from rfl]
    rw [MeasureTheory.measure_iUnion, tsum_fintype]
    · exact Finset.sum_congr rfl fun c _ => exit_cell_type_mass U i hnt hIH c σ
    · intro c c' hcc'
      have hne : c.1 ≠ c'.1 := fun h => hcc' (Subtype.ext h)
      exact (U.cells_disjoint i hnt hne).mono (hbox_sub _ _) (hbox_sub _ _)
    · intro c
      rw [hbox_eq c]
      exact hmeas.inter (U.cell_measurable i hnt c.1)
  have hrat : ∑ c : U.exitCells i, F c.1 = (lawCoeff (exitLaw s) σ).eval qq :=
    exit_cell_weight_sum U i hnt σ
  refine ⟨?_, ?_, hmeas⟩
  · rw [hsum, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
      (fun c _ => by exact_mod_cast hFnn c)]
    change _ = ENNReal.ofReal (((lawCoeff (exitLaw s) σ).eval qq : ℚ) : ℝ) * _
    rw [← hrat]
    push_cast
    rfl
  · rw [← hrat]
    exact Finset.sum_nonneg fun c _ => hFnn c

/-! ### Crossing states, return events and the law statement -/

/-- The law statement at a crossing state, assuming it for all states of smaller rank. -/
theorem recursion_crossing_law (U : SurfaceUniverse) (i : U.ι) (a b c h : ℕ)
    (hs : (U.M i).s = State.crossing a b c h)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') :
    U.LawStatement i := by
  have hnt : (U.M i).s.terminal = false := by rw [hs]; rfl
  have hv : (U.M i).s.Valid := (U.M i).valid
  have h560 := (single_state_return_chain U i hnt)
  have h551 := (state_law_unfold _ hv hnt).2 a b c h hs
  refine ⟨fun σ => ?_, ?_, ?_⟩
  · have e := ((h560 σ).2 a b c h hs).1
    obtain ⟨m, nn, ms⟩ := exit_event_zero_mass U i hnt hIH σ
    rw [e, h551]
    exact ⟨ms, nn, m⟩
  · have e := ((h560 (default)).2 a b c h hs).2
    rw [e]
    exact (recursion_events_measurable U i hnt hIH i rfl 0 default).2.2.1
  · exact MeasureTheory.measure_mono_null
      ((nonterminating_subset_return_or_bad U i hnt).2 a b c h hs)
      (bad_exit_null U i hnt hIH 0 i rfl)

/-- At `single a c`, the event of returning `k` times has mass `λᵏ · vol`, with `λ` the return
weight, and is measurable. -/
theorem return_event_mass (U : SurfaceUniverse) (a c : ℕ) (ha : 0 < a) (hc : 2 ≤ c) (k : ℕ) :
    ∀ i : U.ι, (U.M i).s = State.single a c →
    (U.M i).μ (U.returnEvent k i) = densityValue ((returnWeight c).pow k) (U.M i).q * (U.M i).μ
        (U.M i).stateSet ∧
    MeasurableSet (U.returnEvent k i) := by
  have hvalid : (State.single a c).Valid := ⟨ha, by omega⟩
  induction k with
  | zero =>
    intro i hs
    obtain ⟨hq, -, -, -, -⟩ := universe_basic_facts U i
    refine ⟨?_, U.stateSet_measurable i⟩
    simp only [SurfaceUniverse.returnEvent, Expr.pow]
    rw [(density_value_arith (U.M i).q hq (.const 1) (.const 1) (by norm_num [Expr.eval])
      (by norm_num [Expr.eval]) 0 _ hvalid).2.2.2.1, one_mul]
  | succ k ih =>
    intro i hs
    obtain ⟨hq, -, -, -, -⟩ := universe_basic_facts U i
    obtain ⟨hmass, hmeas⟩ := self_cells_union_mass U ha hc i hs (U.returnEvent k)
      (densityValue ((returnWeight c).pow k) (U.M i).q) fun i' hs' hq' ↦ by
        rw [← hq']; exact ih i' hs'
    refine ⟨hmass.trans ?_, hmeas⟩
    have hy := (return_weight_bounds _ c hq hc).1.le
    rw [Expr.pow, (density_value_arith (U.M i).q hq _ _ (eval_pow_nonneg _ _ hy k) hy 0 _
      hvalid).1]
    ring

/-- At `single a c` the set of ideals that return infinitely often is measurable and null. -/
theorem never_return_null (U : SurfaceUniverse) (a c : ℕ) (ha : 0 < a) (hc : 2 ≤ c) (i : U.ι)
    (hs : (U.M i).s = State.single a c) :
    (U.M i).μ (⋂ k, U.returnEvent k i) = 0 ∧ MeasurableSet (⋂ k, U.returnEvent k i) := by
  have hmass := fun k => return_event_mass U a c ha hc k i hs
  refine ⟨?_, MeasurableSet.iInter fun k => (hmass k).2⟩
  obtain ⟨hq, -, hfin, -⟩ := universe_basic_facts U i
  obtain ⟨hpos, -, hlt⟩ := return_weight_bounds (U.M i).q c hq hc
  have hlt' : ENNReal.ofReal (((returnWeight c).eval ((U.M i).q : ℚ) : ℚ) : ℝ) < 1 := by
    rw [ENNReal.ofReal_lt_one]; exact_mod_cast hlt
  have hle : ∀ k, (U.M i).μ (⋂ k, U.returnEvent k i) ≤
      (ENNReal.ofReal (((returnWeight c).eval ((U.M i).q : ℚ) : ℚ) : ℝ)) ^ k * (U.M i).μ
          (U.M i).stateSet := by
    intro k
    refine (MeasureTheory.measure_mono (Set.iInter_subset _ k)).trans ?_
    rw [(hmass k).1, densityValue, expression_pow_eval, ← ENNReal.ofReal_pow
        (by exact_mod_cast hpos.le)]
    norm_cast
  have ht := ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt')
    (Or.inr hfin)
  rw [zero_mul] at ht
  exact le_antisymm (ge_of_tendsto' ht hle) zero_le

/-- The law statement at a nonterminal single state, assuming it for all states of smaller rank. -/
theorem recursion_single_law (U : SurfaceUniverse) (i : U.ι) (a c : ℕ) (hc : 2 ≤ c)
    (hs : (U.M i).s = State.single a c)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') :
    U.LawStatement i := by
  have hnt : (U.M i).s.terminal = false := by
    rw [hs]; obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩; rfl
  have hv : (U.M i).s.Valid := (U.M i).valid
  have ha : 0 < a := by rw [hs] at hv; exact hv.1
  have h560 := single_state_return_chain U i hnt
  have h551 := (state_law_unfold _ hv hnt).1 a c hs
  have hq := (universe_basic_facts U i).1
  obtain ⟨hl0, -, hl1⟩ := return_weight_bounds _ c hq hc
  refine ⟨fun σ => ?_, ?_, ?_⟩
  · set q₀ := (U.M i).q with hq₀
    set lam : ℚ := (returnWeight c).eval (q₀ : ℚ) with hlam
    set G : ℚ := (lawCoeff (exitLaw (State.single a c)) σ).eval (q₀ : ℚ) with hGdef
    have hG : 0 ≤ G := by
      have := (exit_event_zero_mass U i hnt hIH σ).2.1
      rwa [hs] at this
    have hexit : ∀ i' : U.ι, (U.M i').s = State.single a c → (U.M i').q = q₀ →
        (U.M i').μ (U.exitEvent σ 0 i') = ENNReal.ofReal (G : ℝ) * (U.M i').μ (U.M i').stateSet
          ∧ MeasurableSet (U.exitEvent σ 0 i') := by
      intro i' hs' hq'
      have hnt' : (U.M i').s.terminal = false := by rw [hs', ← hs]; exact hnt
      have hIH' : ∀ j : U.ι, (U.M j).s.rank < (U.M i').s.rank → U.LawStatement j := by
        rw [hs', ← hs]; exact hIH
      obtain ⟨m, -, ms⟩ := exit_event_zero_mass U i' hnt' hIH' σ
      rw [hs', hq'] at m
      exact ⟨m, ms⟩
    have hk := fun k => exit_event_succ_mass U a c ha hc σ q₀ G hexit k i hs rfl
    obtain ⟨e, hdisj, -⟩ := (h560 σ).1 a c hs
    have hcoef : (lawCoeff (stateLaw (U.M i).s) σ).eval (q₀ : ℚ) = (1 - lam)⁻¹ * G := by
      rw [h551, law_coeff_scale, hs]
      simp only [Expr.eval, Expr.sub, Expr.neg, neg_mul, one_mul, hlam, hGdef]
      ring
    have hpos : (0 : ℚ) < 1 - lam := by linarith
    rw [e, hcoef]
    refine ⟨MeasurableSet.iUnion fun k => (hk k).2, by positivity, ?_⟩
    rw [MeasureTheory.measure_iUnion hdisj fun k => (hk k).2]
    simp only [fun k => (hk k).1]
    rw [ENNReal.tsum_mul_right, densityValue, ← ENNReal.ofReal_tsum_of_nonneg]
    · congr 2
      have := geometric_exit_sum (lam : ℝ) (G : ℝ) (by exact_mod_cast hl0.le)
        (by exact_mod_cast hl1)
      rw [hcoef]
      push_cast
      rw [this.tsum_eq]
      field_simp
    · intro k; push_cast; positivity
    · have := geometric_exit_sum (lam : ℝ) (G : ℝ) (by exact_mod_cast hl0.le)
        (by exact_mod_cast hl1)
      push_cast
      exact this.summable
  · rw [((h560 default).1 a c hs).2.2]
    exact MeasurableSet.iUnion fun k =>
      (recursion_events_measurable U i hnt hIH i rfl k default).2.2.1
  · refine MeasureTheory.measure_mono_null
      ((nonterminating_subset_return_or_bad U i hnt).1 a c hs) ?_
    refine MeasureTheory.measure_union_null
      (never_return_null U a c ha hc i hs).1 ?_
    exact MeasureTheory.measure_iUnion_null fun k =>
      bad_exit_null U i hnt hIH k i rfl

/-- The law statement holds for every member of a surface universe. -/
theorem universal_law_statement (U : SurfaceUniverse) :
    ∀ i : U.ι, U.LawStatement i := by
  have key : ∀ n : ℕ, ∀ i : U.ι, (U.M i).s.rank = n → U.LawStatement i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hn
      have hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i' :=
        fun i' h => ih _ (hn ▸ h) i' rfl
      have hv := (U.M i).valid
      generalize hs : (U.M i).s = s at hv
      cases s with
      | single a c =>
        by_cases h1 : c = 1
        · subst h1
          exact recursion_terminal_law U i (by rw [hs]; rfl)
        · have : 2 ≤ c := by
            have := hv.2; omega
          exact recursion_single_law U i a c this hs hIH
      | crossing a b c h =>
        exact recursion_crossing_law U i a b c h hs hIH
  exact fun i => key _ i rfl

/-! ### Type events -/

/-- The terminating type-`σ` event is measurable, contained in the type-`σ` event, and differs
from it by a subset of the null nonterminating set. -/
theorem type_event_null_difference (U : SurfaceUniverse) (i : U.ι) (σ : FactorType) :
    MeasurableSet (U.termTypeEvent i σ) ∧ U.termTypeEvent i σ ⊆ U.typeEvent i σ ∧
    U.typeEvent i σ ⊆ U.termTypeEvent i σ ∪ U.nonterminatingSet i ∧
    (U.M i).μ (U.nonterminatingSet i) = 0 := by
  have h := universal_law_statement U i
  refine ⟨(h.1 σ).1, Set.inter_subset_left, ?_, h.2.2⟩
  intro J hJ
  by_cases ht : J ∈ U.terminatingSet i
  · exact Or.inl ⟨hJ, ht⟩
  · refine Or.inr ⟨?_, ht⟩
    exact hJ.1

/-- Under the étale type-transport hypotheses, every type event of a surface universe is
measurable. -/
theorem etale_type_event_measurable (U : SurfaceUniverse)
    (hE1 : U.ChildTypesExist) (δ : ∀ i : U.ι, Ideal (U.M i).R → ℕ) (hE2 : U.InvariantDecreases δ)
    (i : U.ι) (σ : FactorType) :
    MeasurableSet (U.typeEvent i σ) := by
  rw [etale_type_event_eq_term U hE1 δ hE2 i σ]
  exact (type_event_null_difference U i σ).1

/-- A decomposition `K ⊗[O] B ≃ ∏ᵢ Lᵢ` of the generic fibre ascends along an unramified extension
`O → Oδ` (with `π` remaining a uniformizer) to `Kδ ⊗[Oδ] B ≃ ∏ᵢ Lᵢ`, compatibly with the
`O`-structures. -/
theorem unramified_generic_fibre_ascent (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ)
    (pi : O) (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi)) (B : Type)
    [CommRing B] [Algebra O B] [Algebra Oδ B] [IsScalarTower O Oδ B] (ι : Type)
    (L : ι → Type) [∀ i, Field (L i)] [∀ i, Algebra (BaseField O) (L i)]
    [∀ i, FiniteDimensional (BaseField O) (L i)]
    (e : TensorProduct O (BaseField O) B ≃ₐ[BaseField O] (∀ i, L i)) :
    ∃ (_ : ∀ i, Algebra (BaseField Oδ) (L i)) (_ : ∀ i, Algebra Oδ (L i))
        (_ : ∀ i, IsScalarTower Oδ (BaseField Oδ) (L i))
        (_ : ∀ i, FiniteDimensional (BaseField Oδ) (L i))
        (_ : TensorProduct Oδ (BaseField Oδ) B ≃ₐ[BaseField Oδ] (∀ i, L i)),
    ∀ i (c : O),
    algebraMap Oδ (L i) (algebraMap O Oδ c) = algebraMap (BaseField O) (L i)
        (algebraMap O (BaseField O) c) := by
  obtain ⟨-, -, hfr⟩ := unramified_fraction_base_change O Oδ δ hrank pi hpi hpiδ
  set K := BaseField O
  set Kδ := BaseField Oδ
  let rA : Algebra Oδ (TensorProduct O K Oδ) := Algebra.TensorProduct.rightAlgebra
  -- Oδ-algebra equivalence K ⊗ Oδ ≃ Oδ ⊗ K
  let c : TensorProduct O K Oδ ≃ₐ[Oδ] TensorProduct O Oδ K :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm O K Oδ).toRingEquiv) (by
      intro x
      change (Algebra.TensorProduct.comm O K Oδ) ((1 : K) ⊗ₜ x) = x ⊗ₜ (1 : K)
      simp)
  have : IsFractionRing Oδ (TensorProduct O Oδ K) := IsLocalization.isLocalization_of_algEquiv _ c
  let ψ : Kδ ≃ₐ[Oδ] TensorProduct O Oδ K :=
    IsLocalization.algEquiv (nonZeroDivisors Oδ) Kδ (TensorProduct O Oδ K)
  let Θ : TensorProduct Oδ Kδ B ≃+* TensorProduct O K B :=
    ((Algebra.TensorProduct.comm Oδ Kδ B).toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[Oδ] B) ψ).toRingEquiv).trans
      ((Algebra.TensorProduct.cancelBaseChange O Oδ Oδ B K).toRingEquiv.trans
        (Algebra.TensorProduct.comm O B K).toRingEquiv)
  let E₀ : TensorProduct Oδ Kδ B ≃+* (∀ i, L i) := Θ.trans e.toRingEquiv
  let f : ∀ i, Kδ →+* L i := fun i =>
    (Pi.evalRingHom L i).comp (E₀.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom)
  let iA : ∀ i, Algebra Kδ (L i) := fun i => (f i).toAlgebra
  let iB : ∀ i, Algebra Oδ (L i) := fun i => ((algebraMap Kδ (L i)).comp
      (algebraMap Oδ Kδ)).toAlgebra
  have iC : ∀ i, IsScalarTower Oδ Kδ (L i) := fun i => IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let φ : K →+* Kδ := ψ.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  let : Algebra K Kδ := φ.toAlgebra
  have hΘ : ∀ k : K, Θ (φ k ⊗ₜ 1) = k ⊗ₜ 1 := by
    intro k
    simp [Θ, φ]
  have : ∀ i, IsScalarTower K Kδ (L i) := fun i => IsScalarTower.of_algebraMap_eq (fun k => by
    change algebraMap K (L i) k = (e (Θ (φ k ⊗ₜ 1))) i
    rw [hΘ]
    have := e.commutes k
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this
    rw [this]
    rfl)
  have iD : ∀ i, FiniteDimensional Kδ (L i) := fun i => Module.Finite.of_restrictScalars_finite K Kδ
      (L i)
  refine ⟨iA, iB, iC, iD, AlgEquiv.ofRingEquiv (f := E₀) ?_, ?_⟩
  · exact fun r => rfl
  -- the `Oδ`-structure restricts to the `O`-structure through `K`
  have hφO : ∀ c : O, φ (algebraMap O K c) = algebraMap Oδ Kδ (algebraMap O Oδ c) := by
    intro c
    change ψ.symm (Algebra.TensorProduct.includeRight (algebraMap O K c)) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O Oδ (TensorProduct O Oδ K)]
    exact ψ.symm.commutes _
  intro i c
  change algebraMap Kδ (L i) (algebraMap Oδ Kδ (algebraMap O Oδ c)) = algebraMap K (L i)
      (algebraMap O K c)
  rw [← hφO, IsScalarTower.algebraMap_apply K Kδ (L i)]
  rfl

end SurfaceBlowup
