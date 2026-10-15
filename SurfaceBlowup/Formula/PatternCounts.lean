/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.Directions
import SurfaceBlowup.Measure.AdicTransport
import SurfaceBlowup.Formula.FiniteFieldCounts
import SurfaceBlowup.Formula.StateCombinatorics

/-!
# Counting divisors with a given tangent pattern

Over a finite field `k`, the exceptional divisors realizing a tangent pattern `P` of a state
`s` are in bijection with tuples of colorings of the nonboundary closed directions (one
coloring per degree), which yields the closed formula `#patternDivisors = tangentCount(q)`
with `q = #k`. Consequences: tangent counts and state-law coefficients are nonnegative at
prime powers. The file also records the count of nonboundary closed directions of each degree
and a continuity criterion for congruence-compatible maps.

## Main results

* `SurfaceBlowup.nonboundary_direction_count`: number of nonboundary directions of degree `δ`.
* `SurfaceBlowup.patternDivisors_equiv_colorings`: divisors with pattern `P` ≃ colorings.
* `SurfaceBlowup.pattern_divisor_count`: `#patternDivisors k s P = tangentCount s P (#k)`.
* `SurfaceBlowup.tangent_count_nonneg`, `SurfaceBlowup.state_law_coeff_nonneg`.
* `SurfaceBlowup.continuousOn_of_congruence_compatible`.

Provenance: `Thm_SurfaceBlowupV2_{nonboundary_direction_count,
pattern_divisors_equiv_colorings_v2, pattern_divisor_count, tangent_count_nonneg,
state_law_coeff_nonneg, continuousOn_of_congruence_compatible}` (the second inlines the proof
of `divisor_degree_pattern_weight`).
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-- Over a finite field `k`, the number of nonboundary closed directions of degree `δ > 0` is
the value at `q = #k` of `availablePoints` (with offset `-1` at a crossing state, where the
zero direction is also boundary). -/
theorem nonboundary_direction_count (k : Type) [Field k] [Finite k] (s : State) (δ : ℕ)
    (hδ : 0 < δ) :
    ((Nat.card {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧
        directionDegree k Q = δ} : ℕ) : ℚ) =
      (availablePoints
        (match s with | State.single _ _ => (0 : ℤ) | State.crossing _ _ _ _ => (-1 : ℤ))
        δ).eval (Nat.card k) := by
  have hN := finite_field_irreducible_count k δ hδ
  have hp1 : (pointCount 1).eval (Nat.card k) = (Nat.card k : ℚ) := by
    simp [pointCount, Expr.sum, Expr.eval, Expr.pow]
  set C : Prop := ((s matches State.crossing _ _ _ _) = true) with hC
  set T : Set (Polynomial k) :=
    {g | (g.Monic ∧ Irreducible g ∧ g.natDegree = δ) ∧ (C → g ≠ Polynomial.X)} with hT
  have hcard : Nat.card {Q : ClosedDirection k //
      Q ∉ boundaryDirections k s ∧ directionDegree k Q = δ} = Set.ncard T := by
    rw [← Nat.card_coe_set_eq]
    let f : T → {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧ directionDegree k Q = δ} :=
      fun g ↦ ⟨some ⟨g.1, g.2.1.1, g.2.1.2.1⟩, by
        obtain ⟨g, ⟨hm, hi, hd⟩, hx⟩ := g
        refine ⟨?_, hd⟩
        cases s <;> simp_all [boundaryDirections, infinityDirection, zeroDirection, C]⟩
    refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
    · rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
      simp only [f, Subtype.mk.injEq, Option.some.injEq] at h
      exact Subtype.ext h
    · rintro ⟨Q, hQ, hd⟩
      cases Q with
      | none => cases s <;> simp [boundaryDirections, infinityDirection] at hQ
      | some φ =>
        refine ⟨⟨φ.1, ⟨φ.2.1, φ.2.2, hd⟩, fun hc h ↦ hQ ?_⟩, rfl⟩
        cases s
        · simp [C] at hc
        · exact Or.inr (congrArg some (Subtype.ext h))
  rw [hcard]
  set A : Set (Polynomial k) := {g | g.Monic ∧ Irreducible g ∧ g.natDegree = δ} with hA
  have hNA : ((Set.ncard A : ℕ) : ℚ) = (pointCount δ).eval (Nat.card k) := by
    rw [← Nat.card_coe_set_eq]; exact hN
  by_cases h1 : δ = 1
  · subst h1
    have hq : ((Set.ncard A : ℕ) : ℚ) = Nat.card k := by rw [hNA, hp1]
    cases s with
    | single a c =>
      have : T = A := by ext g; simp [T, A, C]
      rw [this, hq]; simp [availablePoints, Expr.eval]
    | crossing a b c h =>
      have hTA : T = A \ {Polynomial.X} := by ext g; simp [T, A, C]
      have hXA : Polynomial.X ∈ A :=
        ⟨Polynomial.monic_X, Polynomial.irreducible_X, Polynomial.natDegree_X⟩
      have hfin : A.Finite := Set.finite_of_ncard_pos (by
        have : (0 : ℚ) < (Set.ncard A : ℕ) := by rw [hq]; exact_mod_cast Nat.card_pos
        exact_mod_cast this)
      have := Set.ncard_sdiff_singleton_add_one hXA hfin
      have h2 : ((Set.ncard (A \ {Polynomial.X}) : ℕ) : ℚ) + 1 = Nat.card k := by
        rw [← hq]; exact_mod_cast this
      rw [hTA]
      simp [availablePoints, Expr.eval]; linarith
  · have : T = A := by
      ext g
      simp only [T, A, Set.mem_ofPred_eq, and_iff_left_iff_imp]
      rintro ⟨-, -, hd⟩ - rfl
      exact h1 (hd ▸ Polynomial.natDegree_X)
    rw [this, hNA]; simp [availablePoints, h1]

/-! ### Divisors with a given pattern and colorings

The statement `patternDivisors_equiv_colorings` carries the extra hypothesis `hrx`
(`P.rx = 0` at a single state), the clause of `Allowed s P` that `HasPattern` does not carry;
without it the bijection fails. -/

section Colorings

variable (k : Type) [Field k]

/-- Every closed direction has positive degree. -/
theorem directionDegree_pos (Q : ClosedDirection k) : 0 < directionDegree k Q := by
  cases Q with
  | none => simp [directionDegree]
  | some φ => exact φ.property.2.natDegree_pos

private theorem inf_mem_bdry (s : State) : infinityDirection k ∈ boundaryDirections k s := by
  cases s <;> simp [boundaryDirections]

private theorem zero_ne_inf : zeroDirection k ≠ infinityDirection k := by
  simp [zeroDirection, infinityDirection]

private theorem mem_bdry_single (a c : ℕ) (Q : ClosedDirection k) :
    Q ∈ boundaryDirections k (State.single a c) ↔ Q = infinityDirection k := by
  simp [boundaryDirections]

private theorem mem_bdry_crossing (a b c h : ℕ) (Q : ClosedDirection k) :
    Q ∈ boundaryDirections k (State.crossing a b c h) ↔
      Q = infinityDirection k ∨ Q = zeroDirection k := by
  simp [boundaryDirections]

private theorem deg_of_mem_bdry (s : State) (Q : ClosedDirection k)
    (hQ : Q ∈ boundaryDirections k s) : directionDegree k Q = 1 := by
  cases s with
  | single a c =>
    rw [mem_bdry_single] at hQ
    subst hQ; rfl
  | crossing a b c h =>
    rcases (mem_bdry_crossing k a b c h Q).1 hQ with rfl | rfl
    · rfl
    · simp [directionDegree, zeroDirection]

/-- Closed directions of bounded degree over a finite field are finite. -/
private theorem finite_directionDegree_le [Finite k] (n : ℕ) :
    Finite {Q : ClosedDirection k // directionDegree k Q ≤ n} := by
  let f : {Q : ClosedDirection k // directionDegree k Q ≤ n} → Option (Fin (n+1) → k) :=
    fun Q ↦ Option.map (fun φ : AffineDirection k ↦ fun i : Fin (n+1) ↦ φ.val.coeff i) Q.1
  refine Finite.of_injective f ?_
  rintro ⟨Q, hQ⟩ ⟨Q', hQ'⟩ h
  apply Subtype.ext
  simp only [f] at h
  cases Q with
  | none =>
    cases Q' with
    | none => rfl
    | some _ => simp at h
  | some φ =>
    cases Q' with
    | none => simp at h
    | some ψ =>
      simp only [Option.map_some, Option.some.injEq] at h
      refine congrArg some (Subtype.ext (Polynomial.ext fun i ↦ ?_))
      by_cases hi : i < n + 1
      · exact congrFun h ⟨i, hi⟩
      · have h1 : φ.val.natDegree < i := by simp [directionDegree] at hQ; omega
        have h2 : ψ.val.natDegree < i := by simp [directionDegree] at hQ'; omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt h1,
          Polynomial.coeff_eq_zero_of_natDegree_lt h2]

/-- The nonboundary points of degree `i + 1`. -/
private abbrev Pt (s : State) (i : Fin s.degree) : Type :=
  {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧ directionDegree k Q = i.val + 1}

/-- Colorings of the degree-`(i + 1)` nonboundary points with the prescribed counts. -/
private abbrev Col (s : State) (P : TangentPattern s.degree) (i : Fin s.degree) : Type :=
  {f : Pt k s i → Option (Fin s.degree) //
    ∀ j : Fin s.degree, Nat.card {Q // f Q = some j} = (P.other (i, j)).val}

private theorem card_fiber_eq (s : State) (D : ExceptionalDivisor k) (i j : Fin s.degree)
    (f : Pt k s i → Option (Fin s.degree))
    (hf : ∀ Q : Pt k s i, f Q = some j ↔ D Q.1 = j.val + 1) :
    Nat.card {Q : Pt k s i // f Q = some j} =
      Nat.card {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧
        directionDegree k Q = i.val + 1 ∧ D Q = j.val + 1} :=
  Nat.card_congr
    { toFun := fun Q ↦ ⟨Q.1.1, Q.1.2.1, Q.1.2.2, (hf Q.1).1 Q.2⟩
      invFun := fun Q ↦ ⟨⟨Q.1, Q.2.1, Q.2.2.1⟩, (hf _).2 Q.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-! #### Forward direction: divisor → colorings -/

private theorem deg_mul_mult_le (s : State) (P : TangentPattern s.degree)
    (D : patternDivisors k s P) (Q : ClosedDirection k) :
    directionDegree k Q * D.1 Q ≤ s.degree := by
  have hdeg : exceptionalDegree k D.1 = P.d.val := D.2.1
  have h3 : P.d.val ≤ s.degree := Nat.lt_succ_iff.mp P.d.isLt
  by_cases hQ : D.1 Q = 0
  · simp [hQ]
  · have h1 : directionDegree k Q * D.1 Q ≤ exceptionalDegree k D.1 :=
      Finset.single_le_sum (f := fun P ↦ directionDegree k P * D.1 P)
        (fun _ _ ↦ Nat.zero_le _) (Finsupp.mem_support_iff.mpr hQ)
    omega

private theorem mult_le (s : State) (P : TangentPattern s.degree) (D : patternDivisors k s P)
    (Q : ClosedDirection k) : D.1 Q ≤ s.degree :=
  (Nat.le_mul_of_pos_left _ (directionDegree_pos k Q)).trans (deg_mul_mult_le k s P D Q)

private def toColFun (s : State) (P : TangentPattern s.degree) (D : patternDivisors k s P)
    (i : Fin s.degree) : Pt k s i → Option (Fin s.degree) :=
  fun Q ↦ if D.1 Q.1 = 0 then none
    else some ⟨D.1 Q.1 - 1, by have := mult_le k s P D Q.1; omega⟩

private theorem toColFun_eq_some_iff (s : State) (P : TangentPattern s.degree)
    (D : patternDivisors k s P) (i j : Fin s.degree) (Q : Pt k s i) :
    toColFun k s P D i Q = some j ↔ D.1 Q.1 = j.val + 1 := by
  unfold toColFun
  split_ifs with h
  · simp only [false_iff]; omega
  · simp only [Option.some.injEq, Fin.ext_iff]; omega

private def toCol (s : State) (P : TangentPattern s.degree) (D : patternDivisors k s P) :
    ∀ i : Fin s.degree, Col k s P i :=
  fun i ↦ ⟨toColFun k s P D i, fun j ↦ by
    rw [card_fiber_eq k s D.1 i j _ (toColFun_eq_some_iff k s P D i j)]
    exact D.2.2.2.2 (i, j)⟩

/-! #### Backward direction: colorings → divisor -/

private theorem coloring_congr (s : State) (P : TangentPattern s.degree)
    (F : ∀ i : Fin s.degree, Col k s P i) (i i' : Fin s.degree) (hii : i = i')
    (Q : ClosedDirection k) (hb : Q ∉ boundaryDirections k s)
    (h1 : directionDegree k Q = i.val + 1) (h2 : directionDegree k Q = i'.val + 1) :
    (F i).1 ⟨Q, hb, h1⟩ = (F i').1 ⟨Q, hb, h2⟩ := by
  subst hii; rfl

private theorem elim_le (n : ℕ) (o : Option (Fin n)) :
    Option.elim o 0 (fun j ↦ j.val + 1) ≤ n := by
  cases o with
  | none => exact Nat.zero_le _
  | some j => exact j.isLt

open scoped Classical in
/-- The multiplicity at `Q` of the divisor attached to a tuple of colorings. -/
private noncomputable def mult (s : State) (P : TangentPattern s.degree)
    (F : ∀ i : Fin s.degree, Col k s P i) (Q : ClosedDirection k) : ℕ :=
  if Q = infinityDirection k then P.rt.val
  else if hb : Q ∈ boundaryDirections k s then P.rx.val
  else if h : directionDegree k Q ≤ s.degree then
    Option.elim ((F ⟨directionDegree k Q - 1, by have := directionDegree_pos k Q; omega⟩).1
      ⟨Q, hb, (by have := directionDegree_pos k Q; omega :
        directionDegree k Q = directionDegree k Q - 1 + 1)⟩) 0 (fun j ↦ j.val + 1)
  else 0

private theorem mult_inf (s : State) (P : TangentPattern s.degree)
    (F : ∀ i : Fin s.degree, Col k s P i) :
    mult k s P F (infinityDirection k) = P.rt.val := by
  unfold mult; rw [if_pos rfl]

private theorem mult_zero_crossing (a b c h : ℕ)
    (P : TangentPattern (State.crossing a b c h).degree)
    (F : ∀ i : Fin (State.crossing a b c h).degree, Col k (State.crossing a b c h) P i) :
    mult k (State.crossing a b c h) P F (zeroDirection k) = P.rx.val := by
  unfold mult
  rw [if_neg (zero_ne_inf k), dif_pos ((mem_bdry_crossing k a b c h _).2 (Or.inr rfl))]

private theorem mult_nonbdry (s : State) (P : TangentPattern s.degree)
    (F : ∀ i : Fin s.degree, Col k s P i) (i : Fin s.degree) (Q : Pt k s i) :
    mult k s P F Q.1 = Option.elim ((F i).1 Q) 0 (fun j ↦ j.val + 1) := by
  obtain ⟨Q, hb, hQ⟩ := Q
  have hinf : Q ≠ infinityDirection k := fun h ↦ hb (h ▸ inf_mem_bdry k s)
  have hle : directionDegree k Q ≤ s.degree := by omega
  have hpos := directionDegree_pos k Q
  change mult k s P F Q = Option.elim ((F i).1 ⟨Q, hb, hQ⟩) 0 (fun j ↦ j.val + 1)
  unfold mult
  rw [if_neg hinf, dif_neg hb, dif_pos hle]
  congr 1
  exact coloring_congr k s P F ⟨directionDegree k Q - 1, by omega⟩ i
    (Fin.ext (by change directionDegree k Q - 1 = i.val; omega)) Q hb
    (by omega : directionDegree k Q = directionDegree k Q - 1 + 1) hQ

private theorem mult_support_finite [Finite k] (s : State) (P : TangentPattern s.degree)
    (F : ∀ i : Fin s.degree, Col k s P i) : (Function.support (mult k s P F)).Finite := by
  have hfin : Set.Finite {Q : ClosedDirection k | directionDegree k Q ≤ max 1 s.degree} :=
    Set.finite_coe_iff.mp (finite_directionDegree_le k (max 1 s.degree))
  refine hfin.subset fun Q hQ ↦ ?_
  rw [Function.mem_support] at hQ
  change directionDegree k Q ≤ max 1 s.degree
  unfold mult at hQ
  split_ifs at hQ with h1 h2 h3
  · subst h1; exact le_max_left _ _
  · rw [deg_of_mem_bdry k s Q h2]; exact le_max_left _ _
  · exact le_trans h3 (le_max_right _ _)
  · exact absurd rfl hQ

/-- The exceptional divisor attached to a tuple of colorings. -/
private noncomputable def toDiv [Finite k] (s : State) (P : TangentPattern s.degree)
    (F : ∀ i : Fin s.degree, Col k s P i) : ExceptionalDivisor k :=
  Finsupp.ofSupportFinite (mult k s P F) (mult_support_finite k s P F)

private theorem toDiv_apply [Finite k] (s : State) (P : TangentPattern s.degree)
    (F : ∀ i : Fin s.degree, Col k s P i) (Q : ClosedDirection k) :
    toDiv k s P F Q = mult k s P F Q := rfl

private theorem toDiv_some_iff [Finite k] (s : State) (P : TangentPattern s.degree)
    (F : ∀ i : Fin s.degree, Col k s P i) (i j : Fin s.degree) (Q : Pt k s i) :
    (F i).1 Q = some j ↔ toDiv k s P F Q.1 = j.val + 1 := by
  rw [toDiv_apply, mult_nonbdry k s P F i Q]
  cases (F i).1 Q with
  | none => simp
  | some j' => simp [Fin.ext_iff]

private theorem toDiv_card [Finite k] (s : State) (P : TangentPattern s.degree)
    (F : ∀ i : Fin s.degree, Col k s P i) (ij : Fin s.degree × Fin s.degree) :
    Nat.card {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧
      directionDegree k Q = ij.1.val + 1 ∧ toDiv k s P F Q = ij.2.val + 1} =
        (P.other ij).val := by
  rw [← card_fiber_eq k s (toDiv k s P F) ij.1 ij.2 (F ij.1).1 (toDiv_some_iff k s P F ij.1 ij.2)]
  exact (F ij.1).2 ij.2

/-- Degree of an exceptional divisor of bounded degrees and multiplicities, split into the
boundary part and the pattern weight of its nonboundary part (the proof of the node
`divisor_degree_pattern_weight`). -/
private theorem degree_formula [Finite k] (s : State) (Dv : ExceptionalDivisor k) (n : ℕ)
    (hdeg : ∀ Q, 0 < Dv Q → directionDegree k Q ≤ n) (hmult : ∀ Q, Dv Q ≤ n) :
    exceptionalDegree k Dv = Dv (infinityDirection k) + (match s with
      | State.single _ _ => (0 : ℕ) | State.crossing _ _ _ _ => Dv (zeroDirection k)) +
      ∑ ij : Fin n × Fin n, (ij.1.val + 1) * (ij.2.val + 1) *
        Nat.card {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧
          directionDegree k Q = ij.1.val + 1 ∧ Dv Q = ij.2.val + 1} := by
  classical
  obtain ⟨B, hB, hBsum⟩ : ∃ B : Finset (ClosedDirection k),
      (∀ Q, Q ∈ boundaryDirections k s ↔ Q ∈ B) ∧
      ∑ Q ∈ B, directionDegree k Q * Dv Q = Dv (infinityDirection k) +
        (match s with
          | State.single _ _ => (0 : ℕ) | State.crossing _ _ _ _ => Dv (zeroDirection k)) := by
    cases s with
    | single _ _ =>
      exact ⟨{infinityDirection k}, fun Q ↦ by simp [boundaryDirections],
        by simp [infinityDirection, directionDegree]⟩
    | crossing _ _ _ _ =>
      refine ⟨{infinityDirection k, zeroDirection k}, fun Q ↦ by simp [boundaryDirections], ?_⟩
      rw [Finset.sum_pair (by simp [infinityDirection, zeroDirection])]
      simp [infinityDirection, zeroDirection, directionDegree]
  set f : ClosedDirection k → ℕ := fun Q ↦ directionDegree k Q * Dv Q with hf
  change ∑ Q ∈ Dv.support, f Q = _
  rw [← Finset.sum_filter_add_sum_filter_not Dv.support (fun Q ↦ Q ∈ B)]
  congr 1
  · rw [← hBsum]
    refine Finset.sum_subset (fun Q hQ ↦ (Finset.mem_filter.1 hQ).2) fun Q hQB hQ ↦ ?_
    have : Dv Q = 0 := by
      by_contra h
      exact hQ (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 h, hQB⟩)
    simp [f, this]
  · rcases n with _ | m
    · simp [fun Q ↦ Nat.le_zero.1 (hmult Q)]
    · set g : ClosedDirection k → Fin (m+1) × Fin (m+1) :=
        fun Q ↦ (⟨(directionDegree k Q - 1) % (m+1), Nat.mod_lt _ (Nat.succ_pos _)⟩,
          ⟨(Dv Q - 1) % (m+1), Nat.mod_lt _ (Nat.succ_pos _)⟩)
      rw [← Finset.sum_fiberwise_of_maps_to (s := Dv.support.filter (fun Q ↦ Q ∉ B))
        (t := Finset.univ) (g := g) (fun _ _ ↦ Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun ij _ ↦ ?_
      have hmem : ∀ Q, Q ∈ (Dv.support.filter (fun Q ↦ Q ∉ B)).filter (fun Q ↦ g Q = ij) ↔
          (Q ∉ boundaryDirections k s ∧ directionDegree k Q = ij.1.val + 1 ∧
            Dv Q = ij.2.val + 1) := by
        intro Q
        simp only [Finset.mem_filter, Finsupp.mem_support_iff, hB, g, Prod.ext_iff, Fin.ext_iff]
        have h1 := directionDegree_pos k Q
        constructor
        · rintro ⟨⟨hne, hnb⟩, ha, hb⟩
          have hd := hdeg Q (Nat.pos_of_ne_zero hne)
          have hm := hmult Q
          rw [Nat.mod_eq_of_lt (by omega)] at ha hb
          exact ⟨hnb, by omega, by omega⟩
        · rintro ⟨hnb, ha, hb⟩
          refine ⟨⟨by omega, hnb⟩, ?_, ?_⟩
          · rw [ha, Nat.add_sub_cancel, Nat.mod_eq_of_lt ij.1.2]
          · rw [hb, Nat.add_sub_cancel, Nat.mod_eq_of_lt ij.2.2]
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun Q ↦ (hmem Q).symm)),
        Nat.card_eq_finsetCard,
        Finset.sum_congr rfl (g := fun _ ↦ (ij.1.val + 1) * (ij.2.val + 1)),
        Finset.sum_const, smul_eq_mul, mul_comm]
      intro Q hQ
      obtain ⟨_, ha, hb⟩ := (hmem Q).1 hQ
      simp [f, ha, hb]

private theorem toDiv_hasPattern [Finite k] (s : State) (P : TangentPattern s.degree)
    (hP : P.rt.val + P.rx.val + patternWeight P.other = P.d.val)
    (hrx : ∀ a c, s = State.single a c → P.rx.val = 0)
    (F : ∀ i : Fin s.degree, Col k s P i) : HasPattern k s (toDiv k s P F) P := by
  have hdeg : ∀ Q, 0 < toDiv k s P F Q → directionDegree k Q ≤ s.degree := by
    intro Q hQ
    rw [toDiv_apply] at hQ
    unfold mult at hQ
    split_ifs at hQ with h1 h2 h3
    · subst h1
      change 1 ≤ s.degree
      have := P.rt.isLt; omega
    · rw [deg_of_mem_bdry k s Q h2]; have := P.rx.isLt; omega
    · exact h3
    · exact absurd hQ (lt_irrefl 0)
  have hmult : ∀ Q, toDiv k s P F Q ≤ s.degree := by
    intro Q
    rw [toDiv_apply]
    unfold mult
    split_ifs with h1 h2 h3
    · exact Nat.lt_succ_iff.mp P.rt.isLt
    · exact Nat.lt_succ_iff.mp P.rx.isLt
    · exact elim_le _ _
    · exact Nat.zero_le _
  have hsum : ∑ ij : Fin s.degree × Fin s.degree, (ij.1.val + 1) * (ij.2.val + 1) *
      Nat.card {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧
        directionDegree k Q = ij.1.val + 1 ∧ toDiv k s P F Q = ij.2.val + 1} =
      patternWeight P.other :=
    Finset.sum_congr rfl fun ij _ ↦ by rw [toDiv_card k s P F ij]
  refine ⟨?_, mult_inf k s P F, ?_, toDiv_card k s P F⟩
  · rw [degree_formula k s (toDiv k s P F) s.degree hdeg hmult, hsum, toDiv_apply, mult_inf]
    cases s with
    | single a c =>
      have := hrx a c rfl
      change P.rt.val + 0 + patternWeight P.other = P.d.val
      omega
    | crossing a b c h =>
      change P.rt.val + toDiv k _ P F (zeroDirection k) + patternWeight P.other = P.d.val
      rwa [toDiv_apply, mult_zero_crossing]
  · cases s with
    | single a c => trivial
    | crossing a b c h =>
      change toDiv k _ P F (zeroDirection k) = P.rx.val
      rw [toDiv_apply, mult_zero_crossing]

/-! #### Round trips -/

private theorem toDiv_toCol [Finite k] (s : State) (P : TangentPattern s.degree)
    (D : patternDivisors k s P) : toDiv k s P (toCol k s P D) = D.1 := by
  ext Q
  rw [toDiv_apply]
  by_cases h1 : Q = infinityDirection k
  · subst h1; rw [mult_inf]; exact D.2.2.1.symm
  by_cases h2 : Q ∈ boundaryDirections k s
  · cases s with
    | single a c => exact absurd ((mem_bdry_single k a c Q).1 h2) h1
    | crossing a b c h =>
      rcases (mem_bdry_crossing k a b c h Q).1 h2 with rfl | rfl
      · exact absurd rfl h1
      · rw [mult_zero_crossing]
        exact D.2.2.2.1.symm
  by_cases h3 : directionDegree k Q ≤ s.degree
  · have hpos := directionDegree_pos k Q
    rw [mult_nonbdry k s P (toCol k s P D) ⟨directionDegree k Q - 1, by omega⟩
      ⟨Q, h2, (by omega : directionDegree k Q = directionDegree k Q - 1 + 1)⟩]
    unfold toCol toColFun
    dsimp only
    split_ifs with hz
    · simp only [Option.elim]; omega
    · simp only [Option.elim]
      change D.1 Q - 1 + 1 = D.1 Q
      omega
  · unfold mult
    rw [if_neg h1, dif_neg h2, dif_neg h3]
    by_contra hne
    have h4 := deg_mul_mult_le k s P D Q
    have h5 : directionDegree k Q ≤ directionDegree k Q * D.1 Q :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (Ne.symm hne))
    omega

private theorem toCol_toDiv [Finite k] (s : State) (P : TangentPattern s.degree)
    (hP : P.rt.val + P.rx.val + patternWeight P.other = P.d.val)
    (hrx : ∀ a c, s = State.single a c → P.rx.val = 0)
    (F : ∀ i : Fin s.degree, Col k s P i) :
    toCol k s P ⟨toDiv k s P F, toDiv_hasPattern k s P hP hrx F⟩ = F := by
  funext i
  refine Subtype.ext (funext fun Q ↦ ?_)
  change toColFun k s P ⟨toDiv k s P F, toDiv_hasPattern k s P hP hrx F⟩ i Q = (F i).1 Q
  have hm : toDiv k s P F Q.1 = Option.elim ((F i).1 Q) 0 (fun j ↦ j.val + 1) :=
    mult_nonbdry k s P F i Q
  unfold toColFun
  cases hFQ : (F i).1 Q with
  | none =>
    rw [hFQ] at hm
    exact if_pos hm
  | some j =>
    rw [hFQ] at hm
    simp only [Option.elim] at hm
    rw [if_neg (by change toDiv k s P F Q.1 ≠ 0; omega)]
    exact congrArg some (Fin.ext (by change toDiv k s P F Q.1 - 1 = j.val; omega))

end Colorings

/-- Over a finite field, the exceptional divisors with tangent pattern `P` are in bijection
with tuples, indexed by degrees `i + 1`, of colorings of the nonboundary directions of that
degree by `Fin s.degree ⊕ none` with color counts `P.other (i, j)`. -/
theorem patternDivisors_equiv_colorings (k : Type) [Field k] [Finite k] (s : State)
    (P : TangentPattern s.degree) (hP : P.rt.val + P.rx.val + patternWeight P.other = P.d.val)
    (hrx : ∀ a c, s = State.single a c → P.rx.val = 0) :
    Nonempty (patternDivisors k s P ≃ ∀ i : Fin s.degree,
      {f : {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧
          directionDegree k Q = i.val + 1} → Option (Fin s.degree) //
        ∀ j : Fin s.degree, Nat.card {Q // f Q = some j} = (P.other (i, j)).val}) :=
  ⟨{ toFun := toCol k s P
     invFun := fun F ↦ ⟨toDiv k s P F, toDiv_hasPattern k s P hP hrx F⟩
     left_inv := fun D ↦ Subtype.ext (toDiv_toCol k s P D)
     right_inv := fun F ↦ toCol_toDiv k s P hP hrx F }⟩

/-! ### Counting pattern divisors -/

/-- Number of colorings of a finite set `T` by `Fin r ⊕ none` with prescribed color counts
`m j`: a falling factorial over a product of factorials. -/
private theorem card_colorings (T : Type) [Finite T] (r : ℕ) (m : Fin r → ℕ) :
    ((Nat.card {f : T → Option (Fin r) // ∀ j : Fin r, Nat.card {x // f x = some j} = m j} :
        ℕ) : ℚ)
      = ((List.range (∑ i : Fin r, m i)).map fun j ↦ (Nat.card T : ℚ) - j).prod
          / ∏ i : Fin r, (Nat.factorial (m i) : ℚ) := by
  obtain e := Finite.equivFin T
  have hequiv : {f : T → Option (Fin r) // ∀ j : Fin r, Nat.card {x // f x = some j} = m j} ≃
      {f : Fin (Nat.card T) → Option (Fin r) //
        ∀ i : Fin r, Nat.card {x : Fin (Nat.card T) // f x = some i} = m i} := by
    refine Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl _)) fun f ↦ forall_congr' fun j ↦ ?_
    rw [Nat.card_congr (e.subtypeEquiv (p := fun x ↦ f x = some j)
      (q := fun x ↦ (Equiv.arrowCongr e (Equiv.refl _) f) x = some j)
      fun x ↦ by simp [Equiv.arrowCongr_apply])]
  rw [Nat.card_congr hequiv, colored_subset_count]

/-- For an allowed pattern over a finite field `k`, there are finitely many divisors with
pattern `P`, and their number is `tangentCount s P` evaluated at `#k`. -/
theorem pattern_divisor_count (k : Type) [Field k] [Finite k] (s : State)
    (P : TangentPattern s.degree) (hP : Allowed s P) :
    Finite (patternDivisors k s P) ∧
      ((Nat.card (patternDivisors k s P) : ℕ) : ℚ) = (tangentCount s P).eval (Nat.card k) := by
  obtain ⟨e⟩ := patternDivisors_equiv_colorings k s P hP.2.1
    (fun a c hs ↦ by subst hs; exact hP.2.2.2.1)
  have hfin : ∀ i : Fin s.degree, Finite
      {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧ directionDegree k Q = i.val + 1} :=
    fun i ↦ have := finite_directionDegree_le k (i.val + 1)
      Finite.of_injective (fun Q ↦ (⟨Q.1, Q.2.2.le⟩ : {Q // directionDegree k Q ≤ i.val + 1}))
        fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_pi, Nat.cast_prod]
  unfold tangentCount divisorCount
  rw [expression_prod_eval, List.map_map, Finset.prod_map_toList]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have := hfin i
  rw [card_colorings]
  simp only [Function.comp, Expr.eval, falling, expression_prod_eval, List.map_map]
  rw [nonboundary_direction_count k s (i.val + 1) (Nat.succ_pos _), div_eq_mul_one_div]
  congr 2
  refine List.map_congr_left fun j _ ↦ ?_
  cases s <;> simp [Expr.sub, Expr.neg, Expr.eval, sub_eq_add_neg]

/-- Tangent counts are nonnegative at prime powers (they count divisors over `GF(p, e)`). -/
theorem tangent_count_nonneg (Q : ℕ) (hQ : PrimePower Q) (s : State)
    (P : TangentPattern s.degree) (hP : Allowed s P) :
    0 ≤ (tangentCount s P).eval Q := by
  obtain ⟨p, e, hp, he, rfl⟩ := hQ
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (GaloisField p e) := Module.finite_of_finite (ZMod p)
  have h := (pattern_divisor_count (GaloisField p e) s P hP).2
  rw [GaloisField.card p e he.ne'] at h
  exact h ▸ Nat.cast_nonneg _

/-! ### Nonnegativity of state-law coefficients -/

private theorem primePower_pow (Q : ℕ) (hQ : PrimePower Q) (δ : ℕ) (hδ : 0 < δ) :
    PrimePower (Q ^ δ) := by
  obtain ⟨p, r, hp, hr, rfl⟩ := hQ
  exact ⟨p, r * δ, hp, Nat.mul_pos hr hδ, (pow_mul p r δ).symm⟩

private theorem stateLawFuel_coeff_nonneg (k : ℕ) :
    ∀ (s : State), s.Valid → ∀ Q : ℕ, PrimePower Q → ∀ σ : FactorType,
      0 ≤ (lawCoeff (stateLawFuel k s) σ).eval Q := by
  classical
  induction k with
  | zero =>
    intro s _ Q _ σ
    simp only [stateLawFuel]
    exact le_of_eq ((law_coeff_nonneg_closure (Q : ℚ)).2.2.2.2.2.2.2 σ).symm
  | succ k ih =>
    intro s hs Q hQ σ
    obtain ⟨hScale, -, hProd, hFlat, hDesc, hAtom, -, hNil⟩ := law_coeff_nonneg_closure (Q : ℚ)
    have hQ2 : 2 ≤ Q := prime_power_ge_two Q hQ
    have hterms : ∀ σ : FactorType, 0 ≤ (lawCoeff ((allowedPatterns s).toList.flatMap fun P ↦
        if SelfPattern s P then [] else
          lawScale (.mul (tangentCount s P) (divisorProbability s P.d.val))
            (lawProd ((children s P).map fun z ↦ lawDescend z.1 (stateLawFuel k z.2)))) σ).eval
              Q := by
      refine hFlat _ _ _ fun P hPmem σ ↦ ?_
      have hP : Allowed s P := by
        rw [Finset.mem_toList, allowedPatterns, Finset.mem_filter] at hPmem
        exact hPmem.2
      split_ifs
      · exact le_of_eq (hNil σ).symm
      · refine hScale _ _ (by
          simpa only [Expr.eval] using mul_nonneg (tangent_count_nonneg Q hQ s P hP)
            (divisor_probability_pos Q hQ2 s P.d.val 2 le_rfl).1.le) (hProd _ ?_) σ
        simp only [List.mem_map]
        rintro _ ⟨z, hz, rfl⟩
        have hz1 := children_residue_degree_pos s P z hz
        refine hDesc z.1 hz1 _ fun σ ↦ ?_
        exact_mod_cast ih z.2 (children_valid s hs P hP z hz) (Q ^ z.1)
          (primePower_pow Q hQ z.1 hz1) σ
    cases s with
    | single a c =>
      rcases c with _ | _ | c
      · exact absurd hs.2 (lt_irrefl 0)
      · exact hAtom a 1 σ
      · exact hScale _ _
          (divisor_probability_pos Q hQ2 (State.single a 0) 0 (c + 2) (by omega)).2.le hterms σ
    | crossing a b c h => exact hterms σ

/-- At a prime power `Q`, the coefficients of the law of a valid state, and of all its
descents, are nonnegative. -/
theorem state_law_coeff_nonneg (Q : ℕ) (hQ : PrimePower Q) (s : State) (hs : s.Valid)
    (σ : FactorType) :
    0 ≤ (lawCoeff (stateLaw s) σ).eval Q ∧
      ∀ δ : ℕ, 0 < δ → 0 ≤ (lawCoeff (lawDescend δ (stateLaw s)) σ).eval Q := by
  refine ⟨stateLawFuel_coeff_nonneg _ s hs Q hQ σ, fun δ hδ ↦ ?_⟩
  refine (law_coeff_nonneg_closure (Q : ℚ)).2.2.2.2.1 δ hδ _ (fun σ ↦ ?_) σ
  exact_mod_cast stateLawFuel_coeff_nonneg (s.rank + 1) s hs (Q ^ δ) (primePower_pow Q hQ δ hδ) σ

/-! ### Continuity of congruence-compatible maps -/

/-- A map between finite products of adic rings that preserves congruence modulo `I₁ ^ L`
(sending it to congruence modulo `I₂ ^ L`) on a set `C` is continuous on `C`. -/
theorem continuousOn_of_congruence_compatible (O₁ O₂ : Type) [CommRing O₁] [TopologicalSpace O₁]
    [IsTopologicalRing O₁] (I₁ : Ideal O₁) (h₁ : IsAdic I₁) [CommRing O₂] [TopologicalSpace O₂]
    [IsTopologicalRing O₂] (I₂ : Ideal O₂) (h₂ : IsAdic I₂) (ι : Type) [Finite ι] (d : ι → ℕ)
    (n₂ : ℕ) (C : Set (∀ i, Fin (d i) → O₁)) (f : (∀ i, Fin (d i) → O₁) → (Fin n₂ → O₂))
    (hf : ∀ (L : ℕ), ∀ a ∈ C, ∀ a' ∈ C, (∀ i j, a i j - a' i j ∈ I₁ ^ L) →
      ∀ j, f a j - f a' j ∈ I₂ ^ L) :
    ContinuousOn f C := by
  have := Fintype.ofFinite ι
  intro a ha s hs
  obtain ⟨t, ht, hat, hts⟩ := ((finite_coordinate_cylinder_basis O₂ I₂ h₂ n₂).mem_nhds_iff).1 hs
  rcases ht with rfl | ⟨L, x, rfl⟩
  · exact absurd hat (Set.notMem_empty _)
  have hU : {a' : ∀ i, Fin (d i) → O₁ | ∀ i j, a' i j - a i j ∈ I₁ ^ L} ∈ nhds a := by
    have : {a' : ∀ i, Fin (d i) → O₁ | ∀ i j, a' i j - a i j ∈ I₁ ^ L}
        = ⋂ i, (fun a' ↦ a' i) ⁻¹' {b : Fin (d i) → O₁ | ∀ j, b j - a i j ∈ I₁ ^ L} := by
      ext a'; simp
    refine IsOpen.mem_nhds ?_ (by simp)
    rw [this]
    exact isOpen_iInter_of_finite fun i ↦
      ((coordinate_cylinder_clopen O₁ I₁ h₁ L).1 (d i) (a i)).1.preimage (continuous_apply i)
  have hmem : {a' | ∀ i j, a' i j - a i j ∈ I₁ ^ L} ∩ C ∈ nhdsWithin a C :=
    Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hU) self_mem_nhdsWithin
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hmem fun a' ⟨h1, h2'⟩ ↦ hts ?_
  change adicCongr I₂ L (f a') x
  have hc : adicCongr I₂ L (f a') (f a) := by
    rw [finite_coordinate_adic_congruence]
    intro j
    have := (I₂ ^ L).neg_mem (hf L a ha a' h2' (fun i j ↦ by
      simpa using (Ideal.neg_mem_iff _).2 (h1 i j)) j)
    simpa using this
  exact (adic_congruence_rules O₂ (Fin n₂ → O₂) I₂).2.2.1 L _ _ _ hc hat

end SurfaceBlowup
