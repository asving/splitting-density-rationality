/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Measure.Haar

/-!
# Child members and terminal states of the blowup recursion

This file constructs the concrete child members attached to closed points of the exceptional
divisor of a blowup (via the `t`-chart and the point at infinity), assembles them into cell
child data, and shows that the tangent divisor of an ideal is unique, so tangent cells are
disjoint. It then treats terminal states `single a 1`: the curve order is a DVR whose generic
fibre is a field with field invariant `(a, 1)`. Finally it develops the terminating sets of a
surface universe: their cell decomposition, uniqueness of the factorization type, the law in
the terminal case, and the return-chain decomposition for single states.

## Main results

* `t_chart_point_child_member`, `direction_child_member_exists`, `cell_child_data_exists`.
* `tangent_divisor_unique`, `concrete_member_cells_disjoint`.
* `terminal_curve_order_dvr`, `terminal_field_invariant`, `concrete_member_terminal_type`.
* `terminates_cell_decomposition`, `terminates_type_unique`, `recursion_terminal_law`,
  `term_type_event_cell_decomposition`, `single_state_return_chain`, `universe_basic_facts`.

Provenance: `Thm_SurfaceBlowupV2_` nodes `t_chart_point_child_member`,
`direction_child_member_exists`, `cell_child_data_exists`, `tangent_divisor_unique`,
`concrete_member_cells_disjoint`, `terminal_curve_order_{local_principal,dvr}`,
`terminal_generic_fibre_field`, `terminal_field_invariant`, `concrete_member_terminal_type`,
`terminates_{cell_decomposition,type_unique}`, `recursion_terminal_step`,
`term_type_event_cell_decomposition`, `single_state_return_chain`, `universe_basic_facts`.
-/

open scoped BigOperators ENNReal TensorProduct

namespace SurfaceBlowup

/-! ### Child members at points of the exceptional divisor -/

/-- If `P = (T, Z - α)` is a maximal ideal with `α` zero or a unit, then `Z ∈ P` exactly when
`α = 0`. -/
private theorem mem_span_sub_iff_eq_zero {O A : Type} [CommRing O] [CommRing A] (f : O →+* A)
    (P : Ideal A) [P.IsMaximal] (T Z : A) (α : O) (hα : α = 0 ∨ IsUnit α)
    (hP : P = Ideal.span {T, Z - f α}) : Z ∈ P ↔ α = 0 := by
  refine ⟨fun hZP ↦ hα.resolve_right fun hunit ↦ ?_, fun h0 ↦ ?_⟩
  · have hsub : Z - f α ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
    exact Ideal.IsMaximal.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem P
      (by simpa using P.sub_mem hZP hsub) (hunit.map _))
  · rw [hP, h0]
    exact Ideal.subset_span (by simp)

/-- If `Φ` is an unramified lift of degree `≥ 2` and `Φ(Z)` lies in a maximal ideal `P`, then
`Z ∉ P`: the constant coefficient of `Φ` is a unit. -/
private theorem not_mem_of_eval₂_mem {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    (f : O →+* A) (P : Ideal A) [P.IsMaximal] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (h2 : 2 ≤ Φ.natDegree) (Z : A) (hmem : Φ.eval₂ f Z ∈ P) : Z ∉ P := by
  intro hZP
  have hc0 : IsUnit (Φ.coeff 0) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    have hX : Polynomial.X ∣ residuePoly O Φ := by
      rw [Polynomial.X_dvd_iff, residuePoly, Polynomial.coeff_map]; exact h0
    have hd := Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated
        (Polynomial.irreducible_X.associated_of_dvd hΦ.2 hX))
    rw [Polynomial.natDegree_X, residuePoly, hΦ.1.natDegree_map] at hd
    omega
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := Φ)
  rw [show Φ = Polynomial.C (Φ.coeff 0) + Polynomial.X * q by rw [← hq]; ring,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Ideal.add_mem_iff_left _ (P.mul_mem_right _ hZP)] at hmem
  exact Ideal.IsMaximal.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem P hmem (hc0.map _))

open scoped Classical in
/-- A closed point of degree `δ` on the exceptional line of the `t`-chart carries a concrete child
member: a concrete surface over a finite free `O`-algebra of rank `δ` (residue field of size
`q^δ`) in any prescribed compatible state, with measure-compatible coordinates and an
identification of its ring with the completed local ring at the point. -/
theorem t_chart_point_child_member (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (pi : O) (hpi : Irreducible pi)
    (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)))
    [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
      (surfaceT O pi u a b) ∈ P)
    (δ : ℕ) (hδ : 0 < δ)
    (hdeg : Module.length (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b)
      (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸ P) = (δ : ℕ∞))
    (s' : State)
    (hs' : StateShape (a + b) (if (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) ∈ P then b else 0) s') :
    ∃ mc : ConcreteMember,
    ∃ (_ : Algebra O mc.O) (_ : Module.Finite O mc.O) (_ : Module.Free O mc.O),
    Module.finrank O mc.O = δ ∧
    Nat.card (IsLocalRing.ResidueField mc.O) = Nat.card (IsLocalRing.ResidueField O) ^ δ ∧
    mc.pi = algebraMap O mc.O pi ∧ mc.a = a + b ∧
    mc.b = (if (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) ∈ P then b else 0) ∧
    mc.s = s' ∧
    (∃ pc : mc.O ≃ₗ[O] (Fin δ → O), Continuous pc ∧ Continuous pc.symm ∧ Measurable pc ∧
      Measurable pc.symm ∧
      MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map pc.symm
          (coefficientMeasure O δ))
      ∧ ∀ r : ℕ, coefficientMeasure mc.O r = MeasureTheory.Measure.pi
        (fun _ : Fin r => MeasureTheory.Measure.map pc.symm (coefficientMeasure O δ))) ∧
    ∃ Eq : CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) P ≃+* mc.R,
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) P) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) (surfaceT O pi u a b))) = mc.S.t ∧
    ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ∈ P →
      Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) P) (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))) = mc.S.x) ∧
    ∀ c : O,
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) P) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) (algebraMap O (ConcreteSurface O pi u a b) c))) =
      algebraMap O mc.R c := by
  rcases Nat.lt_or_ge δ 2 with hlt | h2
  · obtain rfl : δ = 1 := by omega
    obtain ⟨α, hα, hPspan, u', Eq, h1, h2, h3⟩ :=
      t_chart_rational_point_child_data O pi hpi u a b ha P hP (by exact_mod_cast hdeg)
    have hZiff : chartSlope _ (surfaceT O pi u a b) (surfaceX O pi u a b) ∈ P ↔ α = 0 :=
      mem_span_sub_iff_eq_zero ((chartBase _ (surfaceT O pi u a b) (surfaceX O pi u a b)).comp
        (algebraMap O _)) P _ _ α hα hPspan
    simp only [hZiff] at hs' ⊢
    obtain ⟨i1, i2, S, hSpi, hSt, hSx, hSa, hSb, ⟨atlas⟩⟩ :=
      concrete_member_data_exists O pi hpi u' (a + b) (if α = 0 then b else 0) (by omega) s' hs'
    have := coefficient_measure_probability O htop 1
    obtain ⟨-, hm2, hm3, hm4, hm5, hm6⟩ := coefficient_measure_pi_one O htop pi hpi 0
    refine ⟨⟨O, htop, pi, hpi, u', a + b, if α = 0 then b else 0, by omega, S, hSpi, hSt, hSx,
        hSa, hSb, s', hs', atlas⟩, Algebra.id O, Module.Finite.self O, Module.Free.self O,
        Module.finrank_self O, by simp, by simp, rfl, rfl, rfl,
        ⟨(LinearEquiv.funUnique (Fin 1) O O).symm, hm4, hm3, hm6, hm5, by simpa using hm2,
          fun r ↦ by simpa using (coefficient_measure_pi_one O htop pi hpi r).1⟩,
        Eq, by simpa [hSt] using h1, fun hZP ↦ ?_, fun c ↦ by simpa using h3 c⟩
    simpa [hSx, hZP] using h2
  · obtain ⟨Φ, hΦ, rfl, hPspan, hθ, Eq, h1, h3⟩ :=
      t_chart_nonrational_point_child_data O pi hpi u a b ha P hP δ hdeg h2
    have hZ : chartSlope _ (surfaceT O pi u a b) (surfaceX O pi u a b) ∉ P :=
      not_mem_of_eval₂_mem ((chartBase _ (surfaceT O pi u a b) (surfaceX O pi u a b)).comp
        (algebraMap O _)) P Φ hΦ h2 _ (by rw [hPspan]; exact Ideal.subset_span (by simp))
    simp only [hZ, if_false] at hs' ⊢
    let τ : TopologicalSpace (AdjoinRoot Φ) := unramifiedTopology O Φ hΦ.1
    let μ : MeasurableSpace (AdjoinRoot Φ) := unramifiedMeasurableSpace O Φ hΦ.1
    obtain ⟨i1, i2, hchar, hdvr, hcomp, hfin, hcard, htr, hcpt, ht2, hsc, hbor, htop'⟩ :=
      unramified_extension_measure_package O htop Φ hΦ rfl rfl
    have hpi' : Irreducible (algebraMap O (AdjoinRoot Φ) pi) :=
      (unramified_is_dvr O Φ hΦ).2.2.2.2.1 pi hpi
    obtain ⟨hfree, hfinite, hrank⟩ := unramified_free_module O Φ hΦ.1
    obtain ⟨-, -, -, -, -, hc1, hc2, hc3, hc4⟩ := power_coordinates_transport O Φ hΦ.1 rfl rfl
    obtain ⟨-, hprob, -⟩ := unramified_coefficient_measure_haar O Φ hΦ.1 rfl rfl htop
    obtain ⟨j1, j2, S, hSpi, hSt, hSx, hSa, hSb, ⟨atlas⟩⟩ :=
      concrete_member_data_exists (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) hpi'
        (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
          (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) *
          shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0 (by omega) s' hs'
    refine ⟨⟨AdjoinRoot Φ, htop', _, hpi', _, a + b, 0, by omega, S, hSpi, hSt, hSx, hSa, hSb, s',
        hs', atlas⟩, inferInstance, hfinite, hfree, hrank, hcard, rfl, rfl, rfl, rfl,
        ⟨powerCoordinates O Φ hΦ.1, hc1, hc2, hc3, hc4, hprob, fun r ↦
          (unramified_coefficient_measure_pi O htop Φ hΦ rfl rfl r).1⟩, Eq,
        by simpa [hSt] using h1, fun hZP ↦ hZP.elim, fun c ↦ ?_⟩
    rw [h3 c]
    exact (IsScalarTower.algebraMap_apply O (AdjoinRoot Φ) _ c).symm

/-- The child state at the point at infinity has the shape of the infinity chart. -/
private theorem infinity_child_state_shape (m : ConcreteMember)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField m.R)) (d : ℕ) (hQ : 0 < Dv none)
    (hb : d < stateContactT m.s) :
    StateShape (m.a + m.b) m.a (pointChildState (IsLocalRing.ResidueField m.R) m.s d Dv none) := by
  have hsh := m.shape
  generalize m.s = s at hsh hb ⊢
  cases s with
  | single a c =>
    obtain ⟨h1, h2, h3⟩ := hsh
    simp only [pointChildState, infinityDirection, if_true, StateShape, stateContactT] at hb ⊢
    subst h1
    exact ⟨by omega, rfl, m.ha, hQ, by omega⟩
  | crossing a b c h =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hsh
    simp only [pointChildState, infinityDirection, if_true, StateShape, stateContactT] at hb ⊢
    subst h1 h2
    exact ⟨rfl, rfl, m.ha, hQ, by omega⟩

/-- `direction_child_member_exists` with the chart coordinates `t`, `x` given up to equality. -/
private theorem direction_child_member_of_eq (m : ConcreteMember) (t x : m.R)
    (ht : t = surfaceT m.O m.pi m.u m.a m.b) (hx : x = surfaceX m.O m.pi m.u m.a m.b)
    (e : (BlowupChart m.R t x ⧸ chartExceptional m.R t x) ≃+* Polynomial
        (IsLocalRing.ResidueField m.R))
    (hdp : ∀ φ : AffineDirection (IsLocalRing.ResidueField m.R),
      (directionPoint m.R t x e φ).IsMaximal ∧ chartBase m.R t x t ∈ directionPoint m.R t x e φ ∧
      (chartSlope m.R t x ∈ directionPoint m.R t x e φ ↔ φ = zeroAffine
          (IsLocalRing.ResidueField m.R)) ∧
      Module.length m.R (BlowupChart m.R t x ⧸ directionPoint m.R t x e φ) = (φ.val.natDegree : ℕ∞))
    (hinf : (infinityPoint m.R t x).IsPrime)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField m.R)) (d : ℕ) (Q : divisorSupport Dv)
    (hb : Q.val = infinityDirection (IsLocalRing.ResidueField m.R) → d < stateContactT m.s)
    (hz : Q.val = zeroDirection (IsLocalRing.ResidueField m.R) →
      ∀ h : ℕ, stateContactX m.s = some h → d < h) :
    ∃ cm : ChildMember m (directionDegree (IsLocalRing.ResidueField m.R) Q.val)
        (pointChildState (IsLocalRing.ResidueField m.R) m.s d Dv Q.val),
    ∃ Eq : divisorLocalRing m.R t x e Dv hinf Q ≃+* cm.mc.R,
    Eq (divisorException m.R t x e Dv hinf Q) = cm.mc.S.t ∧
    ((Q.val = infinityDirection (IsLocalRing.ResidueField m.R) ∨ Q.val = zeroDirection
        (IsLocalRing.ResidueField m.R)) → Eq (divisorBoundary m.R t x e Dv hinf Q) = cm.mc.S.x) ∧
    ∀ r : m.O,
    Eq (divisorFromSurface m.R t x e Dv hinf Q (algebraMap m.O m.R r)) = algebraMap cm.mc.O cm.mc.R
        (algebraMap m.O cm.mc.O r) := by
  classical
  subst ht hx
  obtain ⟨Q, hQ⟩ := Q
  cases Q with
  | none =>
    have key := infinity_child_state_shape m Dv d hQ (hb rfl)
    obtain ⟨mc, alg, fin, free, hrank, hcard, hpi, -, -, hs, ⟨pc, c1, c2, c3, c4, -, hmeas⟩,
      Eq, h1, h2, h3⟩ := infinity_point_child_member m.O m.htop m.pi m.hpi m.u m.a m.b m.ha
        (hinf := hinf) _ key
    refine ⟨@ChildMember.mk m _ _ mc alg fin free hrank hcard hpi hs pc ⟨c1, c2, c3, c4⟩ hmeas,
      Eq, h1, fun _ => h2, fun r => ?_⟩
    exact (h3 r).trans (IsScalarTower.algebraMap_apply m.O mc.O mc.R r)
  | some φ =>
    obtain ⟨hmax, htP, hZ, hlen⟩ := hdp φ
    have hδ : 0 < φ.val.natDegree := Irreducible.natDegree_pos φ.property.2
    have key : StateShape (m.a + m.b)
        (if chartSlope m.R (surfaceT m.O m.pi m.u m.a m.b) (surfaceX m.O m.pi m.u m.a m.b) ∈
          directionPoint m.R (surfaceT m.O m.pi m.u m.a m.b) (surfaceX m.O m.pi m.u m.a m.b) e φ
          then m.b else 0)
        (pointChildState (IsLocalRing.ResidueField m.R) m.s d Dv (some φ)) := by
      have hsh := m.shape
      have hz' := hz
      simp only at hz'
      have hinfne : (some φ : ClosedDirection (IsLocalRing.ResidueField m.R)) ≠
          infinityDirection (IsLocalRing.ResidueField m.R) := by simp [infinityDirection]
      have hzero : (some φ : ClosedDirection (IsLocalRing.ResidueField m.R)) =
          zeroDirection (IsLocalRing.ResidueField m.R) ↔ φ = zeroAffine
              (IsLocalRing.ResidueField m.R) := by
        simp [zeroDirection, zeroAffine]
      rw [← hzero] at hZ
      simp only [hZ]
      generalize m.s = s at hsh hz' ⊢
      cases s with
      | single a c =>
        obtain ⟨h1, h2, h3⟩ := hsh
        subst h1
        simp only [pointChildState, hinfne, if_false, StateShape, h2]
        split_ifs <;> exact ⟨by omega, rfl, hQ⟩
      | crossing a b c h =>
        obtain ⟨h1, h2, h3, h4, h5⟩ := hsh
        subst h1 h2
        simp only [pointChildState, hinfne, if_false]
        by_cases hq : (some φ : ClosedDirection (IsLocalRing.ResidueField m.R)) =
          zeroDirection (IsLocalRing.ResidueField m.R)
        · have := hz' hq h rfl
          simp only [hq, if_true, StateShape]
          rw [← hq]
          refine ⟨?_, ?_, h3, hQ, by omega⟩ <;> simp
        · simp only [hq, if_false, StateShape]
          refine ⟨?_, ?_, hQ⟩ <;> simp
    obtain ⟨mc, alg, fin, free, hrank, hcard, hpi, -, -, hs, ⟨pc, c1, c2, c3, c4, -, hmeas⟩,
      Eq, h1, h2, h3⟩ := t_chart_point_child_member m.O m.htop m.pi m.hpi m.u m.a m.b m.ha
        _ htP _ hδ hlen _ key
    refine ⟨@ChildMember.mk m _ _ mc alg fin free hrank hcard hpi hs pc ⟨c1, c2, c3, c4⟩ hmeas,
      Eq, h1, fun hq => h2 ?_, fun r => ?_⟩
    · rw [hZ]
      rcases hq with hq | hq
      · simp [infinityDirection] at hq
      · simpa [zeroDirection, zeroAffine] using hq
    · exact (h3 r).trans (IsScalarTower.algebraMap_apply m.O mc.O mc.R r)

/-- Every support point `Q` of an exceptional divisor (with the boundary contact conditions)
carries a child member of degree `deg Q` in the state `pointChildState`, whose ring is
identified with the local ring at `Q` compatibly with the exceptional and boundary parameters. -/
theorem direction_child_member_exists (m : ConcreteMember)
    (e : (BlowupChart m.R m.S.t m.S.x ⧸ chartExceptional m.R m.S.t m.S.x) ≃+* Polynomial
        (IsLocalRing.ResidueField m.R))
    (he : ∀ r : m.R, e (Ideal.Quotient.mk (chartExceptional m.R m.S.t m.S.x)
        (chartBase m.R m.S.t m.S.x r)) = Polynomial.C (IsLocalRing.residue m.R r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional m.R m.S.t m.S.x) (chartSlope m.R m.S.t m.S.x)) =
        Polynomial.X)
    (hinf : (infinityPoint m.R m.S.t m.S.x).IsPrime)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField m.R)) (d : ℕ) (Q : divisorSupport Dv)
    (hb : Q.val = infinityDirection (IsLocalRing.ResidueField m.R) → d < stateContactT m.s)
    (hz : Q.val = zeroDirection (IsLocalRing.ResidueField m.R) →
      ∀ h : ℕ, stateContactX m.s = some h → d < h) :
    ∃ cm : ChildMember m (directionDegree (IsLocalRing.ResidueField m.R) Q.val)
        (pointChildState (IsLocalRing.ResidueField m.R) m.s d Dv Q.val),
    ∃ Eq : divisorLocalRing m.R m.S.t m.S.x e Dv hinf Q ≃+* cm.mc.R,
    Eq (divisorException m.R m.S.t m.S.x e Dv hinf Q) = cm.mc.S.t ∧
    ((Q.val = infinityDirection (IsLocalRing.ResidueField m.R) ∨ Q.val = zeroDirection
        (IsLocalRing.ResidueField m.R)) → Eq (divisorBoundary m.R m.S.t m.S.x e Dv hinf Q) =
        cm.mc.S.x) ∧
    ∀ r : m.O,
    Eq (divisorFromSurface m.R m.S.t m.S.x e Dv hinf Q (algebraMap m.O m.R r)) = algebraMap cm.mc.O
        cm.mc.R (algebraMap m.O cm.mc.O r) := by
  refine direction_child_member_of_eq m m.S.t m.S.x m.hS_t m.hS_x e (fun φ => ?_) hinf Dv d Q hb hz
  obtain ⟨h1, h2, h3, -, h5, -⟩ :=
    direction_point_maximal m.O m.R m.S e he heZ φ
  exact ⟨h1, h2, h3, h5⟩

private theorem pattern_d_lt_contactT (s : State) (P : TangentPattern s.degree) (hP : Allowed s P)
    (hrt : 0 < P.rt.val) : P.d.val < stateContactT s := by
  cases s <;> simp only [Allowed, stateContactT] at * <;> tauto

private theorem pattern_d_lt_contactX (k : Type) [Field k] (s : State) (P : TangentPattern s.degree)
    (hP : Allowed s P)
    (Dv : ExceptionalDivisor k) (hDv : HasPattern k s Dv P) (hpos : 0 < Dv (zeroDirection k))
    (h : ℕ) (hh : stateContactX s = some h) : P.d.val < h := by
  cases s with
  | single a c => simp [stateContactX] at hh
  | crossing a b c h' =>
    simp only [stateContactX, Option.some.injEq] at hh
    subst hh
    simp only [Allowed, HasPattern] at hP hDv
    rw [hDv.2.2.1] at hpos
    exact hP.2.2.2.2.2.1 hpos

/-- Every tangent cell of a concrete member admits cell child data: an assignment of children to
divisor points together with the corresponding child members and identifications. -/
theorem cell_child_data_exists (m : ConcreteMember) (c : m.cellIndex) :
    Nonempty (CellChildData m c) := by
  obtain ⟨e, he, heZ⟩ := exceptional_line_equiv_residue_field m.O m.R m.S
  have hinf : (infinityPoint m.R m.S.t m.S.x).IsPrime :=
    (infinity_point_maximal m.O m.R m.S).1.isPrime
  have : Finite (IsLocalRing.ResidueField m.R) := Finite.of_equiv _ m.S.residueEquiv.toEquiv
  let asg : CellAssignment (IsLocalRing.ResidueField m.R) m.s c.1.1 c.2.1 :=
    Classical.choice (cell_assignment_exists _ m.s (m.shape.valid m.ha) c.1.1 c.1.2 c.2.1 c.2.2)
  have key : ∀ j : m.toMeasured.childIdx c,
      ∃ cm : ChildMember m (m.toMeasured.childDelta c j) (m.toMeasured.childState c j),
      ∃ Eq : divisorLocalRing m.R m.S.t m.S.x e c.2.1 hinf (asg.point j) ≃+* cm.mc.R,
        Eq (divisorException m.R m.S.t m.S.x e c.2.1 hinf (asg.point j)) = cm.mc.S.t ∧
        ((asg.pt j = infinityDirection (IsLocalRing.ResidueField m.R) ∨
          asg.pt j = zeroDirection (IsLocalRing.ResidueField m.R)) →
          Eq (divisorBoundary m.R m.S.t m.S.x e c.2.1 hinf (asg.point j)) = cm.mc.S.x) ∧
        ∀ r : m.O, Eq (divisorFromSurface m.R m.S.t m.S.x e c.2.1 hinf (asg.point j)
          (algebraMap m.O m.R r)) = algebraMap cm.mc.O cm.mc.R (algebraMap m.O cm.mc.O r) := by
    intro j
    have hP := c.1.2
    have hDv := c.2.2
    have hpos : 0 < c.2.1 (asg.pt j) := (asg.supp _).mpr ⟨j, rfl⟩
    have hb : (asg.point j).val = infinityDirection (IsLocalRing.ResidueField m.R) →
        c.1.1.d.val < stateContactT m.s := by
      intro hQ
      have hQ' : asg.pt j = infinityDirection _ := hQ
      rw [hQ'] at hpos
      exact pattern_d_lt_contactT m.s c.1.1 hP (hDv.2.1 ▸ hpos)
    have hz : (asg.point j).val = zeroDirection (IsLocalRing.ResidueField m.R) →
        ∀ h : ℕ, stateContactX m.s = some h → c.1.1.d.val < h := by
      intro hQ h hh
      have hQ' : asg.pt j = zeroDirection _ := hQ
      rw [hQ'] at hpos
      exact pattern_d_lt_contactX _ m.s c.1.1 hP c.2.1 hDv hpos h hh
    have := direction_child_member_exists m e he heZ hinf c.2.1 c.1.1.d.val (asg.point j) hb hz
    have h1 : m.toMeasured.childDelta c j = directionDegree _ (asg.point j).val := (asg.deg j).symm
    have h2 : m.toMeasured.childState c j = pointChildState _ m.s c.1.1.d.val c.2.1
        (asg.point j).val :=
      asg.state j
    rwa [h1, h2]
  choose child Eq hEq_e hEq_b hEq_c using key
  exact ⟨⟨e, he, heZ, hinf, asg, child, Eq, hEq_e, hEq_b, hEq_c⟩⟩

/-! ### Uniqueness of the tangent divisor -/

/-- The tangent order `d` and the tangent divisor `Dv` of an ideal on a regular surface are
uniquely determined. -/
theorem tangent_divisor_unique (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R] (S : SurfaceData O R)
    (hreg : RegularParameterPair R S.t S.x) (J : Ideal R) (d d' : ℕ)
    (Dv Dv' : ExceptionalDivisor (IsLocalRing.ResidueField R)) (h : HasTangentDivisor O R S J d Dv)
    (h' : HasTangentDivisor O R S J d' Dv') :
    d = d' ∧ Dv = Dv' := by
  set m := IsLocalRing.maximalIdeal R with hm
  have hM := has_tangent_divisor_multiplicity O R S hreg J d Dv h
  have hM' := has_tangent_divisor_multiplicity O R S hreg J d' Dv' h'
  have hdd : d = d' := by
    rcases lt_trichotomy d d' with hlt | heq | hgt
    · exact absurd (hM'.1.trans (Ideal.pow_le_pow_right hlt)) hM.2
    · exact heq
    · exact absurd (hM.1.trans (Ideal.pow_le_pow_right hgt)) hM'.2
  subst hdd
  refine ⟨rfl, ?_⟩
  obtain ⟨f, H, hJ, ⟨hH0, hHd, hHnone, hHfac⟩, hf⟩ := h
  obtain ⟨f', H', hJ', ⟨hH0', hHd', hHnone', hHfac'⟩, hf'⟩ := h'
  have hass : Associated f f' := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← hJ, ← hJ']
  obtain ⟨u, hu⟩ := hass
  have hfm : f ∈ m ^ d := hM.1 (hJ ▸ Ideal.subset_span rfl)
  have hsurj : Function.Surjective (IsLocalRing.residue R) := Ideal.Quotient.mk_surjective
  have hrr : ∀ c, IsLocalRing.residue R (residueRepresentative R c) = c := fun c =>
    Function.invFun_eq (hsurj c)
  set ub := IsLocalRing.residue R (u : R) with hub
  set w := residueRepresentative R ub with hw
  have huw : (u : R) - w ∈ m := by
    rw [hm, ← IsLocalRing.ker_residue, RingHom.mem_ker, map_sub, hw, hrr, sub_self]
  have hdiff : tangentLift O R S d H' - w * tangentLift O R S d H ∈ m ^ (d+1) := by
    have e : tangentLift O R S d H' - w * tangentLift O R S d H =
      -(f' - tangentLift O R S d H') + f * ((u : R) - w) + w * (f - tangentLift O R S d H) := by
      rw [← hu]; ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.add_mem _ (neg_mem hf') ?_) (Ideal.mul_mem_left _ _ hf)
    rw [pow_succ]
    exact Ideal.mul_mem_mul hfm huw
  have : (Ideal.span ({S.t, S.x} : Set R)).IsMaximal := by
    rw [S.parameters]; exact IsLocalRing.maximalIdeal.isMaximal R
  have hcoef : ∀ i : Fin (d+1),
      residueRepresentative R (H'.coeff i.val) - w * residueRepresentative R (H.coeff i.val) ∈
        m := by
    by_contra! hcon
    obtain ⟨i₀, hi₀⟩ := hcon
    rw [hm, ← S.parameters] at hi₀
    refine homogeneous_form_not_mem_pow_succ R S.t S.x hreg d (fun i ↦ residueRepresentative R
      (H'.coeff i.val) - w * residueRepresentative R (H.coeff i.val)) i₀ hi₀ ?_
    rw [S.parameters]
    convert hdiff using 1
    unfold tangentLift
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hub0 : ub ≠ 0 := by
    rw [hub]; exact (u.isUnit.map (IsLocalRing.residue R)).ne_zero
  have hHH : H' = Polynomial.C ub * H := by
    ext n
    rw [Polynomial.coeff_C_mul]
    by_cases hn : n ≤ d
    · have := hcoef ⟨n, Nat.lt_succ_of_le hn⟩
      rwa [hm, ← IsLocalRing.ker_residue, RingHom.mem_ker, map_sub, map_mul, hrr, hrr, hrr,
        sub_eq_zero] at this
    · push Not at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hHd hn),
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hHd' hn), mul_zero]
  have hdeg : H'.natDegree = H.natDegree := by
    rw [hHH, Polynomial.natDegree_C_mul hub0]
  obtain ⟨hA, hcnt⟩ := divisor_affine_polynomial_normalized_factors _ Dv
  obtain ⟨hA', hcnt'⟩ := divisor_affine_polynomial_normalized_factors _ Dv'
  have hAA : divisorAffinePolynomial _ Dv' = divisorAffinePolynomial _ Dv := by
    have e : Polynomial.C H'.leadingCoeff * divisorAffinePolynomial _ Dv' =
        Polynomial.C (ub * H.leadingCoeff) * divisorAffinePolynomial _ Dv := by
      rw [← hHfac', hHH, map_mul, mul_assoc, ← hHfac]
    have hl := congrArg Polynomial.leadingCoeff e
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_C, hA.leadingCoeff, hA'.leadingCoeff, mul_one, mul_one] at hl
    rw [hl] at e
    refine mul_left_cancel₀ ?_ e
    rw [Ne, Polynomial.C_eq_zero, ← hl]
    exact Polynomial.leadingCoeff_ne_zero.mpr hH0'
  ext P
  cases P with
  | none => rw [hHnone, hHnone', hdeg]
  | some φ => rw [← hcnt, ← hcnt', hAA]

/-- The tangent cells of a concrete member are pairwise disjoint. -/
theorem concrete_member_cells_disjoint (m : ConcreteMember) :
    Pairwise fun c c' : m.toMeasured.cellIndex => Disjoint (m.toMeasured.cell c)
        (m.toMeasured.cell c') := by
  intro c c' hne
  rw [Set.disjoint_left]
  intro J h1 h2
  have hreg : RegularParameterPair m.R m.S.t m.S.x := by
    rw [m.hS_t, m.hS_x]
    exact concrete_surface_regular_pair_tx m.O m.pi m.hpi.ne_zero m.u m.a m.b m.ha
  obtain ⟨hd, hD⟩ := tangent_divisor_unique m.O m.R m.S hreg J _ _ _ _ h1.2 h2.2
  have hP : c.1.1 = c'.1.1 := by
    refine allowed_pattern_of_divisor_unique _ m.s c.2.1 c.1.1 c'.1.1 c.1.2 c'.1.2 c.2.2 ?_
    rw [hD]; exact c'.2.2
  apply hne
  obtain ⟨⟨P, hPa⟩, ⟨D, hDp⟩⟩ := c
  obtain ⟨⟨P', hPa'⟩, ⟨D', hDp'⟩⟩ := c'
  simp only at hP hD
  subst hP
  subst hD
  rfl

/-! ### Terminal states -/

/-- For `J = (f)` in the terminal state `single a 1`: `(f, t)` is the maximal ideal, and `R/J` is a
Noetherian local ring with principal maximal ideal `(t)`, finite free of rank `a` over `O`. -/
private theorem terminal_curve_order_local_principal (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hSpi : S.pi = pi)
    (hSt : S.t = (surfaceT O pi u a b)) (hSx : S.x = (surfaceX O pi u a b)) (hSa : S.a = a)
    (hSb : S.b = b) (J : Ideal (ConcreteSurface O pi u a b))
    (hJ : J ∈ surfaceStateSet O (ConcreteSurface O pi u a b) S (State.single a 1))
    (f : (ConcreteSurface O pi u a b)) (hf : J = Ideal.span {f}) :
    Ideal.span {f} ⊔ Ideal.span {(surfaceT O pi u a b)} = IsLocalRing.maximalIdeal
        (ConcreteSurface O pi u a b) ∧
    (∃ _ : IsLocalRing ((ConcreteSurface O pi u a b) ⧸ J), IsLocalRing.maximalIdeal
        ((ConcreteSurface O pi u a b) ⧸ J) = Ideal.span {(Ideal.Quotient.mk J
        (surfaceT O pi u a b))}) ∧
    IsNoetherianRing ((ConcreteSurface O pi u a b) ⧸ J) ∧
    Module.Free O ((ConcreteSurface O pi u a b) ⧸ J) ∧
    Module.Finite O ((ConcreteSurface O pi u a b) ⧸ J) ∧
    Module.finrank O ((ConcreteSurface O pi u a b) ⧸ J) = a := by
  have hJne := surface_state_ideal_proper O _ S _ J hJ
  obtain ⟨-, -, -, hb0, hc⟩ := hJ
  have hb : b = 0 := hSb ▸ hb0
  subst hb
  unfold idealContact at hc
  rw [hSt, hf] at hc
  have hmax : Ideal.span {f} ⊔ Ideal.span {surfaceT O pi u a 0} =
      IsLocalRing.maximalIdeal (ConcreteSurface O pi u a 0) := by
    have h1 : Module.length (ConcreteSurface O pi u a 0)
        (ConcreteSurface O pi u a 0 ⧸ (Ideal.span {f} ⊔ Ideal.span {surfaceT O pi u a 0})) = 1 := by
      exact_mod_cast hc
    rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom] at h1
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_def.mpr h1)
  subst hf
  have : Nontrivial (ConcreteSurface O pi u a 0 ⧸ Ideal.span {f}) :=
    Ideal.Quotient.nontrivial_iff.mpr hJne
  have : IsLocalRing (ConcreteSurface O pi u a 0 ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have := concrete_surface_isNoetherianRing O pi u a 0
  obtain ⟨e, he⟩ := concrete_surface_special_fiber_equiv O pi hpi u a 0
  have hcon := (concrete_surface_contact_eq_special_fiber_contact O pi u a 0 ha e he f).1
  have hcontact : contact (e (Ideal.Quotient.mk (Ideal.span
      {algebraMap O (ConcreteSurface O pi u a 0) pi}) f)) (fiberT (IsLocalRing.ResidueField O) a 0)
      = (1 : ℕ) := by
    rw [← hcon]; exact_mod_cast hc
  obtain ⟨h1, h2, h3⟩ := concrete_surface_single_curve_free O pi hpi u a ha f e 1 one_pos hcontact
  refine ⟨hmax, ⟨inferInstance, ?_⟩, inferInstance, h1, h2, by simpa using h3⟩
  have hle : Ideal.span {f} ≤ IsLocalRing.maximalIdeal (ConcreteSurface O pi u a 0) :=
    hmax ▸ le_sup_left
  have hm : (IsLocalRing.maximalIdeal (ConcreteSurface O pi u a 0)).map
      (Ideal.Quotient.mk (Ideal.span {f})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) (surfaceT O pi u a 0)} := by
    rw [← hmax, Ideal.map_sup, Ideal.map_span, Ideal.map_span]
    simp
  rw [← hm]
  have hM := Ideal.IsMaximal.map_of_surjective_of_ker_le (f := Ideal.Quotient.mk (Ideal.span {f}))
    (m := IsLocalRing.maximalIdeal _) Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  exact (@IsLocalRing.eq_maximalIdeal (ConcreteSurface O pi u a 0 ⧸ Ideal.span {f}) _ _ _ hM).symm

private theorem isDVR_of_maximalIdeal_eq_span (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] [IsNoetherianRing B] [Module.Free O B]
    (pi : O) (hpi : Irreducible pi) (a : ℕ) (ha : 0 < a) (tb w : B) (hunit : IsUnit w)
    (hvert : algebraMap O B pi = w * tb ^ a)
    (hm : IsLocalRing.maximalIdeal B = Ideal.span {tb}) :
    ∃ _ : IsDomain B, IsDiscreteValuationRing B ∧ Irreducible tb ∧
      Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) =
        (IsLocalRing.maximalIdeal B) ^ a := by
  classical
  have hinj : Function.Injective (algebraMap O B) := FaithfulSMul.algebraMap_injective O B
  have hnil : ∀ N : ℕ, tb ^ N ≠ 0 := by
    intro N hN
    have h1 : algebraMap O B (pi ^ N) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
      rw [map_pow, hvert, mul_pow, ← pow_mul, hk, add_mul, one_mul, pow_add, hN, mul_zero, mul_zero]
    have h2 : pi ^ N ≠ 0 := pow_ne_zero _ hpi.ne_zero
    exact h2 (hinj (h1.trans (map_zero _).symm))
  have hmpow : ∀ n : ℕ, IsLocalRing.maximalIdeal B ^ n = Ideal.span {tb ^ n} := by
    intro n; rw [hm, Ideal.span_singleton_pow]
  have hmne : IsLocalRing.maximalIdeal B ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  have hfac : ∀ x : B, x ≠ 0 → ∃ (n : ℕ) (v : B), IsUnit v ∧ x = v * tb ^ n := by
    intro x hx
    have hK := iInf_sup_pow_eq_of_isLocalRing B (IsLocalRing.maximalIdeal B) ⊥ hmne
    have hex : ∃ N, x ∉ Ideal.span {tb ^ N} := by
      by_contra hcon
      push Not at hcon
      apply hx
      have : x ∈ (⨅ n : ℕ, (⊥ : Ideal B) ⊔ IsLocalRing.maximalIdeal B ^ n) := by
        rw [Ideal.mem_iInf]; intro n; rw [bot_sup_eq, hmpow]; exact hcon n
      rw [hK] at this; exact (Submodule.mem_bot _).mp this
    set N := Nat.find hex with hN
    have hNs : x ∉ Ideal.span {tb ^ N} := Nat.find_spec hex
    have hNpos : N ≠ 0 := by
      intro h0; apply hNs; rw [h0, pow_zero, Ideal.span_singleton_one]; trivial
    obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hmem : x ∈ Ideal.span {tb ^ n} := by simpa using Nat.find_min hex (by omega : n < N)
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨n, v, ?_, hv.symm⟩
    by_contra hvu
    have hvm : v ∈ IsLocalRing.maximalIdeal B := hvu
    rw [hm] at hvm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hvm
    apply hNs
    rw [hn, Ideal.mem_span_singleton']
    exact ⟨w, by rw [← hv, ← hw, pow_succ]; ring⟩
  have hdom : IsDomain B := by
    have : NoZeroDivisors B := by
      constructor
      intro x y hxy
      by_contra hne
      push Not at hne
      obtain ⟨n, v, hv, rfl⟩ := hfac x hne.1
      obtain ⟨n', v', hv', rfl⟩ := hfac y hne.2
      have : (v * v') * tb ^ (n + n') = 0 := by rw [← hxy, pow_add]; ring
      exact hnil (n + n') ((hv.mul hv').mul_right_eq_zero.mp this)
    exact NoZeroDivisors.to_isDomain B
  have hnf : ¬ IsField B := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm]
    intro h
    exact hnil 1 (by rw [pow_one]; exact Ideal.span_singleton_eq_bot.mp h)
  have hp : (IsLocalRing.maximalIdeal B).IsPrincipal := ⟨⟨tb, hm⟩⟩
  have hdvr : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnf).out 0 4).mpr hp
  refine ⟨hdom, hdvr, ?_, ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer tb).mpr hm
  · rw [hpi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hvert,
      Ideal.span_singleton_mul_left_unit hunit, hmpow]

/-- In the terminal state `single a 1`, the curve order `R/J` is a DVR with uniformizer `t`, and
the maximal ideal of `O` extends to the `a`-th power of its maximal ideal. -/
theorem terminal_curve_order_dvr (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    [IsDomain (ConcreteSurface O pi u a b)] [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hSpi : S.pi = pi)
    (hSt : S.t = (surfaceT O pi u a b)) (hSx : S.x = (surfaceX O pi u a b)) (hSa : S.a = a)
    (hSb : S.b = b) (J : Ideal (ConcreteSurface O pi u a b))
    (hJ : J ∈ surfaceStateSet O (ConcreteSurface O pi u a b) S (State.single a 1))
    (f : (ConcreteSurface O pi u a b)) (hf : J = Ideal.span {f}) :
    ∃ (_ : IsDomain ((ConcreteSurface O pi u a b) ⧸ J)) (_ : IsLocalRing
        ((ConcreteSurface O pi u a b) ⧸ J)),
    IsDiscreteValuationRing ((ConcreteSurface O pi u a b) ⧸ J) ∧
    Irreducible (Ideal.Quotient.mk J (surfaceT O pi u a b)) ∧
    Ideal.map (algebraMap O ((ConcreteSurface O pi u a b) ⧸ J) : O →+*
        ((ConcreteSurface O pi u a b) ⧸ J)) (IsLocalRing.maximalIdeal O) =
        (IsLocalRing.maximalIdeal ((ConcreteSurface O pi u a b) ⧸ J))^a := by
  obtain ⟨-, ⟨hloc, hm⟩, hnoeth, hfree, hfin, hrank⟩ :=
    terminal_curve_order_local_principal O pi hpi u a b ha S hSpi hSt hSx hSa hSb J hJ f hf
  obtain rfl : b = 0 := hSb ▸ hJ.2.2.2.1
  have hvert : (algebraMap O ((ConcreteSurface O pi u a 0) ⧸ J) : O →+*
      ((ConcreteSurface O pi u a 0) ⧸ J)) pi =
      Ideal.Quotient.mk J (surfaceUnit O pi u a 0 : ConcreteSurface O pi u a 0) *
        (Ideal.Quotient.mk J (surfaceT O pi u a 0)) ^ a := by
    rw [← Ideal.Quotient.mk_algebraMap, concrete_surface_vertical]
    simp [map_mul, map_pow]
  obtain ⟨hdom, hdvr, hirr, hmap⟩ := isDVR_of_maximalIdeal_eq_span O
      ((ConcreteSurface O pi u a 0) ⧸ J) pi hpi a ha
    _ _ ((Units.isUnit _).map _) hvert hm
  exact ⟨hdom, hloc, hdvr, hirr, hmap⟩

/-- In the terminal state, the generic fibre `K ⊗[O] B` of (an algebra `B` isomorphic to) the
curve order is a finite field extension of `K` in which `B` embeds as the integral closure. -/
private theorem terminal_generic_fibre_field (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hSpi : S.pi = pi)
    (hSt : S.t = (surfaceT O pi u a b)) (hSx : S.x = (surfaceX O pi u a b)) (hSa : S.a = a)
    (hSb : S.b = b) (J : Ideal (ConcreteSurface O pi u a b))
    (hJ : J ∈ surfaceStateSet O (ConcreteSurface O pi u a b) S (State.single a 1))
    (f : (ConcreteSurface O pi u a b)) (hf : J = Ideal.span {f}) (B : Type) [CommRing B]
    [Algebra O B] (eB : B ≃ₐ[O] ((ConcreteSurface O pi u a b) ⧸ J)) :
    IsField (TensorProduct O (BaseField O) B) ∧
    Module.Finite (BaseField O) (TensorProduct O (BaseField O) B) ∧
    Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[O]
        (TensorProduct O (BaseField O) B)) ∧
    integralClosure O (TensorProduct O (BaseField O) B) =
        (Algebra.TensorProduct.includeRight : B →ₐ[O] (TensorProduct O (BaseField O) B)).range := by
  obtain ⟨-, -, -, hfree, hfin, -⟩ := terminal_curve_order_local_principal O pi hpi u a b ha S
    hSpi hSt hSx hSa hSb J hJ f hf
  obtain ⟨hdomA, -, hdvr, -, -⟩ := terminal_curve_order_dvr O pi hpi u a b ha S
    hSpi hSt hSx hSa hSb J hJ f hf
  set A := (ConcreteSurface O pi u a b) ⧸ J
  have : IsDomain B := Function.Injective.isDomain eB.toRingHom eB.injective
  have : IsIntegrallyClosed A := inferInstance
  have : IsIntegrallyClosed B := @IsIntegrallyClosed.of_equiv A B _ _
      (eB.symm.toRingEquiv : A ≃+* B) _
  have : Module.Free O B := Module.Free.of_equiv eB.symm.toLinearEquiv
  have : Module.Finite O B := Module.Finite.equiv eB.symm.toLinearEquiv
  set K := BaseField O
  set L := TensorProduct O K B
  let _ : Algebra B L := Algebra.TensorProduct.rightAlgebra
  have hinjO : Function.Injective (algebraMap O B) := FaithfulSMul.algebraMap_injective O B
  set Mo := Algebra.algebraMapSubmonoid B (nonZeroDivisors O)
  have hloc : IsLocalization Mo L := IsLocalization.tensorRight (A := K) (S := B)
      (nonZeroDivisors O)
  have hM : Mo ≤ nonZeroDivisors B := by
    rintro _ ⟨o, ho, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinjO).2 (nonZeroDivisors.ne_zero ho))
  have hinj : Function.Injective (algebraMap B L) := IsLocalization.injective L hM
  have : IsDomain L := IsLocalization.isDomain_of_le_nonZeroDivisors L hM
  have : Module.Finite K L := inferInstance
  have : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  have hfield : IsField L :=
    (Algebra.IsIntegral.isField_iff_isField (R := K) (S := L) (algebraMap K L).injective).1
      (Field.toIsField K)
  have hfr : IsFractionRing B L := by
    refine IsLocalization.of_le Mo _ hM (fun r hr => ?_)
    have hx : algebraMap B L r ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hr)
    obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx
    exact IsUnit.of_mul_eq_one _ hy
  refine ⟨hfield, inferInstance, hinj, ?_⟩
  ext x
  constructor
  · intro hx
    have hxB : IsIntegral B x := IsIntegral.tower_top (A := B) hx
    obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (K := L)).1 hxB
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := O) y).map
        (Algebra.TensorProduct.includeRight : B →ₐ[O] L)

private theorem fieldInvariant_eq_of_dvr (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    (Q : Type) [CommRing Q] [IsDomain Q] [IsDiscreteValuationRing Q] [Algebra O Q]
    [Module.Free O Q] [Module.Finite O Q] (a : ℕ) (ha : 0 < a) (hrank : Module.finrank O Q = a)
    (hmap : (IsLocalRing.maximalIdeal O).map (algebraMap O Q) = (IsLocalRing.maximalIdeal Q) ^ a)
    (B : Type) [CommRing B] [Algebra O B] (eB : B ≃ₐ[O] Q)
    (hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[O]
        (TensorProduct O (BaseField O) B)))
    (hrange : integralClosure O (TensorProduct O (BaseField O) B) =
      (Algebra.TensorProduct.includeRight : B →ₐ[O] (TensorProduct O (BaseField O) B)).range) :
    fieldInvariant O (TensorProduct O (BaseField O) B) = (a, 1) := by
  set L := TensorProduct O (BaseField O) B
  let ψ : Q ≃ₐ[O] integralClosure O L := eB.symm.trans
    ((AlgEquiv.ofInjective _ hinj).trans (Subalgebra.equivOfEq _ _ hrange.symm))
  have : IsDomain (integralClosure O L) := MulEquiv.isDomain Q ψ.symm.toMulEquiv
  have hD : IsDiscreteValuationRing (integralClosure O L) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing ψ
  have : Algebra.IsIntegral O Q := Algebra.IsIntegral.of_finite O Q
  have hinjQ : Function.Injective (algebraMap O Q) := FaithfulSMul.algebraMap_injective O Q
  have hinjB : Function.Injective (algebraMap O (integralClosure O L)) := by
    have : algebraMap O (integralClosure O L) = (ψ : Q →+* integralClosure O L).comp
        (algebraMap O Q) := by
      ext x; simp
    rw [this]; exact ψ.injective.comp hinjQ
  obtain ⟨he, hfd⟩ := dvr_algEquiv_ramification_inertia O Q (integralClosure O L) hinjQ hinjB ψ
  have h512 := dvr_extension_maximalIdeal_map_eq_pow O Q hinjQ
  have h251 := finite_flat_local_ramification_degree O Q
  have hea : (IsLocalRing.maximalIdeal Q).ramificationIdx O = a := by
    rw [hmap] at h512
    have hne : IsLocalRing.maximalIdeal Q ≠ ⊥ := IsDiscreteValuationRing.not_a_field Q
    exact ((Ideal.pow_right_strictAnti _ hne (Ideal.IsMaximal.ne_top inferInstance)).injective
        h512).symm
  have hf1 : (IsLocalRing.maximalIdeal Q).inertiaDeg O = 1 := by
    rw [hea, hrank] at h251
    exact Nat.eq_of_mul_eq_mul_left ha (by simpa using h251)
  have hl : IsLocalRing (integralClosure O L) := hD.toIsLocalRing
  unfold fieldInvariant
  dsimp only
  rw [dif_pos hl, ← he, ← hfd, hea, hf1]

/-- In the terminal state `single a 1`, the generic fibre of the curve order has field invariant
`(a, 1)`: ramification index `a` and residue degree `1`. -/
theorem terminal_field_invariant (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    [IsDomain (ConcreteSurface O pi u a b)] [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hSpi : S.pi = pi)
    (hSt : S.t = (surfaceT O pi u a b)) (hSx : S.x = (surfaceX O pi u a b)) (hSa : S.a = a)
    (hSb : S.b = b) (J : Ideal (ConcreteSurface O pi u a b))
    (hJ : J ∈ surfaceStateSet O (ConcreteSurface O pi u a b) S (State.single a 1))
    (f : (ConcreteSurface O pi u a b)) (hf : J = Ideal.span {f}) (B : Type) [CommRing B]
    [Algebra O B] (eB : B ≃ₐ[O] ((ConcreteSurface O pi u a b) ⧸ J)) :
    fieldInvariant O (TensorProduct O (BaseField O) B) = (a, 1)  := by
  obtain ⟨-, -, -, hfree, hfin, hrank⟩ := terminal_curve_order_local_principal O pi hpi u a b ha S
    hSpi hSt hSx hSa hSb J hJ f hf
  obtain ⟨hdom, hloc, hdvr, -, hmap⟩ := terminal_curve_order_dvr O pi hpi u a b ha S
    hSpi hSt hSx hSa hSb J hJ f hf
  obtain ⟨-, -, hinj, hrange⟩ := terminal_generic_fibre_field O pi hpi u a b ha S
    hSpi hSt hSx hSa hSb J hJ f hf B eB
  exact @fieldInvariant_eq_of_dvr O _ _ _ (ConcreteSurface O pi u a b ⧸ J) _ hdom hdvr _ hfree hfin
      a ha hrank hmap B _ _ eB hinj hrange

/-- In the terminal state `single a 1`, every ideal of the state set has algebra type `{(a, 1)}`. -/
theorem concrete_member_terminal_type (m : ConcreteMember) (a : ℕ) (hs : m.s = State.single a 1)
    (J : Ideal m.R) (hJ : J ∈ m.toMeasured.stateSet) :
    HasAlgebraType m.O (m.R ⧸ J) {(a, 1)} := by
  have hsh := m.shape
  rw [hs] at hsh
  obtain ⟨rfl, -, -⟩ := hsh
  have hJ' : J ∈ surfaceStateSet m.O m.R m.S (State.single m.a 1) := by
    have : J ∈ surfaceStateSet m.O m.R m.S m.s := hJ
    rwa [hs] at this
  obtain ⟨f, hf⟩ := hJ'.1
  have h1 := terminal_generic_fibre_field m.O m.pi m.hpi m.u m.a m.b m.ha m.S
    m.hS_pi m.hS_t m.hS_x m.hS_a m.hS_b J hJ' f hf (m.R ⧸ J) (AlgEquiv.refl)
  have h2 := terminal_field_invariant m.O m.pi m.hpi m.u m.a m.b m.ha m.S
    m.hS_pi m.hS_t m.hS_x m.hS_a m.hS_b J hJ' f hf (m.R ⧸ J) (AlgEquiv.refl)
  let _ : Field (TensorProduct m.O (BaseField m.O) (m.R ⧸ J)) := h1.1.toField
  obtain ⟨-, -, -, -, _, -⟩ := terminal_curve_order_local_principal m.O m.pi m.hpi m.u
    m.a m.b m.ha m.S m.hS_pi m.hS_t m.hS_x m.hS_a m.hS_b J hJ' f hf
  have hcl := Module.Finite.equiv
    ((AlgEquiv.ofInjective _ h1.2.2.1).trans (Subalgebra.equivOfEq _ _ h1.2.2.2.symm)).toLinearEquiv
  let _ : Algebra (BaseField m.O) (TensorProduct m.O (BaseField m.O) (m.R ⧸ J)) :=
    Algebra.TensorProduct.leftAlgebra (R := m.O) (S := BaseField m.O) (A := BaseField m.O)
      (B := m.R ⧸ J)
  have hfd : FiniteDimensional (BaseField m.O) (TensorProduct m.O (BaseField m.O) (m.R ⧸ J)) :=
      h1.2.1
  refine ⟨Unit, inferInstance, fun _ => TensorProduct m.O (BaseField m.O) (m.R ⧸ J), fun _ =>
      inferInstance,
    fun _ => inferInstance,
    fun _ => Algebra.TensorProduct.instAlgebra (R := m.O) (A := BaseField m.O) (B := m.R ⧸ J),
    fun _ => inferInstance, fun _ => hfd,
    (AlgEquiv.funUnique (BaseField m.O) Unit (TensorProduct m.O (BaseField m.O) (m.R ⧸ J))).symm,
    by rw [Fintype.sum_unique]; exact congrArg _ h2.symm, fun _ => hcl⟩

/-! ### Terminating sets of a surface universe -/

/-- The terminating set lies in the state set, equals it in terminal states, and in nonterminal
states its intersection with each cell is the child box of the children's terminating sets. -/
theorem terminates_cell_decomposition (U : SurfaceUniverse) (i : U.ι) :
    U.terminatingSet i ⊆ (U.M i).stateSet ∧
    ((U.M i).s.terminal = true → U.terminatingSet i = (U.M i).stateSet) ∧
    ((U.M i).s.terminal = false → ∀ c : (U.M i).cellIndex, U.terminatingSet i ∩ (U.M i).cell c =
        U.childBox i c (fun j => U.terminatingSet (U.child i c j))) := by
  have h1 : U.terminatingSet i ⊆ (U.M i).stateSet := by
    intro J hJ
    cases hJ with
    | leaf _ _ hJ _ => exact hJ
    | node _ c _ hJ hnt _ =>
      rw [U.cells_cover i hnt]
      exact Set.mem_iUnion.2 ⟨c, hJ⟩
  refine ⟨h1, fun ht => Set.Subset.antisymm h1 fun J hJ => SurfaceUniverse.Terminates.leaf i J hJ
      ht, ?_⟩
  intro hnt c
  ext J
  constructor
  · rintro ⟨hJ, hc⟩
    refine ⟨hc, ?_⟩
    change U.Terminates i J at hJ
    cases hJ with
    | leaf _ _ _ ht => rw [ht] at hnt; cases hnt
    | node _ c' _ hJ' _ h =>
      have : c' = c := by
        by_contra hne
        exact Set.disjoint_left.1 (U.cells_disjoint i hnt hne) hJ' hc
      subst this
      exact Set.mem_univ_pi.2 h
  · rintro ⟨hc, hp⟩
    exact ⟨SurfaceUniverse.Terminates.node i c J hc hnt (Set.mem_univ_pi.1 hp), hc⟩

/-- Every terminating ideal has a factorization type, and this type is unique. -/
theorem terminates_type_unique (U : SurfaceUniverse) (i : U.ι) (J : Ideal (U.M i).R)
    (hJ : U.Terminates i J) :
    ∃ σ : FactorType, HasAlgebraType (U.M i).O ((U.M i).R ⧸ J) σ ∧ ∀ τ : FactorType,
    HasAlgebraType (U.M i).O ((U.M i).R ⧸ J) τ → τ = σ := by
  have ex : ∃ σ : FactorType, HasAlgebraType (U.M i).O ((U.M i).R ⧸ J) σ := by
    induction hJ with
    | leaf i J hJ ht =>
      have : ∃ a, (U.M i).s = State.single a 1 := by
        cases hs : (U.M i).s with
        | single a c =>
          rw [hs] at ht
          cases c with
          | zero => simp [State.terminal] at ht
          | succ n =>
            cases n with
            | zero => exact ⟨a, rfl⟩
            | succ m => simp [State.terminal] at ht
        | crossing a b c h => rw [hs] at ht; simp [State.terminal] at ht
      obtain ⟨a, ha⟩ := this
      exact ⟨_, U.terminal_type i a ha J hJ⟩
    | node i c J hJ hnt h ih =>
      choose τ hτ using ih
      exact ⟨_, U.type_add i hnt c J hJ τ hτ⟩
  obtain ⟨σ, hσ⟩ := ex
  refine ⟨σ, hσ, fun τ hτ => ?_⟩
  have := (U.M i).instDomain
  exact algebra_type_unique (U.M i).O _ τ σ hτ hσ

/-- The law statement holds at terminal states of a surface universe. -/
theorem recursion_terminal_law (U : SurfaceUniverse) (i : U.ι) (ht : (U.M i).s.terminal = true) :
    U.LawStatement i := by
  obtain ⟨a, ha⟩ : ∃ a, (U.M i).s = State.single a 1 := by
    generalize (U.M i).s = s at ht
    cases s with
    | single a c =>
      cases c with
      | zero => simp [State.terminal] at ht
      | succ c =>
        cases c with
        | zero => exact ⟨a, rfl⟩
        | succ c => simp [State.terminal] at ht
    | crossing a b c h => simp [State.terminal] at ht
  have hT : U.terminatingSet i = (U.M i).stateSet :=
    (terminates_cell_decomposition U i).2.1 ht
  have hm := U.stateSet_measurable i
  refine ⟨fun σ => ?_, by rw [hT]; exact hm, ?_⟩
  · have hev : U.termTypeEvent i σ = if σ = {(a,1)} then (U.M i).stateSet else ∅ := by
      ext J
      simp only [SurfaceUniverse.termTypeEvent, SurfaceUniverse.typeEvent, Set.mem_inter_iff,
        Set.mem_ofPred_eq, hT]
      split_ifs with hσ
      · subst hσ
        exact ⟨fun h => h.1.1, fun h => ⟨⟨h, U.terminal_type i a ha J h⟩, h⟩⟩
      · simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨hJ, hty⟩, -⟩
        have h1 := U.terminal_type i a ha J hJ
        obtain ⟨s, -, hs⟩ := terminates_type_unique U i J
          (SurfaceUniverse.Terminates.leaf i J hJ ht)
        exact hσ ((hs σ hty).trans (hs _ h1).symm)
    have hc : lawCoeff (stateLaw (U.M i).s) σ =
        Expr.add (if ({(a,1)} : FactorType) = σ then Expr.const 1 else Expr.const 0)
          (Expr.const 0) := by
      rw [ha, terminal_law]
      simp [lawCoeff, lawAtom, Expr.sum]
    rw [hev]
    by_cases hσ : σ = {(a,1)}
    · subst hσ
      simp only [if_true]
      have : densityValue (lawCoeff (stateLaw (U.M i).s) {(a,1)}) (U.M i).q = 1 := by
        rw [hc]; simp [densityValue, Expr.eval]
      refine ⟨hm, ?_, ?_⟩
      · rw [hc]; simp [Expr.eval]
      · rw [this, one_mul]
    · have hσ' : ¬ ({(a,1)} : FactorType) = σ := fun h => hσ h.symm
      simp only [hσ, if_false]
      have : densityValue (lawCoeff (stateLaw (U.M i).s) σ) (U.M i).q = 0 := by
        rw [hc]; simp [densityValue, Expr.eval, hσ']
      refine ⟨MeasurableSet.empty, ?_, ?_⟩
      · rw [hc]; simp [Expr.eval, hσ']
      · rw [this, zero_mul, MeasureTheory.measure_empty]
  · unfold SurfaceUniverse.nonterminatingSet
    rw [hT, Set.inter_compl_self, MeasureTheory.measure_empty]

/-- At a nonterminal state, the terminating type-`σ` event intersected with a cell is the type box
of that cell. -/
theorem term_type_event_cell_decomposition (U : SurfaceUniverse) (i : U.ι)
    (hnt : (U.M i).s.terminal = false) (c : (U.M i).cellIndex) (σ : FactorType) :
    U.termTypeEvent i σ ∩ (U.M i).cell c = U.typeBox i c σ := by
  ext J
  constructor
  · rintro ⟨⟨⟨hJs, hJσ⟩, hJt⟩, hJc⟩
    have hdec := (terminates_cell_decomposition U i).2.2 hnt c
    have hmem : J ∈ U.childBox i c (fun j => U.terminatingSet (U.child i c j)) := by
      rw [← hdec]; exact ⟨hJt, hJc⟩
    have hchild : ∀ j, U.Terminates (U.child i c j) (U.Φ i c J j) := fun j =>
      (Set.mem_univ_pi.mp hmem.2) j
    choose τ hτ _ using fun j => terminates_type_unique U (U.child i c j) _ (hchild j)
    have hadd := U.type_add i hnt c J hJc τ hτ
    obtain ⟨σ0, _, hu⟩ := terminates_type_unique U i J hJt
    have h1 : σ = ∑ j, scaleType ((U.M i).childDelta c j) (τ j) := by
      rw [hu σ hJσ, hu _ hadd]
    refine Set.mem_iUnion.mpr ⟨τ, Set.mem_iUnion.mpr ⟨h1, hJc, ?_⟩⟩
    refine Set.mem_univ_pi.mpr fun j => ⟨⟨?_, hτ j⟩, hchild j⟩
    exact ((U.Φ_bij i hnt c).mapsTo hJc) j (Set.mem_univ _)
  · intro h
    obtain ⟨τ, h⟩ := Set.mem_iUnion.mp h
    obtain ⟨h1, h⟩ := Set.mem_iUnion.mp h
    obtain ⟨hJc, hΦ⟩ := h
    have hp := Set.mem_univ_pi.mp hΦ
    have hterm : U.Terminates i J :=
      SurfaceUniverse.Terminates.node i c J hJc hnt fun j => (hp j).2
    refine ⟨⟨⟨?_, ?_⟩, hterm⟩, hJc⟩
    · rw [U.cells_cover i hnt]; exact Set.mem_iUnion.mpr ⟨c, hJc⟩
    · rw [h1]; exact U.type_add i hnt c J hJc τ fun j => (hp j).1.2

section

variable (U : SurfaceUniverse)

private theorem self_list {i : U.ι} {c : (U.M i).cellIndex} (h : (U.M i).IsSelfCell c) :
    (U.M i).childList c = [(1, (U.M i).s)] :=
  h.choose_spec.choose_spec.2

private theorem self_len {i : U.ι} {c : (U.M i).cellIndex} (h : (U.M i).IsSelfCell c) :
    ((U.M i).childList c).length = 1 := by
  rw [self_list U h]; rfl

private theorem self_get {i : U.ι} {c : (U.M i).cellIndex} (h : (U.M i).IsSelfCell c)
    (j : (U.M i).childIdx c) : ((U.M i).childList c).get j = (1, (U.M i).s) := by
  simp [self_list U h]

private theorem self_delta {i : U.ι} {c : (U.M i).cellIndex} (h : (U.M i).IsSelfCell c)
    (j : (U.M i).childIdx c) : (U.M i).childDelta c j = 1 := by
  unfold MeasuredSurface.childDelta; rw [self_get U h]

private theorem self_state {i : U.ι} {c : (U.M i).cellIndex} (h : (U.M i).IsSelfCell c)
    (j : (U.M i).childIdx c) : (U.M (U.child i c j)).s = (U.M i).s := by
  rw [U.child_state]; unfold MeasuredSurface.childState; rw [self_get U h]

private def selfChildIdx {i : U.ι} {c : (U.M i).cellIndex} (h : (U.M i).IsSelfCell c) :
    (U.M i).childIdx c := ⟨0, by rw [self_len U h]; omega⟩

private theorem self_sub {i : U.ι} {c : (U.M i).cellIndex} (h : (U.M i).IsSelfCell c)
    (j j' : (U.M i).childIdx c) : j = j' := by
  have := self_len U h
  apply Fin.ext; have := j.2; have := j'.2; omega

private theorem scale_one (σ : FactorType) : scaleType 1 σ = σ := by
  simp [scaleType]

private theorem self_sum {i : U.ι} {c : (U.M i).cellIndex} (h : (U.M i).IsSelfCell c)
    (σ : FactorType) :
    σ = ∑ j : (U.M i).childIdx c, scaleType ((U.M i).childDelta c j) σ := by
  simp only [self_delta U h, scale_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    self_len U h, one_smul]

/-- Exit events are contained in terminating type events. -/
private theorem exit_sub (σ : FactorType) : ∀ k (i : U.ι), (U.M i).s.terminal = false →
    U.exitEvent σ k i ⊆ U.termTypeEvent i σ := by
  intro k
  induction k with
  | zero =>
    intro i hnt J hJ
    simp only [SurfaceUniverse.exitEvent, Set.mem_iUnion] at hJ
    obtain ⟨c, hc⟩ := hJ
    rw [← term_type_event_cell_decomposition U i hnt c.1 σ] at hc
    exact hc.1
  | succ k ih =>
    intro i hnt J hJ
    simp only [SurfaceUniverse.exitEvent, Set.mem_iUnion] at hJ
    obtain ⟨c, hc⟩ := hJ
    have hJ' : J ∈ U.typeBox i c.1 σ := by
      simp only [SurfaceUniverse.typeBox, Set.mem_iUnion]
      refine ⟨fun _ => σ, self_sum U c.2 σ, hc.1, ?_⟩
      intro j _
      have hnt' : (U.M (U.child i c.1 j)).s.terminal = false := by
        rw [self_state U c.2 j]; exact hnt
      exact ih _ hnt' (hc.2 j (Set.mem_univ _))
    rw [← term_type_event_cell_decomposition U i hnt c.1 σ] at hJ'
    exact hJ'.1

private theorem term_exit_sub : ∀ k (i : U.ι), (U.M i).s.terminal = false →
    U.termExitEvent k i ⊆ U.terminatingSet i := by
  intro k
  induction k with
  | zero =>
    intro i hnt J hJ
    simp only [SurfaceUniverse.termExitEvent, Set.mem_iUnion] at hJ
    obtain ⟨c, hc⟩ := hJ
    exact SurfaceUniverse.Terminates.node i c.1 J hc.1 hnt (fun j => hc.2 j (Set.mem_univ _))
  | succ k ih =>
    intro i hnt J hJ
    simp only [SurfaceUniverse.termExitEvent, Set.mem_iUnion] at hJ
    obtain ⟨c, hc⟩ := hJ
    refine SurfaceUniverse.Terminates.node i c.1 J hc.1 hnt (fun j => ?_)
    have hnt' : (U.M (U.child i c.1 j)).s.terminal = false := by
      rw [self_state U c.2 j]; exact hnt
    exact ih _ hnt' (hc.2 j (Set.mem_univ _))

private theorem term_sub_exit (σ : FactorType) (i : U.ι) (J : Ideal (U.M i).R)
    (hT : U.Terminates i J) :
    (U.M i).s.terminal = false → J ∈ U.typeEvent i σ → ∃ k, J ∈ U.exitEvent σ k i := by
  induction hT with
  | leaf i J _ ht => intro hnt; rw [ht] at hnt; cases hnt
  | node i c J hJ hnt h ih =>
    intro _ hty
    have hmem : J ∈ U.termTypeEvent i σ ∩ (U.M i).cell c :=
      ⟨⟨hty, SurfaceUniverse.Terminates.node i c J hJ hnt h⟩, hJ⟩
    rw [term_type_event_cell_decomposition U i hnt c σ] at hmem
    by_cases hs : (U.M i).IsSelfCell c
    · simp only [SurfaceUniverse.typeBox, Set.mem_iUnion] at hmem
      obtain ⟨τ, hτ, hb⟩ := hmem
      let j0 := selfChildIdx U hs
      have hτ0 : σ = τ j0 := by
        rw [hτ]
        simp only [self_delta U hs, scale_one]
        rw [Fintype.sum_eq_single j0 (fun j hj => absurd (self_sub U hs j j0) hj)]
      have hc0 : U.Φ i c J j0 ∈ U.termTypeEvent (U.child i c j0) (τ j0) := hb.2 j0 (Set.mem_univ _)
      rw [← hτ0] at hc0
      have hnt' : (U.M (U.child i c j0)).s.terminal = false := by
        rw [self_state U hs j0]; exact hnt
      obtain ⟨k, hk⟩ := ih j0 hnt' hc0.1
      refine ⟨k+1, ?_⟩
      simp only [SurfaceUniverse.exitEvent, Set.mem_iUnion]
      refine ⟨⟨c, hs⟩, hJ, ?_⟩
      intro j _
      rw [self_sub U hs j j0]; exact hk
    · refine ⟨0, ?_⟩
      simp only [SurfaceUniverse.exitEvent, Set.mem_iUnion]
      exact ⟨⟨c, hs⟩, hmem⟩

private theorem term_sub_texit (i : U.ι) (J : Ideal (U.M i).R) (hT : U.Terminates i J) :
    (U.M i).s.terminal = false → ∃ k, J ∈ U.termExitEvent k i := by
  induction hT with
  | leaf i J _ ht => intro hnt; rw [ht] at hnt; cases hnt
  | node i c J hJ hnt h ih =>
    intro _
    by_cases hs : (U.M i).IsSelfCell c
    · let j0 := selfChildIdx U hs
      have hnt' : (U.M (U.child i c j0)).s.terminal = false := by
        rw [self_state U hs j0]; exact hnt
      obtain ⟨k, hk⟩ := ih j0 hnt'
      refine ⟨k+1, ?_⟩
      simp only [SurfaceUniverse.termExitEvent, Set.mem_iUnion]
      refine ⟨⟨c, hs⟩, hJ, ?_⟩
      intro j _
      rw [self_sub U hs j j0]; exact hk
    · refine ⟨0, ?_⟩
      simp only [SurfaceUniverse.termExitEvent, Set.mem_iUnion]
      exact ⟨⟨c, hs⟩, hJ, fun j _ => h j⟩

private theorem exit_disj (σ : FactorType) : ∀ k k' (i : U.ι), (U.M i).s.terminal = false → k ≠ k' →
    Disjoint (U.exitEvent σ k i) (U.exitEvent σ k' i) := by
  intro k
  induction k with
  | zero =>
    intro k' i hnt hk
    obtain ⟨k', rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by omega⟩
    rw [Set.disjoint_left]
    intro J h1 h2
    simp only [SurfaceUniverse.exitEvent, Set.mem_iUnion] at h1 h2
    obtain ⟨c1, hc1⟩ := h1
    obtain ⟨c2, hc2⟩ := h2
    have hne : c1.1 ≠ c2.1 := fun e => c1.2 (e ▸ c2.2)
    have hJ1 : J ∈ (U.M i).cell c1.1 := by
      simp only [SurfaceUniverse.typeBox, Set.mem_iUnion] at hc1
      obtain ⟨_, _, hb⟩ := hc1; exact hb.1
    exact Set.disjoint_left.mp (U.cells_disjoint i hnt hne) hJ1 hc2.1
  | succ k ih =>
    intro k' i hnt hk
    rw [Set.disjoint_left]
    intro J h1 h2
    cases k' with
    | zero =>
      simp only [SurfaceUniverse.exitEvent, Set.mem_iUnion] at h1 h2
      obtain ⟨c1, hc1⟩ := h1
      obtain ⟨c2, hc2⟩ := h2
      have hne : c1.1 ≠ c2.1 := fun e => c2.2 (e ▸ c1.2)
      have hJ2 : J ∈ (U.M i).cell c2.1 := by
        simp only [SurfaceUniverse.typeBox, Set.mem_iUnion] at hc2
        obtain ⟨_, _, hb⟩ := hc2; exact hb.1
      exact Set.disjoint_left.mp (U.cells_disjoint i hnt hne) hc1.1 hJ2
    | succ k' =>
      simp only [SurfaceUniverse.exitEvent, Set.mem_iUnion] at h1 h2
      obtain ⟨c1, hc1⟩ := h1
      obtain ⟨c2, hc2⟩ := h2
      by_cases hne : c1.1 = c2.1
      · have : c1 = c2 := Subtype.ext hne
        subst this
        let j0 := selfChildIdx U c1.2
        have hnt' : (U.M (U.child i c1.1 j0)).s.terminal = false := by
          rw [self_state U c1.2 j0]; exact hnt
        exact Set.disjoint_left.mp (ih k' _ hnt' (by omega)) (hc1.2 j0 (Set.mem_univ _))
          (hc2.2 j0 (Set.mem_univ _))
      · exact Set.disjoint_left.mp (U.cells_disjoint i hnt hne) hc1.1 hc2.1

end

/-- For a single state, the terminating type-`σ` event (resp. the terminating set) is the disjoint
union over `k` of the exit events (resp. terminating exit events) after `k` returns; for a
crossing state only `k = 0` occurs. -/
theorem single_state_return_chain (U : SurfaceUniverse) (i : U.ι) (hnt : (U.M i).s.terminal = false)
    (σ : FactorType) :
    (∀ a c : ℕ, (U.M i).s = State.single a c → U.termTypeEvent i σ = ⋃ k, U.exitEvent σ k i ∧
        Pairwise (fun k k' : ℕ => Disjoint (U.exitEvent σ k i) (U.exitEvent σ k' i)) ∧
        U.terminatingSet i = ⋃ k, U.termExitEvent k i) ∧
    (∀ a b c h : ℕ, (U.M i).s = State.crossing a b c h → U.termTypeEvent i σ = U.exitEvent σ 0 i ∧
        U.terminatingSet i = U.termExitEvent 0 i) := by
  have hA : U.termTypeEvent i σ = ⋃ k, U.exitEvent σ k i := by
    apply Set.Subset.antisymm
    · intro J hJ
      obtain ⟨k, hk⟩ := term_sub_exit U σ i J hJ.2 hnt hJ.1
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
    · exact Set.iUnion_subset fun k => exit_sub U σ k i hnt
  have hB : U.terminatingSet i = ⋃ k, U.termExitEvent k i := by
    apply Set.Subset.antisymm
    · intro J hJ
      obtain ⟨k, hk⟩ := term_sub_texit U i J hJ hnt
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
    · exact Set.iUnion_subset fun k => term_exit_sub U k i hnt
  refine ⟨fun _ _ _ => ⟨hA, fun k k' hk => exit_disj U σ k k' i hnt hk, hB⟩, ?_⟩
  intro a b c h hs
  have noself : ∀ c' : (U.M i).cellIndex, ¬ (U.M i).IsSelfCell c' := by
    intro c' hc'
    obtain ⟨a', c'', hs', _⟩ := hc'
    rw [hs] at hs'; cases hs'
  constructor
  · rw [hA]
    apply Set.Subset.antisymm
    · intro J hJ
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hJ
      cases k with
      | zero => exact hk
      | succ k =>
        simp only [SurfaceUniverse.exitEvent, Set.mem_iUnion] at hk
        obtain ⟨c', _⟩ := hk
        exact absurd c'.2 (noself c'.1)
    · exact Set.subset_iUnion (fun k => U.exitEvent σ k i) 0
  · rw [hB]
    apply Set.Subset.antisymm
    · intro J hJ
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hJ
      cases k with
      | zero => exact hk
      | succ k =>
        simp only [SurfaceUniverse.termExitEvent, Set.mem_iUnion] at hk
        obtain ⟨c', _⟩ := hk
        exact absurd c'.2 (noself c'.1)
    · exact Set.subset_iUnion (fun k => U.termExitEvent k i) 0

/-- Basic facts on a surface universe: `q ≥ 2` for every member and child, the state set has
positive finite measure, and there are finitely many cells. -/
theorem universe_basic_facts (U : SurfaceUniverse) (i : U.ι) :
    2 ≤ (U.M i).q ∧ 0 < (U.M i).μ (U.M i).stateSet ∧ (U.M i).μ (U.M i).stateSet ≠ ⊤ ∧
    (∀ (c : (U.M i).cellIndex) (j : (U.M i).childIdx c), 2 ≤ (U.M (U.child i c j)).q) ∧
    Finite (U.M i).cellIndex := by
  have hq : ∀ k : U.ι, 2 ≤ (U.M k).q := fun k => by
    exact Finite.one_lt_card
  have hA0 := fun k => density_value_arith (U.M k).q (hq k) (.const 1) (.const 1)
    (by simp [Expr.eval]) (by simp [Expr.eval]) 0 (U.M k).s (U.M k).valid
  have hA := fun k => density_value_arith (U.M k).q (hq k) (stateVolume (U.M k).s) (.const 1)
    (hA0 k).2.2.2.2.2.2.1.le (by simp [Expr.eval]) 0 (U.M k).s (U.M k).valid
  refine ⟨hq i, ?_, ?_, ?_, ?_⟩
  · rw [U.volume]
    exact pos_iff_ne_zero.2 ((hA i).2.2.2.2.2.1 (hA0 i).2.2.2.2.2.2.1)
  · rw [U.volume]; exact (hA i).2.2.2.2.1
  · intro c j
    rw [U.child_residue]
    have hd : 0 < (U.M i).childDelta c j :=
      children_residue_degree_pos (U.M i).s c.1.1 _ (List.get_mem _ _)
    calc 2 ≤ (U.M i).q := hq i
      _ ≤ _ := Nat.le_self_pow hd.ne' _
  · have : ∀ P : (U.M i).allowedPattern, Finite (patternDivisors
      (IsLocalRing.ResidueField (U.M i).R) (U.M i).s P.1) :=
      fun P => U.divisors_finite i P.1
    have : Finite (U.M i).allowedPattern := inferInstance
    change Finite (Σ P : (U.M i).allowedPattern,
      patternDivisors (IsLocalRing.ResidueField (U.M i).R) (U.M i).s P.1)
    infer_instance

end SurfaceBlowup
