/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Surfaces.ConcreteStrictTransforms
import SurfaceBlowup.Unramified.DescentTypes

/-!
# Members of the recursion universe

This file sets up the objects on which the measure-theoretic recursion of Theorem 8.1 runs.
A `MeasuredSurface` is a regular local surface over a complete DVR with finite residue field,
equipped with a state and an atlas of division charts, hence with a state measure; a
`SurfaceUniverse` is a family of measured surfaces closed under passing to the children of
tangent cells. Concrete members (`ConcreteMember`) are the surfaces `O[[T,X]]/(π − u T^a X^b)`;
for them we prove the chart, measurability and finiteness inputs, and the structure of the
generators of state ideals. We also define the recursion events (type, return and exit events).

## Main definitions

* `CellAssignment`, `MeasuredSurface`, `SurfaceUniverse`, `ConcreteMember`, `ChildMember`,
  `CellChildData`, `SurfaceUniverse.Terminates`, `SurfaceUniverse.LawStatement`.

## Main results

* `concrete_member_charts`, `concrete_member_cell_measurable`,
  `concrete_member_stateSet_measurable`, `concrete_member_measure_finite_support`:
  measure-theoretic inputs for concrete members.
* `concrete_member_curve_order_free`, `concrete_member_state_generator_division`,
  `concrete_member_division_chart_measure`: generators of state ideals give division charts.
* `cell_datum_point_equiv`: children of a cell correspond to points of two-chart curve data.
* `concrete_type_add_of_index_map`: additivity of algebra types along a child decomposition.
* `curve_sections_connecting_map_exists`: the connecting map of the Čech sequence.

Provenance: `Def_SurfaceBlowupV2_{CellAssignments, MeasuredSurfaces, ConcreteMembers,
CellChildData, RecursionEvents}`; `Thm_SurfaceBlowupV2_{allowed_pattern_of_divisor_unique,
baseChange_bijective_of_finite_cokernel, boundary_contact_length_ne_zero_iff,
cell_child_mem_stateSet, cell_datum_point_equiv, chart_cell_law_generic,
coefficient_measure_pi_one, concrete_member_{charts, cell_measurable, data_exists,
stateSet_measurable, measure_finite_support, state_generator_contact_length,
state_generator_regular, division_chart_measure, state_generator_transverse, curve_order_free,
state_generator_division}, concrete_surface_crossing_curve_free, concrete_type_add_of_index_map,
coordinate_ideal_measurableEmbedding, curve_sections_connecting_map_exists}`.
-/

noncomputable section

namespace SurfaceBlowup

open IsLocalRing MeasureTheory
open scoped BigOperators ENNReal

/-! ### Cell assignments -/

section CellAssignments

variable (k : Type) [Field k]

open scoped Classical in
/-- The child state at the point Q of a degree-d tangent divisor Dv of a parent in state s,
equations (7.1)–(7.2): the point at infinity (old t-boundary) gives T(a,a; Dv(∞), c−d) resp.
T(a+b,a; Dv(∞), c−d); at a crossing the point Z = 0 (old x-boundary) gives T(a+b,b; Dv(Z), h−d);
every other point gives S(a; Dv(Q)) resp. S(a+b; Dv(Q)). -/
def pointChildState (s : State) (d : ℕ) (Dv : ExceptionalDivisor k) (Q : ClosedDirection k) :
    State :=
  match s with
  | State.single a c =>
    if Q = infinityDirection k then State.crossing a a (Dv Q) (c - d) else State.single a (Dv Q)
  | State.crossing a b c h =>
    if Q = infinityDirection k then State.crossing (a + b) a (Dv Q) (c - d)
    else if Q = zeroDirection k then State.crossing (a + b) b (Dv Q) (h - d)
    else State.single (a + b) (Dv Q)
/-- A cell assignment for the pattern P and the divisor Dv: a bijection between the entries of the
children list `children s P` and the support of Dv, sending the j-th entry to a point of the
prescribed degree whose child state (`pointChildState`) is the listed state. Existence follows
from `HasPattern` by counting. -/
structure CellAssignment (s : State) (P : TangentPattern s.degree) (Dv : ExceptionalDivisor k) where
  pt : Fin (children s P).length → ClosedDirection k
  inj : Function.Injective pt
  supp : ∀ Q : ClosedDirection k, 0 < Dv Q ↔ ∃ j, pt j = Q
  deg : ∀ j, directionDegree k (pt j) = ((children s P).get j).1
  state : ∀ j, ((children s P).get j).2 = pointChildState k s P.d.val Dv (pt j)

end CellAssignments

/-! ### Measured surfaces and the recursion universe -/

/-- A surface realizing a state, over a complete DVR O with finite residue field and its compact
adic Borel structure, together with a finite atlas of division charts of its state set. -/
structure MeasuredSurface where
  O : Type
  [instCommRing : CommRing O]
  [instDomain : IsDomain O]
  [instDVR : IsDiscreteValuationRing O]
  [instComplete : IsAdicComplete (maximalIdeal O) O]
  [instFinite : Finite (ResidueField O)]
  [instTop : TopologicalSpace O]
  [instTopRing : IsTopologicalRing O]
  [instCompact : CompactSpace O]
  [instT2 : T2Space O]
  [instSecond : SecondCountableTopology O]
  [instMeas : MeasurableSpace O]
  [instBorel : BorelSpace O]
  htop : IsAdic (maximalIdeal O)
  R : Type
  [instCommRingR : CommRing R]
  [instDomainR : IsDomain R]
  [instAlgebra : Algebra O R]
  [instRegular : IsRegularLocalRing R]
  S : SurfaceData O R
  s : State
  valid : s.Valid
  atlas : IdealAtlas O R S.pi s.degree (surfaceStateSet O R S s)
attribute [instance] MeasuredSurface.instCommRing MeasuredSurface.instDomain
  MeasuredSurface.instDVR MeasuredSurface.instComplete MeasuredSurface.instFinite
      MeasuredSurface.instTop
  MeasuredSurface.instTopRing MeasuredSurface.instCompact MeasuredSurface.instT2
      MeasuredSurface.instSecond
  MeasuredSurface.instMeas MeasuredSurface.instBorel MeasuredSurface.instCommRingR
      MeasuredSurface.instDomainR
  MeasuredSurface.instAlgebra MeasuredSurface.instRegular
namespace MeasuredSurface
variable (M : MeasuredSurface)
/-- The residue cardinality q of the coefficient ring. -/
abbrev q : ℕ := Nat.card (ResidueField M.O)
/-- The state set `surfaceStateSet` of the surface in its state. -/
abbrev stateSet : Set (Ideal M.R) := surfaceStateSet M.O M.R M.S M.s
/-- The intrinsic σ-algebra `idealChartSigma` on the curve ideals of the surface. -/
instance measurableSpaceIdeal : MeasurableSpace (Ideal M.R) := idealChartSigma M.O M.R M.S.pi
/-- The state measure `stateMeasure` for the chosen atlas, with the intrinsic σ-algebra. -/
noncomputable def μ : Measure (Ideal M.R) := stateMeasure M.O M.R M.S.pi M.s.degree M.q M.atlas
/-- Allowed patterns of the state, as a type. -/
abbrev allowedPattern : Type := {P : TangentPattern M.s.degree // Allowed M.s P}
/-- A tangent cell index: an allowed pattern together with a divisor realizing it. -/
abbrev cellIndex : Type := Σ P : M.allowedPattern, patternDivisors (ResidueField M.R) M.s P.1
/-- The degree `d` of the tangent pattern of a cell. -/
def cellDegree (c : M.cellIndex) : ℕ := c.1.1.d.val
/-- The fixed-tangent cell `fixedTangentCell` attached to a cell index. -/
def cell (c : M.cellIndex) : Set (Ideal M.R) :=
  fixedTangentCell M.O M.R M.S M.s (M.cellDegree c) c.2.1
/-- The list of (residue degree, state) pairs of the children of a cell. -/
def childList (c : M.cellIndex) : List (ℕ × State) := children M.s c.1.1
/-- The index type of the children of a cell. -/
abbrev childIdx (c : M.cellIndex) : Type := Fin (M.childList c).length
/-- The residue degree of the `j`-th child of a cell. -/
def childDelta (c : M.cellIndex) (j : M.childIdx c) : ℕ := ((M.childList c).get j).1
/-- The state of the `j`-th child of a cell. -/
def childState (c : M.cellIndex) (j : M.childIdx c) : State := ((M.childList c).get j).2
/-- A cell is a self cell if its pattern returns to the parent state. -/
def IsSelfCell (c : M.cellIndex) : Prop := SelfPattern M.s c.1.1
end MeasuredSurface
/-- The recursion interface record: a family of measured surfaces closed under passing to the
children of every tangent cell, with the geometric inputs of Theorem 8.1 as explicit fields (facts
about cells, child surfaces, the fixed-tangent bijections and types). No field mentions stateLaw. -/
structure SurfaceUniverse where
  ι : Type 1
  M : ι → MeasuredSurface
  stateSet_measurable : ∀ i, MeasurableSet (M i).stateSet
  volume : ∀ i, (M i).μ (M i).stateSet = densityValue (stateVolume (M i).s) (M i).q
  divisors_finite : ∀ i (P : TangentPattern (M i).s.degree),
    Finite (patternDivisors (ResidueField (M i).R) (M i).s P)
  divisor_count : ∀ i, (M i).s.terminal = false → ∀ P : TangentPattern (M i).s.degree, Allowed
      (M i).s P →
    ((Nat.card (patternDivisors (ResidueField (M i).R) (M i).s P) : ℕ) : ℚ) =
      (tangentCount (M i).s P).eval ((M i).q : ℚ)
  cell_measurable : ∀ i, (M i).s.terminal = false → ∀ c : (M i).cellIndex, MeasurableSet
      ((M i).cell c)
  cells_cover : ∀ i, (M i).s.terminal = false → (M i).stateSet = ⋃ c : (M i).cellIndex, (M i).cell c
  cells_disjoint : ∀ i, (M i).s.terminal = false →
    Pairwise fun c c' : (M i).cellIndex => Disjoint ((M i).cell c) ((M i).cell c')
  child : ∀ i (c : (M i).cellIndex), (M i).childIdx c → ι
  child_state : ∀ i c j, (M (child i c j)).s = (M i).childState c j
  child_residue : ∀ i c j, (M (child i c j)).q = (M i).q ^ (M i).childDelta c j
  Φ : ∀ i (c : (M i).cellIndex), Ideal (M i).R → ∀ j : (M i).childIdx c, Ideal (M (child i c j)).R
  Φ_bij : ∀ i, (M i).s.terminal = false → ∀ c,
    Set.BijOn (Φ i c) ((M i).cell c) (Set.pi Set.univ fun j => (M (child i c j)).stateSet)
  Φ_measurable : ∀ i, (M i).s.terminal = false → ∀ c (G : ∀ j, Set (Ideal (M (child i c j)).R)),
    (∀ j, MeasurableSet (G j)) → MeasurableSet ((M i).cell c ∩ Φ i c ⁻¹' Set.pi Set.univ G)
  Φ_measure : ∀ i, (M i).s.terminal = false → ∀ c (G : ∀ j, Set (Ideal (M (child i c j)).R)),
    (∀ j, MeasurableSet (G j)) →
    (M i).μ ((M i).cell c ∩ Φ i c ⁻¹' Set.pi Set.univ G) =
      ((M i).q : ℝ≥0∞)⁻¹ ^ tri ((M i).cellDegree c) * ∏ j, (M (child i c j)).μ (G j)
  type_add : ∀ i, (M i).s.terminal = false → ∀ c (J : Ideal (M i).R), J ∈ (M i).cell c →
    ∀ τ : (M i).childIdx c → FactorType,
    (∀ j, HasAlgebraType (M (child i c j)).O ((M (child i c j)).R ⧸ Φ i c J j) (τ j)) →
    HasAlgebraType (M i).O ((M i).R ⧸ J) (∑ j, scaleType ((M i).childDelta c j) (τ j))
  terminal_type : ∀ i (a : ℕ), (M i).s = State.single a 1 → ∀ J ∈ (M i).stateSet,
    HasAlgebraType (M i).O ((M i).R ⧸ J) {(a,1)}

/-- In a surface universe `U`, every child ideal of a typed cell ideal again has an algebra type. -/
def SurfaceUniverse.ChildTypesExist (U : SurfaceUniverse) : Prop :=
  ∀ i, (U.M i).s.terminal = false → ∀ (c : (U.M i).cellIndex) (J : Ideal (U.M i).R),
    J ∈ (U.M i).cell c → ∀ σ : FactorType, HasAlgebraType (U.M i).O ((U.M i).R ⧸ J) σ → ∀ j,
      ∃ τ : FactorType, HasAlgebraType (U.M (U.child i c j)).O
          ((U.M (U.child i c j)).R ⧸ U.Φ i c J j) τ

/-- An invariant `δ` of the ideals of a surface universe `U` does not increase when passing from a
typed cell ideal to a child, and strictly decreases on self cells. -/
def SurfaceUniverse.InvariantDecreases (U : SurfaceUniverse)
    (δ : ∀ i : U.ι, Ideal (U.M i).R → ℕ) : Prop :=
  ∀ i, (U.M i).s.terminal = false → ∀ (c : (U.M i).cellIndex) (J : Ideal (U.M i).R),
    J ∈ (U.M i).cell c → (∃ σ : FactorType, HasAlgebraType (U.M i).O ((U.M i).R ⧸ J) σ) → ∀ j,
      δ (U.child i c j) (U.Φ i c J j) ≤ δ i J ∧
        ((U.M i).IsSelfCell c → δ (U.child i c j) (U.Φ i c J j) < δ i J)

/-! ### Concrete members -/

/-- The states realized by a concrete surface with vertical exponents (a, b): S(a;c) when b = 0 and
T(a,b;c,h) when b > 0, with every displayed entry positive (compare S.a = a, S.b = b in
`surfaceStateSet`). -/
def StateShape (a b : ℕ) : State → Prop
  | State.single a' c => a' = a ∧ b = 0 ∧ 0 < c
  | State.crossing a' b' c h => a' = a ∧ b' = b ∧ 0 < b ∧ 0 < c ∧ 0 < h
/-- A state of the shape of a concrete surface with `0 < a` is valid. -/
theorem StateShape.valid {a b : ℕ} (ha : 0 < a) {s : State} (h : StateShape a b s) : s.Valid := by
  cases s with
  | single => obtain ⟨rfl, -, h3⟩ := h; exact ⟨ha, h3⟩
  | crossing => obtain ⟨rfl, rfl, h3, h4, h5⟩ := h; exact ⟨ha, h3, h4, h5⟩
/-- A concrete member of the recursion universe: a complete DVR O with finite residue field and
its compact adic Borel structure, the concrete surface R = O[[T,X]]/(pi − u T^a X^b) with its
regular local structure and a `SurfaceData` whose parameters are the concrete ones, a state of
matching shape, and an ideal atlas of its state set. All fields are data or elementary
predicates. -/
structure ConcreteMember where
  O : Type
  [instCommRing : CommRing O]
  [instDomain : IsDomain O]
  [instDVR : IsDiscreteValuationRing O]
  [instComplete : IsAdicComplete (maximalIdeal O) O]
  [instFinite : Finite (ResidueField O)]
  [instTop : TopologicalSpace O]
  [instTopRing : IsTopologicalRing O]
  [instCompact : CompactSpace O]
  [instT2 : T2Space O]
  [instSecond : SecondCountableTopology O]
  [instMeas : MeasurableSpace O]
  [instBorel : BorelSpace O]
  htop : IsAdic (maximalIdeal O)
  pi : O
  hpi : Irreducible pi
  u : (TwoSeries O)ˣ
  a : ℕ
  b : ℕ
  ha : 0 < a
  [instDomainR : IsDomain (ConcreteSurface O pi u a b)]
  [instRegular : IsRegularLocalRing (ConcreteSurface O pi u a b)]
  S : SurfaceData O (ConcreteSurface O pi u a b)
  hS_pi : S.pi = pi
  hS_t : S.t = surfaceT O pi u a b
  hS_x : S.x = surfaceX O pi u a b
  hS_a : S.a = a
  hS_b : S.b = b
  s : State
  shape : StateShape a b s
  atlas : IdealAtlas O (ConcreteSurface O pi u a b) S.pi s.degree
    (surfaceStateSet O (ConcreteSurface O pi u a b) S s)
attribute [instance] ConcreteMember.instCommRing ConcreteMember.instDomain
  ConcreteMember.instDVR ConcreteMember.instComplete ConcreteMember.instFinite
      ConcreteMember.instTop
  ConcreteMember.instTopRing ConcreteMember.instCompact ConcreteMember.instT2
      ConcreteMember.instSecond
  ConcreteMember.instMeas ConcreteMember.instBorel ConcreteMember.instDomainR
      ConcreteMember.instRegular
namespace ConcreteMember
variable (m : ConcreteMember)
/-- The concrete surface of a member. -/
abbrev R : Type := ConcreteSurface m.O m.pi m.u m.a m.b
/-- The member as a measured surface: same coefficient ring, surface, SurfaceData, state and
atlas. -/
def toMeasured : MeasuredSurface where
  O := m.O
  htop := m.htop
  R := m.R
  S := m.S
  s := m.s
  valid := m.shape.valid m.ha
  atlas := m.atlas
/-- The cell indices of a member, written on `m.R` (definitionally `m.toMeasured.cellIndex`):
an allowed pattern and a divisor realizing it. -/
abbrev cellIndex : Type :=
  Σ P : {P : TangentPattern m.s.degree // Allowed m.s P}, patternDivisors (ResidueField m.R) m.s P.1
end ConcreteMember

/-! ### Child data of a cell -/

section FromSurface
variable (R : Type) [CommRing R] (t x : R) [IsLocalRing R]
  (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (ResidueField R))
  (Dv : ExceptionalDivisor (ResidueField R)) (hinf : (infinityPoint R t x).IsPrime)
/-- The canonical map from the surface into the completed local ring at a point of the support:
through the right chart at ∞, through the left chart at an affine point. -/
def divisorFromSurface : ∀ Q, R →+* divisorLocalRing R t x e Dv hinf Q
  | ⟨none, _⟩ => (@completedPointMap (BlowupChart R x t) _ (infinityPoint R t x) hinf).comp
      (chartBase R x t)
  | ⟨some φ, _⟩ => (completedPointMap (BlowupChart R t x) (directionPoint R t x e φ)).comp
      (chartBase R t x)
end FromSurface
/-- The point of the support of Dv assigned to the j-th child by a cell assignment; kept as a
definition so that `divisorLocalRing … (asg.point j)` is not unfolded by instance resolution. -/
def CellAssignment.point {k : Type} [Field k] {s : State} {P : TangentPattern s.degree}
    {Dv : ExceptionalDivisor k}
    (asg : CellAssignment k s P Dv) (j : Fin (children s P).length) : divisorSupport Dv :=
  ⟨asg.pt j, (asg.supp _).mpr ⟨j, rfl⟩⟩
/-- A child member with its tower data over the parent coefficient ring `m.O`: a concrete member
`mc` in the state `s'` whose coefficient ring is a finite free `m.O`-algebra of rank δ with residue
field of cardinality q^δ and the same uniformizer, with coordinates `pc : mc.O ≃ₗ[m.O] m.O^δ` that
are a homeomorphism and a measurable equivalence under which the coefficient Haar measures of
`mc.O^r` are products of the parent's. Instance fields are non-dependent so that they are available
to the later fields. -/
structure ChildMember (m : ConcreteMember) (δ : ℕ) (s' : State) where
  mc : ConcreteMember
  [algO : Algebra m.O mc.O]
  [finO : Module.Finite m.O mc.O]
  [freeO : Module.Free m.O mc.O]
  hrank : Module.finrank m.O mc.O = δ
  hcard : Nat.card (ResidueField mc.O) = Nat.card (ResidueField m.O) ^ δ
  hpi : mc.pi = algebraMap m.O mc.O m.pi
  hstate : mc.s = s'
  pc : mc.O ≃ₗ[m.O] (Fin δ → m.O)
  pc_cont : Continuous pc ∧ Continuous pc.symm ∧ Measurable pc ∧ Measurable pc.symm
  pc_measure : ∀ r : ℕ, coefficientMeasure mc.O r =
    Measure.pi (fun _ : Fin r => Measure.map pc.symm (coefficientMeasure m.O δ))
attribute [instance] ChildMember.algO ChildMember.finO ChildMember.freeO
/-- The child data of a cell `c` (allowed pattern P, divisor Dv) of a concrete member `m`: the
exceptional-line isomorphism e with its formulas, the primality of the point at infinity, a
cell assignment matching the children list with the support of Dv, for each child index j a
child member (ChildMember) in the listed child state with the listed residue degree, and a ring
isomorphism Eq j from the completed local ring at the assigned point onto the child's surface
carrying the exceptional equation to T′, the old boundary to X′ at the boundary points, and the
coefficients through the tower. All fields are data or elementary predicates. -/
structure CellChildData (m : ConcreteMember) (c : m.cellIndex) where
  e : (BlowupChart m.R m.S.t m.S.x ⧸ chartExceptional m.R m.S.t m.S.x) ≃+* Polynomial
      (ResidueField m.R)
  he : ∀ r : m.R, e (Ideal.Quotient.mk (chartExceptional m.R m.S.t m.S.x)
      (chartBase m.R m.S.t m.S.x r)) =
    Polynomial.C (residue m.R r)
  heZ : e (Ideal.Quotient.mk (chartExceptional m.R m.S.t m.S.x) (chartSlope m.R m.S.t m.S.x)) =
      Polynomial.X
  hinf : (infinityPoint m.R m.S.t m.S.x).IsPrime
  asg : CellAssignment (ResidueField m.R) m.s c.1.1 c.2.1
  child : ∀ j : m.toMeasured.childIdx c, ChildMember m (m.toMeasured.childDelta c j)
      (m.toMeasured.childState c j)
  Eq : ∀ j, divisorLocalRing m.R m.S.t m.S.x e c.2.1 hinf (asg.point j) ≃+* (child j).mc.R
  hEq_e : ∀ j, Eq j (divisorException m.R m.S.t m.S.x e c.2.1 hinf (asg.point j)) = (child j).mc.S.t
  hEq_b : ∀ j, (asg.pt j = infinityDirection (ResidueField m.R) ∨ asg.pt j = zeroDirection
      (ResidueField m.R)) →
    Eq j (divisorBoundary m.R m.S.t m.S.x e c.2.1 hinf (asg.point j)) = (child j).mc.S.x
  hEq_c : ∀ (j) (r : m.O), Eq j (divisorFromSurface m.R m.S.t m.S.x e c.2.1 hinf (asg.point j)
    (algebraMap m.O m.R r)) = algebraMap (child j).mc.O (child j).mc.R
        (algebraMap m.O (child j).mc.O r)
namespace CellChildData
variable {m : ConcreteMember} {c : m.toMeasured.cellIndex} (D : CellChildData m c)
/-- The j-th child member. -/
abbrev mc (j : m.toMeasured.childIdx c) : ConcreteMember := (D.child j).mc
/-- The point of the support assigned to the j-th child. -/
abbrev point (j : m.toMeasured.childIdx c) : divisorSupport c.2.1 := D.asg.point j
/-- The pullback into the j-th child surface as an O-algebra homomorphism. -/
def alpha (j : m.toMeasured.childIdx c) : m.R →ₐ[m.O] (D.mc j).R where
  toRingHom := (D.Eq j).toRingHom.comp (divisorFromSurface m.R m.S.t m.S.x D.e c.2.1 D.hinf
      (D.point j))
  commutes' r := (D.hEq_c j r).trans (IsScalarTower.algebraMap_apply m.O (D.mc j).O (D.mc j).R
      r).symm
/-- The strict-transform map of the recursion record on this cell: the colon strict transform
(`strictTransformIdeal`) of a parent ideal along alpha j by the d-th power of the child's
exceptional equation T′, d the degree of the cell. -/
def Φ (J : Ideal m.R) (j : m.toMeasured.childIdx c) : Ideal (D.mc j).R :=
  strictTransformIdeal (D.alpha j) ((D.mc j).S.t) (m.toMeasured.cellDegree c) J
end CellChildData

/-! ### Recursion events -/

namespace SurfaceUniverse
variable (U : SurfaceUniverse)
/-- The type event: ideals of the state whose curve order has type σ. -/
def typeEvent (i : U.ι) (σ : FactorType) : Set (Ideal (U.M i).R) :=
  {J | J ∈ (U.M i).stateSet ∧ HasAlgebraType (U.M i).O ((U.M i).R ⧸ J) σ}
/-- The recursion tree of J is finite: J is in a terminal state, or J lies in a cell all of whose
child ideals have finite trees. -/
inductive Terminates : ∀ i : U.ι, Ideal (U.M i).R → Prop
  | leaf (i : U.ι) (J : Ideal (U.M i).R) (hJ : J ∈ (U.M i).stateSet)
      (ht : (U.M i).s.terminal = true) : Terminates i J
  | node (i : U.ι) (c : (U.M i).cellIndex) (J : Ideal (U.M i).R) (hJ : J ∈ (U.M i).cell c)
      (hnt : (U.M i).s.terminal = false)
      (h : ∀ j, Terminates (U.child i c j) (U.Φ i c J j)) : Terminates i J
/-- The ideals of member `i` whose recursion tree is finite. -/
def terminatingSet (i : U.ι) : Set (Ideal (U.M i).R) := {J | U.Terminates i J}
/-- The ideals of the state set of member `i` whose recursion tree is infinite. -/
def nonterminatingSet (i : U.ι) : Set (Ideal (U.M i).R) := (U.M i).stateSet ∩ (U.terminatingSet i)ᶜ
/-- The measurable core of the type event: terminating ideals of type σ. -/
def termTypeEvent (i : U.ι) (σ : FactorType) : Set (Ideal (U.M i).R) :=
  U.typeEvent i σ ∩ U.terminatingSet i
/-- The self cells of member `i`. -/
def selfCells (i : U.ι) : Type := {c : (U.M i).cellIndex // (U.M i).IsSelfCell c}
/-- The non-self (exit) cells of member `i`. -/
def exitCells (i : U.ι) : Type := {c : (U.M i).cellIndex // ¬ (U.M i).IsSelfCell c}
/-- The part of a cell whose child ideals lie in the prescribed sides G_j. -/
def childBox (i : U.ι) (c : (U.M i).cellIndex) (G : ∀ j, Set (Ideal (U.M (U.child i c j)).R)) :
    Set (Ideal (U.M i).R) :=
  (U.M i).cell c ∩ U.Φ i c ⁻¹' Set.pi Set.univ G
/-- The part of a cell whose children terminate with types τ_j adding up (with residue scaling) to
σ. -/
def typeBox (i : U.ι) (c : (U.M i).cellIndex) (σ : FactorType) : Set (Ideal (U.M i).R) :=
  ⋃ (τ : (U.M i).childIdx c → FactorType) (_ : σ = ∑ j, scaleType ((U.M i).childDelta c j) (τ j)),
    U.childBox i c (fun j => U.termTypeEvent (U.child i c j) (τ j))
/-- At least k successive self returns. -/
def returnEvent : ℕ → ∀ i : U.ι, Set (Ideal (U.M i).R)
  | 0, i => (U.M i).stateSet
  | k+1, i => ⋃ c : U.selfCells i, U.childBox i c.1 (fun j => returnEvent k (U.child i c.1 j))
/-- Exactly k self returns, then an exit cell whose children terminate with total type σ. -/
def exitEvent (σ : FactorType) : ℕ → ∀ i : U.ι, Set (Ideal (U.M i).R)
  | 0, i => ⋃ c : U.exitCells i, U.typeBox i c.1 σ
  | k+1, i => ⋃ c : U.selfCells i, U.childBox i c.1 (fun j => exitEvent σ k (U.child i c.1 j))
/-- Exactly k self returns, then an exit cell all of whose children terminate. -/
def termExitEvent : ℕ → ∀ i : U.ι, Set (Ideal (U.M i).R)
  | 0, i => ⋃ c : U.exitCells i, U.childBox i c.1 (fun j => U.terminatingSet (U.child i c.1 j))
  | k+1, i => ⋃ c : U.selfCells i, U.childBox i c.1 (fun j => termExitEvent k (U.child i c.1 j))
/-- Exactly k self returns, then an exit cell with some nonterminating child. -/
def badExitEvent : ℕ → ∀ i : U.ι, Set (Ideal (U.M i).R)
  | 0, i => ⋃ c : U.exitCells i, ⋃ j₀ : (U.M i).childIdx c.1,
      U.childBox i c.1 (Function.update (fun _ => Set.univ) j₀
          (U.nonterminatingSet (U.child i c.1 j₀)))
  | k+1, i => ⋃ c : U.selfCells i, U.childBox i c.1 (fun j => badExitEvent k (U.child i c.1 j))
/-- The inductive statement of Theorem 8.1 for one member: the terminating type events are
measurable, the law coefficients are nonnegative and give the measures, the terminating set is
measurable and the nonterminating set is null. -/
def LawStatement (i : U.ι) : Prop :=
  (∀ σ : FactorType, MeasurableSet (U.termTypeEvent i σ) ∧
    0 ≤ (lawCoeff (stateLaw (U.M i).s) σ).eval ((U.M i).q : ℚ) ∧
    (U.M i).μ (U.termTypeEvent i σ) =
      densityValue (lawCoeff (stateLaw (U.M i).s) σ) (U.M i).q * (U.M i).μ (U.M i).stateSet) ∧
  MeasurableSet (U.terminatingSet i) ∧ (U.M i).μ (U.nonterminatingSet i) = 0
end SurfaceUniverse
/-! ### Patterns, base change and boundary contact -/

/-- An exceptional divisor has at most one allowed tangent pattern. -/
theorem allowed_pattern_of_divisor_unique (k : Type) [Field k] (s : State)
    (Dv : ExceptionalDivisor k) (P P' : TangentPattern s.degree) (hP : Allowed s P)
    (hP' : Allowed s P') (h : HasPattern k s Dv P) (h' : HasPattern k s Dv P') :
    P = P' := by
  obtain ⟨d1, t1, x1, o1⟩ := h
  obtain ⟨d2, t2, x2, o2⟩ := h'
  have hd : P.d = P'.d := Fin.ext (d1.symm.trans d2)
  have ht : P.rt = P'.rt := Fin.ext (t1.symm.trans t2)
  have hx : P.rx = P'.rx := Fin.ext <| by
    cases s with
    | single => exact hP.2.2.2.1.trans hP'.2.2.2.1.symm
    | crossing => exact x1.symm.trans x2
  have ho : P.other = P'.other := funext fun ij ↦ Fin.ext ((o1 ij).symm.trans (o2 ij))
  cases P; cases P'
  cases hd; cases ht; cases hx; cases ho
  rfl

/-- An injective linear map over a DVR whose cokernel has finite length becomes bijective
after base change to the fraction field. -/
theorem baseChange_bijective_of_finite_cokernel (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (M N : Type) [AddCommGroup M] [Module O M] [AddCommGroup N]
    [Module O N] (φ : M →ₗ[O] N) (hinj : Function.Injective φ) (ℓ : ℕ)
    (hℓ : Module.length O (N ⧸ LinearMap.range φ) = ℓ) :
    Function.Bijective (LinearMap.baseChange (BaseField O) φ) := by
  have hflat : Module.Flat O (BaseField O) :=
    IsLocalization.flat (BaseField O) (nonZeroDivisors O)
  constructor
  · rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap φ hinj
  · obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hmax := hpi.maximalIdeal_eq
    have key := linear_image_bound_from_cokernel_length O M N pi hmax φ ℓ hℓ
    have hne : algebraMap O (BaseField O) pi ≠ 0 := fun h ↦
      hpi.ne_zero (IsFractionRing.injective O (BaseField O) (by simpa using h))
    have hu : IsUnit ((algebraMap O (BaseField O) pi)^ℓ) := (pow_ne_zero ℓ hne).isUnit
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul k y =>
      obtain ⟨m, hm⟩ := key y
      obtain ⟨u, hu'⟩ := hu
      refine ⟨(k * ↑u⁻¹) ⊗ₜ[O] m, ?_⟩
      rw [LinearMap.baseChange_tmul, hm, ← TensorProduct.smul_tmul, Algebra.smul_def, map_pow,
        ← hu']
      congr 1
      rw [mul_left_comm, Units.mul_inv, mul_one]
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩

/-- On the chart at infinity, the curve `∑ cᵢ W^(d-i)` meets the boundary `W = 0` iff its constant
coefficient `c_d` lies in the maximal ideal. -/
theorem boundary_contact_length_ne_zero_iff (R : Type) [CommRing R] [IsLocalRing R] (t x : R)
    (hmax : maximalIdeal R = Ideal.span {t, x}) (d : ℕ) (c : Fin (d + 1) → R) :
    Module.length (BlowupChart R x t) (BlowupChart R x t ⧸ (Ideal.span
      {(∑ i : Fin (d+1), algebraMap R (BlowupChart R x t) (c i) * (chartSlope R x t)^(d - i.val))} ⊔
      Ideal.span {chartSlope R x t})) ≠ 0 ↔ c (Fin.last d) ∈ maximalIdeal R := by
  set B := BlowupChart R x t
  set W := chartSlope R x t
  set g : B := ∑ i : Fin (d+1), algebraMap R B (c i) * W^(d - i.val) with hg
  have hdiff : g - algebraMap R B (c (Fin.last d)) ∈ Ideal.span {W} := by
    rw [hg, Fin.sum_univ_castSucc]
    simp only [Fin.val_last, Fin.val_castSucc]
    rw [Nat.sub_self, pow_zero, mul_one, add_sub_cancel_right]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [show d - (i : ℕ) = (d - i - 1) + 1 by have := i.isLt; omega, pow_succ, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self W)
  rw [Ne, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]
  constructor
  · intro h
    by_contra hc
    refine h (Ideal.eq_top_of_isUnit_mem _ ?_ ((notMem_maximalIdeal.mp hc).map (algebraMap R B)))
    simpa using Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self g))
      (Ideal.mem_sup_right hdiff)
  · intro hc hI
    obtain ⟨ρ, hρ1, hρ2⟩ := boundary_chart_quotient_equiv R t x
    have htm : Ideal.span {t} ≤ maximalIdeal R := by
      rw [Ideal.span_singleton_le_iff_mem, hmax]; exact Ideal.subset_span (by simp)
    let φ : B →+* R ⧸ maximalIdeal R :=
      (Ideal.Quotient.factor htm).comp
        ((ρ : _ →+* _).comp (Ideal.Quotient.mk (Ideal.span {W})))
    have hφW : φ W = 0 := by
      change Ideal.Quotient.factor htm (ρ (Ideal.Quotient.mk (Ideal.span {W}) W)) = 0
      rw [hρ2]; simp
    have hφa : φ (algebraMap R B (c (Fin.last d))) = 0 := by
      change Ideal.Quotient.factor htm (ρ (Ideal.Quotient.mk (Ideal.span {W})
          (chartBase R x t (c (Fin.last d))))) = 0
      rw [hρ1]
      simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hc)
    have hφg : φ g = 0 := by
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hdiff
      rw [← sub_add_cancel g (algebraMap R B _), hy, map_add, map_mul, hφW, hφa, zero_mul, zero_add]
    have : (1 : B) ∈ Ideal.span {g} ⊔ Ideal.span {W} := hI ▸ Submodule.mem_top
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp this
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hp
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.mp hq
    have := congrArg φ hpq
    rw [map_add, map_mul, map_mul, hφg, hφW] at this
    simp at this

/-- The strict-transform map sends an ideal of a cell into the state set of each child. -/
theorem cell_child_mem_stateSet (U : SurfaceUniverse) (i : U.ι) (hnt : (U.M i).s.terminal = false)
    (c : (U.M i).cellIndex) (J : Ideal (U.M i).R) (hJ : J ∈ (U.M i).cell c)
    (j : (U.M i).childIdx c) :
    U.Φ i c J j ∈ (U.M (U.child i c j)).stateSet :=
  Set.mem_univ_pi.mp ((U.Φ_bij i hnt c).mapsTo hJ) j

/-! ### Points of a cell -/

private theorem completedLocalAt_equiv_of_eq {R : Type} [CommRing R] [IsLocalRing R] (t x : R)
    (P P' : Ideal (BlowupChart R t x))
    [hP : P.IsPrime] [hP' : P'.IsPrime] (h : P = P') :
    ∃ ι : CompletedLocalAt (BlowupChart R t x) P ≃+* CompletedLocalAt (BlowupChart R t x) P',
      (∀ a, ι (completedPointMap _ P a) = completedPointMap _ P' a) ∧
      ∀ d J, Ideal.map ι.toRingHom
        (strictTransformAt R t x P d J) = strictTransformAt R t x P' d J := by
  subst h
  exact ⟨RingEquiv.refl _, fun _ ↦ rfl, fun _ _ ↦ Ideal.map_id _⟩

private theorem directionPoint_quot_surjective {R : Type} [CommRing R] [IsLocalRing R] (t x : R)
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (ResidueField R)) :
    Function.Surjective (e.toRingHom.comp (Ideal.Quotient.mk (chartExceptional R t x))) :=
  e.surjective.comp Ideal.Quotient.mk_surjective

private theorem directionPoint_isMaximal {R : Type} [CommRing R] [IsLocalRing R] (t x : R)
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (ResidueField R))
    (φ : AffineDirection (ResidueField R)) : (directionPoint R t x e φ).IsMaximal := by
  have : (Ideal.span {φ.val}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible φ.property.2
  exact Ideal.comap_isMaximal_of_surjective _ (directionPoint_quot_surjective t x e)

private theorem directionPoint_injective {R : Type} [CommRing R] [IsLocalRing R] (t x : R)
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (ResidueField R)) :
    Function.Injective (directionPoint R t x e) := by
  intro φ ψ h
  have hs := Ideal.map_comap_of_surjective _ (directionPoint_quot_surjective t x e)
  have h3 : Ideal.span {φ.val} = Ideal.span {ψ.val} := by
    rw [← hs (Ideal.span {φ.val}), ← hs (Ideal.span {ψ.val})]
    exact congrArg (Ideal.map _) h
  rw [Ideal.span_singleton_eq_span_singleton] at h3
  exact Subtype.ext (Polynomial.eq_of_monic_of_associated φ.2.1 ψ.2.1 h3)

private theorem directionPoint_eq_comap {R : Type} [CommRing R] [IsLocalRing R] (t x : R)
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (ResidueField R))
    (φ : AffineDirection (ResidueField R)) (Q : Ideal (BlowupOverlap R t x)) [Q.IsMaximal]
    (hQ : Q = (directionPoint R t x e φ).map
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) :
    directionPoint R t x e φ = Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) := by
  have hmax := directionPoint_isMaximal t x e φ
  refine hmax.eq_of_le (Ideal.IsPrime.comap _).ne_top ?_
  rw [hQ]
  exact Ideal.le_comap_map

private theorem map_trans_symm_eq_span {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (ι0 : A ≃+* B) (L : C ≃+* B)
    (I : Ideal A) (g : C) (h : Ideal.map ι0.toRingHom I = Ideal.span {L g}) :
    Ideal.map (ι0.trans L.symm : A →+* C) I = Ideal.span {g} := by
  have e2 := congrArg (Ideal.map L.symm.toRingHom) h
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton] at e2
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at e2
  exact e2

/-- Given two-chart curve data matching the divisor of a cell, the children of the cell are in
bijection with the points of the curve data, compatibly with the completed local rings, the maps
from the surface, and the strict transforms. -/
theorem cell_datum_point_equiv (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c)
    (J : Ideal m.R) (beta : BlowupRestriction m.R m.S.t m.S.x)
    (Df : TwoChartCurveData m.R m.S.t m.S.x beta) (hst : (∀ s : Df.ι ⊕ Df.ι0, strictTransformAt m.R
    m.S.t m.S.x (leftPoint Df s) (m.toMeasured.cellDegree c) J = Ideal.span {leftData Df s}) ∧ ∀ s :
    Df.ι ⊕ Df.ιinf, strictTransformAt m.R m.S.x m.S.t (rightPoint Df s) (m.toMeasured.cellDegree c)
    J = Ideal.span {rightData Df s}) (hm : MatchesDivisor D.e Df c.2.1)
    (hpos : (∀ i : Df.ι, 0 < commonMultiplicity Df i) ∧ (∀ k : Df.ι0, 0 < leftMultiplicity Df
    (Sum.inr k)) ∧ ∀ l : Df.ιinf, 0 < rightMultiplicity Df (Sum.inr l)) :
    ∃ ee : m.toMeasured.childIdx c ≃ AllPoints Df, ∀ j : m.toMeasured.childIdx c, ∃ ι :
      divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) ≃+* localRing Df (ee j),
      (∀ r : m.R, ι (divisorFromSurface m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) r) =
      localFromSurface Df (ee j) r) ∧ Ideal.map (ι : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1
      D.hinf (D.point j) →+* localRing Df (ee j)) (divisorStrictTransform m.R m.S.t m.S.x D.e c.2.1
      D.hinf (m.toMeasured.cellDegree c) J (D.point j)) = Ideal.span {localCurve Df (ee j)} := by
  let φc : Df.ι → AffineDirection (ResidueField m.R) := fun i => Classical.choose (hm.common i)
  have hφc : ∀ i, φc i ≠ zeroAffine _ ∧ Df.Q i = (directionPoint m.R m.S.t m.S.x D.e (φc i)).map
      (algebraMap (BlowupChart m.R m.S.t m.S.x) (BlowupOverlap m.R m.S.t m.S.x)) ∧
      c.2.1 (some (φc i)) = commonMultiplicity Df i := fun i => Classical.choose_spec (hm.common i)
  let p : AllPoints Df → divisorSupport c.2.1 := fun a => match a with
    | Sum.inl i => ⟨some (φc i), by rw [(hφc i).2.2]; exact hpos.1 i⟩
    | Sum.inr (Sum.inl k) => ⟨some (zeroAffine _), (hm.zero k).2 ▸ hpos.2.1 k⟩
    | Sum.inr (Sum.inr l) => ⟨none, (hm.inf l).2 ▸ hpos.2.2 l⟩
  have hcφ : ∀ i, directionPoint m.R m.S.t m.S.x D.e (φc i) =
      (Df.Q i).comap (algebraMap (BlowupChart m.R m.S.t m.S.x) (BlowupOverlap m.R m.S.t m.S.x)) :=
    fun i => directionPoint_eq_comap _ _ D.e (φc i) (Df.Q i) (hφc i).2.1
  have hloc : ∀ (a : AllPoints Df) (Q : divisorSupport c.2.1), p a = Q →
      ∃ ι : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf Q ≃+* localRing Df a,
        (∀ r : m.R, ι (divisorFromSurface m.R m.S.t m.S.x D.e c.2.1 D.hinf Q r) =
          localFromSurface Df a r) ∧
        Ideal.map (ι : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf Q →+* localRing Df a)
          (divisorStrictTransform m.R m.S.t m.S.x D.e c.2.1 D.hinf (m.toMeasured.cellDegree c) J
            Q) = Ideal.span {localCurve Df a} := by
    rintro a Q rfl
    rcases a with i | k | l
    · obtain ⟨ι0, h1, h2⟩ := completedLocalAt_equiv_of_eq m.S.t m.S.x _ _ (hcφ i)
      refine ⟨ι0.trans (Df.leftIso i).symm, fun r => ?_, ?_⟩
      · exact (congrArg (Df.leftIso i).symm (h1 _)).trans
          ((Df.leftIso i).symm_apply_eq.mpr (Df.leftIso_compat i _).symm)
      · exact map_trans_symm_eq_span ι0 (Df.leftIso i) _ (Df.g i)
          ((h2 _ J).trans (hst.1 (Sum.inl i)))
    · obtain ⟨ι0, h1, h2⟩ := completedLocalAt_equiv_of_eq m.S.t m.S.x
        (directionPoint m.R m.S.t m.S.x D.e (zeroAffine _))
        (leftPoint Df (Sum.inr k)) (hm.zero k).1.symm
      exact ⟨ι0, fun r => h1 _, (h2 _ J).trans (hst.1 (Sum.inr k))⟩
    · obtain ⟨ι0, h1, h2⟩ := @completedLocalAt_equiv_of_eq _ _ _ m.S.x m.S.t
        (infinityPoint m.R m.S.t m.S.x)
        (rightPoint Df (Sum.inr l)) D.hinf _ (hm.inf l).1.symm
      exact ⟨ι0, fun r => h1 _, (h2 _ J).trans (hst.2 (Sum.inr l))⟩
  have hp : Function.Bijective p := by
    constructor
    · intro a b hab
      have hv := congrArg Subtype.val hab
      rcases a with i | k | l <;> rcases b with i' | k' | l'
      · have h1 : φc i = φc i' := Option.some.inj hv
        exact congrArg Sum.inl (Df.inj (by rw [(hφc i).2.1, (hφc i').2.1, h1]))
      · exact absurd (Option.some.inj hv) (hφc i).1
      · simp [p] at hv
      · exact absurd (Option.some.inj hv).symm (hφc i').1
      · exact congrArg (fun z => Sum.inr (Sum.inl z)) (Df.inj0
          (by rw [(hm.zero k).1, (hm.zero k').1]))
      all_goals first
        | (simp [p] at hv; done)
        | exact congrArg (fun z => Sum.inr (Sum.inr z)) (Df.injinf
            (by rw [(hm.inf l).1, (hm.inf l').1]))
    · rintro ⟨q, hq⟩
      rcases q with _ | φ
      · obtain ⟨l⟩ := hm.inf_surj hq
        exact ⟨Sum.inr (Sum.inr l), rfl⟩
      · by_cases hφ : φ = zeroAffine _
        · subst hφ
          obtain ⟨k⟩ := hm.zero_surj hq
          exact ⟨Sum.inr (Sum.inl k), rfl⟩
        · obtain ⟨i, hi⟩ := hm.common_surj φ hφ hq
          refine ⟨Sum.inl i, Subtype.ext ?_⟩
          change some (φc i) = some φ
          congr 1
          apply directionPoint_injective m.S.t m.S.x D.e
          rw [hcφ i, directionPoint_eq_comap _ _ D.e φ (Df.Q i) hi]
  have hasg : Function.Bijective D.point := by
    refine ⟨fun j j' h => D.asg.inj (congrArg Subtype.val h), fun Q => ?_⟩
    obtain ⟨j, hj⟩ := (D.asg.supp Q.val).mp Q.property
    exact ⟨j, Subtype.ext hj⟩
  let ee : m.toMeasured.childIdx c ≃ AllPoints Df := (Equiv.ofBijective _ hasg).trans
      (Equiv.ofBijective p hp).symm
  exact ⟨ee, fun j ↦ hloc (ee j) (D.point j) (Equiv.ofBijective_apply_symm_apply p hp _)⟩

/-! ### Charts and measures of concrete members -/

/-- Transfer of a cell law through a single coordinate chart: if a chart covers the set `X` and the
type event in `X` agrees up to a null set with a set of measure given by the law, then the
coefficient measure of the polynomial type event equals the law density, and `μ X = q⁻ʳ`. -/
theorem chart_cell_law_generic (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (htop : IsAdic (maximalIdeal O)) (pi : O)
    (R : Type) [CommRing R] [Algebra O R] [MeasurableSpace (Ideal R)] (r : ℕ) (f : R)
    (b : Fin r → R) (hmeas : Measurable (coordinateIdeal pi f b))
    (X : Set (Ideal R)) (hcell : ∀ z : Fin r → O, coordinateIdeal pi f b z ∈ X)
    (μ : Measure (Ideal R)) (hμ : μ = (((Nat.card (ResidueField O)) : ℝ≥0∞)⁻¹ ^ r) •
    (coefficientMeasure O r).map (coordinateIdeal pi f b)) (htype : ∀ (z : Fin r → O)
    (σ : FactorType), HasAlgebraType O (R ⧸ coordinateIdeal pi f b z) σ ↔ HasPolynomialTypeF O
    (monicPolynomial O (pi • z)) σ) (σ : FactorType) (F N : Set (Ideal R)) (hFm : MeasurableSet F)
    (hFE : F ⊆ {J | J ∈ X ∧ HasAlgebraType O (R ⧸ J) σ}) (hEF :
    {J | J ∈ X ∧ HasAlgebraType O (R ⧸ J) σ} ⊆ F ∪ N) (hN : μ N = 0)
    (hF : μ F = densityValue (lawCoeff (stateLaw (State.single 1 r)) σ) (Nat.card (ResidueField O))
    * μ X) :
    coefficientMeasure O r {z : Fin r → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} =
      densityValue (lawCoeff (stateLaw (State.single 1 r)) σ) (Nat.card (ResidueField O)) ∧ μ X =
      ((Nat.card (ResidueField O)) : ℝ≥0∞)⁻¹ ^ r := by
  set c := coordinateIdeal pi f b with hc
  set ν := coefficientMeasure O r with hν
  set q : ℝ≥0∞ := ((Nat.card (ResidueField O)) : ℝ≥0∞) with hq
  have := coefficient_measure_probability O htop r
  have hq0 : q ≠ 0 := by
    rw [hq]; exact_mod_cast (Nat.card_pos (α := ResidueField O)).ne'
  have hk0 : q⁻¹ ^ r ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  have hkt : q⁻¹ ^ r ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hq0)
  have hpreX : c ⁻¹' X = Set.univ := Set.eq_univ_of_forall hcell
  have hmapX : (ν.map c) X = 1 := by
    apply le_antisymm
    · calc (ν.map c) X ≤ (ν.map c) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by rw [Measure.map_apply hmeas MeasurableSet.univ]; simp
    · calc (1 : ℝ≥0∞) = ν (c ⁻¹' X) := by rw [hpreX]; simp
        _ ≤ (ν.map c) X := Measure.le_map_apply hmeas.aemeasurable _
  have hX : μ X = q⁻¹ ^ r := by
    rw [hμ, Measure.smul_apply, hmapX, smul_eq_mul, mul_one]
  refine ⟨?_, hX⟩
  have hpreE : c ⁻¹' {J | J ∈ X ∧ HasAlgebraType O (R ⧸ J) σ}
      = {z : Fin r → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} := by
    ext z; simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨fun h => (htype z σ).1 h.2, fun h => ⟨hcell z, (htype z σ).2 h⟩⟩
  have hNnull : ν (c ⁻¹' N) = 0 := by
    have h1 : (ν.map c) N = 0 := by
      rw [hμ, Measure.smul_apply, smul_eq_mul] at hN
      exact (mul_eq_zero.1 hN).resolve_left hk0
    exact le_antisymm (h1 ▸ Measure.le_map_apply hmeas.aemeasurable _) (zero_le)
  have hEq : ν (c ⁻¹' {J | J ∈ X ∧ HasAlgebraType O (R ⧸ J) σ}) = ν (c ⁻¹' F) := by
    apply le_antisymm
    · calc _ ≤ ν (c ⁻¹' F ∪ c ⁻¹' N) := by
            rw [← Set.preimage_union]; exact measure_mono (Set.preimage_mono hEF)
        _ ≤ ν (c ⁻¹' F) + ν (c ⁻¹' N) := measure_union_le _ _
        _ = ν (c ⁻¹' F) := by rw [hNnull, add_zero]
    · exact measure_mono (Set.preimage_mono hFE)
  rw [← hpreE, hEq]
  rw [hX, hμ, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hmeas hFm, mul_comm] at hF
  exact (ENNReal.mul_left_inj hk0 hkt).1 hF

/-- The coefficient Haar measure on `O^r` is the product of the coefficient measure on `O`,
transported along `O^1 ≃ O`, which is a homeomorphic measurable equivalence. -/
theorem coefficient_measure_pi_one (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (htop : IsAdic (maximalIdeal O)) (pi : O)
    (hpi : Irreducible pi) (r : ℕ) [SigmaFinite ((coefficientMeasure O 1).map
    (LinearEquiv.funUnique (Fin 1) O O))] :
    coefficientMeasure O r = Measure.pi (fun _ : Fin r => (coefficientMeasure O 1).map
      (LinearEquiv.funUnique (Fin 1) O O)) ∧ IsProbabilityMeasure
      ((coefficientMeasure O 1).map (LinearEquiv.funUnique (Fin 1) O O)) ∧ Continuous
      (LinearEquiv.funUnique (Fin 1) O O) ∧ Continuous (LinearEquiv.funUnique (Fin 1) O O).symm ∧
      Measurable (LinearEquiv.funUnique (Fin 1) O O) ∧ Measurable
      (LinearEquiv.funUnique (Fin 1) O O).symm := by
  have hc : Continuous (LinearEquiv.funUnique (Fin 1) O O) := continuous_apply _
  have hc' : Continuous (LinearEquiv.funUnique (Fin 1) O O).symm := continuous_pi
      (fun _ => continuous_id)
  have hm : Measurable (LinearEquiv.funUnique (Fin 1) O O) := hc.measurable
  have hm' : Measurable (LinearEquiv.funUnique (Fin 1) O O).symm := hc'.measurable
  obtain ⟨-, h1, h2, -, -⟩ := coefficient_space_strict_instances O htop pi hpi 1
  obtain ⟨-, h3, h4, -, -⟩ := coefficient_space_strict_instances O htop pi hpi r
  have hν : Measure.IsAddHaarMeasure ((coefficientMeasure O 1).map
      (LinearEquiv.funUnique (Fin 1) O O)) :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure (coefficientMeasure O 1)
      (LinearEquiv.funUnique (Fin 1) O O).toAddMonoidHom hc (LinearEquiv.funUnique (Fin 1) O
          O).surjective
  have hp : IsProbabilityMeasure ((coefficientMeasure O 1).map
      (LinearEquiv.funUnique (Fin 1) O O)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  refine ⟨?_, hp, hc, hc', hm, hm'⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The division-coordinate module `O^deg × R` of a concrete member is `π`-adically complete. -/
theorem concrete_member_division_module_isAdicComplete (m : ConcreteMember) :
    IsAdicComplete (Ideal.span {m.toMeasured.S.pi})
      ((Fin m.toMeasured.s.degree → m.toMeasured.O) × m.toMeasured.R) := by
  change IsAdicComplete (Ideal.span {m.S.pi}) ((Fin m.s.degree → m.O) × ConcreteSurface m.O m.pi
    m.u m.a m.b)
  rw [m.hS_pi]
  exact division_coordinate_module_isAdicComplete m.O m.pi m.hpi m.u m.a m.b m.ha _

/-- Each chart of the atlas of a concrete member is an injective measurable map onto its
residue cell. -/
theorem concrete_member_charts (m : ConcreteMember) (i : m.atlas.ι) :
    Function.Injective (coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b) ∧ Set.range
      (coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b) = residueIdealCell
      (algebraMap m.O m.R m.S.pi) (m.atlas.chart i).f ∧ @Measurable (Fin m.s.degree → m.O)
      (Ideal m.R) inferInstance (idealChartSigma m.O m.R m.S.pi)
      (coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b) := by
  obtain ⟨hp0, hpm⟩ := surface_vertical_parameter m.O m.R m.S
  have : IsAdicComplete (Ideal.span {m.S.pi}) ((Fin m.s.degree → m.O) × m.R) :=
    concrete_member_division_module_isAdicComplete m
  have h1 := coordinate_ideal_cell_bijection m.O m.R m.s.degree m.S.pi
    (m.atlas.chart i).b (m.atlas.chart i).E hp0 hpm (m.atlas.chart i).f
    (m.atlas.chart i).division (m.atlas.chart i).regular
  exact ⟨h1.1, h1.2, coordinate_ideal_measurable_chart_sigma m.O m.htop m.R m.S.pi
    m.toMeasured.S.pi_irreducible hp0 hpm _ _ _ (m.atlas.chart i).isDivisionChart⟩

/-- The fixed-tangent cells of a concrete member are measurable. -/
theorem concrete_member_cell_measurable (m : ConcreteMember) (c : m.toMeasured.cellIndex) :
    MeasurableSet (m.toMeasured.cell c) := by
  have hcov := m.atlas.cover
  have hsub : m.toMeasured.cell c ⊆ ⋃ i, Set.range (coordinateIdeal (O := m.O) (R := m.R) m.S.pi
      (m.atlas.chart i).f (m.atlas.chart i).b) := by
    intro J hJ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov.subset hJ.1)
    exact Set.mem_iUnion.2 ⟨i, (Set.ext_iff.1 (concrete_member_charts m i).2.1 J).2 hi⟩
  rw [← Set.inter_eq_left.2 hsub, Set.inter_iUnion]
  refine MeasurableSet.iUnion fun i => ?_
  have hirr : Irreducible m.S.pi := m.toMeasured.S.pi_irreducible
  obtain ⟨reps, hreps⟩ := coordinate_coset_representatives_exist m.O m.S.pi hirr m.s.degree
      (m.toMeasured.cellDegree c)
  have hmax : Ideal.span {m.S.pi} = maximalIdeal m.O := (hirr.maximalIdeal_eq).symm
  have hb := finite_coordinate_borel_cylinders m.O (maximalIdeal m.O) m.htop m.s.degree
  have hcoset : ∀ z₀ : Fin m.s.degree → m.O, MeasurableSet (coordinateCoset m.S.pi
      (m.toMeasured.cellDegree c) z₀) := by
    intro z₀
    have h2 : @MeasurableSet _ (adicCylinderSpace (maximalIdeal m.O) (Fin m.s.degree → m.O))
        (coordinateCoset m.S.pi (m.toMeasured.cellDegree c) z₀) := by
      rw [← hmax]
      exact MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨_, z₀, rfl⟩)
    rw [← hb] at h2
    exact h2
  have hf : Ideal.span {(m.atlas.chart i).f} ∈ surfaceStateSet m.O m.R m.S m.s :=
    hcov.symm.subset (Set.mem_iUnion.2 ⟨i, ⟨_, rfl⟩, by rw [Ideal.map_span]; simp⟩)
  exact fixed_tangent_cell_chart_measurable m.O m.R m.S m.s m.s.degree (m.atlas.chart i).b
    (m.atlas.chart i).f hf (concrete_member_charts m i).1 (m.atlas.chart i).isDivisionChart _
    (m.toMeasured.cellDegree c) le_rfl _ reps hreps hcoset

/-- Every admissible shape is realized: the concrete surface carries surface data with the concrete
parameters and an ideal atlas of the state set. -/
theorem concrete_member_data_exists (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a) (s : State)
    (hs : StateShape a b s) :
    ∃ (_ : IsDomain (ConcreteSurface O pi u a b)) (_ : IsRegularLocalRing
      (ConcreteSurface O pi u a b)) (S : SurfaceData O (ConcreteSurface O pi u a b)), S.pi = pi ∧
      S.t = surfaceT O pi u a b ∧ S.x = surfaceX O pi u a b ∧ S.a = a ∧ S.b = b ∧ Nonempty
      (IdealAtlas O (ConcreteSurface O pi u a b) S.pi s.degree
      (surfaceStateSet O (ConcreteSurface O pi u a b) S s)) := by
  obtain ⟨hD, hR, S, hSpi, hSt, hSx, -, hSa, hSb⟩ :=
    concrete_surface_data_exists_unconditional O pi hpi u a b ha
  obtain ⟨e, he⟩ := concrete_surface_special_fiber_equiv O pi hpi u a b
  refine ⟨hD, hR, S, hSpi, hSt, hSx, hSa, hSb, ?_⟩
  cases s with
  | single a' c =>
    obtain ⟨h1, h2, h3⟩ := hs
    subst h1 h2
    obtain ⟨A, -⟩ := concrete_single_state_atlas_exists O pi hpi u a' ha S hSt hSa hSb e he c
        h3
    rw [hSpi]
    exact ⟨A⟩
  | crossing a' b' c h =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hs
    subst h1 h2
    obtain ⟨A, -⟩ := concrete_crossing_state_atlas_exists O pi hpi u a' b' ha h3 S hSt hSx hSa
        hSb e he c h h4 h5
    rw [hSpi]
    exact ⟨A⟩

/-- The state set of a concrete member is measurable. -/
theorem concrete_member_stateSet_measurable (m : ConcreteMember) :
    MeasurableSet m.toMeasured.stateSet := by
  have h : m.toMeasured.stateSet = ⋃ i, Set.range (coordinateIdeal m.S.pi (m.atlas.chart i).f
      (m.atlas.chart i).b) := by
    refine (m.atlas.cover).trans ?_
    exact Set.iUnion_congr fun i => (concrete_member_charts m i).2.1.symm
  rw [h]
  have : Fintype m.atlas.ι := m.atlas.fin
  have : Countable m.atlas.ι := Finite.to_countable
  refine @MeasurableSet.iUnion _ _ (idealChartSigma m.O m.R m.S.pi) _ _ fun i => ?_
  rw [← Set.image_univ]
  exact chart_image_measurable_chart_sigma m.O m.R m.S.pi _ _ _
    (m.atlas.chart i).isDivisionChart _ MeasurableSet.univ

/-- The state measure of a concrete member is finite and concentrated on the state set. -/
theorem concrete_member_measure_finite_support (m : ConcreteMember) :
    IsFiniteMeasure m.toMeasured.μ ∧ ∀ X : Set (Ideal m.toMeasured.R), m.toMeasured.μ X =
      m.toMeasured.μ (X ∩ m.toMeasured.stateSet) := by
  have hS := concrete_member_stateSet_measurable m
  have hnull : m.toMeasured.μ m.toMeasured.stateSetᶜ = 0 := by
    change stateMeasure _ _ _ _ _ _ _ = 0
    unfold stateMeasure
    rw [Measure.smul_apply, Measure.finsetSum_apply]
    simp only [smul_eq_mul]
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    obtain ⟨-, hr, hm⟩ := concrete_member_charts m i
    unfold chartMeasure
    refine (Measure.map_apply hm hS.compl).trans ?_
    have : (coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b) ⁻¹'
        m.toMeasured.stateSetᶜ = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx ↦
        hx (m.atlas.cover.symm.subset (Set.mem_iUnion.2 ⟨i, ?_⟩))
      rw [← hr]; exact ⟨x, rfl⟩
    exact (congrArg (coefficientMeasure m.O m.s.degree) this).trans measure_empty
  refine ⟨⟨?_⟩, ?_⟩
  · let inst : MeasurableSpace (Ideal m.R) := m.toMeasured.measurableSpaceIdeal
    have h := state_measure_total_mass m.O m.R m.htop m.S.pi m.s.degree _ m.atlas
      (fun i => (concrete_member_charts m i).2.2)
    refine h.trans_lt ?_
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.pow_lt_top
      (ENNReal.inv_lt_top.2 (by exact_mod_cast Nat.card_pos (α := ResidueField m.O))))
  · intro X
    rw [← measure_inter_add_sdiff X hS, measure_mono_null (Set.sdiff_subset_compl _ _) hnull,
        add_zero]

/-! ### Generators of state ideals -/

/-- Multiplication by the parameter `t` of a concrete member is injective. -/
theorem concrete_member_mul_t_injective {m : ConcreteMember} {e : m.toMeasured.R}
    (he : e = m.toMeasured.S.t) : Function.Injective (fun z : m.toMeasured.R => e * z) := by
  have h := (concrete_surface_equiv_regular_pair m.R m.O m.pi m.hpi m.u m.a m.b m.ha
    (RingEquiv.refl _)).2.2
  rw [he]
  change Function.Injective (fun z : m.R => m.S.t * z)
  rwa [m.hS_t]

/-- The degree of the state of a concrete member is positive. -/
theorem concrete_member_one_le_degree (m : ConcreteMember) : 1 ≤ m.toMeasured.s.degree := by
  have hv : m.toMeasured.s.Valid := m.toMeasured.valid
  revert hv
  cases m.toMeasured.s with
  | single a c => exact fun hv => Nat.mul_pos hv.1 hv.2
  | crossing a b c h =>
    intro hv; have := Nat.mul_pos hv.1 hv.2.2.1; simp only [State.degree]; omega

/-- A generator of an ideal of the state set meets `T = 0` with `O`-length the first contact
of the state. -/
theorem concrete_member_state_generator_contact_length (m : ConcreteMember) (g : m.toMeasured.R)
    (hg : Ideal.span {g} ∈ m.toMeasured.stateSet) :
    Module.length m.toMeasured.O (m.toMeasured.R ⧸ (Ideal.span {g} ⊔ Ideal.span {m.toMeasured.S.t}))
      = (m.toMeasured.s.firstContact : ℕ∞) := by
  have hfin : Finite (ResidueField m.toMeasured.R) :=
    Finite.of_equiv _ m.toMeasured.S.residueEquiv.toEquiv
  have hcard : Nat.card (ResidueField m.toMeasured.R) =
      Nat.card (ResidueField m.toMeasured.O) ^ 1 := by
    rw [pow_one]; exact (Nat.card_congr m.toMeasured.S.residueEquiv.toEquiv).symm
  obtain ⟨_, _, hc⟩ := hg
  have key : Module.length m.toMeasured.R (m.toMeasured.R ⧸ (Ideal.span {g} ⊔ Ideal.span
      {m.toMeasured.S.t})) = (m.toMeasured.s.firstContact : ℕ∞) := by
    generalize m.toMeasured.s = s at hc ⊢
    cases s with
    | single a c => exact hc.2.2
    | crossing a b c h => exact hc.2.2.1
  have := length_scaling_of_residue_card m.toMeasured.O m.toMeasured.R 1 hcard
    (m.toMeasured.R ⧸ (Ideal.span {g} ⊔ Ideal.span {m.toMeasured.S.t})) m.toMeasured.s.firstContact
        key
  simpa using this

/-- A generator of an ideal of the state set is a nonzero nonunit that is regular modulo `π`. -/
theorem concrete_member_state_generator_regular (m : ConcreteMember) (g : m.toMeasured.R)
    (hg : Ideal.span {g} ∈ m.toMeasured.stateSet) :
    g ≠ 0 ∧ ¬ IsUnit g ∧ Function.Injective (fun y : m.toMeasured.R ⧸ Ideal.span
      {(algebraMap m.toMeasured.O m.toMeasured.R m.toMeasured.S.pi)} => y * Ideal.Quotient.mk
      (Ideal.span {(algebraMap m.toMeasured.O m.toMeasured.R m.toMeasured.S.pi)}) g) := by
  have hprop := surface_state_ideal_proper _ _ m.toMeasured.S m.toMeasured.s _ hg
  have hnu : ¬ IsUnit g := fun h => hprop (Ideal.span_singleton_eq_top.mpr h)
  have hpi := surface_vertical_parameter m.toMeasured.O m.toMeasured.R m.toMeasured.S
  have hcov := m.toMeasured.atlas.cover
  have hg' : Ideal.span {g} ∈ ⋃ i, residueIdealCell (algebraMap m.toMeasured.O m.toMeasured.R
      m.toMeasured.S.pi) (m.toMeasured.atlas.chart i).f := by
    rw [← hcov]; exact hg
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg'
  set mk := Ideal.Quotient.mk (Ideal.span {(algebraMap m.toMeasured.O m.toMeasured.R
      m.toMeasured.S.pi)}) with hmk
  have h1 : Ideal.span {mk (m.toMeasured.atlas.chart i).f} = Ideal.span {mk g} := by
    rw [← principal_ideal_image _ _ mk g]
    exact hi.2.symm
  obtain ⟨u, hu⟩ := regular_principal_generators_associated _ _ _
    (m.toMeasured.atlas.chart i).regular h1
  have hreg : Function.Injective (fun y : m.toMeasured.R ⧸ Ideal.span
      {(algebraMap m.toMeasured.O m.toMeasured.R m.toMeasured.S.pi)} => y * mk g) := by
    intro a b hab
    simp only [hu] at hab
    have : (a * ↑u) * mk (m.toMeasured.atlas.chart i).f = (b * ↑u) * mk
        (m.toMeasured.atlas.chart i).f := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hab
    have := (m.toMeasured.atlas.chart i).regular this
    exact (IsUnit.mul_left_inj u.isUnit).mp this
  refine ⟨fun h0 ↦ ?_, hnu, hreg⟩
  have h01 : (1 : m.toMeasured.R ⧸ Ideal.span {algebraMap m.toMeasured.O m.toMeasured.R
      m.toMeasured.S.pi})
      = 0 := hreg (by simp [h0])
  exact (mem_maximalIdeal _).mp hpi.2
    (Ideal.span_singleton_eq_top.mp (Ideal.Quotient.zero_eq_one_iff.mp h01.symm))

/-- A division chart centred at a generator of an ideal of the state set is injective, lands in
the state set, and scales the coefficient measure by `q^(-deg s)`. -/
theorem concrete_member_division_chart_measure (m : ConcreteMember) (g : m.toMeasured.R)
    (hg : Ideal.span {g} ∈ m.toMeasured.stateSet) (bc : Fin m.toMeasured.s.degree → m.toMeasured.R)
    (E : m.toMeasured.R ≃ₗ[m.toMeasured.O] ((Fin m.toMeasured.s.degree → m.toMeasured.O) ×
    m.toMeasured.R)) (hE : ∀ w, E.symm w = divisionMap g bc w) :
    Function.Injective (coordinateIdeal m.toMeasured.S.pi g bc) ∧ Set.range
      (coordinateIdeal m.toMeasured.S.pi g bc) ⊆ m.toMeasured.stateSet ∧ ∀ S : Set
      (Fin m.toMeasured.s.degree → m.toMeasured.O), MeasurableSet S → m.toMeasured.μ
      (coordinateIdeal m.toMeasured.S.pi g bc '' S) = (m.toMeasured.q : ℝ≥0∞)⁻¹ ^
      m.toMeasured.s.degree * coefficientMeasure m.toMeasured.O m.toMeasured.s.degree S := by
  classical
  have := concrete_member_division_module_isAdicComplete m
  obtain ⟨hp0, hpm⟩ := surface_vertical_parameter m.toMeasured.O m.toMeasured.R m.toMeasured.S
  obtain ⟨-, -, hreg⟩ := concrete_member_state_generator_regular m g hg
  have hch : IsDivisionChart _ _ m.toMeasured.S.pi g bc := ⟨⟨E, hE⟩, hreg⟩
  have hinj : Function.Injective (coordinateIdeal m.toMeasured.S.pi g bc) :=
    coordinate_ideal_injective _ _ _ _ bc E hp0 hpm g hE hreg
  -- the atlas chart containing span {g}
  obtain ⟨i, hi⟩ : ∃ i, Ideal.span {g} ∈ _ := by
    change Ideal.span {g} ∈ surfaceStateSet _ _ _ _ at hg
    rwa [m.toMeasured.atlas.cover, Set.mem_iUnion] at hg
  have hres : Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap m.toMeasured.O m.toMeasured.R
      m.toMeasured.S.pi}) (m.toMeasured.atlas.chart i).f}
      = Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap m.toMeasured.O m.toMeasured.R
          m.toMeasured.S.pi}) g} := by
    rw [← hi.2, principal_ideal_image]
  have hcell : ∀ z, coordinateIdeal m.toMeasured.S.pi g bc z ∈
      residueIdealCell (algebraMap m.toMeasured.O m.toMeasured.R m.toMeasured.S.pi)
          (m.toMeasured.atlas.chart i).f := fun z =>
    have := coordinate_ideal_in_residue_cell _ _ _ m.toMeasured.S.pi bc g z
    ⟨this.1, this.2.trans hres.symm⟩
  have hrange : Set.range (coordinateIdeal m.toMeasured.S.pi g bc) ⊆ m.toMeasured.stateSet := by
    rintro _ ⟨z, rfl⟩
    change _ ∈ surfaceStateSet _ _ _ _
    rw [m.toMeasured.atlas.cover, Set.mem_iUnion]
    exact ⟨i, hcell z⟩
  refine ⟨hinj, hrange, ?_⟩
  intro S hS
  set c := m.toMeasured.atlas.chart i with hc_def
  obtain ⟨g', c', F, h0, hF, hfg, hreg', hcoord⟩ :=
    division_chart_same_cell_recenter _ _ m.toMeasured.S.pi hpm _ c.f g c.b bc
      c.isDivisionChart hch hres
  have hmeas' := coordinate_ideal_measurable_chart_sigma _ m.toMeasured.htop _ _
    m.toMeasured.S.pi_irreducible hp0 hpm _ g' c' ⟨⟨F, hF⟩, hreg'⟩
  have hmeasΨ := coordinate_ideal_measurable_chart_sigma _ m.toMeasured.htop _ _
    m.toMeasured.S.pi_irreducible hp0 hpm _ g bc hch
  have hpush : (coefficientMeasure m.toMeasured.O m.toMeasured.s.degree).map
      (coordinateIdeal m.toMeasured.S.pi c.f c.b)
      = (coefficientMeasure m.toMeasured.O m.toMeasured.s.degree).map
          (coordinateIdeal m.toMeasured.S.pi g bc) := by
    rw [ideal_chart_pushforward_independent _ _ _ _ c.b c.E hp0 hpm c.f c.division c.regular g' c' F
      hF hreg' h0 hfg m.toMeasured.htop m.toMeasured.S.pi_irreducible hmeas']
    exact congrArg (Measure.map · _) (funext fun z => (hcoord z).symm)
  have hSm : MeasurableSet (coordinateIdeal m.toMeasured.S.pi g bc '' S) :=
    chart_image_measurable_chart_sigma _ _ _ _ g bc hch S hS
  have hsum : ∀ k, chartMeasure m.toMeasured.O m.toMeasured.R m.toMeasured.S.pi
      m.toMeasured.s.degree
      (m.toMeasured.atlas.chart k) (coordinateIdeal m.toMeasured.S.pi g bc '' S)
      = if k = i then coefficientMeasure m.toMeasured.O m.toMeasured.s.degree S else 0 := by
    intro k
    obtain ⟨-, hrk, hmk⟩ := concrete_member_charts m k
    unfold chartMeasure
    split_ifs with hk
    · subst hk
      rw [hpush, Measure.map_apply hmeasΨ hSm, Set.preimage_image_eq _ hinj]
    · rw [Measure.map_apply (by exact hmk) hSm]
      convert measure_empty (μ := coefficientMeasure m.toMeasured.O m.toMeasured.s.degree)
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨w, -, hw⟩
      exact Set.disjoint_left.mp (m.toMeasured.atlas.disjoint hk) (hrk ▸ Set.mem_range_self z)
        (hw ▸ hcell w)
  change stateMeasure m.toMeasured.O m.toMeasured.R m.toMeasured.S.pi m.toMeasured.s.degree
      m.toMeasured.q
    m.toMeasured.atlas _ = _
  unfold stateMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  simp only [hsum, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A generator `g` of an ideal of the state set and the parameter `T` form a regular sequence
in both orders. -/
theorem concrete_member_state_generator_transverse (m : ConcreteMember) (g : m.toMeasured.R)
    (hg : Ideal.span {g} ∈ m.toMeasured.stateSet) :
    Function.Injective (fun w : m.toMeasured.R ⧸ Ideal.span {m.toMeasured.S.t} => Ideal.Quotient.mk
      (Ideal.span {m.toMeasured.S.t}) g * w) ∧ Function.Injective
      (fun y : m.toMeasured.R ⧸ Ideal.span {g} => Ideal.Quotient.mk (Ideal.span {g})
      m.toMeasured.S.t * y) := by
  change m.R at g
  -- finite contact
  have hfin : idealContact m.R (Ideal.span {g}) (surfaceT m.O m.pi m.u m.a m.b) ≠ ⊤ := by
    obtain ⟨_, _, hs⟩ := hg
    rw [← m.hS_t]
    revert hs
    cases m.toMeasured.s with
    | single a c => rintro ⟨_, _, h⟩; exact fun h' ↦ ENat.natCast_ne_top c (h.symm.trans h')
    | crossing a b c _ =>
      rintro ⟨_, _, h, _⟩; exact fun h' ↦ ENat.natCast_ne_top c (h.symm.trans h')
  obtain ⟨q, -⟩ := concrete_surface_quotient_T_equiv m.O m.pi m.hpi m.u m.a m.b m.ha
  have h878 := concrete_surface_equiv_curve_length_and_regular m.R m.O m.pi m.u m.a m.b
    (RingEquiv.refl _) q g
  have h872 := (concrete_surface_equiv_regular_pair m.R m.O m.pi m.hpi m.u m.a m.b m.ha
    (RingEquiv.refl _)).2.2
  rw [show (RingEquiv.refl m.R).symm = RingEquiv.refl m.R from rfl] at h878 h872
  simp only [RingEquiv.refl_apply] at h878 h872
  set t : m.R := surfaceT m.O m.pi m.u m.a m.b with ht
  have h1 : Function.Injective (fun w : m.R ⧸ Ideal.span {t} =>
      Ideal.Quotient.mk (Ideal.span {t}) g * w) := by
    refine h878.2.mpr ?_
    intro h0
    apply hfin
    unfold idealContact
    rw [ideal_contact_generator, contact]
    exact h878.1.trans (by rw [h0, PowerSeries.order_zero])
  have hker : ∀ y : m.R ⧸ Ideal.span {g}, Ideal.Quotient.mk (Ideal.span {g}) t * y = 0 → y = 0 := by
    intro y hy
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hy
    obtain ⟨r, hr⟩ := hy
    have hr0 : Ideal.Quotient.mk (Ideal.span {t}) g * Ideal.Quotient.mk (Ideal.span {t}) r = 0 := by
      rw [← map_mul, mul_comm, hr, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)
    have hr1 : Ideal.Quotient.mk (Ideal.span {t}) r = 0 := h1 (by simp only; linear_combination hr0)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hr1
    obtain ⟨r', rfl⟩ := hr1
    have : h = g * r' := by
      apply h872
      change t * h = t * (g * r')
      rw [← hr]; ring
    rw [Ideal.Quotient.eq_zero_iff_mem, this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)
  have h2 : Function.Injective (fun y : m.R ⧸ Ideal.span {g} =>
      Ideal.Quotient.mk (Ideal.span {g}) t * y) := fun a b hab =>
    sub_eq_zero.mp (hker (a - b) (by simp only at hab; linear_combination hab))
  change Function.Injective (fun w : m.R ⧸ Ideal.span {m.S.t} =>
      Ideal.Quotient.mk (Ideal.span {m.S.t}) g * w) ∧
    Function.Injective (fun y : m.R ⧸ Ideal.span {g} =>
      Ideal.Quotient.mk (Ideal.span {g}) m.S.t * y)
  rw [m.hS_t]
  exact ⟨h1, h2⟩

/-- A curve on a concrete surface with crossing contacts `(c, h)` has free curve order of rank
`a c + b h`. -/
private theorem concrete_surface_crossing_curve_free (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (pi : O) (hpi : Irreducible pi)
    (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (f : ConcreteSurface O pi u a b)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
    ≃+* SpecialFiber (ResidueField O) a b) (c h : ℕ) (hc : 0 < c)
    (hcontact : contact (e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b)
    pi}) f)) (fiberT (ResidueField O) a b) = c) (hxcontact : contact
    (e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}) f))
    (fiberX (ResidueField O) a b) = h) :
    Module.Free O (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) ∧ Module.Finite O
      (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) ∧ Module.finrank O
      (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) = a*c+b*h := by
  have hreg := special_fiber_crossing_contact_regular _ a b c h ha hb _ hcontact hxcontact
  have hinj := concrete_surface_residue_regular_of_special_fiber O pi u a b f e hreg
  have hlen := crossing_special_fiber_length _ a b c h ha hb _ hcontact hxcontact
  have hlen2 := concrete_surface_special_fiber_length_transport O pi u a b f e
  have hfu : ¬ IsUnit f := by
    intro hu
    have hu' : IsUnit (e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b)
        pi}) f)) :=
      (hu.map (Ideal.Quotient.mk _)).map e
    have h1 : Ideal.span {e (Ideal.Quotient.mk (Ideal.span {algebraMap O
        (ConcreteSurface O pi u a b) pi}) f)} = ⊤ :=
      (Ideal.span_singleton_eq_top).2 hu'
    rw [h1] at hlen
    simp only [Module.length_eq_zero] at hlen
    have : a*c+b*h = 0 := by exact_mod_cast hlen.symm
    have := Nat.mul_pos ha hc
    omega
  exact concrete_surface_curve_free_of_length O pi hpi u a b ha f hinj (a*c+b*h)
      (hlen2.trans hlen)

private theorem single_curve_free_of_eq_zero (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (pi : O) (hpi : Irreducible pi)
    (u : (TwoSeries O)ˣ) (a b : ℕ) (hb : b = 0) (ha : 0 < a) (f : ConcreteSurface O pi u a b)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+*
      SpecialFiber (ResidueField O) a b) (c : ℕ) (hc : 0 < c)
    (hcontact : contact (e (Ideal.Quotient.mk
      (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}) f)) (fiberT (ResidueField O) a b)
      = c) :
    Module.Free O (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) ∧
    Module.Finite O (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) ∧
    Module.finrank O (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) = a * c := by
  subst hb
  exact concrete_surface_single_curve_free O pi hpi u a ha f e c hc hcontact

/-- The curve order `R/J` of an ideal `J` in the state set of a concrete member is a free `O`-module
of rank the degree of the state. -/
theorem concrete_member_curve_order_free (m : ConcreteMember) (J : Ideal m.R)
    (hJ : J ∈ m.toMeasured.stateSet) :
    Module.Free m.O (m.R ⧸ J) ∧ Module.Finite m.O (m.R ⧸ J) ∧ Module.finrank m.O (m.R ⧸ J) =
      m.s.degree := by
  obtain ⟨⟨f, rfl⟩, -, hmatch⟩ := hJ
  obtain ⟨e, he⟩ := concrete_surface_special_fiber_equiv m.O m.pi m.hpi m.u m.a m.b
  have hc := concrete_surface_contact_eq_special_fiber_contact m.O m.pi m.u m.a m.b m.ha e he
      f
  have hT : m.S.t = surfaceT m.O m.pi m.u m.a m.b := m.hS_t
  have hsh := m.shape
  have hmatch' : (match m.s with
    | .single a c => m.S.a = a ∧ m.S.b = 0 ∧ idealContact m.R (Ideal.span {f}) m.S.t = c
    | .crossing a b c h => m.S.a = a ∧ m.S.b = b ∧
      idealContact m.R (Ideal.span {f}) m.S.t = c ∧ idealContact m.R (Ideal.span {f}) m.S.x = h) :=
          hmatch
  revert hmatch' hsh
  generalize m.s = s
  intro hsh hmatch'
  cases s with
  | single a' c =>
    obtain ⟨rfl, hb, hc0⟩ := hsh
    exact single_curve_free_of_eq_zero m.O m.pi m.hpi m.u _ m.b hb m.ha f e c hc0
      (by rw [← hc.1, ← hT]; exact hmatch'.2.2)
  | crossing a' b' c h =>
    obtain ⟨rfl, rfl, hb, hc0, hh0⟩ := hsh
    exact concrete_surface_crossing_curve_free m.O m.pi m.hpi m.u _ _ m.ha hb f e c h hc0
      (by rw [← hc.1, ← hT]; exact hmatch'.2.2.1)
      (by rw [← hc.2 hb, ← m.hS_x]; exact hmatch'.2.2.2)

/-- Every generator of an ideal of the state set admits a division chart. -/
theorem concrete_member_state_generator_division (m : ConcreteMember) (g : m.toMeasured.R)
    (hg : Ideal.span {g} ∈ m.toMeasured.stateSet) :
    ∃ (bc : Fin m.toMeasured.s.degree → m.toMeasured.R) (E : m.toMeasured.R ≃ₗ[m.toMeasured.O]
      ((Fin m.toMeasured.s.degree → m.toMeasured.O) × m.toMeasured.R)), ∀ w, E.symm w = divisionMap
      g bc w := by
  obtain ⟨hF, hFin, hr⟩ := concrete_member_curve_order_free m _ hg
  have hg0 := (concrete_member_state_generator_regular m g hg).1
  have := m.instDomainR
  have : Module.Free m.toMeasured.O (m.toMeasured.R ⧸ Ideal.span {g}) := hF
  have : Module.Finite m.toMeasured.O (m.toMeasured.R ⧸ Ideal.span {g}) := hFin
  let B := Module.finBasisOfFinrankEq m.toMeasured.O (m.toMeasured.R ⧸ Ideal.span {g}) hr
  choose bc hbc using fun i => Ideal.Quotient.mk_surjective (B i)
  obtain ⟨E, hE⟩ := division_linear_equivalence m.toMeasured.O m.toMeasured.R m.toMeasured.s.degree
      g B bc hbc hg0
  exact ⟨bc, E, hE⟩

/-! ### Type additivity and the Čech connecting map -/

/-- Type additivity: if `R/J` embeds with finite-length cokernel into a product of algebras over
unramified extensions, then the type of `R/J` is the sum of the residue-scaled types. -/
theorem concrete_type_add_of_index_map (m : ConcreteMember) (n : ℕ) (mc : Fin n → ConcreteMember)
    [∀ j, Algebra m.O (mc j).O] [∀ j, Module.Finite m.O (mc j).O] [∀ j, Module.Free m.O (mc j).O]
    (δ : Fin n → ℕ) (hrank : ∀ j, Module.finrank m.O (mc j).O = δ j)
    (hpi : ∀ j, Irreducible (algebraMap m.O (mc j).O m.pi)) (J : Ideal m.R) (B : Fin n → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra m.O (B j)] [∀ j, Algebra (mc j).O (B j)]
    [∀ j, IsScalarTower m.O (mc j).O (B j)] [∀ j, Module.Finite (mc j).O (B j)]
    [∀ j, Module.Free (mc j).O (B j)] (ψ : (m.R ⧸ J) →ₐ[m.O] ∀ j, B j) (hψ : Function.Injective ψ)
    (ℓ : ℕ) (hlen : Module.length m.O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = (ℓ : ℕ∞))
    (τ : Fin n → FactorType) (hτ : ∀ j, HasAlgebraType (mc j).O (B j) (τ j)) :
    HasAlgebraType m.O (m.R ⧸ J) (∑ j, scaleType (δ j) (τ j)) := by
  have hdesc : ∀ j, HasAlgebraType m.O (B j) (scaleType (δ j) (τ j)) := fun j =>
    algebra_type_unramified_descent m.O (mc j).O (δ j) (hrank j) m.pi m.hpi
      (hpi j) (B j) (τ j) (hτ j)
  have hprod := algebra_type_pi m.O n B _ hdesc
  have hbij := baseChange_bijective_of_finite_cokernel m.O _ _
    ψ.toLinearMap hψ ℓ hlen
  let f := Algebra.TensorProduct.map (AlgHom.id (BaseField m.O) (BaseField m.O)) ψ
  have hf : ⇑f = ⇑(LinearMap.baseChange (BaseField m.O) ψ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [f, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hfb : Function.Bijective f := hf ▸ hbij
  exact algebra_type_of_generic_fibre_equiv m.O _ _
    (AlgEquiv.ofBijective f hfb) _ hprod

/-- A division chart is a measurable embedding for the intrinsic σ-algebra. -/
theorem coordinate_ideal_measurableEmbedding (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] (htop : IsAdic (maximalIdeal O))
    (R : Type) [CommRing R] [Algebra O R] [IsDomain R] [IsLocalRing R] (pi : O)
    (hpi : Irreducible pi) (hp0 : algebraMap O R pi ≠ 0) (hpm : algebraMap O R pi ∈ maximalIdeal R)
    (n : ℕ) (f : R) (b : Fin n → R) (hchart : IsDivisionChart O R pi f b)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] :
    @MeasurableEmbedding (Fin n → O) (Ideal R) inferInstance (idealChartSigma O R pi)
      (coordinateIdeal pi f b) := by
  obtain ⟨E, hE⟩ := hchart.1
  exact @MeasurableEmbedding.mk _ _ _ (idealChartSigma O R pi) _
    (coordinate_ideal_injective O R n pi b E hp0 hpm f hE hchart.2)
    (coordinate_ideal_measurable_chart_sigma O htop R pi hpi hp0 hpm n f b hchart)
    (fun S hS => chart_image_measurable_chart_sigma O R pi n f b hchart S hS)

/-- Two curve-section representatives of the same class modulo the curve ideal lattice have the
same connecting class. -/
private theorem connecting_class_eq_of_mkQ_eq (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
    (hregSwap : RegularParameterPair R x t) (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta d)) (hregF : Function.Injective
    (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j => Ideal.Quotient.mk
    ((Ideal.span {overlapException R t x})^j) ((algebraMap (BlowupChart R t x)
    (BlowupOverlap R t x)) (G.left j)) * c))
    (p p' : BlowupChart R t x × BlowupChart R x t) (c c' : BlowupOverlap R t x)
    (hc : fullCechDifferential R t x beta 0 p - (algebraMap (BlowupChart R t x)
      (BlowupOverlap R t x)) (G.left j) * c ∈ (Ideal.span {overlapException R t x})^j)
    (hc' : fullCechDifferential R t x beta 0 p' - (algebraMap (BlowupChart R t x)
      (BlowupOverlap R t x)) (G.left j) * c' ∈ (Ideal.span {overlapException R t x})^j)
    (hpp : (curveIdealLattice R t x beta G j).mkQ p = (curveIdealLattice R t x beta G j).mkQ p') :
    (LinearMap.range (finiteCechDifferential R t x beta d j h)).mkQ
        ((cechOutputLattice R t x j).mkQ c) =
      (LinearMap.range (finiteCechDifferential R t x beta d j h)).mkQ
        ((cechOutputLattice R t x j).mkQ c') := by
  have hmem : p - p' ∈ curveIdealLattice R t x beta G j := (Submodule.Quotient.eq _).1 hpp
  have hs := curve_ideal_lattice_le_sections R t x beta d G j hmem
  have hc2 : fullCechDifferential R t x beta 0 (p - p') - (algebraMap (BlowupChart R t x)
      (BlowupOverlap R t x)) (G.left j) * (c - c') ∈ (Ideal.span {overlapException R t x})^j := by
    convert Ideal.sub_mem _ hc hc' using 1
    simp only [map_sub, mul_sub]
    abel
  have := (curve_section_connecting_class_zero_iff R t x beta d G hreg hregSwap j h hregF
    (p - p') hs (c - c') hc2).2 ⟨0, by simpa using hmem⟩
  rwa [map_sub, map_sub, sub_eq_zero] at this

/-- Every curve section has a coefficient `c` with `D p - (left j) * c` in the `j`-th power of the
exceptional ideal of the overlap. -/
private theorem exists_connecting_coefficient (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) {d : ℕ} (G : GluedGenerators R t x beta d) (j : ℕ)
    (p : BlowupChart R t x × BlowupChart R x t) (hp : p ∈ curveSections R t x beta G j) :
    ∃ c, fullCechDifferential R t x beta 0 p - (algebraMap (BlowupChart R t x)
      (BlowupOverlap R t x)) (G.left j) * c ∈ (Ideal.span {overlapException R t x})^j := by
  have hp' : fullCechDifferential R t x beta 0 p ∈ overlapCurveIdeal R t x beta G j := hp
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hp'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  exact ⟨c, by convert hz using 1; rw [← hyz, mul_comm]; abel⟩

/-- The connecting map from curve sections to the Čech cokernel, characterized on
representatives. -/
private theorem exists_connecting_linear_map (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (t x : R) (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
    (hregSwap : RegularParameterPair R x t) (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta d)) (hregF : Function.Injective
    (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j => Ideal.Quotient.mk
    ((Ideal.span {overlapException R t x})^j) ((algebraMap (BlowupChart R t x)
    (BlowupOverlap R t x)) (G.left j)) * c)) :
    ∃ δ : curveSectionsQuot R t x beta G j →ₗ[O] (CechLevelOutput R t x j ⧸ LinearMap.range
      (finiteCechDifferential R t x beta d j h)), ∀ (p : BlowupChart R t x × BlowupChart R x t)
      (hp : p ∈ curveSections R t x beta G j) (c : BlowupOverlap R t x), fullCechDifferential R t x
      beta 0 p - (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * c ∈
      (Ideal.span {overlapException R t x})^j → δ ⟨(curveIdealLattice R t x beta G j).mkQ p,
      Submodule.mem_map_of_mem hp⟩ = (LinearMap.range (finiteCechDifferential R t x beta d j h)).mkQ
      ((cechOutputLattice R t x j).mkQ c) := by
  let L := curveIdealLattice R t x beta G j
  let S := curveSections R t x beta G j
  let I := (Ideal.span {overlapException R t x})^j
  let Q := LinearMap.range (finiteCechDifferential R t x beta d j h)
  let a := (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)
  let D := fullCechDifferential R t x beta 0
  let cl : BlowupOverlap R t x → (CechLevelOutput R t x j ⧸ Q) :=
    fun c => Q.mkQ ((cechOutputLattice R t x j).mkQ c)
  have cl_add : ∀ c c', cl (c + c') = cl c + cl c' := fun c c' => by simp only [cl, map_add]
  have cl_smul : ∀ (o : O) c, cl (o • c) = o • cl c := fun o c => by
    simp only [cl, LinearMap.map_smul_of_tower]
  have exist : ∀ p ∈ S, ∃ c, D p - a * c ∈ I := exists_connecting_coefficient R t x beta G j
  have rep : ∀ u : curveSectionsQuot R t x beta G j, ∃ p ∈ S, L.mkQ p = u :=
    fun u => Submodule.mem_map.1 u.2
  let f : curveSectionsQuot R t x beta G j → (CechLevelOutput R t x j ⧸ Q) := fun u =>
    cl (Classical.choose (exist _ (Classical.choose_spec (rep u)).1))
  have spec : ∀ (u : curveSectionsQuot R t x beta G j) p, p ∈ S → ∀ c, D p - a * c ∈ I → L.mkQ p =
      (u : _) → f u = cl c := by
    intro u p hp c hc hpu
    have h1 := Classical.choose_spec (rep u)
    have h2 := Classical.choose_spec (exist _ h1.1)
    exact connecting_class_eq_of_mkQ_eq R t x hreg beta hregSwap d G j h hregF _ p _ c h2 hc
      (h1.2.trans hpu.symm)
  clear_value f
  have hadd : ∀ u v, f (u + v) = f u + f v := by
    intro u v
    obtain ⟨p, hp, hpu⟩ := rep u
    obtain ⟨q, hq, hqv⟩ := rep v
    obtain ⟨c, hc⟩ := exist p hp
    obtain ⟨c', hc'⟩ := exist q hq
    rw [spec u p hp c hc hpu, spec v q hq c' hc' hqv, ← cl_add]
    apply spec _ _ (S.add_mem hp hq)
    · convert I.add_mem hc hc' using 1; simp [map_add, mul_add]; abel
    · rw [map_add, hpu, hqv, Submodule.coe_add]
  have hsmul : ∀ (o : O) u, f (o • u) = RingHom.id O o • f u := by
    intro o u
    obtain ⟨p, hp, hpu⟩ := rep u
    obtain ⟨c, hc⟩ := exist p hp
    rw [RingHom.id_apply, spec u p hp c hc hpu, ← cl_smul]
    apply spec _ (o • p) (S.smul_of_tower_mem o hp)
    · convert I.smul_of_tower_mem o hc using 1
      rw [LinearMap.map_smul_of_tower, smul_sub, mul_smul_comm]
    · rw [Submodule.coe_smul_of_tower, ← hpu]
      exact LinearMap.map_smul_of_tower L.mkQ o p
  exact ⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul },
    fun p hp c hc => spec _ p hp c hc rfl⟩

/-- The connecting map from curve sections to the Čech cokernel exists, is surjective, and has
kernel the image of the surface. -/
theorem curve_sections_connecting_map_exists (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (t x : R) (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
    (hregSwap : RegularParameterPair R x t) (d : ℕ) (G : GluedGenerators R t x beta d) (j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta d)) (hregF : Function.Injective
    (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j => Ideal.Quotient.mk
    ((Ideal.span {overlapException R t x})^j) ((algebraMap (BlowupChart R t x)
    (BlowupOverlap R t x)) (G.left j)) * c)) :
    ∃ δ : curveSectionsQuot R t x beta G j →ₗ[O] (CechLevelOutput R t x j ⧸ LinearMap.range
      (finiteCechDifferential R t x beta d j h)), (∀ (p : BlowupChart R t x × BlowupChart R x t)
      (hp : p ∈ curveSections R t x beta G j) (c : BlowupOverlap R t x), fullCechDifferential R t x
      beta 0 p - (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * c ∈
      (Ideal.span {overlapException R t x})^j → δ ⟨(curveIdealLattice R t x beta G j).mkQ p,
      Submodule.mem_map_of_mem hp⟩ = (LinearMap.range (finiteCechDifferential R t x beta d j h)).mkQ
      ((cechOutputLattice R t x j).mkQ c)) ∧ Function.Surjective δ ∧ ∀ u : curveSectionsQuot R t x
      beta G j, δ u = 0 ↔ ∃ r : R, (u : (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice
      R t x beta G j) = (curveIdealLattice R t x beta G j).mkQ (surfaceToChartPair R t x r) := by
  obtain ⟨δ, hδ⟩ := exists_connecting_linear_map O R t x hreg beta hregSwap d G j h hregF
  refine ⟨δ, hδ, fun y => ?_, fun u => ?_⟩
  · obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ y'
    obtain ⟨p, hp, hc⟩ := curve_sections_cover_overlap R t x beta d G hreg j c
    exact ⟨_, hδ p hp c hc⟩
  · obtain ⟨u, hu⟩ := u
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hu
    obtain ⟨c, hc⟩ := exists_connecting_coefficient R t x beta G j p hp
    have hδu : δ ⟨(curveIdealLattice R t x beta G j).mkQ p, hu⟩ = _ := hδ p hp c hc
    rw [hδu]
    refine (curve_section_connecting_class_zero_iff R t x beta d G hreg hregSwap j h hregF
      p hp c hc).trans (exists_congr fun r => ?_)
    exact (Submodule.Quotient.eq _).symm

end SurfaceBlowup

end
