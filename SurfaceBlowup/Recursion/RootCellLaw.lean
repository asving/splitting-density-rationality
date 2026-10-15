/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Assembly.MonicCells
import SurfaceBlowup.Blowup.FixedTangentCellBijection
import SurfaceBlowup.Measure.MemberBoxes
import SurfaceBlowup.Recursion.Events

/-!
# The root cell law

The *root cell law* (`RootCellLaw`) computes the measure of the set of `π`-scaled monic
polynomials `monicPolynomial O (π • z)`, `z ∈ O^r`, with a given factorization type `σ`. This
file proves it unconditionally by building a concrete surface universe: every concrete member is
decomposed into cells, each cell ideal is sent to its strict transforms on the children, and the
termination hypotheses (child types exist, order defect decreases) are verified via the index map
of a cell.

## Main results

* `root_cell_law_at_universe_member`: the root cell law at a single universe member.
* `cell_member_index_map`: the index map `R ⧸ J → ∏ B j` of a cell, with cokernel length `d(d-1)/2`.
* `cell_child_bijOn`, `concrete_member_cells_cover`: cells and their children.
* `concrete_universe_exists`: a surface universe indexed by concrete members exists.
* `root_cell_law`: the root cell law.
* `monic_type_event_measurable_of_root_cell_law`: measurability of monic type events.

Provenance: `Thm_SurfaceBlowupV2_{algebra_type_ascent, etale_children_types_exist,
etale_recursion_data_abstract, concrete_termination_data_of_index_map,
monic_type_event_measurable_of_root_cell_law, root_cell_law_at_universe_member,
root_cell_law_of_universe, cell_child_bijOn, cell_datum_multiplicities_pos, cell_member_index_map,
cell_child_termination_data, cell_child_type_add, state_ideal_has_multiplicity,
state_ideal_multiplicity_le_contacts, concrete_member_cells_cover,
concrete_universe_of_cell_measure, concrete_universe_exists, root_cell_law}`.
-/

noncomputable section

namespace SurfaceBlowup

open scoped BigOperators ENNReal

/-! ### Algebra types along unramified extensions -/

/-- **Type ascent.** If `O → Oδ` is a finite free unramified extension of rank `δ` of complete DVRs
and the `Oδ`-algebra `B` has `O`-algebra type `σ`, then `B` has some `Oδ`-algebra type `τ` with
`σ = scaleType δ τ`. -/
private theorem algebra_type_ascent (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ] [Algebra O Oδ] [Module.Finite O Oδ]
    [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ) (pi : O) (hpi : Irreducible pi)
    (hpiδ : Irreducible (algebraMap O Oδ pi)) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (B : Type) [CommRing B] [Algebra O B] [Algebra Oδ B]
    [IsScalarTower O Oδ B] (σ : FactorType) (h : HasAlgebraType O B σ) :
    ∃ τ : FactorType, HasAlgebraType Oδ B τ ∧ σ = scaleType δ τ := by
  have ⟨ι, hι, L, hF, _, _, _, _, e, _, hfinL⟩ := h
  obtain ⟨a1, a2, a3, a4, E, hc⟩ :=
    unramified_generic_fibre_ascent O Oδ δ hrank pi hpi hpiδ B ι L e
  -- closure finiteness over `Oδ` follows from finiteness over `O` (same fields `L i`)
  have hfinδ (i) : Module.Finite Oδ (integralClosure Oδ (L i)) :=
    have : IsScalarTower O Oδ (L i) := .of_algebraMap_eq fun c => by
      rw [hc i c, ← IsScalarTower.algebraMap_apply]
    closure_finite_ascent O Oδ (L i) (hfinL i)
  have hτ : HasAlgebraType Oδ B (∑ i, ({fieldInvariant Oδ (L i)} : FactorType)) :=
    ⟨ι, hι, L, hF, a1, a2, a3, a4, E, rfl, hfinδ⟩
  exact ⟨_, hτ, algebra_type_unique O B σ _ h
    (algebra_type_unramified_descent O Oδ δ hrank pi hpi hpiδ B _ hτ)⟩

/-- If `A` has an algebra type and `ψ : A → ∏ B j` is injective with finite-length cokernel, where
each `B j` is an algebra over an unramified extension `O_j` of `O`, then every `B j` has an
`O_j`-algebra type. -/
private theorem etale_children_types_exist (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (n : ℕ)
    (Oj : Fin n → Type) [∀ j, CommRing (Oj j)] [∀ j, IsDomain (Oj j)]
    [∀ j, IsDiscreteValuationRing (Oj j)] [∀ j, Algebra O (Oj j)] [∀ j, Module.Finite O (Oj j)]
    [∀ j, Module.Free O (Oj j)] (δ : Fin n → ℕ) (hrank : ∀ j, Module.finrank O (Oj j) = δ j)
    (pi : O) (hpi : Irreducible pi) (hpiδ : ∀ j, Irreducible (algebraMap O (Oj j) pi)) (A : Type)
    [CommRing A] [Algebra O A] (B : Fin n → Type) [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)]
    [∀ j, Algebra (Oj j) (B j)] [∀ j, IsScalarTower O (Oj j) (B j)] (ψ : A →ₐ[O] ∀ j, B j)
    (hinj : Function.Injective ψ) (ℓ : ℕ) (hℓ : Module.length O
    ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = ℓ) (σ : FactorType) (hσ : HasAlgebraType O A σ) :
    ∀ j, ∃ τ : FactorType, HasAlgebraType (Oj j) (B j) τ := by
  intro j
  obtain ⟨τ₀, h₀⟩ := algebra_type_children_exists O A n B ψ hinj ℓ hℓ σ hσ j
  obtain ⟨τ, hτ, -⟩ := algebra_type_ascent O (Oj j) (δ j) (hrank j) pi hpi (hpiδ j) (B j) τ₀ h₀
  exact ⟨τ, hτ⟩

/-- The abstract étale recursion data: in the situation of `etale_children_types_exist`, every
child `B j` has an algebra type, its order defect is at most that of `A`, and strictly smaller
when the cokernel of `ψ` is nonzero. -/
private theorem etale_recursion_data_abstract (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (n : ℕ) (Oj : Fin n → Type) [∀ j, CommRing (Oj j)]
    [∀ j, IsDomain (Oj j)] [∀ j, IsDiscreteValuationRing (Oj j)] [∀ j, Algebra O (Oj j)]
    [∀ j, Module.Finite O (Oj j)] [∀ j, Module.Free O (Oj j)] (δ : Fin n → ℕ)
    (hrank : ∀ j, Module.finrank O (Oj j) = δ j) (pi : O) (hpi : Irreducible pi)
    (hpiδ : ∀ j, Irreducible (algebraMap O (Oj j) pi)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Free O A] (B : Fin n → Type) [∀ j, CommRing (B j)]
    [∀ j, Algebra O (B j)] [∀ j, Module.Finite O (B j)] [∀ j, Module.Free O (B j)]
    [∀ j, Algebra (Oj j) (B j)] [∀ j, IsScalarTower O (Oj j) (B j)] (ψ : A →ₐ[O] ∀ j, B j)
    (hinj : Function.Injective ψ) (ℓ : ℕ) (hℓ : Module.length O
    ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = ℓ) (σ : FactorType) (hσ : HasAlgebraType O A σ) :
    ∀ j, (∃ τ : FactorType, HasAlgebraType (Oj j) (B j) τ) ∧ (orderDefect (Oj j) (B j)).toNat ≤
        (orderDefect O A).toNat ∧ (1 ≤ ℓ → (orderDefect (Oj j) (B j)).toNat <
        (orderDefect O A).toNat) := fun j ↦
  ⟨etale_children_types_exist O n Oj δ hrank pi hpi hpiδ A B ψ hinj ℓ hℓ σ hσ j,
    etale_invariant_children O n Oj δ hrank pi hpi hpiδ A B ψ hinj ℓ hℓ σ hσ j⟩

/-- `etale_recursion_data_abstract` specialised to a concrete member `m`, a cell ideal `J` and
child members `mc j`: the quotient `R ⧸ J` plays the role of `A`. -/
private theorem concrete_termination_data_of_index_map (m : ConcreteMember) (n : ℕ)
    (mc : Fin n → ConcreteMember) [∀ j, Algebra m.O (mc j).O] [∀ j, Module.Finite m.O (mc j).O]
    [∀ j, Module.Free m.O (mc j).O] (δ : Fin n → ℕ)
    (hrank : ∀ j, Module.finrank m.O (mc j).O = δ j)
    (hpi : ∀ j, Irreducible (algebraMap m.O (mc j).O m.pi)) (J : Ideal m.R) (B : Fin n → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra m.O (B j)] [∀ j, Algebra (mc j).O (B j)]
    [∀ j, IsScalarTower m.O (mc j).O (B j)] [∀ j, Module.Finite (mc j).O (B j)]
    [∀ j, Module.Free (mc j).O (B j)] (ψ : (m.R ⧸ J) →ₐ[m.O] ∀ j, B j) (hψ : Function.Injective ψ)
    (ℓ : ℕ) (hlen : Module.length m.O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = (ℓ : ℕ∞))
    [Module.Finite m.O (m.R ⧸ J)] [Module.Free m.O (m.R ⧸ J)] (σ : FactorType)
    (hσ : HasAlgebraType m.O (m.R ⧸ J) σ) :
    ∀ j, (∃ τ : FactorType, HasAlgebraType (mc j).O (B j) τ) ∧ (orderDefect (mc j).O (B j)).toNat ≤
        (orderDefect m.O (m.R ⧸ J)).toNat ∧ (1 ≤ ℓ → (orderDefect (mc j).O (B j)).toNat <
        (orderDefect m.O (m.R ⧸ J)).toNat) := by
  have : ∀ j, Module.Finite m.O (B j) := fun j => Module.Finite.trans (mc j).O (B j)
  have : ∀ j, Module.Free m.O (B j) := fun j => Module.Free.trans (S := (mc j).O)
  have h := etale_recursion_data_abstract m.O n (fun j => (mc j).O) δ hrank m.pi m.hpi hpi
    (m.R ⧸ J) B
  exact h ψ hψ ℓ hlen σ hσ

/-- Assuming the root cell law, the set of monic polynomials of degree `n` over `O` with
factorization type `σ` is measurable. -/
theorem monic_type_event_measurable_of_root_cell_law (hroot : RootCellLaw) (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    MeasurableSet {a : Fin n→O | HasPolynomialTypeF O (monicPolynomial O a) σ} := by
  obtain ⟨⟨S, hS⟩, hcov, -⟩ := monic_cells_partition O htop n
  have key : {a : Fin n→O | HasPolynomialTypeF O (monicPolynomial O a) σ} =
      ⋃ D ∈ S, (residueCell O n (divisorAffinePolynomial (IsLocalRing.ResidueField O) D) ∩
          typeEvent O n σ) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    refine ⟨fun h ↦ ?_, fun ⟨_, _, _, h⟩ ↦ h⟩
    obtain ⟨D, ⟨hD, ha⟩, -⟩ := hcov a
    exact ⟨D, (hS D).2 hD, ha, h⟩
  rw [key]
  refine Finset.measurableSet_biUnion _ fun D hD => ?_
  have hD' := (hS D).1 hD
  obtain ⟨⟨m, hm, -⟩, -⟩ := divisor_array_exists_unique (IsLocalRing.ResidueField O) n D hD'.2
  exact (monic_cell_law hroot O htop n D hD' m hm σ).1

/-! ### The root cell law from a concrete universe -/

/-- A surface universe indexed by all concrete members, satisfying the termination hypotheses. -/
private def ConcreteUniverse : Prop :=
  ∃ U : SurfaceUniverse, ∃ eι : U.ι ≃ ConcreteMember, (∀ i, U.M i = (eι i).toMeasured) ∧
    U.ChildTypesExist ∧
      U.InvariantDecreases fun i J ↦ (orderDefect (U.M i).O ((U.M i).R ⧸ J)).toNat

/-- **Root cell law at a universe member.** Let `i` be a member of a surface universe satisfying
the termination hypotheses, whose state is the single state `(1, r)` and whose measure is the
pushforward of the coefficient measure along a coordinate chart `z ↦ (f, b)(π z)` matching
algebra types with polynomial types. Then the type-`σ` event of `π`-scaled monic polynomials is
measurable and has mass `densityValue (lawCoeff (stateLaw (single 1 r)) σ) q`. -/
theorem root_cell_law_at_universe_member (U : SurfaceUniverse)
    (hE1 : U.ChildTypesExist)
    (hE2 : U.InvariantDecreases fun i J ↦ (orderDefect (U.M i).O ((U.M i).R ⧸ J)).toNat)
    (i : U.ι) (r : ℕ) (hr : 0 < r)
    (hs : (U.M i).s = State.single 1 r) (f : (U.M i).R)
    (b : Fin (State.single 1 r).degree → (U.M i).R)
    (hmeas : Measurable (coordinateIdeal (U.M i).S.pi f b))
    (hμ : (U.M i).μ = (((U.M i).q : ℝ≥0∞)⁻¹ ^ (State.single 1 r).degree) •
    (coefficientMeasure (U.M i).O (State.single 1 r).degree).map
    (coordinateIdeal (U.M i).S.pi f b)) (hcell : ∀ z : Fin (State.single 1 r).degree → (U.M i).O,
    (coordinateIdeal (U.M i).S.pi f b) z ∈ (U.M i).stateSet)
    (htype : ∀ (z : Fin (State.single 1 r).degree → (U.M i).O) (σ : FactorType), HasAlgebraType
    (U.M i).O ((U.M i).R ⧸ (coordinateIdeal (U.M i).S.pi f b) z) σ ↔ HasPolynomialTypeF (U.M i).O
    (monicPolynomial (U.M i).O ((U.M i).S.pi • z)) σ) (σ : FactorType) :
    MeasurableSet {z : Fin (State.single 1 r).degree → (U.M i).O | HasPolynomialTypeF (U.M i).O
        (monicPolynomial (U.M i).O ((U.M i).S.pi • z)) σ} ∧ coefficientMeasure (U.M i).O
        (State.single 1 r).degree {z : Fin (State.single 1 r).degree → (U.M i).O |
        HasPolynomialTypeF (U.M i).O (monicPolynomial (U.M i).O ((U.M i).S.pi • z)) σ} =
        densityValue (lawCoeff (stateLaw (State.single 1 r)) σ) (U.M i).q := by
  have hpre : coordinateIdeal (U.M i).S.pi f b ⁻¹' U.typeEvent i σ =
      {z : Fin (State.single 1 r).degree → (U.M i).O | HasPolynomialTypeF (U.M i).O
          (monicPolynomial (U.M i).O ((U.M i).S.pi • z)) σ} := by
    ext z
    simp only [Set.mem_preimage, SurfaceUniverse.typeEvent, Set.mem_ofPred_eq]
    exact ⟨fun h => (htype z σ).1 h.2, fun h => ⟨hcell z, (htype z σ).2 h⟩⟩
  refine ⟨?_, ?_⟩
  · rw [← hpre]
    exact hmeas (etale_type_event_measurable U hE1
      (fun i J => (orderDefect (U.M i).O ((U.M i).R ⧸ J)).toNat) hE2 i σ)
  · have hd : (State.single 1 r).degree = r := by simp [State.degree]
    have hdpos : 0 < (State.single 1 r).degree := by rw [hd]; exact hr
    obtain ⟨hFm, hFE, hEF, hN⟩ := type_event_null_difference U i σ
    have hL := ((universal_law_statement U i).1 σ).2.2
    rw [hs] at hL
    have e : stateLaw (State.single 1 (State.single 1 r).degree) = stateLaw (State.single 1 r) := by
      rw [hd]
    have key := chart_cell_law_generic (U.M i).O (U.M i).htop (U.M i).S.pi
      (U.M i).R (State.single 1 r).degree f b hmeas
      (U.M i).stateSet hcell (U.M i).μ hμ htype σ (U.termTypeEvent i σ) (U.nonterminatingSet i)
      hFm hFE hEF hN (by rw [e]; exact hL)
    rw [e] at key
    exact key.1

/-- The root cell law follows from the existence of a concrete surface universe: the one-chart
member with state `(1, r)` realises the root cell, and the universal law computes its mass. -/
private theorem root_cell_law_of_universe (hU : ConcreteUniverse) : RootCellLaw := by
  obtain ⟨U, eι, hM, hE1, hE2⟩ := hU
  intro O _ _ _ _ _ _ _ _ _ _ _ _ htop pi hpi r hr σ
  obtain ⟨hD, hReg, S, hSpi, hSt, hSx, -, hSa, hSb⟩ :=
    concrete_surface_data_exists_unconditional O pi hpi 1 1 0 one_pos
  obtain ⟨A, i₀, hi₀, hf, hb, hμA⟩ :=
    repeated_root_one_chart_atlas O pi hpi S hSpi hSt hSa hSb r hr
  have hshape : StateShape 1 0 (State.single 1 r) := ⟨rfl, rfl, hr⟩
  let m₀ : ConcreteMember :=
    { O := O, htop := htop, pi := pi, hpi := hpi, u := 1, a := 1, b := 0, ha := one_pos,
      S := S, hS_pi := hSpi, hS_t := hSt, hS_x := hSx, hS_a := hSa, hS_b := hSb,
      s := State.single 1 r, shape := hshape, atlas := A }
  set i := eι.symm m₀
  have hMi : U.M i = m₀.toMeasured := by rw [hM i]; simp [i]
  have hdeg : 0 < (State.single 1 r).degree := by simpa [State.degree] using hr
  have key : ∀ M : MeasuredSurface, M = m₀.toMeasured →
      (M.s = State.single 1 r) ∧ ∃ (f : M.R) (b : Fin (State.single 1 r).degree → M.R),
        Measurable (coordinateIdeal M.S.pi f b) ∧
        M.μ = ((M.q : ℝ≥0∞)⁻¹ ^ (State.single 1 r).degree) •
          (coefficientMeasure M.O (State.single 1 r).degree).map (coordinateIdeal M.S.pi f b) ∧
        (∀ z : Fin (State.single 1 r).degree → M.O, (coordinateIdeal M.S.pi f b) z ∈ M.stateSet) ∧
        (∀ (z : Fin (State.single 1 r).degree → M.O) (σ : FactorType),
          HasAlgebraType M.O (M.R ⧸ (coordinateIdeal M.S.pi f b) z) σ ↔
            HasPolynomialTypeF M.O (monicPolynomial M.O (M.S.pi • z)) σ) := by
    intro M hM'
    subst hM'
    have hch := concrete_member_charts m₀ i₀
    refine ⟨rfl, (A.chart i₀).f, (A.chart i₀).b, hch.2.2, ?_, ?_, ?_⟩
    · let _ : MeasurableSpace (Ideal (ConcreteSurface O pi 1 1 0)) :=
        idealChartSigma O (ConcreteSurface O pi 1 1 0) S.pi
      change stateMeasure O (ConcreteSurface O pi 1 1 0) S.pi (State.single 1 r).degree
        (Nat.card (IsLocalRing.ResidueField O)) A = _
      rw [hμA]
      change _ = _ • (coefficientMeasure O (State.single 1 r).degree).map
        (coordinateIdeal S.pi (A.chart i₀).f (A.chart i₀).b)
      rw [hf, hb]
      rfl
    · intro z
      have hz : coordinateIdeal m₀.S.pi (m₀.atlas.chart i₀).f (m₀.atlas.chart i₀).b z ∈
          residueIdealCell (algebraMap m₀.O m₀.R m₀.S.pi) (m₀.atlas.chart i₀).f := by
        rw [← hch.2.1]; exact ⟨z, rfl⟩
      exact (Set.ext_iff.1 A.cover _).2 (Set.mem_iUnion.2 ⟨i₀, hz⟩)
    · intro z τ
      have e : ∀ z' : Fin (State.single 1 r).degree → O,
          HasAlgebraType O (ConcreteSurface O pi 1 1 0 ⧸
            coordinateIdeal S.pi (A.chart i₀).f (A.chart i₀).b z') τ ↔
          HasPolynomialTypeF O (monicPolynomial O (S.pi • z')) τ := by
        intro z'
        rw [hf, hb, hSpi]
        exact repeated_root_chart_type O pi hpi _ hdeg z' τ
      exact e z
  have back : ∀ M : MeasuredSurface, M = m₀.toMeasured →
      (MeasurableSet {z : Fin (State.single 1 r).degree → M.O | HasPolynomialTypeF M.O
          (monicPolynomial M.O (M.S.pi • z)) σ} ∧ coefficientMeasure M.O (State.single 1 r).degree
          {z : Fin (State.single 1 r).degree → M.O | HasPolynomialTypeF M.O
          (monicPolynomial M.O (M.S.pi • z)) σ} = densityValue
          (lawCoeff (stateLaw (State.single 1 r)) σ) M.q) →
      MeasurableSet {z : Fin r → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} ∧
      coefficientMeasure O r {z : Fin r → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} =
        densityValue (lawCoeff (stateLaw (State.single 1 r)) σ)
            (Nat.card (IsLocalRing.ResidueField O)) := by
    intro M hM' h
    subst hM'
    have hpi' : m₀.toMeasured.S.pi = pi := hSpi
    rw [hpi'] at h
    exact root_cell_clauses_reindex O pi σ _ _ r (Nat.one_mul r) h
  obtain ⟨hs, f, b, hmeas, hμ, hcell, htype⟩ := key (U.M i) hMi
  exact back (U.M i) hMi (root_cell_law_at_universe_member U hE1 hE2 i r hr hs f b hmeas hμ hcell
      htype σ)

private theorem pattern_degree_facts_of_hasPattern (k : Type) [Field k] (a b : ℕ) (s : State)
    (hsh : StateShape a b s)
    (P : TangentPattern s.degree) (hP : Allowed s P) (Dv : ExceptionalDivisor k)
        (hD : HasPattern k s Dv P) :
    0 < P.d.val ∧
    ((∃ c : ℕ, s = State.single a c ∧ b = 0) ∨ (∃ c h : ℕ, s = State.crossing a b c h ∧ 0 < b)) ∧
    P.d.val ≤ stateContactT s ∧ (∀ h : ℕ, stateContactX s = some h → P.d.val ≤ h) ∧
    (0 < Dv none ↔ P.d.val < stateContactT s) ∧
    (∀ h : ℕ, stateContactX s = some h → (0 < Dv (zeroDirection k) ↔ P.d.val < h)) ∧
    exceptionalDegree k Dv = P.d.val := by
  obtain ⟨hdeg, hinf, hz, -⟩ := hD
  have hinf' : Dv none = P.rt.val := hinf
  cases s with
  | single a' c =>
    obtain ⟨rfl, hb, -⟩ := hsh
    obtain ⟨h0, -, h1, -, h3⟩ := hP
    refine ⟨h0, Or.inl ⟨c, rfl, hb⟩, h1, fun h hh => by simp [stateContactX] at hh, ?_,
      fun h hh => by simp [stateContactX] at hh, hdeg⟩
    rw [hinf']; exact h3
  | crossing a' b' c h =>
    obtain ⟨rfl, rfl, hb, -, -⟩ := hsh
    obtain ⟨h0, -, h1, h2, h3, h4⟩ := hP
    have hz' : Dv (zeroDirection k) = P.rx.val := hz
    refine ⟨h0, Or.inr ⟨c, h, rfl, hb⟩, h1, fun h' hh => ?_, ?_, fun h' hh => ?_, hdeg⟩
    · simp only [stateContactX, Option.some.injEq] at hh; subst hh; exact h2
    · rw [hinf']; exact h3
    · simp only [stateContactX, Option.some.injEq] at hh; subst hh; rw [hz']; exact h4

private theorem divisorStrictTransform_bijOn (m : ConcreteMember) (t x : m.R)
    (ht : t = surfaceT m.O m.pi m.u m.a m.b) (hx : x = surfaceX m.O m.pi m.u m.a m.b)
    (e : (BlowupChart m.R t x ⧸ chartExceptional m.R t x) ≃+* Polynomial
        (IsLocalRing.ResidueField m.R))
    (he : ∀ r : m.R, e (Ideal.Quotient.mk (chartExceptional m.R t x) (chartBase m.R t x r)) =
      Polynomial.C (IsLocalRing.residue m.R r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional m.R t x) (chartSlope m.R t x)) = Polynomial.X)
    (hinf : (infinityPoint m.R t x).IsPrime)
    (P : TangentPattern m.s.degree) (hP : Allowed m.s P)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField m.R))
    (hD : HasPattern (IsLocalRing.ResidueField m.R) m.s Dv P) :
    Set.BijOn (fun J Q => divisorStrictTransform m.R t x e Dv hinf P.d.val J Q)
      (fixedTangentCell m.O m.R m.S m.s P.d.val Dv)
      (Set.pi Set.univ (childIdealSet m.R t x e Dv hinf m.s P.d.val)) := by
  subst ht hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    pattern_degree_facts_of_hasPattern (IsLocalRing.ResidueField m.R) m.a m.b m.s m.shape P hP Dv hD
  exact strict_transform_bijOn_child_ideals m.O m.pi m.hpi m.u m.a m.b m.ha m.S ⟨m.hS_t, m.hS_x,
      m.hS_a, m.hS_b⟩ e he
      heZ Dv hinf
    m.s P.d.val h1 h2 h3 h4 h5 h6 h7

/-! ### Cells and their children -/

/-- The child map `J ↦ (Φ J j)_j` is a bijection from the cell `c` of a concrete member onto the
product of the children's state sets. -/
theorem cell_child_bijOn (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c) :
    Set.BijOn (fun J j => D.Φ J j) (m.toMeasured.cell c)
        (Set.pi Set.univ fun j => (D.mc j).toMeasured.stateSet) := by
  have hF := divisorStrictTransform_bijOn m m.S.t m.S.x m.hS_t m.hS_x D.e D.he D.heZ D.hinf c.1.1
      c.1.2 c.2.1
      c.2.2
  set d := m.toMeasured.cellDegree c
  let T : (∀ Q, Ideal (divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf Q)) →
      ∀ j : m.toMeasured.childIdx c, Ideal (D.mc j).R :=
    fun u j => Ideal.map (D.Eq j : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j)
        →+* (D.mc j).R)
      (u (D.point j))
  have hmapmap : ∀ j (I : Ideal (divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j))),
      Ideal.map ((D.Eq j).symm : (D.mc j).R →+* divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf
          (D.point j)) (Ideal.map
          (D.Eq j : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) →+* (D.mc j).R)
          I) = I := fun j _ ↦ Ideal.map_of_equiv (D.Eq j)
  have hmapmap' : ∀ j (I : Ideal (D.mc j).R),
      Ideal.map (D.Eq j : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) →+*
          (D.mc j).R) (Ideal.map
          ((D.Eq j).symm : (D.mc j).R →+* divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf
          (D.point j)) I) = I := fun j _ ↦ Ideal.map_of_equiv (D.Eq j).symm
  have hsurjpt : ∀ Q : divisorSupport c.2.1, ∃ j, D.point j = Q := by
    intro Q
    obtain ⟨j, hj⟩ := (D.asg.supp Q.1).mp Q.2
    exact ⟨j, Subtype.ext hj⟩
  have hbij : Function.Bijective (fun j => D.point j) :=
    ⟨fun i j h => D.asg.inj (congrArg Subtype.val h), hsurjpt⟩
  let σ := Equiv.ofBijective _ hbij
  have hT : Set.BijOn T (Set.pi Set.univ (childIdealSet m.R m.S.t m.S.x D.e c.2.1 D.hinf m.s d))
      (Set.pi Set.univ fun j => (D.mc j).toMeasured.stateSet) := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu j _
      exact (child_ideal_set_map_iff_stateSet m c D j (u (D.point j))).mp (hu _ (Set.mem_univ _))
    · intro u _ v _ huv
      funext Q
      obtain ⟨j, rfl⟩ := hsurjpt Q
      have := congrFun huv j
      rw [← hmapmap j (u (D.point j)), ← hmapmap j (v (D.point j))]
      exact congrArg _ this
    · intro w hw
      let v : ∀ j : m.toMeasured.childIdx c, Ideal
          (divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j)) :=
        fun j => Ideal.map ((D.Eq j).symm : (D.mc j).R →+* divisorLocalRing m.R m.S.t m.S.x D.e
            c.2.1 D.hinf (D.point j)) (w j)
      let u := Equiv.piCongrLeft (fun Q => Ideal
          (divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf Q)) σ v
      have hu : ∀ j, u (D.point j) = v j := fun j => Equiv.piCongrLeft_apply_apply
          (fun Q => Ideal (divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf Q)) σ v j
      refine ⟨u, ?_, ?_⟩
      · intro Q _
        obtain ⟨j, rfl⟩ := hsurjpt Q
        rw [hu]
        apply (child_ideal_set_map_iff_stateSet m c D j _).mpr
        exact (hmapmap' j (w j)).symm ▸ hw j (Set.mem_univ _)
      · funext j
        change Ideal.map _ (u (D.point j)) = w j
        rw [hu]
        exact hmapmap' j (w j)
  have hcomp : (fun J j => D.Φ J j) =
      T ∘ (fun J Q => divisorStrictTransform m.R m.S.t m.S.x D.e c.2.1 D.hinf d J Q) := by
    funext J j
    exact cell_child_Phi_eq_map m c D J j
  rw [hcomp]
  exact hT.comp hF

/-- The residue polynomial `H = ∑ᵢ c̄ᵢ Xⁱ` of a family `c` has coefficients `c̄ᵢ`. -/
private theorem residue_sum_coeff {R : Type} [CommRing R] [IsLocalRing R] (d : ℕ)
    (c : Fin (d + 1) → R) (i : Fin (d + 1)) :
    (∑ j : Fin (d + 1), Polynomial.C (IsLocalRing.residue R (c j)) * Polynomial.X ^ j.val).coeff i =
      IsLocalRing.residue R (c i) := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hj ↦ if_neg fun h ↦ hj (Fin.ext h.symm)) (by simp)]
  simp

/-- The residue polynomial `H = ∑ᵢ c̄ᵢ Xⁱ` of a curve `∑ cᵢ tᵈ⁻ⁱ xⁱ` of multiplicity `d` on a
concrete surface is nonzero. -/
private theorem residue_sum_ne_zero (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    [IsLocalRing (ConcreteSurface O pi u a b)] (d : ℕ)
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {(surfaceT O pi u a b), (surfaceX O pi u a b)}) :
    ∑ j : Fin (d + 1), Polynomial.C (IsLocalRing.residue _ (c j)) * Polynomial.X ^ j.val ≠ 0 := by
  obtain ⟨i, hi⟩ := hne
  intro h0
  have := residue_sum_coeff d c i
  rw [h0, Polynomial.coeff_zero, eq_comm, IsLocalRing.residue_eq_zero_iff,
    concrete_surface_maximalIdeal_eq O pi hpi u a b ha] at this
  exact hi this

/-- For a curve `f = ∑ cᵢ tᵈ⁻ⁱ xⁱ` of multiplicity `d` on a concrete surface and two-chart curve
data `D` of its strict transform, all point multiplicities in the `t`-chart are positive. -/
private theorem cell_datum_left_multiplicity_pos (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsLocalRing (ConcreteSurface O pi u a b)] (d : ℕ)
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span
    {(surfaceT O pi u a b), (surfaceX O pi u a b)})
    (e : ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸
    chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ≃+*
    Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (he : ∀ r : (ConcreteSurface O pi u a b), e (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) r)) =
    Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) =
    Polynomial.X) (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (D : TwoChartCurveData (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b) beta)
    (hl : ∀ s : D.ι ⊕ D.ι0, leftData D s = completedPointMap
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (leftPoint D s) (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (c i) *
    (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))^i.val) ∧
    (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (c i) *
    (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))^i.val) ∈
    leftPoint D s) (s : D.ι ⊕ D.ι0) :
    0 < leftMultiplicity D s := by
  classical
  -- the point is a direction point `φ` dividing the residue polynomial `H`
  have : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} : Set
      (ConcreteSurface O pi u a b))).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  obtain ⟨hPmax, -, hPt⟩ := two_chart_left_points_maximal (ConcreteSurface O pi u a b) _ _
    beta D
  have := hPmax s
  obtain ⟨φ, hPφ, hmap, -⟩ := chart_point_eq_directionPoint _ _ _ e he heZ _ (hPt s)
  have hdvd : φ.val ∣ ∑ i : Fin (d + 1),
      Polynomial.C (IsLocalRing.residue _ (c i)) * Polynomial.X ^ i.val := by
    have hmem := (hl s).2
    rw [hPφ] at hmem
    unfold directionPoint at hmem
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hmem
    convert hmem using 1
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_sum,
      map_mul, map_pow, heZ]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (· * _) (he (c i)).symm
  unfold leftMultiplicity leftLevelIdeal finiteLocalCurveIdeal
  rw [(hl s).1, pow_one, concrete_strict_transform_multiplicity O pi hpi u a b ha d c hne
    (leftPoint D s) (hPt s) e he heZ φ.val φ.property hmap, ENat.toNat_natCast]
  exact Multiset.count_pos.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff'
    (residue_sum_ne_zero O pi hpi u a b ha d c hne)).mpr
    ⟨φ.2.2, φ.2.1.normalize_eq_self, hdvd⟩)

/-- For a curve `f = ∑ cᵢ tᵈ⁻ⁱ xⁱ` of multiplicity `d` on a concrete surface and two-chart curve
data `D` of its strict transform, the multiplicities at the points of the `x`-chart away from the
`t`-chart are positive. -/
private theorem cell_datum_right_multiplicity_pos (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsLocalRing (ConcreteSurface O pi u a b)] (d : ℕ)
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span
    {(surfaceT O pi u a b), (surfaceX O pi u a b)})
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (D : TwoChartCurveData (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b) beta)
    (hr : ∀ s : D.ι ⊕ D.ιinf, Ideal.span {rightData D s} = Ideal.span
    {completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
    (surfaceT O pi u a b)) (rightPoint D s) (∑ i : Fin (d+1), algebraMap
    (ConcreteSurface O pi u a b) (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
    (surfaceT O pi u a b)) (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
    (surfaceT O pi u a b))^(d - i.val))} ∧ (∑ i : Fin (d+1), algebraMap
    (ConcreteSurface O pi u a b) (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
    (surfaceT O pi u a b)) (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
    (surfaceT O pi u a b))^(d - i.val)) ∈ rightPoint D s) (l : D.ιinf) :
    0 < rightMultiplicity D (Sum.inr l) := by
  have : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} : Set
      (ConcreteSurface O pi u a b))).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  set H : Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)) :=
    ∑ i : Fin (d+1), Polynomial.C (IsLocalRing.residue _ (c i)) * Polynomial.X ^ i.val with hH
  obtain ⟨hPmax, -, hPx⟩ := two_chart_right_points_maximal (ConcreteSurface O pi u a b) _ _
    beta D
  have hW := D.slopeinf l
  -- the top coefficient lies in the maximal ideal, so `H` has degree `< d`
  have hcd : c (Fin.last d) ∈ IsLocalRing.maximalIdeal _ := by
    by_contra hnot
    have hmem := (hr (Sum.inr l)).2
    rw [Fin.sum_univ_castSucc] at hmem
    simp only [Fin.val_last, Nat.sub_self, pow_zero, mul_one] at hmem
    refine (hPmax (Sum.inr l)).ne_top (Ideal.eq_top_of_isUnit_mem _
      ((Ideal.add_mem_iff_right _ (Ideal.sum_mem _ fun i _ ↦ ?_)).1 hmem)
      ((IsLocalRing.notMem_maximalIdeal.mp hnot).map _))
    have := i.isLt
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (by simp only [Fin.val_castSucc]; omega : d - (Fin.castSucc i).val ≠ 0)
    rw [hk, pow_succ]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hW)
  have hlt : H.natDegree < d := by
    refine (Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ ↦
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.isLt)).lt_of_ne
      fun h ↦ residue_sum_ne_zero O pi hpi u a b ha d c hne ?_
    rw [← Polynomial.leadingCoeff_eq_zero, Polynomial.leadingCoeff, h]
    simpa [IsLocalRing.residue_eq_zero_iff] using (residue_sum_coeff d c (Fin.last d)).trans
      ((IsLocalRing.residue_eq_zero_iff _).2 hcd)
  unfold rightMultiplicity rightLevelIdeal finiteLocalCurveIdeal
  rw [pow_one, Ideal.span_insert, (hr (Sum.inr l)).1, ← Ideal.span_insert,
    concrete_infinity_strict_transform_multiplicity O pi hpi u a b ha d c hne
      (rightPoint D (Sum.inr l)) (hPx _) hW, ENat.toNat_natCast, ← hH]
  omega

private theorem concrete_index_map_reindexed_of_eq (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (t x : ConcreteSurface O pi u a b) (ht : t = surfaceT O pi u a b)
    (hx : x = surfaceX O pi u a b) (beta : BlowupRestriction (ConcreteSurface O pi u a b) t x)
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) t x beta) (f : ConcreteSurface O pi u a b)
    (G : GluedGenerators (ConcreteSurface O pi u a b) t x beta (curveDataDegree D))
    (hf : ∀ j : ℕ, surfaceToCechInput (ConcreteSurface O pi u a b) t x j f =
    (cechInputLattice (ConcreteSurface O pi u a b) t x j).mkQ
    (gluedFunctionPair (ConcreteSurface O pi u a b) t x G j))
    (hG : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk
    ((chartExceptional (ConcreteSurface O pi u a b) t x)^j) (G.left j)} = leftLevelKernel D j ∧
    Ideal.span {Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) x t)^j)
    (G.right j)} = rightLevelKernel D j) (n : ℕ) (e : Fin n ≃ AllPoints D) (B : Fin n → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)] (eB : ∀ j, B j ≃+*
    (localRing D (e j) ⧸ Ideal.span {localCurve D (e j)}))
    (hB : ∀ (j : Fin n) (c : O), (eB j) (algebraMap O (B j) c) = Ideal.Quotient.mk
    (Ideal.span {localCurve D (e j)}) (localFromSurface D (e j)
    (algebraMap O (ConcreteSurface O pi u a b) c))) :
    ∃ ψ : ((ConcreteSurface O pi u a b) ⧸ Ideal.span {f}) →ₐ[O] ∀ j, B j, Function.Injective ψ ∧
        Module.length O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) =
        (chooseTwo (curveDataDegree D) : ℕ∞) ∧ ∀ (r : (ConcreteSurface O pi u a b)) (j : Fin n),
        (eB j) (ψ (Ideal.Quotient.mk (Ideal.span {f}) r) j) = Ideal.Quotient.mk
        (Ideal.span {localCurve D (e j)}) (localFromSurface D (e j) r) := by
  subst ht hx
  exact concrete_index_map_reindexed O pi hpi u a b ha beta D f G hf hG n e B eB hB

/-- All common, left-only and right-only point multiplicities of two-chart curve data of a curve
of multiplicity `d` are positive, with the chart parameters given up to equality. -/
private theorem cell_datum_multiplicities_pos_of_eq (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (t x : ConcreteSurface O pi u a b) (ht : t = surfaceT O pi u a b)
    (hx : x = surfaceX O pi u a b) [IsLocalRing (ConcreteSurface O pi u a b)] (d : ℕ)
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {t, x})
    (e : ((BlowupChart (ConcreteSurface O pi u a b) t x) ⧸ chartExceptional
    (ConcreteSurface O pi u a b) t x) ≃+* Polynomial
    (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (he : ∀ r : (ConcreteSurface O pi u a b), e (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) t x)
    ((chartBase (ConcreteSurface O pi u a b) t x) r)) = Polynomial.C
    (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional (ConcreteSurface O pi u a b) t x)
    (chartSlope (ConcreteSurface O pi u a b) t x)) = Polynomial.X)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) t x)
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) t x beta)
    (hl : ∀ s : D.ι ⊕ D.ι0, leftData D s = completedPointMap
    (BlowupChart (ConcreteSurface O pi u a b) t x) (leftPoint D s)
    (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
    (BlowupChart (ConcreteSurface O pi u a b) t x) (c i) *
    (chartSlope (ConcreteSurface O pi u a b) t x)^i.val) ∧
    (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
    (BlowupChart (ConcreteSurface O pi u a b) t x) (c i) *
    (chartSlope (ConcreteSurface O pi u a b) t x)^i.val) ∈ leftPoint D s)
    (hr : ∀ s : D.ι ⊕ D.ιinf, Ideal.span {rightData D s} = Ideal.span
    {completedPointMap (BlowupChart (ConcreteSurface O pi u a b) x t) (rightPoint D s)
    (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
    (BlowupChart (ConcreteSurface O pi u a b) x t) (c i) *
    (chartSlope (ConcreteSurface O pi u a b) x t)^(d - i.val))} ∧
    (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
    (BlowupChart (ConcreteSurface O pi u a b) x t) (c i) *
    (chartSlope (ConcreteSurface O pi u a b) x t)^(d - i.val)) ∈ rightPoint D s) :
    (∀ i : D.ι, 0 < commonMultiplicity D i) ∧ (∀ k : D.ι0, 0 < leftMultiplicity D (Sum.inr k)) ∧ ∀
        l : D.ιinf, 0 < rightMultiplicity D (Sum.inr l) := by
  subst ht hx
  refine ⟨fun i ↦ ?_, fun k ↦ cell_datum_left_multiplicity_pos O pi hpi u a b ha d c hne e he heZ
    beta D hl (Sum.inr k), cell_datum_right_multiplicity_pos O pi hpi u a b ha d c hne beta D hr⟩
  rw [← (two_chart_common_multiplicity_eq (ConcreteSurface O pi u a b) _ _ beta D i).1]
  exact cell_datum_left_multiplicity_pos O pi hpi u a b ha d c hne e he heZ beta D hl (Sum.inl i)

private theorem two_chart_datum_concrete_instances_of_eq (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (t x : ConcreteSurface O pi u a b) (ht : t = surfaceT O pi u a b)
    (hx : x = surfaceX O pi u a b) (beta : BlowupRestriction (ConcreteSurface O pi u a b) t x)
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) t x beta) :
    (∀ s : D.ι ⊕ D.ι0, IsNoetherianRing (CompletedLocalAt
        (BlowupChart (ConcreteSurface O pi u a b) t x) (leftPoint D s)) ∧ Function.Injective
        (fun y : (CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) t x)
        (leftPoint D s)) => (completedPointMap (BlowupChart (ConcreteSurface O pi u a b) t x)
        (leftPoint D s)) ((chartBase (ConcreteSurface O pi u a b) t x) t) * y)) ∧
        (∀ s : D.ι ⊕ D.ιinf, IsNoetherianRing (CompletedLocalAt
        (BlowupChart (ConcreteSurface O pi u a b) x t) (rightPoint D s)) ∧ Function.Injective
        (fun y : (CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) x t)
        (rightPoint D s)) => (completedPointMap (BlowupChart (ConcreteSurface O pi u a b) x t)
        (rightPoint D s)) ((chartBase (ConcreteSurface O pi u a b) x t) x) * y)) ∧ ∀ p : AllPoints
        D, IsNoetherianRing (localRing D p) ∧ ∃ _ : IsLocalRing (localRing D p), IsAdicComplete
        (IsLocalRing.maximalIdeal (localRing D p)) (localRing D p) ∧ localException D p ∈
        IsLocalRing.maximalIdeal (localRing D p) := by
  subst ht hx
  exact two_chart_datum_concrete_instances O pi hpi u a b ha beta D

private theorem concrete_two_chart_glued_generators_exist_of_eq (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (t x : ConcreteSurface O pi u a b) (ht : t = surfaceT O pi u a b)
    (hx : x = surfaceX O pi u a b) (beta : BlowupRestriction (ConcreteSurface O pi u a b) t x)
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) t x beta) :
    ∃ f : ConcreteSurface O pi u a b, ∃ G : GluedGenerators (ConcreteSurface O pi u a b) t x beta
        (curveDataDegree D), (∀ j : ℕ, surfaceToCechInput (ConcreteSurface O pi u a b) t x j f =
        (cechInputLattice (ConcreteSurface O pi u a b) t x j).mkQ
        (gluedFunctionPair (ConcreteSurface O pi u a b) t x G j)) ∧ ∀ j : ℕ, Ideal.span
        {Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) t x)^j) (G.left j)} =
        leftLevelKernel D j ∧ Ideal.span {Ideal.Quotient.mk
        ((chartExceptional (ConcreteSurface O pi u a b) x t)^j) (G.right j)} = rightLevelKernel D
        j := by
  subst ht hx
  exact concrete_two_chart_glued_generators_exist O pi hpi u a b ha beta D

private theorem fixed_tangent_cell_curve_datum_of_eq (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (t x : ConcreteSurface O pi u a b) (ht : t = surfaceT O pi u a b)
    (hx : x = surfaceX O pi u a b) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hS : S.t = t ∧ S.x = x)
    (e : ((BlowupChart (ConcreteSurface O pi u a b) t x) ⧸ chartExceptional
    (ConcreteSurface O pi u a b) t x) ≃+* Polynomial
    (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (he : ∀ r : (ConcreteSurface O pi u a b), e (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) t x)
    ((chartBase (ConcreteSurface O pi u a b) t x) r)) = Polynomial.C
    (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional (ConcreteSurface O pi u a b) t x)
    (chartSlope (ConcreteSurface O pi u a b) t x)) = Polynomial.X)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField (ConcreteSurface O pi u a b))) (s : State)
    (d : ℕ) (J : Ideal (ConcreteSurface O pi u a b))
    (hJ : J ∈ fixedTangentCell O (ConcreteSurface O pi u a b) S s d Dv)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) t x) :
    ∃ (f : (ConcreteSurface O pi u a b)) (c : Fin (d+1) → (ConcreteSurface O pi u a b))
        (D : TwoChartCurveData (ConcreteSurface O pi u a b) t x beta), J = Ideal.span {f} ∧ f = ∑ i
        : Fin (d+1), c i * t^(d - i.val) * x^i.val ∧
        (∀ s : D.ι ⊕ D.ι0, leftData D s = completedPointMap
        (BlowupChart (ConcreteSurface O pi u a b) t x) (leftPoint D s)
        (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) t x) (c i) *
        (chartSlope (ConcreteSurface O pi u a b) t x)^i.val) ∧
        (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) t x) (c i) *
        (chartSlope (ConcreteSurface O pi u a b) t x)^i.val) ∈ leftPoint D s) ∧
        (∀ s : D.ι ⊕ D.ιinf, Ideal.span {rightData D s} = Ideal.span
        {completedPointMap (BlowupChart (ConcreteSurface O pi u a b) x t) (rightPoint D s)
        (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) x t) (c i) *
        (chartSlope (ConcreteSurface O pi u a b) x t)^(d - i.val))} ∧
        (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) x t) (c i) *
        (chartSlope (ConcreteSurface O pi u a b) x t)^(d - i.val)) ∈ rightPoint D s) ∧
        (∀ s : D.ι ⊕ D.ι0, strictTransformAt (ConcreteSurface O pi u a b) t x (leftPoint D s) d J =
        Ideal.span {leftData D s}) ∧ (∀ s : D.ι ⊕ D.ιinf, strictTransformAt
        (ConcreteSurface O pi u a b) x t (rightPoint D s) d J = Ideal.span {rightData D s}) ∧
        MatchesDivisor e D Dv ∧ curveDataDegree D = exceptionalDegree
        (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)) Dv := by
  subst ht hx
  exact fixed_tangent_cell_curve_datum O pi hpi u a b ha S hS e he heZ Dv s d J hJ beta

/-- If a form `∑ᵢ cᵢ tᵈ⁻ⁱ xⁱ` of degree `d` does not lie in `(t, x)ᵈ⁺¹`, then some coefficient
`cᵢ` does not lie in `(t, x)`. -/
private theorem exists_coeff_notMem_span_of_notMem_pow {R : Type} [CommRing R] (t x : R) (d : ℕ)
    (c : Fin (d + 1) → R)
    (h : ∑ i : Fin (d + 1), c i * t ^ (d - i.val) * x ^ i.val ∉ Ideal.span {t, x} ^ (d + 1)) :
    ∃ i : Fin (d + 1), c i ∉ Ideal.span {t, x} := by
  by_contra! hc
  refine h (Ideal.sum_mem _ fun i _ ↦ ?_)
  have := Ideal.mul_mem_mul (hc i) (Ideal.mul_mem_mul
    (Ideal.pow_mem_pow (Ideal.subset_span (by simp) : t ∈ Ideal.span ({t, x} : Set R)) (d - i.val))
    (Ideal.pow_mem_pow (Ideal.subset_span (by simp) : x ∈ Ideal.span ({t, x} : Set R)) i.val))
  rw [← Ideal.IsTwoSided.pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp i.isLt)] at this
  rwa [mul_assoc, Ideal.IsTwoSided.pow_succ]

/-- **The index map of a cell.** For a cell ideal `J` of a concrete member and child quotients
`B j ≅ R_j ⧸ Φ J j`, there is an injective `O`-algebra map `R ⧸ J → ∏ B j` with cokernel of length
`d(d-1)/2` (`d` the cell degree), compatible with the child maps `α j`. -/
theorem cell_member_index_map (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c)
    (J : Ideal m.R) (hJ : J ∈ m.toMeasured.cell c) (B : m.toMeasured.childIdx c → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra m.O (B j)] (eB : ∀ j, B j ≃+* (D.mc j).R ⧸ D.Φ J j)
    (hB : ∀ (j : m.toMeasured.childIdx c) (r : m.O), eB j (algebraMap m.O (B j) r) =
    Ideal.Quotient.mk (D.Φ J j) (algebraMap m.O (D.mc j).R r)) :
    ∃ ψ : (m.R ⧸ J) →ₐ[m.O] ∀ j, B j, Function.Injective ψ ∧ Module.length m.O
        ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = (chooseTwo (m.toMeasured.cellDegree c) : ℕ∞)
        ∧ ∀ (r : m.R) (j : m.toMeasured.childIdx c), eB j (ψ (Ideal.Quotient.mk J r) j) =
        Ideal.Quotient.mk (D.Φ J j) (D.alpha j r) := by
  set d := m.toMeasured.cellDegree c
  obtain ⟨beta⟩ := actual_blowup_restriction_exists m.R m.S.t m.S.x
  obtain ⟨f, cf, Df, hJf, hcf, hl, hr, hstl, hstr, hmatch, hdeg⟩ :=
    fixed_tangent_cell_curve_datum_of_eq m.O m.pi m.hpi m.u m.a m.b m.ha m.S.t m.S.x m.hS_t m.hS_x
      m.S ⟨rfl, rfl⟩ D.e D.he D.heZ c.2.1 m.s d J hJ beta
  have hdeg' : curveDataDegree Df = d := hdeg.trans c.2.2.1
  have hreg : RegularParameterPair m.R m.S.t m.S.x := by
    rw [m.hS_t, m.hS_x]
    exact concrete_surface_regular_pair_tx m.O m.pi m.hpi.ne_zero m.u m.a m.b m.ha
  have hregSwap : RegularParameterPair m.R m.S.x m.S.t := by
    rw [m.hS_t, m.hS_x]
    exact concrete_surface_regular_pair_xt m.O m.pi m.hpi.ne_zero m.u m.a m.b m.ha
  have hmultJ := has_tangent_divisor_multiplicity m.O m.R m.S hreg J d c.2.1 hJ.2
  have hmax : IsLocalRing.maximalIdeal m.R = Ideal.span {m.S.t, m.S.x} := by
    rw [concrete_surface_maximalIdeal_eq m.O m.pi m.hpi m.u m.a m.b m.ha, surfaceParameterIdeal,
        m.hS_t, m.hS_x]
  have hd : f ∈ (Ideal.span {m.S.t, m.S.x})^d := by
    have := hmultJ.1; rwa [hJf, Ideal.span_singleton_le_iff_mem, hmax] at this
  have hmult : f ∉ (Ideal.span {m.S.t, m.S.x})^(d+1) := by
    have := hmultJ.2; rwa [hJf, Ideal.span_singleton_le_iff_mem, hmax] at this
  have hne : ∃ i : Fin (d+1), cf i ∉ Ideal.span {m.S.t, m.S.x} :=
    exists_coeff_notMem_span_of_notMem_pow m.S.t m.S.x d cf (hcf ▸ hmult)
  have hpos := cell_datum_multiplicities_pos_of_eq m.O m.pi m.hpi m.u m.a m.b m.ha m.S.t m.S.x
    m.hS_t m.hS_x d cf hne D.e D.he D.heZ beta Df hl hr
  obtain ⟨ee, hee⟩ := cell_datum_point_equiv m c D J beta Df ⟨hstl, hstr⟩ hmatch hpos
  choose ι hι1 hι2 using hee
  obtain ⟨f', G, hf', hG⟩ := concrete_two_chart_glued_generators_exist_of_eq m.O m.pi m.hpi m.u m.a
    m.b m.ha m.S.t m.S.x m.hS_t m.hS_x beta Df
  have : (Ideal.span ({m.S.t, m.S.x} : Set m.R)).IsMaximal := by
    rw [m.hS_t, m.hS_x]
    exact concrete_surface_parameterIdeal_isMaximal m.O m.pi m.hpi m.u m.a m.b m.ha
  have : IsNoetherianRing m.R := concrete_surface_isNoetherianRing m.O m.pi m.u m.a m.b
  have : IsNoetherianRing (BlowupChart m.R m.S.t m.S.x) :=
    blowupChart_concrete_isNoetherianRing m.O m.pi m.u m.a m.b _ _
  have : IsNoetherianRing (BlowupChart m.R m.S.x m.S.t) :=
    blowupChart_concrete_isNoetherianRing m.O m.pi m.u m.a m.b _ _
  have hregF := fun j ↦ two_chart_left_generators_regular_on_overlap m.R m.S.t m.S.x beta Df _ G
    hG hreg hregSwap j
  have h910 := two_chart_datum_concrete_instances_of_eq m.O m.pi m.hpi m.u m.a m.b m.ha m.S.t m.S.x
    m.hS_t m.hS_x beta Df
  have hmem := strict_transforms_give_level_lattice_membership m.R m.S.t m.S.x beta Df
    (curveDataDegree Df) G hG f (hdeg' ▸ hd) (fun s ↦ by rw [hdeg', ← hJf]; exact hstl s)
    (fun s ↦ by rw [hdeg', ← hJf]; exact hstr s)
  have hJf' : J = Ideal.span {f'} := hJf.trans <| parent_ideal_unique_of_level_lattice m.R m.S.t
    m.S.x hreg hregSwap beta _ G hregF f' hf' f hmem (hdeg' ▸ hmult)
  have hmapΦ : ∀ j, Ideal.span {localCurve Df (ee j)} =
      (D.Φ J j).map (((D.Eq j).symm.trans (ι j) : (D.mc j).R ≃+* localRing Df (ee j)) :
        (D.mc j).R →+* localRing Df (ee j)) := by
    intro j
    rw [cell_child_Phi_eq_map m c D J j, Ideal.map_map, ← hι2 j]
    congr 1
    ext y
    simp
  let qE : ∀ j, (D.mc j).R ⧸ D.Φ J j ≃+* localRing Df (ee j) ⧸ Ideal.span {localCurve Df (ee j)} :=
    fun j => Ideal.quotientEquiv _ _ ((D.Eq j).symm.trans (ι j)) (hmapΦ j)
  have hqE : ∀ j (r : m.R), qE j (Ideal.Quotient.mk (D.Φ J j) (D.alpha j r)) =
      Ideal.Quotient.mk _ (localFromSurface Df (ee j) r) := by
    intro j r
    change Ideal.Quotient.mk _ (ι j
        ((D.Eq j).symm (D.Eq j (divisorFromSurface m.R m.S.t m.S.x D.e c.2.1 D.hinf
      (D.point j) r)))) = _
    rw [RingEquiv.symm_apply_apply, hι1]
  let eB' : ∀ j, B j ≃+* localRing Df (ee j) ⧸ Ideal.span {localCurve Df (ee j)} :=
    fun j => (eB j).trans (qE j)
  have hB' : ∀ (j : m.toMeasured.childIdx c) (r : m.O), eB' j (algebraMap m.O (B j) r) =
      Ideal.Quotient.mk (Ideal.span {localCurve Df (ee j)})
          (localFromSurface Df (ee j) (algebraMap m.O m.R r)) := by
    intro j r
    change qE j (eB j (algebraMap m.O (B j) r)) = _
    rw [hB, ← (D.alpha j).commutes r, hqE]
  obtain ⟨ψ', hinj, hlen, hform⟩ := concrete_index_map_reindexed_of_eq m.O m.pi m.hpi m.u m.a m.b
    m.ha m.S.t m.S.x m.hS_t m.hS_x beta Df f' G hf' hG _ ee B eB' hB'
  let E := Ideal.quotientEquivAlgOfEq m.O hJf'
  refine ⟨ψ'.comp E.toAlgHom, hinj.comp E.injective, ?_, fun r j ↦ (qE j).injective ?_⟩
  · rw [AlgHom.comp_toLinearMap, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr E.surjective), hlen, hdeg']
  · rw [hqE]
    exact hform r j

private theorem one_le_chooseTwo_of_selfPattern (s : State) (hv : s.Valid)
    (hnt : s.terminal = false)
    (P : TangentPattern s.degree)
    (hA : Allowed s P) (hs : SelfPattern s P) : 1 ≤ chooseTwo P.d.val := by
  cases s with
  | crossing a b c h =>
    obtain ⟨a', c', h', -⟩ := hs
    cases h'
  | single a c₀ =>
    obtain ⟨a', c', h', hch⟩ := hs
    cases h'
    have hc : 2 ≤ c₀ := by
      rcases hv with ⟨-, hc0⟩
      by_contra hlt
      have : c₀ = 1 := by omega
      subst this
      simp [State.terminal] at hnt
    have := (self_patterns_of_single_state a c₀ 2 hv.1 hc).1 P hA ⟨a, c₀, rfl, hch⟩
    rw [this.1]
    unfold chooseTwo
    apply Nat.div_pos _ (by norm_num)
    rcases c₀ with _ | _ | k
    · omega
    · omega
    · simp only [Nat.add_sub_cancel]; nlinarith

/-- The child quotients `B j ≅ R_j ⧸ Φ J j` of a cell ideal are free and finite over `O_j`. -/
private theorem cellChild_free_finite (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c)
    (J : Ideal m.R) (hJ : J ∈ m.toMeasured.cell c) (B : m.toMeasured.childIdx c → Type)
    [∀ j, CommRing (B j)] (eB : ∀ j, B j ≃+* (D.mc j).R ⧸ D.Φ J j)
    [∀ j, Algebra (D.mc j).O (B j)] (hBalg : ∀ (j : m.toMeasured.childIdx c)
    (o : (D.mc j).O), eB j (algebraMap (D.mc j).O (B j) o) = Ideal.Quotient.mk (D.Φ J j)
    (algebraMap (D.mc j).O (D.mc j).R o)) (j : m.toMeasured.childIdx c) :
    Module.Free (D.mc j).O (B j) ∧ Module.Finite (D.mc j).O (B j) := by
  have hmem : D.Φ J j ∈ (D.mc j).toMeasured.stateSet :=
    (cell_child_bijOn m c D).mapsTo hJ j (Set.mem_univ j)
  obtain ⟨_, _, -⟩ := concrete_member_curve_order_free (D.mc j) _ hmem
  let e : B j ≃ₐ[(D.mc j).O] (D.mc j).R ⧸ D.Φ J j :=
    AlgEquiv.ofRingEquiv (f := eB j) fun o ↦ by rw [hBalg j o]; rfl
  exact ⟨.of_equiv e.symm.toLinearEquiv, .equiv e.symm.toLinearEquiv⟩

/-- Termination data for the children of a cell ideal with algebra type `σ`: each child has an
algebra type, and its order defect is at most that of `R ⧸ J`, strictly smaller on self cells. -/
private theorem cell_child_termination_data (m : ConcreteMember) (c : m.cellIndex)
    (hnt : m.s.terminal = false) (D : CellChildData m c) (J : Ideal m.R)
    (hJ : J ∈ m.toMeasured.cell c) (B : m.toMeasured.childIdx c → Type) [∀ j, CommRing (B j)]
    [∀ j, Algebra m.O (B j)] (eB : ∀ j, B j ≃+* (D.mc j).R ⧸ D.Φ J j)
    (hB : ∀ (j : m.toMeasured.childIdx c) (r : m.O), eB j (algebraMap m.O (B j) r) =
    Ideal.Quotient.mk (D.Φ J j) (algebraMap m.O (D.mc j).R r)) [∀ j, Algebra (D.mc j).O (B j)]
    [∀ j, IsScalarTower m.O (D.mc j).O (B j)] (hBalg : ∀ (j : m.toMeasured.childIdx c)
    (o : (D.mc j).O), eB j (algebraMap (D.mc j).O (B j) o) = Ideal.Quotient.mk (D.Φ J j)
    (algebraMap (D.mc j).O (D.mc j).R o)) (σ : FactorType) (hσ : HasAlgebraType m.O (m.R ⧸ J) σ) :
    ∀ j, (∃ τ : FactorType, HasAlgebraType (D.mc j).O (B j) τ) ∧
        (orderDefect (D.mc j).O (B j)).toNat ≤ (orderDefect m.O (m.R ⧸ J)).toNat ∧
        (m.toMeasured.IsSelfCell c → (orderDefect (D.mc j).O (B j)).toNat <
        (orderDefect m.O (m.R ⧸ J)).toNat) := by
  obtain ⟨ψ, hψi, hlen, -⟩ := cell_member_index_map m c D J hJ B eB hB
  obtain ⟨hfree, hfin, -⟩ := concrete_member_curve_order_free m J hJ.1
  have hfr := cellChild_free_finite m c D J hJ B eB hBalg
  have key := @concrete_termination_data_of_index_map m _ (fun j => D.mc j) _ _ _
    (fun j => m.toMeasured.childDelta c j) (fun j => (D.child j).hrank)
    (fun j => by rw [← (D.child j).hpi]; exact (D.mc j).hpi) J B _ _ _ _ (fun j => (hfr j).2)
    (fun j => (hfr j).1) ψ hψi (chooseTwo (m.toMeasured.cellDegree c)) hlen hfin hfree σ hσ
  intro j
  obtain ⟨h1, h2, h3⟩ := key j
  exact ⟨h1, h2, fun hs ↦
    h3 (one_le_chooseTwo_of_selfPattern m.s m.toMeasured.valid hnt c.1.1 c.1.2 hs)⟩

/-- **Type additivity.** If the children `B j` of a cell ideal `J` have algebra types `τ j`, then
`R ⧸ J` has algebra type `∑ j, scaleType δ_j (τ j)`. -/
private theorem cell_child_type_add (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c)
    (J : Ideal m.R) (hJ : J ∈ m.toMeasured.cell c) (B : m.toMeasured.childIdx c → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra m.O (B j)] (eB : ∀ j, B j ≃+* (D.mc j).R ⧸ D.Φ J j)
    (hB : ∀ (j : m.toMeasured.childIdx c) (r : m.O), eB j (algebraMap m.O (B j) r) =
    Ideal.Quotient.mk (D.Φ J j) (algebraMap m.O (D.mc j).R r)) [∀ j, Algebra (D.mc j).O (B j)]
    [∀ j, IsScalarTower m.O (D.mc j).O (B j)] (hBalg : ∀ (j : m.toMeasured.childIdx c)
    (o : (D.mc j).O), eB j (algebraMap (D.mc j).O (B j) o) = Ideal.Quotient.mk (D.Φ J j)
    (algebraMap (D.mc j).O (D.mc j).R o)) (τ : m.toMeasured.childIdx c → FactorType)
    (hτ : ∀ j, HasAlgebraType (D.mc j).O (B j) (τ j)) :
    HasAlgebraType m.O (m.R ⧸ J) (∑ j, scaleType (m.toMeasured.childDelta c j) (τ j)) := by
  obtain ⟨ψ, hψ, hlen, -⟩ := cell_member_index_map m c D J hJ B eB hB
  have hfr := cellChild_free_finite m c D J hJ B eB hBalg
  have : ∀ j, Module.Free (D.mc j).O (B j) := fun j ↦ (hfr j).1
  have : ∀ j, Module.Finite (D.mc j).O (B j) := fun j ↦ (hfr j).2
  exact concrete_type_add_of_index_map m _ D.mc (m.toMeasured.childDelta c)
    (fun j => (D.child j).hrank) (fun j => by rw [← (D.child j).hpi]; exact (D.mc j).hpi) J B ψ hψ
        _ hlen τ hτ

/-! ### Every state ideal lies in a cell -/

/-- Every ideal in a state set of a concrete surface has a positive multiplicity `d`. -/
private theorem state_ideal_has_multiplicity (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hSt : S.t = surfaceT O pi u a b) (s : State)
    (J : Ideal (ConcreteSurface O pi u a b))
    (hJ : J ∈ surfaceStateSet O (ConcreteSurface O pi u a b) S s) :
    ∃ d : ℕ, 0 < d ∧ HasMultiplicity (ConcreteSurface O pi u a b) J d := by
  classical
  set R := ConcreteSurface O pi u a b
  obtain ⟨f, hf⟩ := hJ.1
  have hfm : f ∈ IsLocalRing.maximalIdeal R :=
    surface_state_generator_mem_maximal O R S s J hJ f hf
  -- contact is finite
  have hfin : ∃ c : ℕ, idealContact R J S.t = c := by
    have h2 := hJ.2.2
    cases s with
    | single a' c => exact ⟨c, h2.2.2⟩
    | crossing a' b' c h => exact ⟨c, h2.2.2.1⟩
  have hf0 : f ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := hfin
    have hJ0 : J = ⊥ := by rw [hf, h0]; simp
    unfold idealContact at hc
    rw [hJ0, hSt] at hc
    obtain ⟨q, -⟩ := concrete_surface_quotient_T_equiv O pi hpi u a b ha
    let e : (R ⧸ (⊥ ⊔ Ideal.span {surfaceT O pi u a b})) ≃+*
        (PowerSeries (IsLocalRing.ResidueField O) ⧸
          Ideal.span {(0 : PowerSeries (IsLocalRing.ResidueField O))}) :=
      (Ideal.quotEquivOfEq (by simp)).trans
        (q.trans ((RingEquiv.quotientBot _).symm.trans
          (Ideal.quotEquivOfEq (by simp)).symm))
    have := quotient_ring_length_intrinsic _ _ _ _ e
    have h3 := (powerSeries_quotient_length_eq_order (IsLocalRing.ResidueField O) 0).1
    rw [hc] at this
    rw [← this] at h3
    simp at h3
  have hne : IsLocalRing.maximalIdeal R ≠ ⊤ := IsLocalRing.maximalIdeal.isMaximal R |>.ne_top
  have hK := iInf_sup_pow_eq_of_isLocalRing R (IsLocalRing.maximalIdeal R) ⊥ hne
  have hex : ∃ n : ℕ, f ∉ (IsLocalRing.maximalIdeal R)^(n+1) := by
    by_contra hcon
    push Not at hcon
    have : f ∈ (⨅ n : ℕ, ⊥ ⊔ (IsLocalRing.maximalIdeal R)^n) := by
      rw [Ideal.mem_iInf]
      intro n
      rcases n with _ | n
      · simp
      · simpa using hcon n
    rw [hK] at this
    exact hf0 (by simpa using this)
  have hpos : Nat.find hex ≠ 0 := fun h0 ↦ by
    have := Nat.find_spec hex
    rw [h0] at this
    exact this (by simpa using hfm)
  refine ⟨Nat.find hex, Nat.pos_of_ne_zero hpos, ?_,
    fun hle ↦ Nat.find_spec hex (hle (hf ▸ Ideal.mem_span_singleton_self f))⟩
  rw [hf, Ideal.span_le, Set.singleton_subset_iff]
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [hk]
  exact not_not.mp (Nat.find_min hex (show k < Nat.find hex by omega))

private theorem le_and_lt_iff_of_natCast_eq_add (d c : ℕ) (ℓ : ℕ∞) (h : (c : ℕ∞) = (d : ℕ∞) + ℓ) :
    d ≤ c ∧ (d < c ↔ ℓ ≠ 0) := by
  induction ℓ using ENat.recTopCoe with
  | top => simp at h
  | coe n =>
    obtain rfl : c = d + n := by exact_mod_cast h
    exact ⟨by omega, by simp; omega⟩

/-- For a state ideal `J = (f)` with `f = ∑ cᵢ tᵈ⁻ⁱ xⁱ` of multiplicity `d`, the multiplicity is
bounded by the contact orders of the state, with strict inequality exactly when the corresponding
boundary coefficient lies in the maximal ideal. -/
private theorem state_ideal_multiplicity_le_contacts (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hSt : S.t = surfaceT O pi u a b)
    (hSx : S.x = surfaceX O pi u a b) (s : State) (J : Ideal (ConcreteSurface O pi u a b))
    (hJ : J ∈ surfaceStateSet O (ConcreteSurface O pi u a b) S s) (d : ℕ)
    (f : (ConcreteSurface O pi u a b)) (hf : J = Ideal.span {f})
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hc : f = (∑ i : Fin (d + 1), c i * (surfaceT O pi u a b) ^ (d - i.val) *
    (surfaceX O pi u a b) ^ i.val)) :
    match s with
    | State.single _ c₀ =>
      d ≤ c₀ ∧ (d < c₀ ↔ c (Fin.last d) ∈ IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b))
    | State.crossing _ _ c₀ h₀ =>
      d ≤ c₀ ∧ (d < c₀ ↔ c (Fin.last d) ∈ IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b)) ∧
        d ≤ h₀ ∧ (d < h₀ ↔ c 0 ∈ IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b)) := by
  set t := surfaceT O pi u a b
  set x := surfaceX O pi u a b
  have hpi0 : pi ≠ 0 := hpi.ne_zero
  have hmax : IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b) = Ideal.span {t, x} := by
    rw [← S.parameters, hSt, hSx]
  have hmax' : IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b) = Ideal.span {x, t} := by
    rw [hmax, Ideal.span_pair_comm]
  have : (Ideal.span ({t, x} : Set (ConcreteSurface O pi u a b))).IsMaximal := by
    rw [← hmax]; exact IsLocalRing.maximalIdeal.isMaximal (ConcreteSurface O pi u a b)
  have : (Ideal.span ({x, t} : Set (ConcreteSurface O pi u a b))).IsMaximal := by
    rw [← hmax']; exact IsLocalRing.maximalIdeal.isMaximal (ConcreteSurface O pi u a b)
  -- t-contact
  have ht := (boundary_contact_of_twisted_generator (ConcreteSurface O pi u a b) t x
    (concrete_surface_regular_pair_tx O pi hpi0 u a b ha) d f c hc).2
  have htn := boundary_contact_length_ne_zero_iff (ConcreteSurface O pi u a b) t x hmax d c
  -- x-contact
  have hc' : f = ∑ j : Fin (d+1), c (Fin.rev j) * x^(d - j.val) * t^j.val := by
    rw [hc, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have hj := j.isLt
    rw [show d - (d + 1 - (j.val + 1)) = j.val by omega,
      show d + 1 - (j.val + 1) = d - j.val by omega]
    ring
  have hx := (boundary_contact_of_twisted_generator (ConcreteSurface O pi u a b) x t
    (concrete_surface_regular_pair_xt O pi hpi0 u a b ha) d f (fun j => c (Fin.rev j)) hc').2
  have hxn := boundary_contact_length_ne_zero_iff (ConcreteSurface O pi u a b) x t hmax' d
      (fun j => c (Fin.rev j))
  simp only [Fin.rev_last] at hxn
  obtain ⟨-, -, hs⟩ := hJ
  rw [hf] at hs
  cases s with
  | single a' c₀ =>
    obtain ⟨-, -, h1⟩ := hs
    unfold idealContact at h1
    rw [hSt, ht] at h1
    exact (le_and_lt_iff_of_natCast_eq_add d c₀ _ h1.symm).imp_right (·.trans htn)
  | crossing a' b' c₀ h₀ =>
    obtain ⟨-, -, h1, h2⟩ := hs
    unfold idealContact at h1 h2
    rw [hSt, ht] at h1
    rw [hSx, hx] at h2
    have e1 := le_and_lt_iff_of_natCast_eq_add d c₀ _ h1.symm
    have e2 := le_and_lt_iff_of_natCast_eq_add d h₀ _ h2.symm
    exact ⟨e1.1, e1.2.trans htn, e2.1, e2.2.trans hxn⟩

private theorem allowed_pattern_of_cell_ideal (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    [IsDomain (ConcreteSurface O pi u a b)] [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hSt : S.t = surfaceT O pi u a b)
    (hSx : S.x = surfaceX O pi u a b) (s : State) (J : Ideal (ConcreteSurface O pi u a b))
    (hJ : J ∈ surfaceStateSet O (ConcreteSurface O pi u a b) S s) (d : ℕ)
    (f : (ConcreteSurface O pi u a b)) (hf : J = Ideal.span {f})
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hc : f = (∑ i : Fin (d + 1), c i * (surfaceT O pi u a b) ^ (d - i.val) *
        (surfaceX O pi u a b) ^ i.val))
    {k : Type} [Field k] (Dv : ExceptionalDivisor k)
    (e1 : 0 < Dv (infinityDirection k) ↔ c (Fin.last d) ∈ IsLocalRing.maximalIdeal
        (ConcreteSurface O pi u a b))
    (e0 : 0 < Dv (zeroDirection k) ↔ c 0 ∈ IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b))
    (hs : s.Valid) [Finite k] (hd : 0 < d) (hdeg : exceptionalDegree k Dv = d)
    (hQ : ∀ Q, 0 < Dv Q → directionDegree k Q ≤ d) (hmult : ∀ Q, Dv Q ≤ d) :
    ∃ P : TangentPattern s.degree, P.d.val = d ∧ Allowed s P ∧ HasPattern k s Dv P := by
  have hcon := state_ideal_multiplicity_le_contacts O pi hpi u a b ha S hSt hSx s J hJ
    d f hf c hc
  cases s with
  | single a' c' =>
    obtain ⟨h1, h2⟩ := hcon
    exact allowed_pattern_of_divisor k _ hs Dv d hd hdeg hQ hmult ⟨h1, e1.trans h2.symm⟩
  | crossing a' b' c' h' =>
    obtain ⟨h1, h2, h3, h4⟩ := hcon
    exact allowed_pattern_of_divisor k _ hs Dv d hd hdeg hQ hmult
      ⟨h1, e1.trans h2.symm, h3, e0.trans h4.symm⟩

/-- The cells of a concrete member cover its state set. -/
theorem concrete_member_cells_cover (m : ConcreteMember) :
    m.toMeasured.stateSet = ⋃ c : m.toMeasured.cellIndex, m.toMeasured.cell c := by
  ext J
  simp only [Set.mem_iUnion]
  refine ⟨fun hJ ↦ ?_, fun ⟨_, hc⟩ ↦ hc.1⟩
  change J ∈ surfaceStateSet m.O m.R m.S m.s at hJ
  obtain ⟨d, hd, hmul⟩ := state_ideal_has_multiplicity m.O m.pi m.hpi m.u m.a m.b m.ha m.S
    m.hS_t m.s J hJ
  obtain ⟨f, hf⟩ := hJ.1
  have hf1 : f ∈ (IsLocalRing.maximalIdeal m.R)^d :=
    hmul.1 (hf ▸ Ideal.subset_span (Set.mem_singleton f))
  have hf2 : f ∉ (IsLocalRing.maximalIdeal m.R)^(d+1) := fun h ↦
    hmul.2 (by rw [hf, Ideal.span_le, Set.singleton_subset_iff]; exact h)
  have hmax : IsLocalRing.maximalIdeal m.R = Ideal.span {surfaceT m.O m.pi m.u m.a m.b,
      surfaceX m.O m.pi m.u m.a m.b} := by
    rw [← m.hS_t, ← m.hS_x]; exact m.S.parameters.symm
  obtain ⟨c, hc, i₀, hi₀⟩ := has_multiplicity_initial_form m.R _ _ hmax d f hf1 hf2
  set H : Polynomial (IsLocalRing.ResidueField m.R) :=
    ∑ i : Fin (d+1), Polynomial.C (IsLocalRing.residue m.R (c i)) * Polynomial.X^i.val with hH
  have hcoeff : ∀ n : Fin (d+1), H.coeff n = IsLocalRing.residue m.R (c n) := by
    intro n
    rw [hH, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow, Fin.val_inj]
    simp
  have hH0 : H ≠ 0 := by
    intro h0
    have := hcoeff i₀
    rw [h0, Polynomial.coeff_zero, eq_comm, IsLocalRing.residue_eq_zero_iff] at this
    exact hi₀ this
  have hdeg : H.natDegree ≤ d := by
    rw [hH]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.isLt)
  obtain ⟨Dv, hDv, hinf, haff, hdegDv⟩ := homogeneous_divisor_of_polynomial _ d H hH0 hdeg
  have hT := initial_form_has_tangent_divisor m.O m.R m.S d f c
    (by rw [m.hS_t, m.hS_x]; exact hc) H hH Dv hDv
  obtain ⟨b1, b2, b3, b4⟩ := homogeneous_divisor_boundary_multiplicities _ d H hH0 hdeg Dv hinf
      haff
  have e1 : 0 < Dv (infinityDirection _) ↔ c (Fin.last d) ∈ IsLocalRing.maximalIdeal m.R := by
    rw [b1, ← IsLocalRing.residue_eq_zero_iff]
    have := hcoeff (Fin.last d); simp only [Fin.val_last] at this; rw [this]
  have e0 : 0 < Dv (zeroDirection _) ↔ c 0 ∈ IsLocalRing.maximalIdeal m.R := by
    rw [b2, ← IsLocalRing.residue_eq_zero_iff]
    have := hcoeff 0; simp only [Fin.val_zero] at this; rw [this]
  have : Finite (IsLocalRing.ResidueField m.R) := Finite.of_equiv _ m.S.residueEquiv.toEquiv
  obtain ⟨P, hPd, hPa, hPD⟩ := allowed_pattern_of_cell_ideal m.O m.pi m.hpi m.u m.a m.b m.ha m.S
    m.hS_t m.hS_x m.s J hJ d f hf c hc Dv e1 e0 (m.shape.valid m.ha)
    hd hdegDv b4 b3
  refine ⟨⟨⟨P, hPa⟩, ⟨Dv, hPD⟩⟩, ?_⟩
  change J ∈ fixedTangentCell m.O m.R m.S m.s P.d.val Dv
  rw [hPd]
  exact ⟨hJ, hf ▸ hT⟩

/-! ### Existence of a concrete universe -/

/-- A concrete universe exists provided the child maps of all cells are measurable and scale the
measure by `q^{-tri d}` on boxes. -/
private theorem concrete_universe_of_cell_measure (hmeas : ∀ (m : ConcreteMember) (c : m.cellIndex)
    (D : CellChildData m c), m.s.terminal = false → ∀
    (G : ∀ j : m.toMeasured.childIdx c, Set (Ideal (D.mc j).toMeasured.R)),
    (∀ j, MeasurableSet (G j)) → MeasurableSet (m.toMeasured.cell c ∩ (fun J j => D.Φ J j) ⁻¹'
    Set.pi Set.univ G)) (hmass : ∀ (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c),
    m.s.terminal = false → ∀ (G : ∀ j : m.toMeasured.childIdx c, Set
    (Ideal (D.mc j).toMeasured.R)), (∀ j, MeasurableSet (G j)) → m.toMeasured.μ
    (m.toMeasured.cell c ∩ (fun J j => D.Φ J j) ⁻¹' Set.pi Set.univ G) = (m.toMeasured.q : ℝ≥0∞)⁻¹
    ^ tri (m.toMeasured.cellDegree c) * ∏ j, (D.mc j).toMeasured.μ (G j)) :
    ConcreteUniverse := by
  let D : ∀ (m : ConcreteMember) (c : m.cellIndex), CellChildData m c :=
    fun m c => Classical.choice (cell_child_data_exists m c)
  let U : SurfaceUniverse :=
    { ι := ConcreteMember
      M := ConcreteMember.toMeasured
      stateSet_measurable := concrete_member_stateSet_measurable
      volume := concrete_member_volume
      divisors_finite := fun m => (concrete_member_divisor_count m).1
      divisor_count := fun m => (concrete_member_divisor_count m).2
      cell_measurable := fun m _ c => concrete_member_cell_measurable m c
      cells_cover := fun m _ => concrete_member_cells_cover m
      cells_disjoint := fun m _ => concrete_member_cells_disjoint m
      child := fun m c j => (D m c).mc j
      child_state := fun m c j => ((D m c).child j).hstate
      child_residue := fun m c j => ((D m c).child j).hcard
      Φ := fun m c J j => (D m c).Φ J j
      Φ_bij := fun m _ c => cell_child_bijOn m c (D m c)
      Φ_measurable := fun m hnt c G hG => hmeas m c (D m c) hnt G hG
      Φ_measure := fun m hnt c G hG => hmass m c (D m c) hnt G hG
      type_add := fun m _ c J hJ τ hτ =>
        cell_child_type_add m c (D m c) J hJ (fun j => ((D m c).mc j).R ⧸ (D m c).Φ J j)
          (fun j => RingEquiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl) τ hτ
      terminal_type := fun m a hs J hJ => concrete_member_terminal_type m a hs J hJ }
  refine ⟨U, Equiv.refl _, fun _ => rfl, ?_, ?_⟩
  · intro i hnt c J hJ σ hσ j
    exact (cell_child_termination_data i c hnt (D i c) J hJ
        (fun j => ((D i c).mc j).R ⧸ (D i c).Φ J j)
      (fun j => RingEquiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl) σ hσ j).1
  · rintro i hnt c J hJ ⟨σ, hσ⟩ j
    exact (cell_child_termination_data i c hnt (D i c) J hJ
        (fun j => ((D i c).mc j).R ⧸ (D i c).Φ J j)
      (fun j => RingEquiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl) σ hσ j).2

private theorem firstContact_pointChildState (k : Type) [Field k] (s : State) (d : ℕ)
    (Dv : ExceptionalDivisor k) (Q : ClosedDirection k) :
    (pointChildState k s d Dv Q).firstContact = Dv Q := by
  cases s <;> unfold pointChildState <;> split_ifs <;> rfl

private theorem cellChild_algebraMap_pi (m : ConcreteMember) (c : m.cellIndex)
    (D : CellChildData m c) : ∀ j,
    algebraMap m.O (D.mc j).O m.S.pi = (D.mc j).S.pi := by
  intro j
  rw [m.hS_pi, (D.mc j).hS_pi, ← (D.child j).hpi]

private theorem cellChild_degree_sum (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c)
    : ∑ j,
    m.toMeasured.childDelta c j * (D.mc j).toMeasured.s.degree = m.toMeasured.s.degree := by
  rw [← member_children_degree_sum m c]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ * (D.child j).mc.s.degree = _
  rw [(D.child j).hstate]

private theorem cellChild_pi_pow_eq (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c)
    : ∀ j, ∃
    (s : ℕ) (cj : (D.mc j).R), algebraMap m.O (D.mc j).R m.S.pi ^ s = (D.mc j).S.t ^
    m.toMeasured.cellDegree c * cj := by
  intro j
  refine ⟨m.toMeasured.cellDegree c, ((D.mc j).S.unit : (D.mc j).R) ^ m.toMeasured.cellDegree c *
      (D.mc j).S.t ^ (m.toMeasured.cellDegree c * ((D.mc j).S.a - 1)) * (D.mc j).S.x ^
      (m.toMeasured.cellDegree c * (D.mc j).S.b), ?_⟩
  rw [IsScalarTower.algebraMap_apply m.O (D.mc j).O (D.mc j).R, cellChild_algebraMap_pi m c D j,
    (D.mc j).S.vertical]
  have ha := (D.mc j).S.a_pos
  obtain ⟨k, hk⟩ : ∃ k, (D.mc j).S.a = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos ha).symm⟩
  rw [hk, Nat.add_sub_cancel]
  ring

private theorem cellChild_firstContact_sum (m : ConcreteMember) (c : m.cellIndex)
    (D : CellChildData m c) : ∑ j,
    m.toMeasured.childDelta c j * (D.mc j).toMeasured.s.firstContact = m.toMeasured.cellDegree c :=
    by
  have h1 : ∀ j, m.toMeasured.childDelta c j * (D.mc j).toMeasured.s.firstContact = directionDegree
      _ (D.asg.pt j) * c.2.1 (D.asg.pt j) := by
    intro j
    change _ * (D.child j).mc.s.firstContact = _
    rw [(D.child j).hstate]
    have hd := D.asg.deg j
    have hs := D.asg.state j
    change ((children m.s c.1.1).get j).1 * ((children m.s c.1.1).get j).2.firstContact = _
    rw [← hd, hs]
    rw [firstContact_pointChildState]
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  have h2 := c.2.2.1
  change _ = c.1.1.d.val
  rw [← h2, exceptionalDegree, Finsupp.sum]
  refine Finset.sum_bij (fun j _ => D.asg.pt j) ?_ ?_ ?_ ?_
  · intro j _
    rw [Finsupp.mem_support_iff]
    exact Nat.pos_iff_ne_zero.mp ((D.asg.supp _).mpr ⟨j, rfl⟩)
  · intro a _ b _ h; exact D.asg.inj h
  · intro Q hQ
    obtain ⟨j, hj⟩ := (D.asg.supp Q).mp (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hQ))
    exact ⟨j, Finset.mem_univ _, hj⟩
  · intro j _; rfl

private theorem divisorFromSurface_t_x_dvd (R : Type) [CommRing R] (t x : R) [IsLocalRing R]
  (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (IsLocalRing.ResidueField R))
  (Dv : ExceptionalDivisor (IsLocalRing.ResidueField R)) (hinf : (infinityPoint R t x).IsPrime)
      (Q : divisorSupport Dv) :
    ∃ a1 a2, divisorFromSurface R t x e Dv hinf Q t = divisorException R t x e Dv hinf Q * a1 ∧
      divisorFromSurface R t x e Dv hinf Q x = divisorException R t x e Dv hinf Q * a2 := by
  rcases Q with ⟨_ | φ, hQ⟩
  · refine ⟨@completedPointMap (BlowupChart R x t) _ (infinityPoint R t x) hinf (chartSlope R x t),
      (1 : @CompletedLocalAt (BlowupChart R x t) _ (infinityPoint R t x) hinf), ?_, ?_⟩
    · change (@completedPointMap (BlowupChart R x t) _ (infinityPoint R t x) hinf)
        (chartBase R x t t) = _
      rw [chartBase_x_eq, map_mul]; rfl
    · change (@completedPointMap (BlowupChart R x t) _ (infinityPoint R t x) hinf)
        (chartBase R x t x) = (@completedPointMap (BlowupChart R x t) _ (infinityPoint R t x) hinf)
        (chartBase R x t x) * 1
      exact (mul_one _).symm
  · refine ⟨(1 : CompletedLocalAt (BlowupChart R t x) (directionPoint R t x e φ)),
      completedPointMap (BlowupChart R t x) (directionPoint R t x e φ) (chartSlope R t x), ?_, ?_⟩
    · change (completedPointMap (BlowupChart R t x) (directionPoint R t x e φ)) (chartBase R t x t)
        =
        (completedPointMap (BlowupChart R t x) (directionPoint R t x e φ)) (chartBase R t x t) * 1
      exact (mul_one _).symm
    · change (completedPointMap (BlowupChart R t x) (directionPoint R t x e φ)) (chartBase R t x x)
        =
        _
      rw [chartBase_x_eq, map_mul]; rfl

private theorem cellChild_strict_generator (m : ConcreteMember) (c : m.cellIndex)
    (D : CellChildData m c) : ∀ f :
    m.R, Ideal.span {f} ∈ m.toMeasured.cell c → ∃ g : (∀ j, (D.mc j).R), ∀ j, D.alpha j f =
    (D.mc j).S.t ^ m.toMeasured.cellDegree c * g j := by
  intro f hf
  obtain ⟨f', co, H, hspan, hf', -⟩ := fixed_tangent_cell_generator_coefficients m.O m.R m.S m.s
      (m.toMeasured.cellDegree c) c.2.1 _ hf
  obtain ⟨r, hr⟩ : ∃ r, f = r * f' := by
    have : f ∈ Ideal.span {f'} := hspan ▸ Ideal.subset_span rfl
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨r, hr.symm⟩
  have hab : ∀ j, ∃ a1 a2, D.alpha j m.S.t = (D.mc j).S.t * a1 ∧ D.alpha j m.S.x = (D.mc j).S.t *
      a2 := by
    intro j
    obtain ⟨a1, a2, h1, h2⟩ := divisorFromSurface_t_x_dvd m.R m.S.t m.S.x D.e c.2.1 D.hinf
        (D.point j)
    refine ⟨D.Eq j a1, D.Eq j a2, ?_, ?_⟩
    · change D.Eq j _ = _
      rw [h1, map_mul]; exact congrArg (· * _) (D.hEq_e j)
    · change D.Eq j _ = _
      rw [h2, map_mul]; exact congrArg (· * _) (D.hEq_e j)
  choose a1 a2 h1 h2 using hab
  refine ⟨fun j => D.alpha j r * ∑ i : Fin (m.toMeasured.cellDegree c + 1), D.alpha j (co i) * a1 j
      ^ (m.toMeasured.cellDegree c - i.val) * a2 j ^ i.val, fun j => ?_⟩
  simp only
  rw [hr, hf', map_mul, map_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, h1, h2, mul_pow, mul_pow]
  rw [← pow_mul_pow_sub ((D.mc j).S.t) (show i.val ≤ m.toMeasured.cellDegree c by omega)]
  ring

private theorem member_t_ne_zero (m : ConcreteMember) : m.S.t ≠ 0 := by
  intro h
  have hv := m.S.vertical
  rw [h, zero_pow m.S.a_pos.ne', mul_zero, zero_mul, ← map_zero (algebraMap m.O m.R)] at hv
  exact m.S.pi_irreducible.ne_zero (m.S.base_injective hv)

private theorem cellChild_index_map (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c)
    : ∀ f :
    m.R, Ideal.span {f} ∈ m.toMeasured.cell c → ∀ g : (∀ j, (D.mc j).R),
    (∀ j, D.alpha j f = (D.mc j).S.t ^ m.toMeasured.cellDegree c * g j) → ∀ iota :
    (m.R ⧸ Ideal.span {f}) →ₗ[m.O] ((∀ j, (D.mc j).R) ⧸ Ideal.span {g}),
    (∀ h : m.R, iota (Ideal.Quotient.mk (Ideal.span {f}) h) = Ideal.Quotient.mk (Ideal.span {g})
    (fun j => D.alpha j h)) → Function.Injective iota ∧ Module.length m.O
    (((∀ j, (D.mc j).R) ⧸ Ideal.span {g}) ⧸ LinearMap.range iota) =
    (chooseTwo (m.toMeasured.cellDegree c) : ℕ∞) := by
  intro f hf g hg iota hiota
  have hΦ : ∀ j, D.Φ (Ideal.span {f}) j = Ideal.span {g j} := fun j =>
    strict_transform_ideal_of_generator m.O m.R (D.mc j).R (D.alpha j) ((D.mc j).S.t) (g j) _ f
        (hg j)
      (fun a b hab => mul_left_cancel₀ (member_t_ne_zero (D.mc j)) hab)
  obtain ⟨ψ, hψinj, hlen, hψ⟩ := cell_member_index_map m c D (Ideal.span {f}) hf
      (fun j => (D.mc j).R ⧸ Ideal.span {g j})
    (fun j => Ideal.quotEquivOfEq (hΦ j).symm) (fun j r => rfl)
  obtain ⟨⟨Ψ, hΨ⟩, -⟩ := pi_quotient_span_linearEquiv m.O (m.toMeasured.childIdx c)
      (fun j => (D.mc j).R) g g
  have hψ' : ∀ h : m.R, ψ (Ideal.Quotient.mk _ h) = fun j => Ideal.Quotient.mk (Ideal.span {g j})
      (D.alpha j h) := by
    intro h; funext j
    apply (Ideal.quotEquivOfEq (hΦ j).symm).injective
    rw [hψ h j]; rfl
  have hcomp : ∀ x, iota x = Ψ.symm (ψ x) := by
    intro x
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hiota, hψ', ← hΨ, LinearEquiv.symm_apply_apply]
  have hrange : (LinearMap.range ψ.toLinearMap).map (Ψ.symm : _ →ₗ[m.O] _) = LinearMap.range
      iota := by
    have hEq : (Ψ.symm : _ →ₗ[m.O] _) ∘ₗ ψ.toLinearMap = iota := LinearMap.ext fun x =>
        (hcomp x).symm
    rw [← LinearMap.range_comp, hEq]
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [hcomp, hcomp] at hab
    exact hψinj (Ψ.symm.injective hab)
  · rw [← hlen]
    exact (LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ Ψ.symm hrange)).symm


/-- **A concrete universe exists**: choosing child data for every cell of every concrete member
yields a surface universe indexed by concrete members that satisfies the termination
hypotheses. -/
theorem concrete_universe_exists : ConcreteUniverse :=
  concrete_universe_of_cell_measure
    (fun m c D _ ↦ @member_cell_box_measurable m c D.mc (fun j ↦ (D.child j).algO)
      (fun j ↦ inferInstanceAs (Algebra m.O (D.mc j).R))
      (fun j ↦ inferInstanceAs (IsScalarTower m.O (D.mc j).O (D.mc j).R)) (fun j ↦ (D.child j).pc)
      (fun j ↦ (D.child j).pc_cont.2.2.1) (fun j ↦ (D.child j).pc_cont.2.2.2)
      (fun j ↦ (D.child j).hcard) (cellChild_algebraMap_pi m c D) (cellChild_degree_sum m c D)
      D.alpha (fun j ↦ (D.mc j).S.t) (fun _ ↦ rfl) (cellChild_pi_pow_eq m c D)
      (cell_child_bijOn m c D) (cellChild_strict_generator m c D) (cellChild_index_map m c D)
      (cellChild_firstContact_sum m c D))
    (fun m c D _ ↦ @member_cell_box_measure m c D.mc (fun j ↦ (D.child j).algO)
      (fun j ↦ inferInstanceAs (Algebra m.O (D.mc j).R))
      (fun j ↦ inferInstanceAs (IsScalarTower m.O (D.mc j).O (D.mc j).R)) (fun j ↦ (D.child j).pc)
      (fun j ↦ (D.child j).pc_cont.2.2.1) (fun j ↦ (D.child j).pc_cont.2.2.2)
      (fun j ↦ (D.child j).hcard) (cellChild_algebraMap_pi m c D) (cellChild_degree_sum m c D)
      D.alpha (fun j ↦ (D.mc j).S.t) (fun _ ↦ rfl) (cellChild_pi_pow_eq m c D)
      (cell_child_bijOn m c D) (cellChild_strict_generator m c D) (cellChild_index_map m c D)
      (cellChild_firstContact_sum m c D))

/-- **The root cell law** holds unconditionally. -/
theorem root_cell_law : RootCellLaw :=
  root_cell_law_of_universe concrete_universe_exists

end SurfaceBlowup
