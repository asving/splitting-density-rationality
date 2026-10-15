/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Assembly.NullBridges

/-!
# Measure of member boxes

Near the center of a cell of a concrete member, the strict transform identifies a box of the parent
coordinate space with a box of the product of child coordinate spaces, scaling Haar measure by
`q^(-tri(cellDegree))`. Summing over the coset decomposition of a cell, we show that the box
`{z ∈ cell : strict transform ∈ Π G_j}` is measurable and compute its measure in terms of the child
state measures.

## Main results

* `member_cell_box_measurable`: the set of ideals of a cell whose strict transforms lie in a
  measurable box `Π G_j` is measurable.
* `member_cell_box_measure`: its measure is `q^(-tri(cellDegree)) ∏ μ_j(G_j)`.

## Implementation notes

All results share the long list of hypotheses describing a cell and its children, which is
declared once as section variables; the local notation `cellStrict` abbreviates the strict-transform
map `J ↦ (strictTransformIdeal (alpha j) (e j) (cellDegree c) J)_j` of the cell, and further local
notations (`𝒪`, `ℛ`, `𝔫`, `ϖ`, `𝔡`, `𝒥`, `𝒱`, `𝐪`, `𝒞`) abbreviate the recurring parent data.
Both public results are obtained chart by chart from the private lemma `member_cell_chart_box`,
which sums the center computation `member_center_box_measure` over the coset decomposition of the
cell.

Provenance: member_center_translate_measure_data, member_center_box_measure,
member_cell_box_measurable, member_cell_box_measure.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-! ### Auxiliary facts -/

/-- Scaling the coordinates by `π^k` maps measurable sets to measurable sets. -/
private theorem measurableSet_coordinateScale_image {O : Type} [CommRing O] {n : ℕ} (pi : O)
    [MeasurableSpace (Fin n → O)]
    (hgen : ‹MeasurableSpace (Fin n → O)› = adicCylinderSpace (Ideal.span {pi}) (Fin n → O))
    (hinj : Function.Injective (fun w : Fin n → O => pi • w)) (k : ℕ) (S : Set (Fin n → O))
    (hS : MeasurableSet S) :
    MeasurableSet (coordinateScale pi k '' S) := by
  induction k with
  | zero =>
    have h0 : (coordinateScale pi 0 : (Fin n → O) → (Fin n → O)) = id := by
      funext w; simp [coordinateScale]
    rwa [h0, Set.image_id]
  | succ k ih =>
    have : coordinateScale pi (k+1) '' S =
        (fun w : Fin n → O => pi • w) '' (coordinateScale pi k '' S) := by
      rw [Set.image_image]; congr 1; funext w; simp [coordinateScale, pow_succ', mul_smul]
    rw [this]; exact measurableSet_smul_image pi hgen hinj _ ih

/-- `q^n · q⁻¹^n = 1` for the (finite, nonzero) residue cardinality `q` of a member. -/
private theorem concreteMember_q_pow_mul_inv_pow (m : ConcreteMember) (n : ℕ) :
    (m.toMeasured.q : ℝ≥0∞) ^ n * (m.toMeasured.q : ℝ≥0∞)⁻¹ ^ n = 1 := by
  rw [← mul_pow, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    (ENNReal.natCast_ne_top _), one_pow]

/-- If `φ ⁻¹' C` is the union of the cosets `Cos z₀` (`z₀ ∈ F`), each a translate `z₀ + D`, and
  `φ (z₀ + w) = ψ z₀ w`, then `φ ⁻¹' (C ∩ Z)` is the union of the translates
  `z₀ + (ψ z₀ ⁻¹' Z ∩ D)`. -/
private theorem preimage_inter_eq_biUnion_translate {V I : Type} [Add V] (φ : V → I)
    (ψ : V → V → I) (C Z : Set I) (D : Set V) (F : Finset V) (Cos : V → Set V)
    (htr : ∀ z₀ w, φ (z₀ + w) = ψ z₀ w) (hcos : ∀ z₀, Cos z₀ = (fun w => z₀ + w) '' D)
    (hdec : φ ⁻¹' C = ⋃ z₀ ∈ F, Cos z₀) :
    φ ⁻¹' (C ∩ Z) = ⋃ z₀ ∈ F, (fun w => z₀ + w) '' (ψ z₀ ⁻¹' Z ∩ D) := by
  ext z
  rw [Set.mem_iUnion₂]
  constructor
  · rintro ⟨hzC, hzZ⟩
    have hz : z ∈ φ ⁻¹' C := hzC
    rw [hdec] at hz
    obtain ⟨z₀, hz₀, hzc⟩ := Set.mem_iUnion₂.mp hz
    rw [hcos] at hzc
    obtain ⟨w, hw, rfl⟩ := hzc
    exact ⟨z₀, hz₀, w, ⟨by rw [Set.mem_preimage, ← htr]; exact hzZ, hw⟩, rfl⟩
  · rintro ⟨z₀, hz₀, w, ⟨hwZ, hw⟩, rfl⟩
    have hzC : z₀ + w ∈ φ ⁻¹' C := by
      rw [hdec]; exact Set.mem_iUnion₂.mpr ⟨z₀, hz₀, by rw [hcos]; exact ⟨w, hw, rfl⟩⟩
    refine ⟨hzC, ?_⟩
    beta_reduce
    rw [htr]
    exact hwZ

/-- If finitely many sets `P p` (`p ∈ T`) partition `C` and `Φ` maps `C` bijectively onto `S`, then
  the measures of the pieces `Y ∩ Φ '' P p` add up to `ν (Y ∩ S)`. -/
private theorem sum_measure_inter_image_of_partition {α β ι : Type} [MeasurableSpace β]
    (ν : MeasureTheory.Measure β) {Φ : α → β} {C : Set α} {S : Set β} (hbij : Set.BijOn Φ C S)
    (T : Finset ι) (P : ι → Set α) (hsub : ∀ p ∈ T, P p ⊆ C) (hcov : C ⊆ ⋃ p ∈ T, P p)
    (hdisj : (T : Set ι).PairwiseDisjoint P) (Y : Set β)
    (hmeas : ∀ p ∈ T, MeasurableSet (Y ∩ Φ '' P p)) :
    ∑ p ∈ T, ν (Y ∩ Φ '' P p) = ν (Y ∩ S) := by
  rw [← MeasureTheory.measure_biUnion_finset _ hmeas]
  · congr 1
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨p, hp, hyY, J, hJ, rfl⟩
      exact ⟨hyY, hbij.mapsTo (hsub p hp hJ)⟩
    · rintro ⟨hyY, hyS⟩
      obtain ⟨J, hJ, rfl⟩ := hbij.surjOn hyS
      obtain ⟨p, hp, hJP⟩ := Set.mem_iUnion₂.mp (hcov hJ)
      exact ⟨p, hp, hyY, J, hJP, rfl⟩
  · intro p hp p' hp' hne
    refine Disjoint.mono Set.inter_subset_right Set.inter_subset_right ?_
    rw [Set.disjoint_left]
    rintro y ⟨J, hJ, rfl⟩ ⟨J', hJ', hJJ⟩
    obtain rfl := hbij.injOn (hsub _ hp' hJ') (hsub _ hp hJ) hJJ
    exact Set.disjoint_left.mp (hdisj hp hp' hne) hJ hJ'

/-- The `i`-th chart `z ↦ (f_i + π Σ zₖ b_{i,k})` of the atlas of a concrete member. -/
private noncomputable def memberChart (m : ConcreteMember) (i : m.atlas.ι) :
    (Fin m.toMeasured.s.degree → m.toMeasured.O) → Ideal m.toMeasured.R :=
  coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b

/-- Every ideal of a cell of a concrete member lies in the range of one of the atlas charts. -/
private theorem member_cell_mem_chart_range (m : ConcreteMember) (c : m.toMeasured.cellIndex)
    (J : Ideal m.toMeasured.R) (hJ : J ∈ m.toMeasured.cell c) :
    ∃ i, J ∈ Set.range (memberChart m i) := by
  have hJs : J ∈ surfaceStateSet m.O m.R m.S m.s := hJ.1
  rw [m.atlas.cover] at hJs
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hJs
  exact ⟨i, (concrete_member_charts m i).2.1 ▸ hi⟩

/-! ### Boxes in a cell -/

section CellBoxes

variable (m : ConcreteMember) (c : m.toMeasured.cellIndex)
    (mc : m.toMeasured.childIdx c → ConcreteMember)

/- Local abbreviations for the parent data: coefficient ring `𝒪`, ring `ℛ`, state degree `𝔫`,
uniformizer `ϖ`, cell degree `𝔡`, child index type `𝒥`, coordinate space `𝒱 = 𝒪^𝔫`, residue
cardinality `𝐪` (as an extended real), and the product `𝒞 = Π R_j` of the child rings. -/
local notation "𝒪" => m.toMeasured.O
local notation "ℛ" => m.toMeasured.R
local notation "𝔫" => m.toMeasured.s.degree
local notation "ϖ" => m.toMeasured.S.pi
local notation "𝔡" => m.toMeasured.cellDegree c
local notation "𝒥" => m.toMeasured.childIdx c
local notation "𝒱" => Fin 𝔫 → 𝒪
local notation "𝐪" => (m.toMeasured.q : ℝ≥0∞)
set_option quotPrecheck false
local notation "𝒞" => ∀ j, (mc j).toMeasured.R
set_option quotPrecheck true

/-- For a scaled normalization whose linear part has a scaled inverse `Q`, the child coordinate map
  `childCoordinateMap π a b E H` on `O^deg` has measurable range and measurable preimages. -/
private theorem member_childCoordinateMap_measurable {R : Type} [CommRing R] [Algebra 𝒪 R] (a : ℕ)
    (b : Fin 𝔫 → R) (E : R ≃ₗ[𝒪] (𝒱 × R)) [IsAdicComplete (Ideal.span {ϖ}) (𝒱 × R)]
    (H : 𝒱 →ₗ[𝒪] R) (k : ℕ) (hk : k < a) (Q : 𝒱 →ₗ[𝒪] 𝒱)
    (hQ : ∀ w, normalizationLinearPart E H (Q w) = (ϖ ^ k) • w) :
    MeasurableSet (Set.range (childCoordinateMap ϖ a b E H)) ∧
      ∀ T, MeasurableSet T → MeasurableSet (childCoordinateMap ϖ a b E H ⁻¹' T) := by
  have hpiIrr : Irreducible ϖ := m.toMeasured.S.pi_irreducible
  have hOc : IsAdicComplete (Ideal.span {ϖ}) 𝒪 := dvr_isAdicComplete_span_uniformizer _ _ hpiIrr
  have hOn : IsAdicComplete (Ideal.span {ϖ}) 𝒱 := finite_free_adic_complete _ _ _
  obtain ⟨hgen, -, -, -, hcontall⟩ :=
    coefficient_space_strict_instances 𝒪 m.toMeasured.htop ϖ hpiIrr 𝔫
  have hinj : Function.Injective (fun w : 𝒱 => ϖ • w) := smul_right_injective _ hpiIrr.ne_zero
  obtain ⟨-, hrange, hpre⟩ := child_coordinate_map_scaled _ _ _ _ a b E H (by omega) hinj
  refine ⟨?_, fun T hT ↦ ?_⟩
  · rw [← Set.preimage_image_eq (Set.range _) hinj, ← hrange,
      strict_normalizer_lattice_image _ _ _ _ a b E _ _ hk Q hQ]
    exact (continuous_const_smul _).measurable
      (isCompact_range (hcontall a _)).isClosed.measurableSet
  · rw [← hpre]
    exact scaled_strict_map_measurable _ _ _ _ a b E _ _ hk Q hQ hgen (hcontall a _)
      (measurableSet_smul_image _ hgen hinj T hT)

variable [∀ j, Algebra m.toMeasured.O (mc j).toMeasured.O]
    [∀ j, Algebra m.toMeasured.O (mc j).toMeasured.R]
    [∀ j, IsScalarTower m.toMeasured.O (mc j).toMeasured.O (mc j).toMeasured.R]
    (pc : ∀ j, (mc j).toMeasured.O ≃ₗ[m.toMeasured.O]
      (Fin (m.toMeasured.childDelta c j) → m.toMeasured.O))
    (hpc : ∀ j, Measurable (pc j)) (hpc' : ∀ j, Measurable (pc j).symm)
    (hcard : ∀ j, (mc j).toMeasured.q = m.toMeasured.q ^ m.toMeasured.childDelta c j)
    (hpiO : ∀ j, algebraMap m.toMeasured.O (mc j).toMeasured.O m.toMeasured.S.pi =
      (mc j).toMeasured.S.pi)
    (hdeg : ∑ j, m.toMeasured.childDelta c j * (mc j).toMeasured.s.degree = m.toMeasured.s.degree)
    (alpha : ∀ j, m.toMeasured.R →ₐ[m.toMeasured.O] (mc j).toMeasured.R)
    (e : ∀ j, (mc j).toMeasured.R) (he : ∀ j, e j = (mc j).toMeasured.S.t)
    (hvert : ∀ j, ∃ (s : ℕ) (cj : (mc j).toMeasured.R),
      algebraMap m.toMeasured.O (mc j).toMeasured.R m.toMeasured.S.pi ^ s =
      e j ^ m.toMeasured.cellDegree c * cj)
    (hbij : Set.BijOn
      (fun (J : Ideal m.toMeasured.R) (j : m.toMeasured.childIdx c) => strictTransformIdeal
      (alpha j) (e j) (m.toMeasured.cellDegree c) J) (m.toMeasured.cell c)
      (Set.pi Set.univ fun j => (mc j).toMeasured.stateSet))
    (hstrict : ∀ f : m.toMeasured.R, Ideal.span {f} ∈ m.toMeasured.cell c →
      ∃ g : (∀ j, (mc j).toMeasured.R), ∀ j, alpha j f = e j ^ m.toMeasured.cellDegree c * g j)
    (hindex : ∀ f : m.toMeasured.R, Ideal.span {f} ∈ m.toMeasured.cell c →
      ∀ g : (∀ j, (mc j).toMeasured.R), (∀ j, alpha j f = e j ^ m.toMeasured.cellDegree c * g j) →
      ∀ iota : (m.toMeasured.R ⧸ Ideal.span {f}) →ₗ[m.toMeasured.O]
      ((∀ j, (mc j).toMeasured.R) ⧸ Ideal.span {g}),
      (∀ h : m.toMeasured.R, iota (Ideal.Quotient.mk (Ideal.span {f}) h) =
      Ideal.Quotient.mk (Ideal.span {g}) (fun j => alpha j h)) → Function.Injective iota ∧
      Module.length m.toMeasured.O
      (((∀ j, (mc j).toMeasured.R) ⧸ Ideal.span {g}) ⧸ LinearMap.range iota) =
      (chooseTwo (m.toMeasured.cellDegree c) : ℕ∞))
    (hsum : ∑ j, m.toMeasured.childDelta c j * (mc j).toMeasured.s.firstContact =
      m.toMeasured.cellDegree c)

/-- The strict-transform map of the cell `c`, sending an ideal to its tuple of child strict
  transforms. -/
local notation "cellStrict" => fun (J : Ideal ℛ) (j : 𝒥) => strictTransformIdeal (alpha j) (e j) 𝔡 J

/-- The box of parent coordinates divisible by `π^k`, the domain of the recentred chart. -/
local notation "centerBox" k => Set.range (coordinateScale ϖ k)

include he hpiO in
/-- The parameter `π` lies in the Jacobson radical of `Π R_j`, and the tuple `e = (t_j)_j` of child
  parameters is a nonzerodivisor of `Π R_j`. -/
private theorem member_children_jacobson_regular :
    algebraMap 𝒪 𝒞 ϖ ∈ Ideal.jacobson (⊥ : Ideal 𝒞) ∧ Function.Injective (fun z : 𝒞 => e * z) := by
  refine pi_algebraMap_mem_jacobson_bot 𝒪 _ _ _ (fun j => ?_) e
    fun j => concrete_member_mul_t_injective (he j)
  rw [IsScalarTower.algebraMap_apply 𝒪 (mc j).toMeasured.O, hpiO j]
  exact (surface_vertical_parameter _ _ (mc j).toMeasured.S).2

include hpiO in
/-- The product `Π R_j` of the child surfaces is `π`-adically complete. -/
private theorem member_children_isAdicComplete : IsAdicComplete (Ideal.span {ϖ}) 𝒞 := by
  have hRj : ∀ j, IsAdicComplete (Ideal.span {ϖ}) (mc j).toMeasured.R := fun j => by
    rw [← IsAdicComplete.map_algebraMap_iff (S := (mc j).toMeasured.O), Ideal.map_span,
      Set.image_singleton, hpiO j]
    change IsAdicComplete (Ideal.span {(mc j).S.pi})
      (ConcreteSurface (mc j).O (mc j).pi (mc j).u (mc j).a (mc j).b)
    rw [(mc j).hS_pi]
    exact concrete_surface_isAdicComplete_span_pi_base _ _ (mc j).hpi _ _ _ (mc j).ha
  exact isAdicComplete_pi _ _ _ _

omit [∀ j, Algebra 𝒪 (mc j).toMeasured.R]
  [∀ j, IsScalarTower 𝒪 (mc j).toMeasured.O (mc j).toMeasured.R] in
/-- Given division charts `E' j` at state generators `g j` of the children and a measurable
  coordinate splitting `ρ`, the child chart map `w ↦ (coordinateIdeal (g j) (ρ w)_j)_j` is
  measurable. -/
private theorem child_chart_map_measurable (g : 𝒞)
    (hgj : ∀ j, Ideal.span {g j} ∈ (mc j).toMeasured.stateSet)
    (bc' : ∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.R)
    (E' : ∀ j, (mc j).toMeasured.R ≃ₗ[(mc j).toMeasured.O]
      ((Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O) × (mc j).toMeasured.R))
    (hE' : ∀ j w, (E' j).symm w = divisionMap (g j) (bc' j) w)
    (ρ : 𝒱 ≃ₗ[𝒪] (∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O))
    (hρ : Measurable ρ) :
    Measurable fun (w : 𝒱) (j : 𝒥) =>
      coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) (ρ w j) := by
  rw [measurable_pi_iff]; intro j
  have := concrete_member_division_module_isAdicComplete (mc j)
  obtain ⟨hp0, hpm⟩ :=
    surface_vertical_parameter (mc j).toMeasured.O (mc j).toMeasured.R (mc j).toMeasured.S
  exact (coordinate_ideal_measurable_chart_sigma _ (mc j).toMeasured.htop _ _
    (mc j).toMeasured.S.pi_irreducible hp0 hpm _ (g j) (bc' j)
    ⟨⟨E' j, hE' j⟩, (concrete_member_state_generator_regular (mc j) (g j) (hgj j)).2.2⟩).comp
    ((measurable_pi_apply j).comp hρ)

include hcard hpiO he hbij hindex hsum

/-- At the center of a cell, the box of parent coordinates whose strict transforms lie in `Π G_j`
  has Haar measure `q^(-tri(cellDegree))` times the measure of the corresponding set of child
  coordinates. -/
private theorem member_center_translate_measure_data
    (s : ℕ) (hs : tri 𝔡 ≤ s) (cc : 𝒞) (hcc : (algebraMap 𝒪 𝒞 ϖ) ^ s = e ^ 𝔡 * cc)
    (f : ℛ) (b : Fin 𝔫 → ℛ) (E₀ : ℛ ≃ₗ[𝒪] (𝒱 × ℛ)) (hE₀ : ∀ w, E₀.symm w = divisionMap f b w)
    (hf : Ideal.span {f} ∈ m.toMeasured.cell c)
    (g : 𝒞) (hg : ∀ j, alpha j f = e j ^ 𝔡 * g j)
    (hgj : ∀ j, Ideal.span {g j} ∈ (mc j).toMeasured.stateSet)
    (bc' : ∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.R)
    (E' : ∀ j, (mc j).toMeasured.R ≃ₗ[(mc j).toMeasured.O]
      ((Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O) × (mc j).toMeasured.R))
    (hE' : ∀ j w, (E' j).symm w = divisionMap (g j) (bc' j) w)
    (ρ : 𝒱 ≃ₗ[𝒪] (∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O))
    (hρ : Measurable ρ) (bc : Fin 𝔫 → 𝒞)
    (hcompat : ∀ (w : 𝒱) (j : 𝒥), coordinateLift bc w j = coordinateLift (bc' j) (ρ w j))
    (a : ℕ) (ha : a = s * 𝔫 - tri 𝔡 + 1) :
    letI : Module 𝒪 𝒞 := Algebra.toModule
    ∀ (E : 𝒞 ≃ₗ[𝒪] (𝒱 × 𝒞)), (∀ w, E.symm w = divisionMap g bc w) →
      ∀ (G : ∀ j, Set (Ideal (mc j).toMeasured.R)), (∀ j, MeasurableSet (G j)) →
      MeasurableSet (Set.range (childCoordinateMap ϖ a bc E
        (pulledVariation (AlgHom.pi alpha) cc b))) ∧
      MeasurableSet (coordinateIdeal ϖ f b ⁻¹' (cellStrict ⁻¹' Set.pi Set.univ G) ∩
        centerBox (s + a - 1)) ∧
      cellStrict '' (coordinateIdeal ϖ f b '' centerBox (s + a - 1)) =
        (fun (w : 𝒱) (j : 𝒥) => coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) (ρ w j)) ''
          Set.range (childCoordinateMap ϖ a bc E (pulledVariation (AlgHom.pi alpha) cc b)) ∧
      coefficientMeasure 𝒪 𝔫
        (coordinateIdeal ϖ f b ⁻¹' (cellStrict ⁻¹' Set.pi Set.univ G) ∩ centerBox (s + a - 1)) =
        𝐪⁻¹ ^ tri 𝔡 * coefficientMeasure 𝒪 𝔫
          ((fun (w : 𝒱) (j : 𝒥) => coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) (ρ w j))
            ⁻¹' Set.pi Set.univ G ∩
            Set.range (childCoordinateMap ϖ a bc E (pulledVariation (AlgHom.pi alpha) cc b))) := by
  -- the strict transform intertwines the parent chart on the center box with the child charts
  -- along the child coordinate map; transport measurability and measure along this square
  intro E hE G hG
  set Φ := fun (J : Ideal ℛ) (j : 𝒥) => strictTransformIdeal (alpha j) (e j) 𝔡 J
  set Ψ := fun (w : 𝒱) (j : 𝒥) => coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) (ρ w j)
  set ch := childCoordinateMap ϖ a bc E (pulledVariation (AlgHom.pi alpha) cc b)
  set sc := coordinateScale (n := 𝔫) ϖ (s + a - 1)
  have hpiIrr : Irreducible ϖ := m.toMeasured.S.pi_irreducible
  have hf' : AlgHom.pi alpha f = e ^ 𝔡 * g := by
    funext j; simp [AlgHom.pi_apply, hg j]
  obtain ⟨hjac, heC⟩ := member_children_jacobson_regular m c mc hpiO e he
  -- completeness of the coordinate modules
  have hOc : IsAdicComplete (Ideal.span {ϖ}) 𝒪 := dvr_isAdicComplete_span_uniformizer _ _ hpiIrr
  have hOn : IsAdicComplete (Ideal.span {ϖ}) 𝒱 := finite_free_adic_complete _ _ _
  have hC := member_children_isAdicComplete m c mc hpiO
  have hprod : IsAdicComplete (Ideal.span {ϖ}) (𝒱 × 𝒞) := isAdicComplete_prod _ _ _ _
  -- product chart and linear part
  obtain ⟨hproj, -, hinjP⟩ := product_chart_projection 𝒪 𝒥 (fun j => (mc j).toMeasured.O)
    (fun j => (mc j).toMeasured.R) (fun j => (mc j).toMeasured.s.degree) _ ρ bc' bc hcompat g _ _
    hpiO
  have hΨ : Function.Injective (coordinateIdeal ϖ g bc) := hinjP fun j =>
    (concrete_member_division_chart_measure (mc j) (g j) (hgj j) (bc' j) (E' j) (hE' j)).1
  obtain ⟨Q, hQ, hD, hkl⟩ := member_center_linear_part m c mc hcard alpha e he hbij hindex hsum
    s hs cc hcc f b E₀ hE₀ hf g hg bc E hE
  have htri : tri 𝔡 ≤ s * 𝔫 :=
    le_trans hs (Nat.le_mul_of_pos_right s (concrete_member_one_le_degree m))
  obtain ⟨hgen, hHaar, hProb, hfinite, hcontall⟩ :=
    coefficient_space_strict_instances 𝒪 m.toMeasured.htop ϖ hpiIrr 𝔫
  have hk : s * 𝔫 - tri 𝔡 < a := by omega
  have hΨm : Measurable Ψ := child_chart_map_measurable m c mc g hgj bc' E' hE' ρ hρ
  set T := Ψ ⁻¹' Set.pi Set.univ G
  have hT : MeasurableSet T := hΨm (MeasurableSet.univ_pi hG)
  -- the strict transform commutes with the coordinate charts
  have hcomm : ∀ z, strictTransformIdeal (AlgHom.pi alpha) e 𝔡 (coordinateIdeal ϖ f b (sc z)) =
      coordinateIdeal ϖ g bc (ch z) :=
    strict_chart_coordinates_commute _ _ _ _ _ s a _ _ f g e cc b hf' hcc heC (by omega) hjac bc E
      hE
  have hcommC : ∀ z, Φ (coordinateIdeal ϖ f b (sc z)) = Ψ (ch z) := fun z => by
    funext j; simp only [Φ, Ψ]
    rw [← (pi_strict_transform_map_eval _ _ _ _ alpha e g _ _).2.2.2 j, hcomm z, hproj]
  have hL : coordinateIdeal ϖ f b ⁻¹' (Φ ⁻¹' Set.pi Set.univ G) ∩ Set.range sc =
      sc '' (ch ⁻¹' T) := by
    ext x; constructor
    · rintro ⟨hx, z, rfl⟩; exact ⟨z, (hcommC z ▸ hx : Ψ (ch z) ∈ Set.pi Set.univ G), rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨(hcommC z ▸ hz : Φ _ ∈ Set.pi Set.univ G), z, rfl⟩
  obtain ⟨hrangeM, hpreM⟩ := member_childCoordinateMap_measurable m a bc E
    (pulledVariation (AlgHom.pi alpha) cc b) _ hk Q hQ
  have himgS : strictTransformIdeal (AlgHom.pi alpha) e 𝔡 '' (coordinateIdeal ϖ f b '' Set.range sc)
      = coordinateIdeal ϖ g bc '' Set.range ch := by
    rw [Set.image_image, ← Set.range_comp, ← Set.range_comp]
    exact congrArg Set.range (funext hcomm)
  refine ⟨hrangeM, ?_, ?_, ?_⟩
  · rw [hL]
    exact measurableSet_coordinateScale_image _ hgen (smul_right_injective _ hpiIrr.ne_zero) _ _
      (hpreM T hT)
  · rw [Set.image_image, ← Set.range_comp, ← Set.range_comp]
    exact congrArg Set.range (funext hcommC)
  · rw [hL, ← strict_chart_preimage_set_identity _ _ _ _ _ s a _ _ f g e cc b hf' hcc heC
      (by omega) hjac bc E hE hΨ T, strict_transform_translate_measure _ _ _ _ _ s a _ _ f g e cc b
      hf' hcc heC (by omega) hjac bc E hE hΨ _ hk Q hQ hD hpiIrr hkl hgen _ hfinite (hcontall a _)
      (fun k S _ => coordinate_scale_measure _ m.toMeasured.htop _ hpiIrr _ k S) htri rfl T hT,
      himgS, ← Set.image_inter hΨ, Set.preimage_image_eq _ hΨ]

include pc hpc hpc' hdeg hstrict in
/-- The coefficient measure of the center box of parent coordinates whose strict transforms lie in
  `Π G_j` is `q^(-tri(cellDegree)) q^(deg)` times the product child measure of the part of `Π G_j`
  reached from the center box. -/
private theorem member_center_box_measure
    (s : ℕ) (hs : tri 𝔡 ≤ s) (cc : 𝒞) (hcc : (algebraMap 𝒪 𝒞 ϖ) ^ s = e ^ 𝔡 * cc)
    (f : ℛ) (b : Fin 𝔫 → ℛ) (E₀ : ℛ ≃ₗ[𝒪] (𝒱 × ℛ)) (hE₀ : ∀ w, E₀.symm w = divisionMap f b w)
    (hf : Ideal.span {f} ∈ m.toMeasured.cell c) (a : ℕ) (ha : a = s * 𝔫 - tri 𝔡 + 1)
    (G : ∀ j, Set (Ideal (mc j).toMeasured.R)) (hG : ∀ j, MeasurableSet (G j)) :
    MeasurableSet (coordinateIdeal ϖ f b ⁻¹' (cellStrict ⁻¹' Set.pi Set.univ G) ∩
      centerBox (s + a - 1)) ∧
    MeasurableSet (cellStrict '' (coordinateIdeal ϖ f b '' centerBox (s + a - 1))) ∧
    coefficientMeasure 𝒪 𝔫
      (coordinateIdeal ϖ f b ⁻¹' (cellStrict ⁻¹' Set.pi Set.univ G) ∩ centerBox (s + a - 1)) =
      𝐪⁻¹ ^ tri 𝔡 * 𝐪 ^ 𝔫 * Measure.pi (fun j => (mc j).toMeasured.μ)
        (Set.pi Set.univ G ∩ cellStrict '' (coordinateIdeal ϖ f b '' centerBox (s + a - 1))) := by
  obtain ⟨g, hg⟩ := hstrict f hf
  have hgj : ∀ j, Ideal.span {g j} ∈ (mc j).toMeasured.stateSet := fun j => by
    simpa [strict_transform_ideal_of_generator _ _ _ (alpha j) (e j) (g j) _ f (hg j)
      (concrete_member_mul_t_injective (he j))] using hbij.mapsTo hf j (Set.mem_univ _)
  choose bc' E' hE' using fun j => concrete_member_state_generator_division (mc j) (g j) (hgj j)
  obtain ⟨ρ, bc, hρ, hρ', hcompat⟩ := product_coordinates_exist 𝒪 𝒥 (fun j => (mc j).toMeasured.O)
    (fun j => (mc j).toMeasured.R) (m.toMeasured.childDelta c) (fun j => (mc j).toMeasured.s.degree)
    pc hpc hpc' 𝔫 hdeg bc'
  obtain ⟨E, hE⟩ := product_division_equiv 𝒪 𝒥 (fun j => (mc j).toMeasured.O)
    (fun j => (mc j).toMeasured.R) (fun j => (mc j).toMeasured.s.degree) 𝔫 ρ bc' bc hcompat g E' hE'
  obtain ⟨h1, h2, h3, h4⟩ := member_center_translate_measure_data m c mc hcard hpiO alpha e he
    hbij hindex hsum s hs cc hcc f b E₀ hE₀ hf g hg hgj bc' E' hE' ρ hρ bc hcompat a ha E hE G hG
  obtain ⟨hemb, hpush⟩ := member_product_chart_pushforward 𝒥 mc g hgj bc' E' hE'
  set T := Set.range (childCoordinateMap ϖ a bc E (pulledVariation (AlgHom.pi alpha) cc b))
  set Ψ := fun (w : ∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O) (j : 𝒥) =>
    coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) (w j)
  have hρT : MeasurableSet (ρ '' T) := by
    rw [LinearEquiv.image_eq_preimage_symm]; exact hρ' h1
  have himg : (fun (w : 𝒱) (j : 𝒥) => coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j)
      (ρ w j)) '' T = Ψ '' (ρ '' T) := by
    rw [Set.image_image]
  refine ⟨h2, ?_, ?_⟩
  · rw [h3, himg]; exact hemb.measurableSet_image' hρT
  · rw [h4, h3, himg]
    set Y := ρ '' T ∩ Ψ ⁻¹' Set.pi Set.univ G
    have hYm : MeasurableSet Y := hρT.inter (hemb.measurable (MeasurableSet.univ_pi hG))
    have hpre : (fun (w : 𝒱) (j : 𝒥) => coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j)
        (ρ w j)) ⁻¹' Set.pi Set.univ G ∩ T = ρ ⁻¹' Y := by
      rw [Set.preimage_inter, Set.preimage_image_eq _ ρ.injective, Set.inter_comm]; rfl
    have hC : (∏ j, ((mc j).toMeasured.q : ℝ≥0∞)⁻¹ ^ (mc j).toMeasured.s.degree) = 𝐪⁻¹ ^ 𝔫 := by
      simp_rw [hcard, Nat.cast_pow, ENNReal.inv_pow, ← pow_mul]
      rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [hpre, ← Measure.map_apply hρ hYm,
      member_coefficient_measure_map_product_coordinates m c mc ρ hρ,
      ← Set.inter_comm, ← Set.image_inter_preimage, hpush Y hYm, hC, mul_assoc,
      ← mul_assoc (𝐪 ^ _), concreteMember_q_pow_mul_inv_pow, one_mul]

open scoped Classical in
include pc hpc hpc' hdeg hstrict in
/-- In the chart `i` of a cell, given coset representatives `reps` of level `s + a - 1`, the chart
  preimage of the box `{J ∈ cell : cellStrict J ∈ Π G_j}` is measurable, and its measure is
  `q^(-tri(cellDegree)) q^deg` times the sum, over the representatives landing in the cell, of the
  child measures of the images of the corresponding cosets. -/
private theorem member_cell_chart_box (s : ℕ) (hs : tri 𝔡 ≤ s) (cc : 𝒞)
    (hcc : (algebraMap 𝒪 𝒞 ϖ) ^ s = e ^ 𝔡 * cc) (a : ℕ) (ha : a = s * 𝔫 - tri 𝔡 + 1)
    (reps : Finset 𝒱) (hrdisj : (reps : Set 𝒱).PairwiseDisjoint (coordinateCoset ϖ (s + a - 1)))
    (i : m.atlas.ι)
    (hdec : memberChart m i ⁻¹' m.toMeasured.cell c =
      ⋃ z₀ ∈ reps.filter (fun z₀ => memberChart m i z₀ ∈ m.toMeasured.cell c),
        coordinateCoset ϖ (s + a - 1) z₀)
    (G : ∀ j, Set (Ideal (mc j).toMeasured.R)) (hG : ∀ j, MeasurableSet (G j)) :
    MeasurableSet (memberChart m i ⁻¹' (m.toMeasured.cell c ∩ cellStrict ⁻¹' Set.pi Set.univ G)) ∧
    coefficientMeasure 𝒪 𝔫
        (memberChart m i ⁻¹' (m.toMeasured.cell c ∩ cellStrict ⁻¹' Set.pi Set.univ G)) =
      𝐪⁻¹ ^ tri 𝔡 * 𝐪 ^ 𝔫 *
        ∑ z₀ ∈ reps.filter (fun z₀ => memberChart m i z₀ ∈ m.toMeasured.cell c),
        Measure.pi (fun j => (mc j).toMeasured.μ) (Set.pi Set.univ G ∩
          cellStrict '' (memberChart m i '' coordinateCoset ϖ (s + a - 1) z₀)) ∧
    ∀ z₀ ∈ reps.filter (fun z₀ => memberChart m i z₀ ∈ m.toMeasured.cell c),
      MeasurableSet (cellStrict '' (memberChart m i '' coordinateCoset ϖ (s + a - 1) z₀)) := by
  set Φ := fun (J : Ideal ℛ) (j : 𝒥) => strictTransformIdeal (alpha j) (e j) 𝔡 J
  have := concrete_member_division_module_isAdicComplete m
  -- `Φi` is the chart, `F` the representatives of the cell in it, and `Φp z₀` the chart recentred
  -- at `z₀`; the chart preimage of the box is the union of the translated center boxes `A z₀`
  let fi : ℛ := (m.atlas.chart i).f
  let bi : Fin 𝔫 → ℛ := (m.atlas.chart i).b
  set Φi := memberChart m i
  set F := reps.filter (fun z₀ => Φi z₀ ∈ m.toMeasured.cell c)
  let Φp (z₀ : 𝒱) : 𝒱 → Ideal ℛ := coordinateIdeal ϖ (fi + ϖ • coordinateLift bi z₀) bi
  have Tr := fun z₀ => member_chart_translate m fi bi (s + a - 1) z₀
  set Y := Set.pi Set.univ G
  set Rg := Set.range (coordinateScale (n := 𝔫) ϖ (s + a - 1))
  let A (z₀ : 𝒱) : Set 𝒱 := (fun z => z₀ + z) '' (Φp z₀ ⁻¹' (Φ ⁻¹' Y) ∩ Rg)
  -- the center box measure applies at every representative
  have hC : ∀ z₀ ∈ F, MeasurableSet (Φp z₀ ⁻¹' (Φ ⁻¹' Y) ∩ Rg) ∧
      MeasurableSet (Φ '' (Φp z₀ '' Rg)) ∧
      coefficientMeasure 𝒪 𝔫 (Φp z₀ ⁻¹' (Φ ⁻¹' Y) ∩ Rg) =
        𝐪⁻¹ ^ tri 𝔡 * 𝐪 ^ 𝔫 *
          Measure.pi (fun j => (mc j).toMeasured.μ) (Y ∩ Φ '' (Φp z₀ '' Rg)) := by
    intro z₀ hz₀
    have hf : Ideal.span {fi + ϖ • coordinateLift bi z₀} ∈ m.toMeasured.cell c := by
      have h0 := (Tr z₀).1 0
      rw [add_zero] at h0
      have : coordinateIdeal ϖ fi bi z₀ = Ideal.span {fi + ϖ • coordinateLift bi z₀} := by
        rw [h0]
        simp [coordinateIdeal, normalizedIdeal, normalizedGenerator, coordinateLift]
      rw [← this]; exact (Finset.mem_filter.mp hz₀).2
    obtain ⟨E₀, hE₀⟩ := @division_data_vertical_perturbation 𝒪 ℛ _ _ _ 𝔫 ϖ fi bi
      (m.atlas.chart i).E (m.atlas.chart i).division this (coordinateLift bi z₀)
    exact member_center_box_measure m c mc pc hpc hpc' hcard hpiO hdeg alpha e he hbij
      hstrict hindex hsum s hs cc hcc _ bi E₀ hE₀ hf a ha G hG
  have hPeq (z₀) : Φp z₀ '' Rg = Φi '' coordinateCoset ϖ (s + a - 1) z₀ := by
    rw [(Tr z₀).2.1, Set.image_image]
    exact congrArg (· '' Rg) (funext fun w => ((Tr z₀).1 w).symm)
  have hXi : Φi ⁻¹' (m.toMeasured.cell c ∩ Φ ⁻¹' Y) = ⋃ z₀ ∈ F, A z₀ :=
    preimage_inter_eq_biUnion_translate Φi Φp _ _ Rg F _ (fun z₀ => (Tr z₀).1)
      (fun z₀ => (Tr z₀).2.1) hdec
  have hAdisj : (F : Set _).PairwiseDisjoint A := by
    intro z₀ hz z₀' hz' hne
    have hsub : ∀ z₁, A z₁ ⊆ coordinateCoset ϖ (s + a - 1) z₁ := fun z₁ => by
      rw [(Tr z₁).2.1]; exact Set.image_mono Set.inter_subset_right
    exact (hrdisj (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz').1 hne).mono (hsub z₀)
      (hsub z₀')
  have hAmeas : ∀ z₀ ∈ F, MeasurableSet (A z₀) := fun z₀ hz => ((Tr z₀).2.2 _).2 (hC z₀ hz).1
  refine ⟨?_, ?_, fun z₀ hz => hPeq z₀ ▸ (hC z₀ hz).2.1⟩
  · rw [hXi]; exact Finset.measurableSet_biUnion _ hAmeas
  · rw [hXi, measure_biUnion_finset hAdisj hAmeas, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z₀ hz => ?_
    rw [← hPeq]
    exact ((Tr z₀).2.2 _).1.trans (hC z₀ hz).2.2

include pc hpc hpc' hdeg hvert hstrict in
/-- The set of ideals in a cell whose strict transforms lie in a measurable box `Π G_j` is
  measurable. -/
theorem member_cell_box_measurable :
    (letI : ∀ j, MeasurableSpace (Ideal (mc j).toMeasured.R) :=
      fun j => (mc j).toMeasured.measurableSpaceIdeal;
      letI : MeasurableSpace (Ideal ℛ) := m.toMeasured.measurableSpaceIdeal;
      ∀ (G : ∀ j, Set (Ideal (mc j).toMeasured.R)), (∀ j, MeasurableSet (G j)) →
      MeasurableSet (m.toMeasured.cell c ∩ (fun (J : Ideal ℛ) (j : 𝒥) =>
        strictTransformIdeal (alpha j) (e j) 𝔡 J) ⁻¹' Set.pi Set.univ G)) := by
  intro G hG
  classical
  obtain ⟨s, cc, hs, hcc⟩ := common_vertical_exponent 𝒪 𝒥 (fun j => (mc j).toMeasured.R) ϖ e 𝔡
    hvert (tri 𝔡)
  set a := s * 𝔫 - tri 𝔡 + 1 with ha
  have htri := tri_chooseTwo 𝔡
  obtain ⟨reps, -, -, hrdisj, hdec⟩ :=
    member_cell_chart_coset_decomposition m c (s + a - 1) (by omega)
  set X := m.toMeasured.cell c ∩ cellStrict ⁻¹' Set.pi Set.univ G
  -- `X` is the union of the images of its chart preimages, which are measurable
  have hX : X = ⋃ i, memberChart m i '' (memberChart m i ⁻¹' X) := by
    ext J
    simp only [Set.mem_iUnion, Set.image_preimage_eq_inter_range, Set.mem_inter_iff]
    constructor
    · intro h; obtain ⟨i, hi⟩ := member_cell_mem_chart_range m c J h.1; exact ⟨i, h, hi⟩
    · rintro ⟨-, h, -⟩; exact h
  rw [hX]
  exact MeasurableSet.iUnion fun i => chart_image_measurable_chart_sigma _ _ _ _ _ _
    (m.atlas.chart i).isDivisionChart _
    (member_cell_chart_box m c mc pc hpc hpc' hcard hpiO hdeg alpha e he hbij hstrict hindex hsum
      s hs cc hcc a ha reps hrdisj i (hdec i) G hG).1

include pc hpc hpc' hdeg hvert hstrict in
/-- The measure of the set of ideals in a cell whose strict transforms lie in a box `Π G_j` is
  `q^(-tri(cellDegree))` times the product of the child state measures of the `G_j`. -/
theorem member_cell_box_measure :
    (letI : ∀ j, MeasurableSpace (Ideal (mc j).toMeasured.R) :=
      fun j => (mc j).toMeasured.measurableSpaceIdeal;
      letI : MeasurableSpace (Ideal ℛ) := m.toMeasured.measurableSpaceIdeal;
      ∀ (G : ∀ j, Set (Ideal (mc j).toMeasured.R)), (∀ j, MeasurableSet (G j)) →
      m.toMeasured.μ (m.toMeasured.cell c ∩ (fun (J : Ideal ℛ) (j : 𝒥) =>
        strictTransformIdeal (alpha j) (e j) 𝔡 J) ⁻¹' Set.pi Set.univ G) =
      𝐪⁻¹ ^ tri 𝔡 * ∏ j, (mc j).toMeasured.μ (G j)) := by
  -- sum the chart computations of `member_cell_chart_box` over the charts; the images of the
  -- cosets in the cell partition the cell, hence their strict transforms partition `Π stateSet_j`
  intro G hG
  classical
  obtain ⟨s, cc, hs, hcc⟩ := common_vertical_exponent 𝒪 𝒥 (fun j => (mc j).toMeasured.R) ϖ e _
    hvert (tri 𝔡)
  set a := s * 𝔫 - tri 𝔡 + 1 with ha
  have htri := tri_chooseTwo 𝔡
  obtain ⟨reps, -, -, hrdisj, hdec⟩ :=
    member_cell_chart_coset_decomposition m c (s + a - 1) (by omega)
  have hbox := fun i => member_cell_chart_box m c mc pc hpc hpc' hcard hpiO hdeg alpha e he hbij
    hstrict hindex hsum s hs cc hcc a ha reps hrdisj i (hdec i) G hG
  -- `F i` are the representatives of the cell in chart `i`, `P ⟨i, z₀⟩` the image of a coset
  let F (i : m.atlas.ι) := reps.filter (fun z₀ => memberChart m i z₀ ∈ m.toMeasured.cell c)
  let P (p : Σ _ : m.atlas.ι, 𝒱) := memberChart m p.1 '' coordinateCoset ϖ (s + a - 1) p.2
  have hdec' (i) : memberChart m i ⁻¹' m.toMeasured.cell c =
      ⋃ z₀ ∈ F i, coordinateCoset ϖ (s + a - 1) z₀ := hdec i
  have hPcell : ∀ p ∈ Finset.univ.sigma F, P p ⊆ m.toMeasured.cell c := by
    rintro ⟨i, z₀⟩ hp J ⟨z, hz, rfl⟩
    have : z ∈ memberChart m i ⁻¹' m.toMeasured.cell c := by
      rw [hdec']; exact Set.mem_biUnion (Finset.mem_sigma.mp hp).2 hz
    exact this
  have hPunion : m.toMeasured.cell c ⊆ ⋃ p ∈ Finset.univ.sigma F, P p := by
    intro J hJc
    obtain ⟨i, z, rfl⟩ := member_cell_mem_chart_range m c J hJc
    have hz : z ∈ memberChart m i ⁻¹' m.toMeasured.cell c := hJc
    rw [hdec'] at hz
    obtain ⟨z₀, hz₀, hzc⟩ := Set.mem_iUnion₂.mp hz
    exact Set.mem_iUnion₂.mpr ⟨⟨i, z₀⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hz₀⟩, z, hzc, rfl⟩
  have hPdisj : ((Finset.univ.sigma F : Finset _) : Set _).PairwiseDisjoint P := by
    rintro ⟨i, z₀⟩ hp ⟨i', z₀'⟩ hp' hne
    have hz := (Finset.mem_sigma.mp hp).2
    have hz' := (Finset.mem_sigma.mp hp').2
    by_cases hii : i = i'
    · subst hii
      have hne' : z₀ ≠ z₀' := fun h => hne (h ▸ rfl)
      exact (Set.disjoint_image_iff (concrete_member_charts m i).1).mpr
        (hrdisj (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz').1 hne')
    · have h := m.atlas.disjoint hii
      simp only at h
      rw [← (concrete_member_charts m i).2.1, ← (concrete_member_charts m i').2.1] at h
      exact h.mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)
  have : ∀ j, IsFiniteMeasure (mc j).toMeasured.μ := fun j =>
    (concrete_member_measure_finite_support (mc j)).1
  have hparts := sum_measure_inter_image_of_partition (Measure.pi fun j => (mc j).toMeasured.μ)
    hbij _ P hPcell hPunion hPdisj (Set.pi Set.univ G) fun p hp => (MeasurableSet.univ_pi hG).inter
      ((hbox p.1).2.2 p.2 (Finset.mem_sigma.mp hp).2)
  rw [Finset.sum_sigma, ← Set.pi_inter_distrib, Measure.pi_pi] at hparts
  -- the state measure is `q^(-deg)` times the sum of the chart measures
  rw [MeasuredSurface.μ, stateMeasure, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  have hmeas := member_cell_box_measurable m c mc pc hpc hpc' hcard hpiO hdeg alpha e he hvert hbij
    hstrict hindex hsum G hG
  calc _ = 𝐪⁻¹ ^ 𝔫 * ∑ i, 𝐪⁻¹ ^ tri 𝔡 * 𝐪 ^ 𝔫 *
        ∑ z₀ ∈ F i, Measure.pi (fun j => (mc j).toMeasured.μ)
          (Set.pi Set.univ G ∩ cellStrict '' P ⟨i, z₀⟩) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [chartMeasure]
        exact (Measure.map_apply (concrete_member_charts m i).2.2 hmeas).trans (hbox i).2.1
    _ = (𝐪 ^ 𝔫 * 𝐪⁻¹ ^ 𝔫) * (𝐪⁻¹ ^ tri 𝔡 * ∏ j, (mc j).toMeasured.μ (G j)) := by
        rw [← Finset.mul_sum, hparts, Finset.prod_congr rfl fun j _ =>
          ((concrete_member_measure_finite_support (mc j)).2 (G j)).symm]
        ring
    _ = _ := by rw [concreteMember_q_pow_mul_inv_pow, one_mul]

end CellBoxes

end SurfaceBlowup
