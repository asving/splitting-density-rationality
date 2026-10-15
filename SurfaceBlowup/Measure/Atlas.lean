/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.PointTransport
import SurfaceBlowup.Measure.Normalizer
import SurfaceBlowup.Measure.StateVolumes

/-!
# Ideal-chart atlases and atlas independence of the state measure

A division chart parametrizes the residue-ideal cell of a generator `f` by the coordinate ideals
`(f + π Σ zᵢ bᵢ)`. We show that this parametrization is a bijection onto the cell, that the
transition map between two charts of the same cell is a congruence-preserving bijection and hence
preserves Haar measure, and conclude that the pushforward chart measures, and so the state measure
of an ideal atlas, do not depend on the choice of charts. We also record how strict transforms and
coordinate ideals decompose over finite products.

## Main results

* `pi_strict_transform_map_eval`, `product_chart_projection`: principal ideals, strict transforms
  and coordinate ideals over a finite product are computed componentwise.
* `coordinate_ideal_cell_bijection`: a division chart is a bijection onto its residue-ideal cell.
* `ideal_chart_transition_haar`: chart transitions preserve Haar measure on `O^n`.
* `ideal_chart_pushforward_independent`, `state_measure_atlas_independent`: the chart measures,
  hence the state measure, do not depend on the choice of charts.

Provenance: `Thm_SurfaceBlowupV2_*`: `pi_strict_transform_map_eval`, `product_chart_projection`,
`coordinate_ideal_{surjective, cell_bijection}`, `coordinate_transition_{ideal_identity, inverse,
congruence_iff, measure_preserving}`, `ideal_chart_transition_haar`,
`division_chart_preimage_image_measurable`, `ideal_chart_pushforward_independent`,
`state_measure_atlas_independent`.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-- Over a finite product `Π C_j`, principal ideals and strict transforms are computed
  componentwise. -/
theorem pi_strict_transform_map_eval (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R]
    (ι : Type) [Finite ι] (C : ι → Type) [∀ j, CommRing (C j)] [∀ j, Algebra O (C j)]
    (alpha : ∀ j, R →ₐ[O] C j) (e g : ∀ j, C j) (d : ℕ) (J : Ideal R) :
    (∀ x : ∀ j, C j, x ∈ Ideal.span {g} ↔ ∀ j, x j ∈ Ideal.span {g j}) ∧
      (∀ j, (Ideal.span {g}).map (Pi.evalRingHom C j) = Ideal.span {g j}) ∧
      (∀ x : ∀ j, C j, x ∈ strictTransformIdeal (AlgHom.pi alpha) e d J ↔ ∀ j,
      x j ∈ strictTransformIdeal (alpha j) (e j) d J) ∧ ∀ j,
      (strictTransformIdeal (AlgHom.pi alpha) e d J).map (Pi.evalRingHom C j) =
      strictTransformIdeal (alpha j) (e j) d J := by
  have := Fintype.ofFinite ι
  classical
  have hmap : ∀ j, (J.map (AlgHom.pi alpha).toRingHom).map (Pi.evalRingHom C j)
      = J.map (alpha j).toRingHom := fun j ↦ by rw [Ideal.map_map]; rfl
  have hpi := (pi_ideal_mem_iff_map_eval ι C (J.map (AlgHom.pi alpha).toRingHom)).1
  have key : ∀ x : ∀ j, C j, x ∈ strictTransformIdeal (AlgHom.pi alpha) e d J ↔
      ∀ j, x j ∈ strictTransformIdeal (alpha j) (e j) d J := by
    intro x
    simp only [strictTransformIdeal, Submodule.mem_colon_singleton, Algebra.smul_def]
    rw [hpi]
    exact forall_congr' fun j ↦ by rw [hmap j]; simp
  refine ⟨fun x ↦ by rw [← Ideal.pi_span, Ideal.mem_pi], fun j ↦ by rw [principal_ideal_image]; rfl,
    key, fun j ↦ le_antisymm (Ideal.map_le_iff_le_comap.2 fun x hx ↦ (key x).1 hx j) fun y hy ↦ ?_⟩
  have : (Pi.single j y : ∀ j, C j) ∈ strictTransformIdeal (AlgHom.pi alpha) e d J :=
    (key _).2 fun k ↦ by
      by_cases h : k = j
      · subst h; simpa using hy
      · simp [Pi.single_eq_of_ne h]
  simpa using Ideal.mem_map_of_mem (Pi.evalRingHom C j) this

/-- A coordinate ideal of a product chart projects to the coordinate ideals of the component charts,
  membership is componentwise, and the chart is injective when all component charts are. -/
theorem product_chart_projection (O : Type) [CommRing O] (ι : Type) [Finite ι] (Oj : ι → Type)
    [∀ j, CommRing (Oj j)] [∀ j, Algebra O (Oj j)] (R : ι → Type) [∀ j, CommRing (R j)]
    [∀ j, Algebra O (R j)] [∀ j, Algebra (Oj j) (R j)] [∀ j, IsScalarTower O (Oj j) (R j)]
    (nn : ι → ℕ) (n : ℕ) (ρ : (Fin n → O) ≃ₗ[O] (∀ j, Fin (nn j) → Oj j))
    (bc' : ∀ j, Fin (nn j) → R j) (bc : Fin n → ∀ j, R j)
    (hcompat : ∀ (w : Fin n → O) (j : ι), coordinateLift bc w j = coordinateLift (bc' j) (ρ w j))
    (g : ∀ j, R j) (pi : O) (pij : ∀ j, Oj j) (hpi : ∀ j, algebraMap O (Oj j) pi = pij j) :
    (∀ (w : Fin n → O) (j : ι), (coordinateIdeal pi g bc w).map (Pi.evalRingHom R j) =
      coordinateIdeal (pij j) (g j) (bc' j) (ρ w j)) ∧
      (∀ (w : Fin n → O) (x : ∀ j, R j), x ∈ coordinateIdeal pi g bc w ↔ ∀ j,
      x j ∈ coordinateIdeal (pij j) (g j) (bc' j) (ρ w j)) ∧
      ((∀ j, Function.Injective (coordinateIdeal (pij j) (g j) (bc' j))) →
      Function.Injective (coordinateIdeal pi g bc)) := by
  have key : ∀ (w : Fin n → O) (j : ι),
      (g + coordinateLift bc (pi • w)) j = g j + coordinateLift (bc' j) (pij j • ρ w j) := by
    intro w j
    simp only [coordinateLift_smul_eq_mul, ← Algebra.smul_def]
    rw [← hpi, algebraMap_smul, Pi.add_apply, Pi.smul_apply, hcompat]
  have proj : ∀ (w : Fin n → O) (j : ι), (coordinateIdeal pi g bc w).map (Pi.evalRingHom R j) =
      coordinateIdeal (pij j) (g j) (bc' j) (ρ w j) := fun w j ↦
    (principal_ideal_image _ _ _ _).trans (congrArg (fun y ↦ Ideal.span {y}) (key w j))
  refine ⟨proj, fun w x ↦ ?_, fun hinj w w' h ↦ ρ.injective <| funext fun j ↦
    hinj j <| by rw [← proj, ← proj, h]⟩
  refine ((pi_strict_transform_map_eval O O ι R (fun j ↦ Algebra.ofId O (R j)) 0
    (g + coordinateLift bc (pi • w)) 0 ⊥).1 x).trans (forall_congr' fun j ↦ ?_)
  rw [key]
  rfl

/-- Every ideal in the residue-ideal cell of `f` is a coordinate ideal of the division chart. -/
private theorem coordinate_ideal_surjective (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ)
    (pi : O) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] [IsDomain R] [IsLocalRing R]
    (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (f : R)
    (hE : ∀ s, E.symm s = divisionMap f b s)
    (hf : Function.Injective
      (fun x : R ⧸ Ideal.span {algebraMap O R pi} => x *
      Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) f))
    (J : Ideal R) (hJ : J ∈ residueIdealCell (algebraMap O R pi) f) :
    ∃ z : Fin n → O, coordinateIdeal pi f b z = J := by
  obtain ⟨h, rfl⟩ := residue_ideal_has_fixed_generator_lift R
    (algebraMap O R pi) f hpm hf J hJ
  refine ⟨(generatorNormalForm pi b E h).1, ?_⟩
  have key := normalizer_generator_equation O R n pi b E f hE h
  obtain ⟨u, hu⟩ := normalizing_factor_is_unit O R pi hpm
    (generatorNormalForm pi b E h).2
  unfold coordinateIdeal normalizedIdeal normalizedGenerator
  simp only [coordinateLift_smul_eq_mul, ← Algebra.smul_def]
  rw [← key, ← hu, principal_ideal_unit_invariance]

/-- The coordinate-ideal map of a division chart is a bijection onto the residue-ideal cell of
`f`. -/
theorem coordinate_ideal_cell_bijection (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (pi : O) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] [IsDomain R] [IsLocalRing R]
    (hp0 : algebraMap O R pi ≠ 0) (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (f : R)
    (hE : ∀ s, E.symm s = divisionMap f b s)
    (hf : Function.Injective
      (fun x : R ⧸ Ideal.span {algebraMap O R pi} => x *
      Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) f))
    :
    Function.Injective (coordinateIdeal pi f b) ∧ Set.range (coordinateIdeal pi f b) =
      residueIdealCell (algebraMap O R pi) f := by
  refine ⟨coordinate_ideal_injective O R n pi b E hp0 hpm f hE hf, Set.ext fun J ↦
    ⟨?_, coordinate_ideal_surjective O R n pi b E hpm f hE hf J⟩⟩
  rintro ⟨z, rfl⟩
  exact coordinate_ideal_in_residue_cell O R n pi b f z

/-- The transition map between two division charts of the same cell intertwines their
  coordinate-ideal maps. -/
private theorem coordinate_transition_ideal_identity (O R : Type) [CommRing O] [CommRing R]
    [Algebra O R]
    (n : ℕ) (pi : O) (b : Fin n → R)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] [IsLocalRing R]
    (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (f g : R) (c : Fin n → R)
    (F : R ≃ₗ[O] ((Fin n → O) × R)) (hF : ∀ s, F.symm s = divisionMap g c s) (h0 : R)
    (hfg : f = g + pi • h0) (z : Fin n → O) :
    coordinateIdeal pi g c (idealTransition pi b c F h0 z) = coordinateIdeal pi f b z := by
  have key := normalizer_generator_equation O R n pi c F g hF
    (h0 + coordinateLift b z)
  have hu := normalizing_factor_is_unit O R pi hpm
    (generatorNormalForm pi c F (h0 + coordinateLift b z)).2
  have hinv := principal_ideal_unit_invariance R
    (g + pi • coordinateLift c (generatorNormalForm pi c F (h0 + coordinateLift b z)).1) hu.unit
  simp only [coordinateIdeal, normalizedIdeal, normalizedGenerator, idealTransition,
    coordinateLift_smul_eq_mul, ← Algebra.smul_def]
  rw [← hinv, IsUnit.unit_spec, key, hfg, smul_add, add_assoc]

/-! ### Transition maps between two division charts of one cell -/

section Transition

variable (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ) (pi : O) (b : Fin n → R)
  (E : R ≃ₗ[O] ((Fin n → O) × R)) [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)]
  [IsDomain R] [IsLocalRing R] (hp0 : algebraMap O R pi ≠ 0)
  (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (f : R)
  (hE : ∀ s, E.symm s = divisionMap f b s)
  (hf : Function.Injective (fun x : R ⧸ Ideal.span {algebraMap O R pi} =>
    x * Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) f))
  (g : R) (c : Fin n → R) (F : R ≃ₗ[O] ((Fin n → O) × R)) (hF : ∀ s, F.symm s = divisionMap g c s)
  (hg : Function.Injective (fun x : R ⧸ Ideal.span {algebraMap O R pi} =>
    x * Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) g))
  (h0 : R) (hfg : f = g + pi • h0)

include hp0 hpm hE hf hF hg hfg

/-- The coordinate transition map between two charts of the same cell is inverted by the reverse
  transition. -/
private theorem coordinate_transition_inverse :
    Function.LeftInverse (idealTransition pi c b E (-h0)) (idealTransition pi b c F h0) ∧
      Function.RightInverse (idealTransition pi c b E (-h0)) (idealTransition pi b c F h0) := by
  have hgf : g = f + pi • (-h0) := by rw [hfg, smul_neg]; abel
  have hfg' := coordinate_transition_ideal_identity O R n pi b hpm f g c F hF h0 hfg
  have hgf' := coordinate_transition_ideal_identity O R n pi c hpm g f b E hE (-h0) hgf
  exact ⟨fun z ↦ coordinate_ideal_injective O R n pi b E hp0 hpm f hE hf (by rw [hgf', hfg']),
    fun z ↦ coordinate_ideal_injective O R n pi c F hp0 hpm g hF hg (by rw [hfg', hgf'])⟩

/-- The coordinate transition map preserves and reflects congruence modulo `(π)^j`. -/
private theorem coordinate_transition_congruence_iff (j : ℕ) (z w : Fin n → O) :
    adicCongr (Ideal.span {pi}) j (idealTransition pi b c F h0 z) (idealTransition pi b c F h0 w) ↔
      adicCongr (Ideal.span {pi}) j z w := by
  refine ⟨fun h ↦ ?_, coordinate_transition_congruence O R n pi b c F h0 j z w⟩
  have hinv := (coordinate_transition_inverse O R n pi b E hp0 hpm f hE hf g c F hF hg h0 hfg).1
  simpa only [hinv z, hinv w] using coordinate_transition_congruence O R n pi c b E (-h0) j _ _ h

/-- The coordinate transition map preserves any probability measure that gives all `π`-adic balls of
  a given radius equal mass. -/
private theorem coordinate_transition_measure_preserving [MeasurableSpace (Fin n → O)]
    (hgen : ‹MeasurableSpace (Fin n → O)› = adicCylinderSpace (Ideal.span {pi}) (Fin n → O))
    (mu : MeasureTheory.Measure (Fin n → O)) [MeasureTheory.IsProbabilityMeasure mu]
    (hball : ∀ j (x y : Fin n → O), mu {z | adicCongr (Ideal.span {pi}) j z x} =
      mu {z | adicCongr (Ideal.span {pi}) j z y}) :
    MeasureTheory.MeasurePreserving (idealTransition pi b c F h0) mu mu :=
  congruence_bijection_measure_preserving O (Fin n → O) (Ideal.span {pi}) hgen _
    (coordinate_transition_inverse O R n pi b E hp0 hpm f hE hf g c F hF hg h0 hfg).2.surjective
    (coordinate_transition_congruence_iff O R n pi b E hp0 hpm f hE hf g c F hF hg h0 hfg) mu hball

variable [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]

/-- The coordinate transition map preserves the Haar probability measure on `O^n`. -/
theorem ideal_chart_transition_haar (htop : IsAdic (IsLocalRing.maximalIdeal O))
    (hpi : Irreducible pi) :
    MeasureTheory.MeasurePreserving (idealTransition pi b c F h0) (coefficientMeasure O n)
      (coefficientMeasure O n) := by
  have := coefficient_measure_probability O htop n
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {pi} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi
  exact coordinate_transition_measure_preserving O R n pi b E hp0 hpm f hE hf g c F hF hg h0 hfg
    (finite_coordinate_borel_cylinders O (Ideal.span {pi}) (hm ▸ htop) n) _ fun j x y ↦ by
      rw [coefficient_uniformizer_cylinder_mass O htop n pi hpi j x,
        coefficient_uniformizer_cylinder_mass O htop n pi hpi j y]

/-- Two division charts of the same residue-ideal cell push Haar measure forward to the same measure
  on ideals. -/
theorem ideal_chart_pushforward_independent (htop : IsAdic (IsLocalRing.maximalIdeal O))
    (hpi : Irreducible pi) [MeasurableSpace (Ideal R)] (hc : Measurable (coordinateIdeal pi g c)) :
    (coefficientMeasure O n).map (coordinateIdeal pi f b) =
      (coefficientMeasure O n).map (coordinateIdeal pi g c) := by
  have hT := ideal_chart_transition_haar O R n pi b E hp0 hpm f hE hf g c F hF hg h0 hfg htop hpi
  have hfun : coordinateIdeal pi f b = coordinateIdeal pi g c ∘ idealTransition pi b c F h0 :=
    funext fun z ↦ (coordinate_transition_ideal_identity O R n pi b hpm f g c F hF h0 hfg z).symm
  rw [hfun, ← MeasureTheory.Measure.map_map hc hT.measurable, hT.map_eq]

end Transition

/-- For two division charts, the preimage under one of the image under the other of a measurable set
  is measurable. -/
theorem division_chart_preimage_image_measurable (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (R : Type) [CommRing R] [Algebra O R] [IsDomain R]
    [IsLocalRing R] (pi : O) (hpi : Irreducible pi) (hp0 : algebraMap O R pi ≠ 0)
    (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (n n' : ℕ)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (f g : R) (b : Fin n → R) (c : Fin n' → R)
    (hb : IsDivisionChart O R pi f b) (hc : IsDivisionChart O R pi g c) (S : Set (Fin n' → O))
    (hS : MeasurableSet S) :
    MeasurableSet (coordinateIdeal pi f b ⁻¹' (coordinateIdeal pi g c '' S)) := by
  obtain ⟨E, hE⟩ := hb.1
  by_cases hres : Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) f} =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) g}
  · obtain rfl := division_chart_rank_eq_of_residue_ideal_eq O R pi hpi n n' f g b c hb hc hres
    obtain ⟨g', c', F, h₀, hF, hfg, hg', hΨ⟩ :=
      division_chart_same_cell_recenter O R pi hpm n f g b c hb hc hres
    have himg : coordinateIdeal pi g c '' S = coordinateIdeal pi g' c' '' S :=
      Set.image_congr fun z _ ↦ hΨ z
    have hT := (ideal_chart_transition_haar O R n pi b E hp0 hpm f hE hb.2 g' c' F hF hg' h₀
      hfg htop hpi).measurable
    have hfun : coordinateIdeal pi f b = coordinateIdeal pi g' c' ∘ idealTransition pi b c' F h₀ :=
      funext fun z ↦
        (coordinate_transition_ideal_identity O R n pi b hpm f g' c' F hF h₀ hfg z).symm
    rw [himg, hfun, Set.preimage_comp,
      (coordinate_ideal_injective O R n pi c' F hp0 hpm g' hF hg').preimage_image]
    exact hT hS
  · convert MeasurableSet.empty
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨s, _, hs⟩
    have h2 := coordinate_ideal_in_residue_cell O R n' pi c g s
    rw [hs] at h2
    exact hres ((coordinate_ideal_in_residue_cell O R n pi b f z).2.symm.trans h2.2)

/-- The state measure does not depend on the ideal atlas used to define it. -/
theorem state_measure_atlas_independent (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) [CommRing R] [Algebra O R]
    [MeasurableSpace (Ideal R)] (pi : O) (hpi : Irreducible pi) (n : ℕ) (X : Set (Ideal R))
    (A B : IdealAtlas O R pi n X)
    (hB : ∀ j, Measurable (coordinateIdeal pi (B.chart j).f (B.chart j).b)) (e : A.ι ≃ B.ι)
    (hcell : ∀ i, residueIdealCell (algebraMap O R pi) (A.chart i).f =
      residueIdealCell (algebraMap O R pi) (B.chart (e i)).f)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] [IsDomain R] [IsLocalRing R]
    (hp0 : algebraMap O R pi ≠ 0) (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) :
    stateMeasure O R pi n (Nat.card (IsLocalRing.ResidueField O)) A =
      stateMeasure O R pi n (Nat.card (IsLocalRing.ResidueField O)) B := by
  have key : ∀ i, chartMeasure O R pi n (A.chart i) = chartMeasure O R pi n (B.chart (e i)) := by
    intro i
    set f := (A.chart i).f
    set g := (B.chart (e i)).f
    have hmem : Ideal.span {f} ∈ residueIdealCell (algebraMap O R pi) f :=
      ⟨⟨f, rfl⟩, by rw [Ideal.map_span, Set.image_singleton]⟩
    rw [hcell i] at hmem
    have hres := hmem.2
    rw [Ideal.map_span, Set.image_singleton] at hres
    obtain ⟨g', c', F, h₀, hF, hfg, hg', hΨ⟩ :=
      division_data_same_cell_recenter O R pi hpm n f g (B.chart (e i)).b (A.chart i).regular
        (B.chart (e i)).E (B.chart (e i)).division hres
    have hfun : coordinateIdeal pi g (B.chart (e i)).b = coordinateIdeal pi g' c' := funext hΨ
    have hc : Measurable (coordinateIdeal pi g' c') := hfun ▸ hB (e i)
    unfold chartMeasure
    rw [show (B.chart (e i)).f = g from rfl, hfun]
    exact ideal_chart_pushforward_independent O R n pi (A.chart i).b (A.chart i).E hp0 hpm f
      (A.chart i).division (A.chart i).regular g' c' F hF hg' h₀ hfg htop hpi hc
  unfold stateMeasure
  congr 1
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun i _ ↦ key i

end SurfaceBlowup
