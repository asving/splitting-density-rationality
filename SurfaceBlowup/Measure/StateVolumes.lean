/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.CurveOrders
import SurfaceBlowup.Surfaces.TruncatedSeries

/-!
# Single-state residue ideal counts and Haar-measure transport

We count the residue ideals of a single state `k⟦T, X⟧ ⧸ (T^a)` with contact `c` with `T`, deduce
the total state measure `q^(-c)`, and collect general facts on transporting Haar probability
measures: congruence-preserving bijections preserve measure, and a continuous injective homomorphism
from a compact group scales Haar measure by the inverse index of its image.

## Main results

* `single_residue_ideal_count`
* `single_state_volume`
* `congruence_bijection_measure_preserving`
* `compact_injective_image_measure`

Provenance: single_residue_ideal_count, single_state_volume,
congruence_bijection_measure_preserving, compact_image_index_mass, compact_injective_comap_measure,
compact_injective_image_measure.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-- The number of single residue ideals of `k⟦T, X⟧ ⧸ (T^a)` with contact `c` with `T` is
  `q^(ac - c)`, where `q = #k`. -/
theorem single_residue_ideal_count (k : Type) [Field k] [Finite k] (a c : ℕ) (ha : 0 < a) :
    Nat.card (singleResidueIdeals k a c) = (Nat.card k)^(a*c-c) := by
  have hcN : c ≤ a * c := Nat.le_mul_of_pos_left c ha
  have hlen : ∀ F : TwoSeries k, axisQuotientLength k 0 F = c →
      Module.length (TwoSeries k) (TwoSeries k ⧸ (monomialIdeal k a 0 ⊔ Ideal.span {F})) =
        ((a*c : ℕ) : ℕ∞) := by
    intro F hF
    have h5 := length_double_quotient_eq (TwoSeries k) (monomialIdeal k a 0) (Ideal.span {F})
    rw [Ideal.map_span, Set.image_singleton] at h5
    rw [← h5, single_special_fiber_length k a c ha _
      (by rw [contact_fiberT_eq_axisQuotientLength k a 0 ha, hF]), Nat.cast_mul]
  have : Finite (IsLocalRing.ResidueField (TwoSeries k)) :=
    .of_equiv _ (twoSeriesResidueEquiv k).toEquiv.symm
  have hmem : ∀ j < a*c+1, ((0:ℕ), j) ∈ truncIndex a 0 (a*c+1) := by
    intro j hj; simp [truncIndex]; omega
  have hE : ∀ j, truncExponent ((0:ℕ), j) = Finsupp.single 1 j := by simp [truncExponent]
  let A : Finset (truncIndex a 0 (a*c+1)) := Finset.univ.filter (fun s => s.1.1 = 0 ∧ s.1.2 < c)
  let B : Finset (truncIndex a 0 (a*c+1)) := {⟨(0, c), hmem c (by omega)⟩}
  have hA : A.card = c := card_truncIndex_axis_segment a 0 _ c Prod.fst Prod.snd ((0, ·))
    (fun _ => ⟨rfl, rfl⟩) (fun x h => Prod.ext h.symm rfl) fun j hj => hmem j (by omega)
  have key := principal_residue_ideal_count k a 0 (a*c) ha (axisQuotientLength k 0 · = c)
    (contact · (fiberT k a 0) = c) (fun F => by rw [contact_fiberT_eq_axisQuotientLength k a 0 ha])
    (fun U F hU hF => by rwa [axisQuotientLength, Ideal.span_singleton_mul_left_unit hU])
    hlen (fun F hF => by
      rw [finite_length_module_card (TwoSeries k) _ _ (hlen F hF),
        Nat.card_congr (twoSeriesResidueEquiv k).toEquiv])
    A B (by simp [A, B]) (Finset.singleton_nonempty _) (fun F => by
      rw [axisQuotientLength_eq_iff k (s := 0) (t := 1) (by decide)]
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        forall_eq, truncCoeffs_apply, hE]
      refine and_congr_left' ⟨fun h ⟨⟨i, j⟩, _⟩ ⟨hi, hj⟩ => ?_,
        fun h j hj => by simpa [hE] using h ⟨_, hmem j (by omega)⟩ ⟨rfl, hj⟩⟩
      obtain rfl : i = 0 := hi
      rw [hE]; exact h j hj)
  rw [hA, Finset.card_singleton, pow_one, Nat.add_sub_cancel,
    show a * c = c + (a * c - c) by omega, pow_add] at key
  have hpos : 0 < (Nat.card k - 1) * Nat.card k ^ c :=
    Nat.mul_pos (by have := Finite.one_lt_card (α := k); omega) (pow_pos Nat.card_pos _)
  unfold singleResidueIdeals
  exact Nat.eq_of_mul_eq_mul_left hpos (by linarith [key])

/-- The total state measure of a single state with contact `c` is `q^(-c)`, where `q` is the residue
  cardinality. -/
theorem single_state_volume (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) [CommRing R] [Algebra O R]
    [MeasurableSpace (Ideal R)] (pi : O) (X : Set (Ideal R))
    (a c : ℕ) (ha : 0 < a) (A : IdealAtlas O R pi (a * c) X)
    (hA : ∀ i, Measurable (coordinateIdeal pi (A.chart i).f (A.chart i).b))
    (hcount : Nonempty (A.ι ≃ singleResidueIdeals (IsLocalRing.ResidueField O) a c)) :
    stateMeasure O R pi (a*c) (Nat.card (IsLocalRing.ResidueField O)) A Set.univ =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^c := by
  rw [state_measure_total_mass O R htop pi (a*c) X A hA]
  obtain ⟨e⟩ := hcount
  have hcard : Fintype.card A.ι = Nat.card (IsLocalRing.ResidueField O) ^ (a*c-c) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e,
      single_residue_ideal_count _ a c ha]
  rw [hcard]
  set q := Nat.card (IsLocalRing.ResidueField O)
  have hq : 0 < q := Nat.card_pos
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
  have hqt : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  have hle : c ≤ a * c := Nat.le_mul_of_pos_left c ha
  obtain ⟨m, hm⟩ : ∃ m, a * c = m + c := ⟨a*c - c, (Nat.sub_add_cancel hle).symm⟩
  rw [hm, Nat.add_sub_cancel, pow_add]
  push_cast
  rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hq0 hqt, one_pow, one_mul]

/-- A surjection preserving every adic congruence preserves any probability measure on adic
  cylinders that gives all balls of the same radius the same mass. -/
theorem congruence_bijection_measure_preserving (O V : Type) [CommRing O] [AddCommGroup V]
    [Module O V] (I : Ideal O) [MeasurableSpace V]
    (hgen : ‹MeasurableSpace V› = adicCylinderSpace I V) (F : V → V) (honto : Function.Surjective F)
    (hcong : ∀ j x y, adicCongr I j (F x) (F y) ↔ adicCongr I j x y) (mu : MeasureTheory.Measure V)
    [MeasureTheory.IsProbabilityMeasure mu]
    (hball : ∀ j (x y : V), mu {z | adicCongr I j z x} = mu {z | adicCongr I j z y}) :
    MeasureTheory.MeasurePreserving F mu mu := by
  have hF : Measurable F := congruence_bijection_measurable O V I hgen F honto hcong
  refine ⟨hF, ?_⟩
  have : MeasureTheory.IsFiniteMeasure (mu.map F) := inferInstance
  refine finite_measures_from_cylinders O V I (mu.map F) mu hgen ?_
  intro j x
  have hmeas : MeasurableSet {y | adicCongr I j y x} := by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨j, x, rfl⟩)
  rw [MeasureTheory.Measure.map_apply hF hmeas]
  obtain ⟨w, rfl⟩ := honto x
  have : F ⁻¹' {y | adicCongr I j y (F w)} = {z | adicCongr I j z w} := by
    ext z; simp [hcong]
  rw [this]
  exact hball j w (F w)

/-- The image of a continuous homomorphism from a compact group, of finite index `n`, has Haar
  probability mass `1 / n`. -/
private theorem compact_image_index_mass (G H : Type) [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (f : G →+ H) (hf : Continuous f) [Finite (H ⧸ f.range)] (nu : MeasureTheory.Measure H)
    [MeasureTheory.IsProbabilityMeasure nu] [MeasureTheory.Measure.IsAddLeftInvariant nu] :
    nu (Set.range f) = (f.range.index : ℝ≥0∞)⁻¹ := by
  have hcl : IsClosed (Set.range f) := (isCompact_range hf).isClosed
  have hm : ∀ a : H ⧸ f.range, MeasurableSet {x | QuotientAddGroup.mk' f.range x = a} := by
    intro a
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective f.range a
    have : {x | QuotientAddGroup.mk' f.range x = QuotientAddGroup.mk' f.range y}
        = (fun x => -y + x) ⁻¹' Set.range f := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, QuotientAddGroup.mk'_apply]
      rw [eq_comm, QuotientAddGroup.eq]
      change _ ↔ _ ∈ (f.range : Set H)
      simp
    rw [this]
    exact (hcl.preimage (continuous_const.add continuous_id)).measurableSet
  have h := finite_quotient_fiber_mass H (H ⧸ f.range) nu
    (QuotientAddGroup.mk' f.range) (QuotientAddGroup.mk'_surjective f.range) hm 0
  have e : {x | QuotientAddGroup.mk' f.range x = 0} = Set.range f := by
    ext x
    simp [QuotientAddGroup.eq_zero_iff]
  rw [e] at h
  rw [h, AddSubgroup.index]

/-- Pulling back a Haar probability measure along a continuous injective homomorphism from a compact
  group of image index `n` gives `1 / n` times Haar measure. -/
private theorem compact_injective_comap_measure (G H : Type) [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G] [MeasurableSpace G]
    [BorelSpace G] [TopologicalSpace H] [IsTopologicalAddGroup H] [T2Space H] [MeasurableSpace H]
    [BorelSpace H] (f : G →+ H) (hf : Continuous f) [Finite (H ⧸ f.range)]
    (hinj : Function.Injective f) (mu : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure mu] [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (nu : MeasureTheory.Measure H) [MeasureTheory.IsProbabilityMeasure nu]
    [MeasureTheory.Measure.IsAddLeftInvariant nu] :
    nu.comap f = (f.range.index : ℝ≥0∞)⁻¹ • mu := by
  have hce : Topology.IsClosedEmbedding f := hf.isClosedEmbedding hinj
  have hme : MeasurableEmbedding f := hce.measurableEmbedding
  have : (nu.comap f).IsAddLeftInvariant :=
    MeasureTheory.Measure.IsAddLeftInvariant.comap nu (f := f) hme
  have huniv : nu.comap f Set.univ = nu (Set.range f) := by
    rw [hme.comap_apply, Set.image_univ]
  have : MeasureTheory.IsFiniteMeasure (nu.comap f) :=
    ⟨by rw [huniv]; exact MeasureTheory.measure_lt_top _ _⟩
  have key := MeasureTheory.Measure.isAddInvariant_eq_smul_of_compactSpace (nu.comap f) mu
  have hc : (MeasureTheory.Measure.addHaarScalarFactor (nu.comap f) mu : ℝ≥0∞)
      = (f.range.index : ℝ≥0∞)⁻¹ := by
    have := congrArg (fun m : MeasureTheory.Measure G => m Set.univ) key
    simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.measure_univ] at this
    rw [← compact_image_index_mass G H f hf nu, ← huniv]
    rw [this, ENNReal.smul_def, smul_eq_mul, mul_one]
  rw [key]
  ext s hs
  simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  rw [← hc, ENNReal.smul_def, smul_eq_mul]

/-- A continuous injective homomorphism from a compact group of image index `n` maps a measurable
  set of Haar mass `m` to a set of Haar mass `m / n`. -/
theorem compact_injective_image_measure (G H : Type) [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G] [MeasurableSpace G]
    [BorelSpace G] [TopologicalSpace H] [IsTopologicalAddGroup H] [T2Space H] [MeasurableSpace H]
    [BorelSpace H] (f : G →+ H) (hf : Continuous f) [Finite (H ⧸ f.range)]
    (hinj : Function.Injective f) (mu : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure mu] [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (nu : MeasureTheory.Measure H) [MeasureTheory.IsProbabilityMeasure nu]
    [MeasureTheory.Measure.IsAddLeftInvariant nu] (S : Set G) :
    nu (f '' S) = (f.range.index : ℝ≥0∞)⁻¹ * mu S := by
  have hemb : MeasurableEmbedding f :=
    (hf.isClosedEmbedding hinj).measurableEmbedding
  have h := compact_injective_comap_measure G H f hf hinj mu nu
  have h2 := congrArg (fun m => m S) h
  rw [hemb.comap_apply] at h2
  rw [h2]
  simp

end SurfaceBlowup
