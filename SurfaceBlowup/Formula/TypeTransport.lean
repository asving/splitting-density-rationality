/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.StrictNormalizer

/-!
# Transport of factorization types and cell measures

This file collects transport statements: the factorization type of a monic polynomial is
invariant under Taylor shift and additive over coprime products, monic irreducible residue
polynomials lift to unramified lifts, a congruence-preserving mass-preserving bijection of
cells transports normalized cell measures, coordinate hyperplanes are null, and scaling by a
uniformizer multiplies coefficient measure by `q⁻ʳ`.

## Main results

* `SurfaceBlowup.block_translation_type_iff`: Taylor shift preserves the factorization type.
* `SurfaceBlowup.coprime_family_type_iff`: types of pairwise coprime products are sums.
* `SurfaceBlowup.exists_unramified_lift`: existence of unramified lifts of the same degree.
* `SurfaceBlowup.cell_transport_preimage`: transport of normalized cell measures.
* `SurfaceBlowup.coordinate_hyperplane_null`: coordinate hyperplanes have measure zero.
* `SurfaceBlowup.scaling_image_borel_mass`: the scaling image has mass `q⁻ʳ` times the original.

Provenance: `Thm_SurfaceBlowupV2_{block_translation_type_iff, coprime_family_type_iff,
exists_unramified_lift, cell_transport_preimage, coordinate_hyperplane_null,
scaling_image_borel_mass}`.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-- The factorization type of a monic polynomial over `O` (viewed over the fraction field) is
invariant under the Taylor shift `X ↦ X + θ`. -/
theorem block_translation_type_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (F : Polynomial O) (hF : F.Monic) (θ : O)
    (σ : FactorType) :
    HasPolynomialTypeF O (F.map (algebraMap O (BaseField O))) σ ↔
      HasPolynomialTypeF O ((Polynomial.taylor θ F).map (algebraMap O (BaseField O))) σ := by
  set K := BaseField O
  have h1 : (Polynomial.taylor θ F).map (algebraMap O K)
      = (Polynomial.algEquivAevalXAddC (algebraMap O K θ)) (F.map (algebraMap O K)) := by
    rw [Polynomial.taylor_apply, Polynomial.algEquivAevalXAddC_apply, ← Polynomial.comp_eq_aeval,
      Polynomial.map_comp]
    simp
  have hm : (Polynomial.taylor θ F).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_taylor]; exact hF
  have hI : (Ideal.span {F.map (algebraMap O K)}).map
      (Polynomial.algEquivAevalXAddC (algebraMap O K θ)).toRingEquiv.toRingHom
      = Ideal.span {(Polynomial.taylor θ F).map (algebraMap O K)} := by
    rw [Ideal.map_span, Set.image_singleton, h1]; rfl
  exact polynomial_type_algEquiv_iff O _ _ (hF.map _) (hm.map _)
    (Ideal.quotientEquivAlg _ _ (Polynomial.algEquivAevalXAddC (algebraMap O K θ)) hI.symm) σ

/-- For a finite family of monic, pairwise coprime polynomials, the product has type `σ`
exactly when `σ` is the sum of types of the factors. -/
theorem coprime_family_type_iff (O : Type) [CommRing O] [IsDomain O] (ι : Type) [Fintype ι]
    (F : ι → Polynomial (BaseField O)) (hF : ∀ i, (F i).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (F i) (F j)) (σ : FactorType) :
    HasPolynomialTypeF O (∏ i, F i) σ ↔
      ∃ τ : ι → FactorType, (∀ i, HasPolynomialTypeF O (F i) (τ i)) ∧ σ = ∑ i, τ i := by
  classical
  have key : ∀ τ : ι → FactorType, (∀ i, HasPolynomialTypeF O (F i) (τ i)) →
      ∀ s : Finset ι, HasPolynomialTypeF O (∏ i ∈ s, F i) (∑ i ∈ s, τ i) := by
    intro τ hτ s
    induction s using Finset.induction_on with
    | empty => exact ⟨[], by simp⟩
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact polynomial_type_mul_coprime O _ _ _ _ (hτ a) ih
        (IsCoprime.prod_right fun i hi ↦ hc a i fun h ↦ ha (h ▸ hi))
  refine ⟨fun h ↦ ?_, fun ⟨τ, hτ, hσ⟩ ↦ hσ ▸ key τ hτ Finset.univ⟩
  choose τ hτ using fun i ↦
    polynomial_type_dvd O _ (F i) σ h (hF i) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact ⟨τ, hτ, polynomial_type_unique O _ _ _ h (key τ hτ Finset.univ)⟩

/-- Every monic irreducible residue polynomial `φ` has an unramified lift `Φ` over `O` of the
same degree. -/
theorem exists_unramified_lift (O : Type) [CommRing O] [IsLocalRing O]
    (φ : Polynomial (IsLocalRing.ResidueField O)) (hφ : φ.Monic) (hirr : Irreducible φ) :
    ∃ Φ : Polynomial O,
      IsUnramifiedLift O Φ ∧ residuePoly O Φ = φ ∧ Φ.natDegree = φ.natDegree := by
  obtain ⟨a, ha⟩ := (residue_cell_cylinder O φ.natDegree φ).2.1 hφ rfl
  obtain ⟨h1, h2, -, -⟩ := monic_poly_reconstruct O φ.natDegree a
  have ha' : residuePoly O (monicPolyO a) = φ := ha
  exact ⟨monicPolyO a, ⟨h1, ha'.symm ▸ hirr⟩, ha', h2⟩

/-- The normalized measure of a measurable cell, as a quotient of coefficient measures. -/
theorem cellMeasure_apply_of_measurableSet (O : Type) [CommRing O] [IsDomain O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] (n : ℕ) (S : Set (Fin n → O))
    (hS : MeasurableSet S) (s : Set (Fin n → O)) :
    cellMeasure O n S s = (coefficientMeasure O n S)⁻¹ * coefficientMeasure O n (s ∩ S) := by
  simp [cellMeasure, MeasureTheory.Measure.restrict_apply' hS]

/-- The normalized measure of a measurable cell `S` only sees the trace on `S`. -/
theorem cellMeasure_cell_inter {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] {n : ℕ} {S : Set (Fin n → O)} (hS : MeasurableSet S)
    (T : Set (Fin n → O)) : cellMeasure O n S (S ∩ T) = cellMeasure O n S T := by
  simp [cellMeasure, MeasureTheory.Measure.restrict_apply' hS, Set.inter_comm S T,
    Set.inter_assoc]

/-- The normalized measure of a measurable cell of positive mass is a probability measure. -/
private theorem cellMeasure_univ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (S : Set (Fin n → O))
    (hS : MeasurableSet S) (h : coefficientMeasure O n S ≠ 0) :
    cellMeasure O n S Set.univ = 1 := by
  have := coefficient_measure_probability O htop n
  rw [cellMeasure_apply_of_measurableSet O n S hS, Set.univ_inter]
  exact ENNReal.inv_mul_cancel h (MeasureTheory.measure_ne_top _ _)

/-- A bijection `f : S₁ → S₂` between coefficient cells that preserves `𝔪ᴸ`-congruence and
the normalized masses of all congruence balls of level `L ≥ 1` transports the normalized cell
measure: `f⁻¹' T` has the same measure in `S₁` as `T` in `S₂`. -/
theorem cell_transport_preimage (O₁ : Type) [CommRing O₁] [IsDomain O₁]
    [IsDiscreteValuationRing O₁] [IsAdicComplete (IsLocalRing.maximalIdeal O₁) O₁]
    [Finite (IsLocalRing.ResidueField O₁)] [TopologicalSpace O₁] [IsTopologicalRing O₁]
    [CompactSpace O₁] [T2Space O₁] [SecondCountableTopology O₁] [MeasurableSpace O₁]
    [BorelSpace O₁] (htop₁ : IsAdic (IsLocalRing.maximalIdeal O₁)) (O₂ : Type) [CommRing O₂]
    [IsDomain O₂] [IsDiscreteValuationRing O₂] [IsAdicComplete (IsLocalRing.maximalIdeal O₂) O₂]
    [Finite (IsLocalRing.ResidueField O₂)] [TopologicalSpace O₂] [IsTopologicalRing O₂]
    [CompactSpace O₂] [T2Space O₂] [SecondCountableTopology O₂] [MeasurableSpace O₂]
    [BorelSpace O₂] (htop₂ : IsAdic (IsLocalRing.maximalIdeal O₂)) (n₁ n₂ : ℕ)
    (S₁ : Set (Fin n₁ → O₁)) (S₂ : Set (Fin n₂ → O₂)) (hS₁ : MeasurableSet S₁)
    (hS₂ : MeasurableSet S₂) (h₁ : coefficientMeasure O₁ n₁ S₁ ≠ 0)
    (h₂ : coefficientMeasure O₂ n₂ S₂ ≠ 0) (f : (Fin n₁ → O₁) → (Fin n₂ → O₂))
    (hf : Set.BijOn f S₁ S₂)
    (hcong : ∀ (L : ℕ), ∀ a ∈ S₁, ∀ a' ∈ S₁, (∀ j, a j - a' j ∈ (IsLocalRing.maximalIdeal O₁) ^ L)
      ↔ ∀ j, f a j - f a' j ∈ (IsLocalRing.maximalIdeal O₂) ^ L)
    (hmass : ∀ (L : ℕ), 1 ≤ L → ∀ a ∈ S₁,
      cellMeasure O₁ n₁ S₁ {a' | ∀ j, a' j - a j ∈ (IsLocalRing.maximalIdeal O₁) ^ L} =
        cellMeasure O₂ n₂ S₂ {b | ∀ j, b j - f a j ∈ (IsLocalRing.maximalIdeal O₂) ^ L}) :
    ∀ T : Set (Fin n₂ → O₂), MeasurableSet T →
      MeasurableSet (S₁ ∩ f ⁻¹' T) ∧ cellMeasure O₁ n₁ S₁ (f ⁻¹' T) = cellMeasure O₂ n₂ S₂ T := by
  classical
  set m₁ := IsLocalRing.maximalIdeal O₁
  set m₂ := IsLocalRing.maximalIdeal O₂
  have hgen₂ := finite_coordinate_borel_cylinders O₂ m₂ htop₂ n₂
  have ht : ∀ (L : ℕ) (x : Fin n₂ → O₂),
      {y | adicCongr m₂ L y x} = {y : Fin n₂ → O₂ | ∀ j, y j - x j ∈ m₂ ^ L} := fun L x ↦ by
    ext y; simp only [Set.mem_ofPred_eq, finite_coordinate_adic_congruence]
  -- the trace on `S₁` of the `f`-preimage of a ball is a ball around a point of `S₁`, or empty
  have htrace : ∀ (L : ℕ) (x : Fin n₂ → O₂),
      (∃ a₀ ∈ S₁, S₁ ∩ f ⁻¹' {y | ∀ j, y j - x j ∈ m₂ ^ L} = S₁ ∩ {y | ∀ j, y j - a₀ j ∈ m₁ ^ L}
        ∧ {y : Fin n₂ → O₂ | ∀ j, y j - x j ∈ m₂ ^ L} = {y | ∀ j, y j - f a₀ j ∈ m₂ ^ L}) ∨
      (S₁ ∩ f ⁻¹' {y | ∀ j, y j - x j ∈ m₂ ^ L} = ∅ ∧
        {y : Fin n₂ → O₂ | ∀ j, y j - x j ∈ m₂ ^ L} ∩ S₂ = ∅) := by
    intro L x
    rcases Set.eq_empty_or_nonempty ({y : Fin n₂ → O₂ | ∀ j, y j - x j ∈ m₂ ^ L} ∩ S₂) with
      hne | ⟨b, hbB, hbS⟩
    · exact Or.inr ⟨Set.eq_empty_of_forall_notMem fun a ⟨ha, hB⟩ ↦
        hne.subset ⟨hB, hf.mapsTo ha⟩, hne⟩
    obtain ⟨a₀, ha₀, rfl⟩ := hf.surjOn hbS
    have hB : {y : Fin n₂ → O₂ | ∀ j, y j - x j ∈ m₂ ^ L} = {y | ∀ j, y j - f a₀ j ∈ m₂ ^ L} :=
      Set.ext fun y ↦ ⟨fun hy j ↦ by simpa using (m₂ ^ L).sub_mem (hy j) (hbB j),
        fun hy j ↦ by simpa using (m₂ ^ L).add_mem (hy j) (hbB j)⟩
    refine Or.inl ⟨a₀, ha₀, Set.ext fun a ↦ ?_, hB⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, hB]
    exact and_congr_right fun ha ↦ (hcong L a ha a₀ ha₀).symm
  -- extend `f` outside `S₁` by a constant to get a measurable map
  obtain ⟨b₀, -⟩ : S₂.Nonempty := Set.nonempty_iff_ne_empty.2 fun h ↦ h₂ (h ▸ by simp)
  let g : (Fin n₁ → O₁) → (Fin n₂ → O₂) := fun a ↦ if a ∈ S₁ then f a else b₀
  have hgS : ∀ T : Set (Fin n₂ → O₂), S₁ ∩ g ⁻¹' T = S₁ ∩ f ⁻¹' T := fun T ↦
    Set.ext fun a ↦ by by_cases ha : a ∈ S₁ <;> simp [g, ha]
  have hgmeas : Measurable g := by
    have : @Measurable _ _ _ (adicCylinderSpace m₂ (Fin n₂ → O₂)) g := by
      refine measurable_generateFrom ?_
      rintro t (rfl | ⟨L, x, rfl⟩)
      · simp
      have hg : g ⁻¹' {y | adicCongr m₂ L y x} =
          (S₁ ∩ g ⁻¹' {y | adicCongr m₂ L y x}) ∪ (S₁ᶜ ∩ {_a | b₀ ∈ {y | adicCongr m₂ L y x}}) :=
        Set.ext fun a ↦ by by_cases ha : a ∈ S₁ <;> simp [g, ha]
      rw [hg, hgS, ht]
      refine MeasurableSet.union ?_ (hS₁.compl.inter (MeasurableSet.const _))
      rcases htrace L x with ⟨a₀, -, h, -⟩ | ⟨h, -⟩ <;> rw [h]
      exacts [hS₁.inter ((coordinate_cylinder_clopen O₁ m₁ htop₁ L).1 n₁ a₀).2.measurableSet,
        .empty]
    rwa [← hgen₂] at this
  have hρ₁ := cellMeasure_apply_of_measurableSet O₁ n₁ S₁ hS₁
  have hρ₂ := cellMeasure_apply_of_measurableSet O₂ n₂ S₂ hS₂
  have hone₁ := cellMeasure_univ O₁ htop₁ n₁ S₁ hS₁ h₁
  have hone₂ := cellMeasure_univ O₂ htop₂ n₂ S₂ hS₂ h₂
  have : MeasureTheory.IsFiniteMeasure (cellMeasure O₂ n₂ S₂) := ⟨by simp [hone₂]⟩
  have hpush : ∀ T : Set (Fin n₂ → O₂), MeasurableSet T →
      (cellMeasure O₁ n₁ S₁).map g T = cellMeasure O₁ n₁ S₁ (f ⁻¹' T) := fun T hT ↦ by
    rw [MeasureTheory.Measure.map_apply hgmeas hT, hρ₁, hρ₁, Set.inter_comm, hgS, Set.inter_comm]
  have hEq : cellMeasure O₂ n₂ S₂ = (cellMeasure O₁ n₁ S₁).map g := by
    refine finite_measures_from_cylinders O₂ (Fin n₂ → O₂) m₂ _ _ hgen₂ fun L x ↦ ?_
    rw [ht, hpush _ ((coordinate_cylinder_clopen O₂ m₂ htop₂ L).1 n₂ x).2.measurableSet]
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top, implies_true, Set.ofPred_true,
        Set.preimage_univ, hone₁, hone₂]
    rcases htrace L x with ⟨a₀, ha₀, h, hB⟩ | ⟨h, hB⟩
    · rw [hρ₁, Set.inter_comm, h, Set.inter_comm, ← hρ₁, hmass L hL a₀ ha₀, hB]
    · rw [hρ₁, hρ₂, hB, Set.inter_comm (f ⁻¹' _), h]; simp
  exact fun T hT ↦ ⟨hgS T ▸ hS₁.inter (hgmeas hT), by rw [← hpush T hT, ← hEq]⟩

/-- A coordinate hyperplane `{b | b j = 0}` is measurable and null for the coefficient
measure. -/
theorem coordinate_hyperplane_null (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (j : Fin n) :
    MeasurableSet {b : Fin n → O | b j = 0} ∧
      coefficientMeasure O n {b : Fin n → O | b j = 0} = 0 := by
  have hcl : IsClosed {b : Fin n → O | b j = 0} :=
    isClosed_eq (continuous_apply j) continuous_const
  refine ⟨hcl.measurableSet, ?_⟩
  have := coefficient_measure_probability O htop n
  have : MeasureTheory.Measure.IsAddLeftInvariant (coefficientMeasure O n) := by
    unfold coefficientMeasure; infer_instance
  set m := IsLocalRing.maximalIdeal O
  set q := Nat.card (IsLocalRing.ResidueField O)
  have hq1 : 1 < q := Finite.one_lt_card_iff_nontrivial.2 inferInstance
  have key : ∀ L : ℕ, coefficientMeasure O n {b : Fin n → O | b j = 0} ≤ ((q : ℝ≥0∞)⁻¹) ^ L := by
    intro L
    have hcard : Nat.card (O ⧸ m ^ L) = q ^ L := residue_quotient_card O L
    have : Finite (O ⧸ m ^ L) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    let π : (Fin n → O) →+ (O ⧸ m ^ L) :=
      (Ideal.Quotient.mk (m ^ L)).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ ↦ O) j)
    have hπ : ∀ b, π b = Ideal.Quotient.mk (m ^ L) (b j) := fun b ↦ rfl
    have hsurj : Function.Surjective π := fun c ↦ by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact ⟨fun _ ↦ y, rfl⟩
    have hm : ∀ a, MeasurableSet {x | π x = a} := by
      intro a
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
      have h1 := (coordinate_cylinder_clopen O m htop L).1 1 (fun _ ↦ y)
      have : {x : Fin n → O | π x = Ideal.Quotient.mk (m ^ L) y}
          = (fun b : Fin n → O ↦ fun _ : Fin 1 ↦ b j) ⁻¹'
            {b : Fin 1 → O | ∀ i, b i - (fun _ ↦ y) i ∈ m ^ L} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, hπ, Ideal.Quotient.eq]
        exact ⟨fun h _ ↦ h, fun h ↦ h 0⟩
      rw [this]
      exact (h1.1.preimage (continuous_pi fun _ ↦ continuous_apply j)).measurableSet
    have hmass := finite_quotient_event_mass (Fin n → O) (O ⧸ m ^ L)
      (coefficientMeasure O n) π hsurj hm {0}
    have hpre : π ⁻¹' {0} = {b : Fin n → O | b j ∈ m ^ L} := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hπ, Ideal.Quotient.eq_zero_iff_mem,
        Set.mem_ofPred_eq]
    rw [hpre] at hmass
    have hsub : {b : Fin n → O | b j = 0} ⊆ {b : Fin n → O | b j ∈ m ^ L} := fun b hb ↦ by
      simp_all
    calc _ ≤ _ := MeasureTheory.measure_mono hsub
      _ = _ := hmass
      _ = ((q : ℝ≥0∞)⁻¹) ^ L := by simp [hcard, ENNReal.inv_pow, div_eq_mul_inv]
  have hlt : (q : ℝ≥0∞)⁻¹ < 1 := by rw [ENNReal.inv_lt_one]; exact_mod_cast hq1
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) key) zero_le

/-- Scaling by a uniformizer `π` maps a measurable set `T ⊆ Oʳ` to a measurable set of
coefficient measure `q⁻ʳ · μ(T)`, where `q` is the residue field cardinality. -/
theorem scaling_image_borel_mass (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (pi : O) (hpi : Irreducible pi) (r : ℕ)
    (T : Set (Fin r → O)) (hT : MeasurableSet T) :
    MeasurableSet ((fun z : Fin r → O ↦ pi • z) '' T) ∧
      coefficientMeasure O r ((fun z : Fin r → O ↦ pi • z) '' T) =
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ r * coefficientMeasure O r T := by
  have e : (fun z : Fin r → O ↦ pi • z) = coordinateScale pi 1 := by
    funext z; simp [coordinateScale]
  refine ⟨?_, by simpa [e] using coordinate_scale_measure O htop pi hpi r 1 T⟩
  have hc : Continuous (fun z : Fin r → O ↦ pi • z) :=
    continuous_pi fun j ↦ continuous_const.mul (continuous_apply j)
  have hi : Function.Injective (fun z : Fin r → O ↦ pi • z) := fun z z' h ↦
    funext fun j ↦ mul_left_cancel₀ hpi.ne_zero (congrFun h j)
  exact (hc.isClosedEmbedding hi).measurableEmbedding.measurableSet_image.2 hT

end SurfaceBlowup
