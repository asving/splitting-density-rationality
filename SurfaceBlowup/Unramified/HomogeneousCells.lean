/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Measure.AdicTransport
import SurfaceBlowup.Unramified.FrobeniusDescent

/-!
# Measure-preserving maps between homogeneous cells

Over a complete discrete valuation ring `O` with finite residue field, the normalized Haar measures
on residue cells of monic polynomials, on reduced form cells and on projective cells are related by
explicit algebraic maps. This file shows that these maps are measure preserving.

## Main results

* `SurfaceBlowup.form_product_measurable`: the reduced form-product map is Borel measurable.
* `SurfaceBlowup.factor_cells_measure_preserving`: multiplying monic lifts of pairwise coprime
  residue factors pushes the product of the factor cell measures to the cell measure of the product.
* `SurfaceBlowup.form_cell_monic_identification`: reduced form cells normalized at the last
  coordinate are monic residue cells, and coordinate reversal identifies the form cell of `X ^ r`
  normalized at `0` with the monic residue cell of `X ^ r`, measure-preservingly.
* `SurfaceBlowup.form_cells_measure_preserving`: the homogeneous analogue of the first result for
  reduced form cells.
* `SurfaceBlowup.projective_cell_normalization_pushforward`: normalizing a primitive vector at a
  coordinate where its residue form is `1` pushes the projective cell measure to the reduced form
  cell measure.

## Implementation notes

The three measure-preservation proofs share one skeleton
(`measurePreserving_cellMeasure_of_balls`): both measures are finite and agree on the
generating `𝔪`-adic balls, which reduces to balls of radius `𝔪 ^ L`, `L ≥ 1`, centred in the
target cell (balls centred outside the cell miss it).

Provenance: `Thm_SurfaceBlowupV2_{form_product_measurable, factor_cells_measure_preserving,
form_cell_monic_identification, form_cells_measure_preserving,
projective_cell_normalization_pushforward}` (`form_product_measurable` moved from
`Unramified/LocalDescent.lean`).
-/

namespace SurfaceBlowup

open scoped BigOperators ENNReal

/-! ### A skeleton for measure preservation onto a cell -/

/-- A measurable map `f` sending `P`-almost every point into a measurable cell `D` (a single
residue class modulo `𝔪`, with `cellMeasure O N D` a probability measure) pushes the probability
measure `P` forward to `cellMeasure O N D` as soon as both measures agree on the `𝔪 ^ L`-balls
(`L ≥ 1`) centred in `D`. -/
private theorem measurePreserving_cellMeasure_of_balls (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O]
    [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) {α : Type} [MeasurableSpace α]
    (P : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure P] (N : ℕ)
    (D : Set (Fin N → O)) (hDm : MeasurableSet D)
    [MeasureTheory.IsProbabilityMeasure (cellMeasure O N D)]
    (hDball : ∀ z ∈ D, D = {y | ∀ j, y j - z j ∈ IsLocalRing.maximalIdeal O})
    (f : α → Fin N → O) (hf : Measurable f) (S : Set α) (hS : P Sᶜ = 0)
    (hSD : Set.MapsTo f S D)
    (hball : ∀ L, 1 ≤ L → ∀ x ∈ D,
      P (f ⁻¹' {y | ∀ j, y j - x j ∈ IsLocalRing.maximalIdeal O ^ L}) =
        cellMeasure O N D {y | ∀ j, y j - x j ∈ IsLocalRing.maximalIdeal O ^ L}) :
    MeasureTheory.MeasurePreserving f P (cellMeasure O N D) := by
  set m := IsLocalRing.maximalIdeal O
  have hgen := finite_coordinate_borel_cylinders O m htop N
  refine ⟨hf, finite_measures_from_cylinders O (Fin N → O) m _ _ hgen fun L x => ?_⟩
  have hB : {y : Fin N → O | adicCongr m L y x} = {y | ∀ j, y j - x j ∈ m ^ L} := by
    ext y; exact finite_coordinate_adic_congruence O N m L y x
  have hBm : MeasurableSet {y : Fin N → O | ∀ j, y j - x j ∈ m ^ L} := by
    have h1 : @MeasurableSet _ (adicCylinderSpace m (Fin N → O)) {y | adicCongr m L y x} :=
      MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨L, x, rfl⟩)
    rwa [← hgen, hB] at h1
  rw [hB, MeasureTheory.Measure.map_apply hf hBm]
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have : {y : Fin N → O | ∀ j, y j - x j ∈ m ^ 0} = Set.univ := by ext y; simp
    rw [this, Set.preimage_univ, MeasureTheory.measure_univ, MeasureTheory.measure_univ]
  by_cases hx : x ∈ D
  · exact hball L hL x hx
  -- a ball around a point outside `D` misses `D`, so both sides vanish
  have hfar : ∀ y ∈ D, ¬ ∀ j, y j - x j ∈ m ^ L := fun y hy hyx => hx <| by
    rw [hDball y hy]
    exact fun j => by simpa only [neg_sub] using m.neg_mem (Ideal.pow_le_self (by omega) (hyx j))
  have h0 : cellMeasure O N D {y | ∀ j, y j - x j ∈ m ^ L} = 0 := by
    rw [cellMeasure, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply' hDm,
      show {y : Fin N → O | ∀ j, y j - x j ∈ m ^ L} ∩ D = ∅ from
        Set.eq_empty_of_forall_notMem fun y ⟨h1, h2⟩ => hfar y h2 h1]
    simp
  rw [h0]
  exact MeasureTheory.measure_mono_null (fun a ha haS => hfar _ (hSD haS) ha) hS

/-! ### Products of monic residue cells -/

/-- Multiplying monic lifts of pairwise coprime monic residue polynomials `g i` pushes the product
of the normalized cell measures forward to the normalized cell measure of `∏ i, g i`. -/
theorem factor_cells_measure_preserving (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (ι : Type) [Fintype ι]
    (g : ι → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ i, (g i).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j))
    [hσ : ∀ i, MeasureTheory.SigmaFinite
      (cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i)))] :
    MeasureTheory.MeasurePreserving (factorProduct (fun i => (g i).natDegree))
      (MeasureTheory.Measure.pi
        (fun i => cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i))))
      (cellMeasure O (∑ i, (g i).natDegree)
        (residueCell O (∑ i, (g i).natDegree) (∏ i, g i))) := by
  set m := IsLocalRing.maximalIdeal O
  set n := ∑ i, (g i).natDegree
  set C := residueCell O n (∏ i, g i)
  set PC := Set.pi Set.univ (fun i => residueCell O (g i).natDegree (g i))
  set f := factorProduct (O := O) (fun i => (g i).natDegree)
  set q : ℝ≥0∞ := (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞) with hq
  have hfm : Measurable f := (factor_product_continuous O ι (fun i => (g i).natDegree)).2
  have hGm : (∏ i, g i).Monic := Polynomial.monic_prod_of_monic _ _ (fun i _ => hg i)
  have hGn : (∏ i, g i).natDegree = n := Polynomial.natDegree_prod_of_monic _ _ (fun i _ => hg i)
  obtain ⟨hCm, hCmass, hρprob⟩ := residue_cell_mass O htop n (∏ i, g i) hGm hGn
  obtain ⟨hPprob, hPnull, hPball⟩ := factor_cell_product_measure O htop ι g hg
  have hbij := factor_product_bijection O ι g hg hc
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hq0 : q ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hqt : q ≠ ⊤ := by simp [hq]
  have hqi0 : q⁻¹ ^ n ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.mpr hqt)
  have hqit : q⁻¹ ^ n ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hq0)
  refine measurePreserving_cellMeasure_of_balls O htop _ n C hCm (residue_cell_cylinder O n _).1 f
    hfm PC hPnull hbij.mapsTo fun j hj x hx => ?_
  set B := {y : Fin n → O | ∀ i, y i - x i ∈ m ^ j} with hBdef
  have hmj : m ^ j ≤ m := Ideal.pow_le_self (by omega)
  obtain ⟨a', ha', hfa'⟩ := hbij.surjOn hx
  have hBC : B ⊆ C := fun y hy => by
    change y ∈ residueCell O n (∏ i, g i)
    rw [(residue_cell_cylinder O n _).1 x hx]
    exact fun i => hmj (hy i)
  have hpre : f ⁻¹' B ∩ PC = Set.pi Set.univ
      (fun i => {b : Fin (g i).natDegree → O | ∀ k, b k - a' i k ∈ m ^ j}) := by
    ext a
    constructor
    · rintro ⟨hfa, haP⟩
      simpa using (factor_product_congruence_iff O ι g hc j a a' haP ha').1
        fun k => by have h := hfa k; rw [← hfa'] at h; exact h
    · intro ha
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, true_implies] at ha
      have haP : a ∈ PC := by
        simp only [PC, Set.mem_pi, Set.mem_univ, true_implies]
        intro i
        rw [(residue_cell_cylinder O _ _).1 _ (ha' i (Set.mem_univ i))]
        exact fun k => hmj (ha i k)
      refine ⟨?_, haP⟩
      change ∀ k, f a k - x k ∈ m ^ j
      rw [← hfa']
      exact (factor_product_congruence_iff O ι g hc j a a' haP ha').2 ha
  have hmass : coefficientMeasure O n B = q⁻¹ ^ (n * j) := by
    have := coefficient_uniformizer_cylinder_mass O htop n pi hpi j x
    rw [← hpi.maximalIdeal_eq] at this
    rw [← this]
    congr 1
    ext y; exact (finite_coordinate_adic_congruence O n m j y x).symm
  rw [← MeasureTheory.measure_inter_conull hPnull, hpre, hPball j hj a' ha', cellMeasure,
    MeasureTheory.Measure.smul_apply, smul_eq_mul, MeasureTheory.Measure.restrict_apply' hCm,
    Set.inter_eq_left.mpr hBC, hCmass, hmass]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, mul_add, mul_one, pow_add, ← mul_assoc, mul_comm _ (q⁻¹ ^ (n * k)),
    mul_assoc, ENNReal.inv_mul_cancel hqi0 hqit, mul_one]

/-! ### Reduced form cells versus monic residue cells -/

private theorem formPoly_coeff_fin {A : Type} [CommRing A] {n : ℕ} (a : Fin (n + 1) → A)
    (k : Fin (n + 1)) : (formPoly a).coeff (k : ℕ) = a k := by
  simp [formPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Fin.val_inj]

private theorem formPoly_inj_fin {A : Type} [CommRing A] {n : ℕ} (a a' : Fin (n + 1) → A) :
    formPoly a = formPoly a' ↔ a = a' :=
  ⟨fun h => funext fun k => by rw [← formPoly_coeff_fin a k, ← formPoly_coeff_fin a' k, h],
    fun h => h ▸ rfl⟩

private theorem formPoly_map_fin {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (a : Fin (n + 1) → A) : (formPoly a).map f = formPoly (fun i => f (a i)) := by
  simp [formPoly, Polynomial.map_sum]

private theorem formPoly_insertOne_last_eq {A : Type} [CommRing A] {d : ℕ} (b : Fin d → A) :
    formPoly (insertOne (Fin.last d) b) = monicPolyO b := by
  unfold formPoly monicPolyO insertOne
  rw [Fin.sum_univ_castSucc]
  simp [add_comm]

private theorem reducedFormCell_last_eq (O : Type) [CommRing O] [IsLocalRing O] (d : ℕ)
    (g : Fin (d + 1) → IsLocalRing.ResidueField O) :
    reducedFormCell O d (Fin.last d) g = residueCell O d (formPoly g) := by
  ext b
  simp only [reducedFormCell, normalizedFormCell, residueCell, Set.mem_ofPred_eq]
  have h1 : insertOne (Fin.last d) b (Fin.last d) = 1 := by simp [insertOne]
  rw [← formPoly_insertOne_last_eq, formPoly_map_fin, formPoly_inj_fin]
  simp only [h1, true_and]
  rfl

private theorem insertOne_last_comp_rev {A : Type} [CommRing A] {r : ℕ} (b : Fin r → A) :
    insertOne (Fin.last r) (b ∘ Fin.rev) = insertOne 0 b ∘ Fin.rev := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [insertOne]
  · simp [insertOne, Fin.rev_castSucc]

private theorem mem_reducedFormCell_zero_iff (O : Type) [CommRing O] [IsLocalRing O] (r : ℕ)
    (b : Fin r → O) :
    b ∈ reducedFormCell O r 0 (Pi.single 0 1) ↔
      b ∘ Fin.rev ∈ residueCell O r (Polynomial.X ^ r) := by
  have hX : (Polynomial.X ^ r : Polynomial (IsLocalRing.ResidueField O))
      = formPoly (Pi.single (Fin.last r) 1) := by
    have h0 : monicPolyO (0 : Fin r → IsLocalRing.ResidueField O) = Polynomial.X ^ r := by
      simp [monicPolyO]
    rw [← h0, ← formPoly_insertOne_last_eq]
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [insertOne]
    · simp [insertOne, Fin.castSucc_ne_last]
  rw [hX, ← reducedFormCell_last_eq]
  simp only [reducedFormCell, normalizedFormCell, Set.mem_ofPred_eq, insertOne_last_comp_rev]
  have h0 : insertOne 0 b 0 = 1 := by simp [insertOne]
  simp only [Function.comp_apply, Fin.rev_last, h0, true_and]
  constructor
  · intro h; rw [← (show (Pi.single 0 1 : Fin (r+1) → IsLocalRing.ResidueField O) ∘ Fin.rev
        = Pi.single (Fin.last r) 1 from ?_), ← h]
    · rfl
    · funext i; simp [Pi.single_apply, Fin.rev_eq_iff]
  · intro h
    funext i
    have := congrFun h (Fin.rev i)
    simp only [residueVector, Function.comp_apply, Fin.rev_rev] at this ⊢
    rw [this]; simp [Pi.single_apply, Fin.rev_eq_iff]

private theorem comp_rev_comp_rev {A : Type} {r : ℕ} (b : Fin r → A) :
    (b ∘ Fin.rev) ∘ Fin.rev = b := by
  funext i; simp

/-- Reduced form cells normalized at the last coordinate are monic residue cells; coordinate
reversal is a bijection, compatible with congruences and measure preserving, from the reduced form
cell of `X ^ r` normalized at `0` onto the monic residue cell of `X ^ r`. -/
theorem form_cell_monic_identification (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (r : ℕ) :
    (∀ (d : ℕ) (g : Fin (d+1) → IsLocalRing.ResidueField O),
      reducedFormCell O d (Fin.last d) g = residueCell O d (formPoly g)) ∧
    Set.BijOn (fun b : Fin r → O => b ∘ Fin.rev) (reducedFormCell O r 0 (Pi.single 0 1))
      (residueCell O r (Polynomial.X ^ r)) ∧
    (∀ (L : ℕ) (b b' : Fin r → O), (∀ j, b j - b' j ∈ (IsLocalRing.maximalIdeal O) ^ L) ↔
      ∀ j, (b ∘ Fin.rev) j - (b' ∘ Fin.rev) j ∈ (IsLocalRing.maximalIdeal O) ^ L) ∧
    MeasureTheory.MeasurePreserving (fun b : Fin r → O => b ∘ Fin.rev)
      (cellMeasure O r (reducedFormCell O r 0 (Pi.single 0 1)))
      (cellMeasure O r (residueCell O r (Polynomial.X ^ r))) := by
  have hcong : ∀ (L : ℕ) (b b' : Fin r → O),
      (∀ j, b j - b' j ∈ (IsLocalRing.maximalIdeal O) ^ L) ↔
        ∀ j, (b ∘ Fin.rev) j - (b' ∘ Fin.rev) j ∈ (IsLocalRing.maximalIdeal O) ^ L :=
    fun L b b' => ⟨fun h j => h _, fun h j => by simpa using h (Fin.rev j)⟩
  refine ⟨reducedFormCell_last_eq O, ?_, hcong, ?_⟩
  · refine ⟨fun b hb => (mem_reducedFormCell_zero_iff O r b).1 hb, ?_,
      fun b' hb' => ⟨b' ∘ Fin.rev, ?_, ?_⟩⟩
    · intro b _ b' _ h
      simpa [comp_rev_comp_rev] using congrArg (fun c : Fin r → O => c ∘ Fin.rev) h
    · rw [mem_reducedFormCell_zero_iff]; simpa [comp_rev_comp_rev] using hb'
    · simp [comp_rev_comp_rev]
  let R : (Fin r → O) ≃ᵐ (Fin r → O) :=
    { toFun := fun b => b ∘ Fin.rev
      invFun := fun b => b ∘ Fin.rev
      left_inv := comp_rev_comp_rev
      right_inv := comp_rev_comp_rev
      measurable_toFun := measurable_pi_iff.2 (fun j => measurable_pi_apply _)
      measurable_invFun := measurable_pi_iff.2 (fun j => measurable_pi_apply _) }
  have hR : ∀ b, R b = b ∘ Fin.rev := fun _ => rfl
  have hμ : MeasureTheory.MeasurePreserving R (coefficientMeasure O r)
      (coefficientMeasure O r) := by
    refine ⟨R.measurable, ?_⟩
    have huniv : coefficientMeasure O r Set.univ = 1 := by
      simpa using coefficient_cylinder_mass O htop r 0 0
    have : MeasureTheory.IsFiniteMeasure (coefficientMeasure O r) := ⟨by simp [huniv]⟩
    refine finite_measures_from_cylinders O (Fin r → O) (IsLocalRing.maximalIdeal O) _ _
      (finite_coordinate_borel_cylinders O _ htop r) fun j x => ?_
    have hset : ∀ z : Fin r → O, {y | adicCongr (IsLocalRing.maximalIdeal O) j y z}
        = {y | ∀ i, y i - z i ∈ (IsLocalRing.maximalIdeal O) ^ j} := fun z => by
      ext y; exact finite_coordinate_adic_congruence O r _ j y z
    rw [hset, R.map_apply]
    have hpre : R ⁻¹' {y | ∀ i, y i - x i ∈ (IsLocalRing.maximalIdeal O) ^ j}
        = {y | ∀ i, y i - (x ∘ Fin.rev) i ∈ (IsLocalRing.maximalIdeal O) ^ j} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hR]
      rw [hcong j y (x ∘ Fin.rev)]
      simp
    rw [hpre, coefficient_cylinder_mass O htop, coefficient_cylinder_mass O htop]
  have hpre : R ⁻¹' residueCell O r (Polynomial.X ^ r) = reducedFormCell O r 0 (Pi.single 0 1) := by
    ext b; simp [hR, mem_reducedFormCell_zero_iff]
  have h2 := hμ.restrict_preimage_emb R.measurableEmbedding (residueCell O r (Polynomial.X ^ r))
  have hmass := hμ.measure_preimage_emb R.measurableEmbedding (residueCell O r (Polynomial.X ^ r))
  rw [hpre] at h2 hmass
  refine ⟨R.measurable, ?_⟩
  unfold cellMeasure
  rw [MeasureTheory.Measure.map_smul, show (fun b : Fin r → O => b ∘ Fin.rev) = ⇑R from rfl,
    h2.map_eq, hmass]

/-! ### Measurability of form products -/

/-- The reduced form-product map is Borel measurable. -/
theorem form_product_measurable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (ι : Type) [Fintype ι] (d : ι → ℕ)
    (ν : ∀ i, Fin (d i + 1)) (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (hgν : ∀ i, g i (ν i) = 1) (hc : FormsCoprime d g) (μ : Fin ((∑ i, d i) + 1))
    (hμ : formProd d g μ = 1) :
    Measurable (reducedFormProduct O d ν g μ) := by
  set m := IsLocalRing.maximalIdeal O
  set f := reducedFormProduct O d ν g μ
  set PC : Set (∀ i, Fin (d i) → O) :=
    Set.pi Set.univ (fun i ↦ reducedFormCell O (d i) (ν i) (g i))
  have hPC : MeasurableSet PC := MeasurableSet.univ_pi (fun i ↦
    (normalized_form_cell_cylinder_mass O htop (d i) (ν i) (g i) (hgν i)).2.2.2.1)
  have hoff : ∀ a, a ∉ PC → f a = 0 := fun a ha ↦ by
    simp only [f, reducedFormProduct]
    exact if_neg fun h ↦ ha fun i _ ↦ h i
  have hball : ∀ (k : ℕ) (L : ℕ) (x : Fin k → O),
      MeasurableSet {b : Fin k → O | ∀ j, b j - x j ∈ m ^ L} := fun k L x ↦ by
    have hk := finite_coordinate_borel_cylinders O m htop k
    have : @MeasurableSet _ (adicCylinderSpace m (Fin k → O)) {b | adicCongr m L b x} :=
      MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨L, x, rfl⟩)
    rw [← hk] at this
    convert this using 1
    ext b
    exact (finite_coordinate_adic_congruence O k m L b x).symm
  have hk := finite_coordinate_borel_cylinders O m htop (∑ i, d i)
  change @Measurable _ _ _ (inferInstance : MeasurableSpace (Fin _ → O)) f
  rw [hk]
  refine measurable_generateFrom ?_
  rintro s (rfl | ⟨L, x, rfl⟩)
  · simp
  obtain ⟨_, hsymm, htrans, -, -⟩ := adic_congruence_rules O (Fin (∑ i, d i) → O) m
  by_cases hne : ∃ a₀ ∈ PC, adicCongr m L (f a₀) x
  · obtain ⟨a₀, ha₀, hfa₀⟩ := hne
    have heq : f ⁻¹' {y | adicCongr m L y x} =
        (PC ∩ Set.pi Set.univ (fun i ↦ {b : Fin (d i) → O | ∀ j, b j - a₀ i j ∈ m ^ L})) ∪
        (PCᶜ ∩ {_a | adicCongr m L (0 : Fin (∑ i, d i) → O) x}) := by
      ext a
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_univ_pi]
      by_cases ha : a ∈ PC
      · simp only [ha, true_and, not_true_eq_false, false_and, or_false]
        constructor
        · intro h
          have h2 : adicCongr m L (f a) (f a₀) := htrans _ _ _ _ h (hsymm _ _ _ hfa₀)
          rw [finite_coordinate_adic_congruence] at h2
          exact form_product_congruence_reflects O ι d ν g hgν hc μ hμ a a₀ ha ha₀ L h2
        · intro h
          refine htrans _ _ _ _ ?_ hfa₀
          rw [finite_coordinate_adic_congruence]
          exact (form_product_maps_to_and_preserves O ι d ν g μ hμ a a₀ ha ha₀).2.2.2 L h
      · simp only [ha, false_and, false_or, not_false_eq_true, true_and, hoff a ha]
    rw [heq]
    exact (hPC.inter (MeasurableSet.univ_pi (fun i ↦ hball _ _ _))).union
      (hPC.compl.inter (MeasurableSet.const _))
  · push Not at hne
    have heq : f ⁻¹' {y | adicCongr m L y x} =
        PCᶜ ∩ {_a | adicCongr m L (0 : Fin (∑ i, d i) → O) x} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      by_cases ha : a ∈ PC
      · simp only [ha, not_true_eq_false, false_and, iff_false]
        exact hne a ha
      · simp only [ha, not_false_eq_true, true_and, hoff a ha]
    rw [heq]
    exact hPC.compl.inter (MeasurableSet.const _)

/-! ### Products of reduced form cells -/

/-- The homogeneous analogue of `factor_cells_measure_preserving`: the reduced form product map
pushes the product of the normalized reduced form cell measures forward to the normalized reduced
form cell measure of the product form. -/
theorem form_cells_measure_preserving (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (ι : Type) [Fintype ι] (d : ι → ℕ)
    (ν : ∀ i, Fin (d i + 1)) (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (hgν : ∀ i, g i (ν i) = 1) (hc : FormsCoprime d g) (μ : Fin ((∑ i, d i) + 1))
    (hμ : formProd d g μ = 1)
    [hσ : ∀ i, MeasureTheory.SigmaFinite
      (cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i)))] :
    MeasureTheory.MeasurePreserving (reducedFormProduct O d ν g μ)
      (MeasureTheory.Measure.pi
        (fun i => cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i))))
      (cellMeasure O (∑ i, d i) (reducedFormCell O (∑ i, d i) μ (formProd d g))) := by
  let m := IsLocalRing.maximalIdeal O
  let f := reducedFormProduct O d ν g μ
  let P := MeasureTheory.Measure.pi
    (fun i => cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i)))
  let PC := Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i))
  let D := reducedFormCell O (∑ i, d i) μ (formProd d g)
  have hfm : Measurable f := form_product_measurable O htop ι d ν g hgν hc μ hμ
  obtain ⟨hPprob, hPnull, hPball⟩ := form_cell_product_measure O htop ι d ν g hgν
  obtain ⟨-, hDball, -, hDmeas, -, hDprob, hDmass⟩ :=
    normalized_form_cell_cylinder_mass O htop (∑ i, d i) μ (formProd d g) hμ
  refine measurePreserving_cellMeasure_of_balls O htop P _ D hDmeas hDball f hfm PC hPnull
    (fun a ha => (form_product_maps_to_and_preserves O ι d ν g μ hμ a a ha ha).1)
    fun L hL x hx => ?_
  have hmL : m ^ L ≤ m := Ideal.pow_le_self (by omega)
  rw [hDmass L x hL hx]
  obtain ⟨a', ha', rfl⟩ := (form_product_bijection O ι d ν g hgν hc μ hμ).surjOn hx
  have hsub : Set.pi Set.univ (fun i => {b : Fin (d i) → O | ∀ j, b j - a' i j ∈ m ^ L}) ⊆
      PC := by
    intro a ha i _
    change a i ∈ reducedFormCell O (d i) (ν i) (g i)
    rw [(normalized_form_cell_cylinder_mass O htop (d i) (ν i) (g i) (hgν i)).2.1 (a' i)
      (ha' i trivial)]
    exact fun j => hmL (ha i trivial j)
  rw [← MeasureTheory.measure_inter_conull hPnull, ← hPball L hL a' ha']
  congr 1
  ext a
  constructor
  · rintro ⟨h1, h2⟩ i _ j
    exact form_product_congruence_reflects O ι d ν g hgν hc μ hμ a a' h2 ha' L h1 i j
  · exact fun ha => ⟨(form_product_maps_to_and_preserves O ι d ν g μ hμ a a' (hsub ha)
      ha').2.2.2 L (fun i j => ha i trivial j), hsub ha⟩

/-! ### Projective cells -/

/-- The number of residue classes modulo `𝔪 ^ L` of units is `q ^ L - q ^ (L - 1)`. -/
private theorem card_units_mod_pow (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (L : ℕ) (hL : 1 ≤ L) :
    Nat.card {c : O ⧸ (IsLocalRing.maximalIdeal O)^L |
        ∃ y, Ideal.Quotient.mk _ y = c ∧ y ∉ IsLocalRing.maximalIdeal O}
      = Nat.card (IsLocalRing.ResidueField O) ^ L -
        Nat.card (IsLocalRing.ResidueField O) ^ (L-1) := by
  set m := IsLocalRing.maximalIdeal O
  have hle : m ^ L ≤ m := Ideal.pow_le_self (by omega)
  set J : Ideal (O ⧸ m ^ L) := m.map (Ideal.Quotient.mk (m ^ L))
  have hU : {c : O ⧸ m^L | ∃ y, Ideal.Quotient.mk _ y = c ∧ y ∉ m} =
      (J : Set (O ⧸ m^L))ᶜ := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, SetLike.mem_coe, J,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · rintro ⟨y, rfl, hy⟩ ⟨z, hz, hzy⟩
      exact hy (by simpa using m.sub_mem hz (hle (Ideal.Quotient.eq.mp hzy)))
    · intro h
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact ⟨y, rfl, fun hy => h ⟨y, hy, rfl⟩⟩
  have hQ := residue_quotient_card O L
  have hq0 : 0 < Nat.card (IsLocalRing.ResidueField O) := Nat.card_pos
  have hfin : Finite (O ⧸ m ^ L) := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  have hcard := Submodule.card_eq_card_quotient_mul_card J
  have hquot : Nat.card ((O ⧸ m ^ L) ⧸ J) = Nat.card (IsLocalRing.ResidueField O) :=
    Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv
  rw [hquot, hQ] at hcard
  have hJ : Nat.card J = Nat.card (IsLocalRing.ResidueField O) ^ (L - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
    rw [pow_succ] at hcard
    simpa using (Nat.eq_of_mul_eq_mul_right hq0 hcard).symm
  rw [hU, Nat.card_coe_set_eq]
  have h2 := Set.ncard_add_ncard_compl (J : Set (O ⧸ m^L))
  have h3 : (J : Set (O ⧸ m^L)).ncard = Nat.card (IsLocalRing.ResidueField O) ^ (L - 1) := by
    rw [← hJ]; rfl
  rw [h3, hQ] at h2
  omega

/-- The set of vectors with unit `μ`-coordinate that are congruent modulo `𝔪 ^ L` to a multiple
of `bt` (with `bt μ = 1`) is measurable, of mass `(q ^ L - q ^ (L - 1)) / (q ^ L) ^ (n + 1)`. -/
private theorem unit_multiple_cylinder_mass (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n L : ℕ) (hL : 1 ≤ L) (μ : Fin (n + 1))
    (bt : Fin (n + 1) → O) (hb : bt μ = 1) :
    MeasurableSet {a : Fin (n+1) → O | a μ ∉ IsLocalRing.maximalIdeal O ∧
      ∀ j, a j - a μ * bt j ∈ (IsLocalRing.maximalIdeal O) ^ L} ∧
    coefficientMeasure O (n+1) {a : Fin (n+1) → O | a μ ∉ IsLocalRing.maximalIdeal O ∧
      ∀ j, a j - a μ * bt j ∈ (IsLocalRing.maximalIdeal O) ^ L}
      = ((Nat.card (IsLocalRing.ResidueField O) ^ L -
          Nat.card (IsLocalRing.ResidueField O) ^ (L-1) : ℕ) : ℝ≥0∞) /
        ((Nat.card (IsLocalRing.ResidueField O) ^ L) ^ (n+1) : ℕ) := by
  set m := IsLocalRing.maximalIdeal O
  have hle : m ^ L ≤ m := Ideal.pow_le_self (by omega)
  have hQ := residue_quotient_card O L
  have : Finite (O ⧸ m ^ L) :=
    Nat.finite_of_card_ne_zero (by rw [hQ]; exact (pow_pos Nat.card_pos L).ne')
  let mk := Ideal.Quotient.mk (m ^ L)
  let π : (Fin (n+1) → O) →+ (Fin (n+1) → O ⧸ m ^ L) :=
    (mk : O →+ O ⧸ m ^ L).compLeft (Fin (n+1))
  have hπ : ∀ a j, π a j = mk (a j) := fun _ _ => rfl
  set U := {c : O ⧸ m^L | ∃ y, mk y = c ∧ y ∉ m} with hUdef
  set S := (fun c : O ⧸ m^L => fun j => c * mk (bt j)) '' U with hSdef
  have hE : {a : Fin (n+1) → O | a μ ∉ m ∧ ∀ j, a j - a μ * bt j ∈ m ^ L} = π ⁻¹' S := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hSdef, hUdef, Set.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨mk (a μ), ⟨a μ, rfl, h1⟩, funext fun j => ?_⟩
      rw [hπ, ← map_mul]
      exact (Ideal.Quotient.eq.mpr (h2 j)).symm
    · rintro ⟨c, ⟨y, rfl, hy⟩, hc⟩
      have hj : ∀ j, mk (a j) = mk y * mk (bt j) := fun j => by rw [← hπ, ← hc]
      have hμ' : mk (a μ) = mk y := by rw [hj μ, hb, map_one, mul_one]
      have hyμ : a μ - y ∈ m ^ L := Ideal.Quotient.eq.mp hμ'
      refine ⟨fun h => hy (by simpa using m.sub_mem h (hle hyμ)),
        fun j => Ideal.Quotient.eq.mp ?_⟩
      rw [map_mul, hj j, hμ']
  have hsurj : Function.Surjective π := fun v =>
    ⟨fun j => (Ideal.Quotient.mk_surjective (v j)).choose,
      funext fun j => (Ideal.Quotient.mk_surjective (v j)).choose_spec⟩
  have hball : ∀ x0 : Fin (n+1) → O,
      MeasurableSet {b' : Fin (n+1) → O | ∀ j, b' j - x0 j ∈ m ^ L} := by
    intro x0
    have : @MeasurableSet _ (adicCylinderSpace m (Fin (n+1) → O))
        {b' : Fin (n+1) → O | ∀ j, b' j - x0 j ∈ m ^ L} := by
      apply MeasurableSpace.measurableSet_generateFrom
      refine Or.inr ⟨L, x0, ?_⟩
      ext y
      simp only [Set.mem_ofPred_eq]
      rw [finite_coordinate_adic_congruence]
    rwa [← finite_coordinate_borel_cylinders O m htop (n+1)] at this
  have hfib : ∀ v, MeasurableSet {x | π x = v} := by
    intro v
    obtain ⟨x0, rfl⟩ := hsurj v
    convert hball x0 using 1
    ext x
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h j => Ideal.Quotient.eq.mp (by rw [← hπ, ← hπ, h]),
      fun h => funext fun j => Ideal.Quotient.eq.mpr (h j)⟩
  have := coefficient_measure_probability O htop (n+1)
  have : MeasureTheory.Measure.IsAddLeftInvariant (coefficientMeasure O (n+1)) := by
    unfold coefficientMeasure; infer_instance
  have hmeas : MeasurableSet (π ⁻¹' S) := by
    have : π ⁻¹' S = ⋃ s ∈ S, {x | π x = s} := by ext; simp
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable S) fun s _ => hfib s
  refine ⟨hE ▸ hmeas, ?_⟩
  rw [hE, finite_quotient_event_mass _ _ (coefficientMeasure O (n+1)) π hsurj hfib S]
  have hS : Nat.card S = Nat.card U :=
    Nat.card_image_of_injective (fun c c' h => by simpa [hb] using congrFun h μ) _
  rw [hS, card_units_mod_pow O L hL, Nat.card_fun, hQ, Nat.card_fin]

private theorem projective_mass_ratio (q n L : ℕ) (hq : 1 < q) (hL : 1 ≤ L) :
    (((q : ℝ≥0∞) - 1) * (q : ℝ≥0∞)⁻¹ ^ (n+1))⁻¹ *
        (((q ^ L - q ^ (L-1) : ℕ) : ℝ≥0∞) / ((q ^ L) ^ (n+1) : ℕ))
      = (q : ℝ≥0∞)⁻¹ ^ (n * (L-1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show q ^ (k+1) - q ^ k = q ^ k * (q - 1) by rw [pow_succ, Nat.mul_sub, mul_one]]
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqt : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  have hqr : (q : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ = 1 := ENNReal.mul_inv_cancel hq0 hqt
  have hq1 : ((q - 1 : ℕ) : ℝ≥0∞) = (q : ℝ≥0∞) - 1 := by
    rw [ENNReal.natCast_sub]; simp
  have hs0 : (q : ℝ≥0∞) - 1 ≠ 0 := by
    rw [← hq1]; exact_mod_cast (by omega : q - 1 ≠ 0)
  have hst : (q : ℝ≥0∞) - 1 ≠ ⊤ := ENNReal.sub_ne_top hqt
  push_cast
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hs0) (Or.inl hst), ← pow_mul]
  simp only [ENNReal.inv_pow, inv_inv]
  set r := (q : ℝ≥0∞)⁻¹
  set Q := (q : ℝ≥0∞)
  set s := Q - 1
  have hss : s⁻¹ * s = 1 := ENNReal.inv_mul_cancel hs0 hst
  rw [show (k+1) * (n+1) = (n + 1 + k) + n * k by ring, pow_add r]
  have hpow : Q ^ (n+1+k) * r ^ (n+1+k) = 1 := by rw [← mul_pow, hqr, one_pow]
  calc s⁻¹ * Q ^ (n + 1) * (Q ^ k * s * (r ^ (n + 1 + k) * r ^ (n * k)))
      = (s⁻¹ * s) * (Q ^ (n+1+k) * r ^ (n+1+k)) * r ^ (n * k) := by ring
    _ = r ^ (n * k) := by rw [hss, hpow, one_mul, one_mul]

private theorem projectiveNormalize_alg (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (G : Fin (n + 1) → IsLocalRing.ResidueField O) (μ : Fin (n + 1)) (hGμ : G μ = 1) :
    Set.MapsTo (projectiveNormalize O n G μ) (projectiveCell O n G) (reducedFormCell O n μ G) ∧
    Set.SurjOn (projectiveNormalize O n G μ) (projectiveCell O n G) (reducedFormCell O n μ G) ∧
    (∀ a ∈ projectiveCell O n G, ∀ a' ∈ projectiveCell O n G,
      projectiveNormalize O n G μ a = projectiveNormalize O n G μ a' ↔
        ∃ u : Oˣ, a' = (u : O) • a) := by
  set PC := projectiveCell O n G
  have hunit : ∀ a ∈ PC, ∃ v : Oˣ, a μ = v ∧
      residueVector O a = IsLocalRing.residue O (v : O) • G := by
    rintro a ⟨-, c, hc, hac⟩
    have hr : IsLocalRing.residue O (a μ) = c := by
      simpa [residueVector, hGμ] using congrFun hac μ
    have hu : IsUnit (a μ) := by
      rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, hr]; exact hc
    exact ⟨hu.unit, rfl, by rw [hac]; simp [hr]⟩
  have hnorm : ∀ (a : Fin (n+1) → O) (v : Oˣ), a μ = v →
      normalizeAt μ a = ((v⁻¹ : Oˣ) : O) • a := fun a v hv => by
    simp only [normalizeAt, hv, Ring.inverse_unit]
  have hins : ∀ w : Fin (n+1) → O, w μ = 1 → insertOne μ (dropCoord μ w) = w := fun w hw => by
    simp only [insertOne, dropCoord]
    rw [← hw]; exact Fin.insertNth_self_removeNth μ w
  have hnm : ∀ a ∈ PC, projectiveNormalize O n G μ a = dropCoord μ (normalizeAt μ a) :=
    fun a ha => if_pos ha
  have hnμ : ∀ a ∈ PC, normalizeAt μ a μ = 1 := by
    intro a ha
    obtain ⟨v, hv, -⟩ := hunit a ha
    rw [hnorm a v hv]; simp [hv]
  have hinj : ∀ a ∈ PC, ∀ a' ∈ PC,
      projectiveNormalize O n G μ a = projectiveNormalize O n G μ a' ↔
        normalizeAt μ a = normalizeAt μ a' := by
    intro a ha a' ha'
    rw [hnm a ha, hnm a' ha']
    exact ⟨fun h => by rw [← hins _ (hnμ a ha), ← hins _ (hnμ a' ha'), h], fun h => by rw [h]⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨v, hv, hres⟩ := hunit a ha
    change insertOne μ (projectiveNormalize O n G μ a) ∈ normalizedFormCell O n μ G
    rw [hnm a ha, hins _ (hnμ a ha)]
    refine ⟨hnμ a ha, ?_⟩
    rw [hnorm a v hv]
    funext i
    have := congrFun hres i
    simp only [residueVector, Pi.smul_apply, smul_eq_mul, map_mul] at this ⊢
    rw [this, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  · intro b hb
    obtain ⟨h1, h2⟩ : insertOne μ b ∈ normalizedFormCell O n μ G := hb
    have hPC : insertOne μ b ∈ PC :=
      ⟨⟨μ, by rw [h1]; exact isUnit_one⟩, 1, one_ne_zero, by rw [h2, one_smul]⟩
    refine ⟨insertOne μ b, hPC, ?_⟩
    rw [hnm _ hPC]
    simp only [normalizeAt]
    rw [h1, Ring.inverse_one, one_smul]
    simp only [dropCoord, insertOne, Fin.removeNth_insertNth]
  · intro a ha a' ha'
    rw [hinj a ha a' ha']
    obtain ⟨v, hv, -⟩ := hunit a ha
    obtain ⟨v', hv', -⟩ := hunit a' ha'
    rw [hnorm a v hv, hnorm a' v' hv']
    constructor
    · intro h
      refine ⟨v' * v⁻¹, funext fun j => ?_⟩
      have := congrFun h j
      simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
      calc a' j = (v' : O) * (((v'⁻¹ : Oˣ) : O) * a' j) := by
              rw [← mul_assoc, Units.mul_inv, one_mul]
        _ = _ := by rw [← this]; simp only [Units.val_mul]; ring
    · rintro ⟨u, rfl⟩
      obtain rfl : v' = u * v := by
        ext; rw [← hv', Units.val_mul, ← hv]; simp
      funext j
      simp only [Pi.smul_apply, smul_eq_mul, mul_inv_rev, Units.val_mul]
      rw [← mul_assoc, mul_assoc (v⁻¹ : Oˣ).val, Units.inv_mul, mul_one]

private theorem projectiveNormalize_preimage_ball (O : Type) [CommRing O] [IsLocalRing O]
    (n : ℕ) (G : Fin (n + 1) → IsLocalRing.ResidueField O) (μ : Fin (n + 1)) (L : ℕ) (hL : 1 ≤ L)
    (x : Fin n → O) (hx : x ∈ reducedFormCell O n μ G) :
    projectiveCell O n G ∩
        projectiveNormalize O n G μ ⁻¹' {y | ∀ j, y j - x j ∈ (IsLocalRing.maximalIdeal O) ^ L}
      = {a | a μ ∉ IsLocalRing.maximalIdeal O ∧
          ∀ j, a j - a μ * insertOne μ x j ∈ (IsLocalRing.maximalIdeal O) ^ L} := by
  set m := IsLocalRing.maximalIdeal O
  have hle : m ^ L ≤ m := Ideal.pow_le_self (by omega)
  obtain ⟨h1, h2⟩ : insertOne μ x ∈ normalizedFormCell O n μ G := hx
  have hxs : ∀ i, insertOne μ x (μ.succAbove i) = x i := fun i => by
    simp [insertOne, Fin.insertNth_apply_succAbove]
  ext a
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨-, c, hc, hac⟩, hB⟩
    have hG : G μ = 1 := by simpa [residueVector, h1] using (congrFun h2 μ).symm
    have hr : IsLocalRing.residue O (a μ) = c := by simpa [residueVector, hG] using congrFun hac μ
    have hu : IsUnit (a μ) := by
      rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, hr]; exact hc
    refine ⟨IsLocalRing.notMem_maximalIdeal.mpr hu, fun j => ?_⟩
    rw [projectiveNormalize, if_pos ⟨⟨μ, hu⟩, c, hc, hac⟩] at hB
    rcases Fin.eq_self_or_eq_succAbove μ j with rfl | ⟨i, rfl⟩
    · rw [h1, mul_one, sub_self]; exact Submodule.zero_mem _
    · have := hB i
      simp only [dropCoord, normalizeAt, Fin.removeNth, Pi.smul_apply, smul_eq_mul] at this
      rw [hxs]
      convert Ideal.mul_mem_left (m ^ L) (a μ) this using 1
      rw [mul_sub, ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]
  · rintro ⟨hμ, hj⟩
    have hu : IsUnit (a μ) := IsLocalRing.notMem_maximalIdeal.mp hμ
    have hres : residueVector O a = IsLocalRing.residue O (a μ) • G := by
      funext j
      have : IsLocalRing.residue O (a j) = IsLocalRing.residue O (a μ * insertOne μ x j) :=
        Ideal.Quotient.eq.mpr (hle (hj j))
      rw [← h2]
      simpa [residueVector, map_mul] using this
    have hPC : a ∈ projectiveCell O n G :=
      ⟨⟨μ, hu⟩, _, (hu.map (IsLocalRing.residue O)).ne_zero, hres⟩
    refine ⟨hPC, fun i => ?_⟩
    rw [projectiveNormalize, if_pos hPC]
    simp only [dropCoord, normalizeAt, Fin.removeNth, Pi.smul_apply, smul_eq_mul]
    have h3 := Ideal.mul_mem_left (m ^ L) (Ring.inverse (a μ)) (hj (μ.succAbove i))
    rw [hxs] at h3
    convert h3 using 1
    rw [mul_sub, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

/-- Normalizing a primitive vector at a coordinate `μ` with `G μ = 1` maps the projective cell of
`G` onto the reduced form cell of `G`, with fibres the unit multiples, and pushes the normalized
projective cell measure forward to the normalized reduced form cell measure. -/
theorem projective_cell_normalization_pushforward (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (G : Fin (n + 1) → IsLocalRing.ResidueField O) (μ : Fin (n + 1)) (hGμ : G μ = 1) :
    Set.MapsTo (projectiveNormalize O n G μ) (projectiveCell O n G) (reducedFormCell O n μ G) ∧
    Set.SurjOn (projectiveNormalize O n G μ) (projectiveCell O n G) (reducedFormCell O n μ G) ∧
    (∀ a ∈ projectiveCell O n G, ∀ a' ∈ projectiveCell O n G,
      projectiveNormalize O n G μ a = projectiveNormalize O n G μ a' ↔
        ∃ u : Oˣ, a' = (u : O) • a) ∧
    MeasureTheory.MeasurePreserving (projectiveNormalize O n G μ)
      (cellMeasure O (n+1) (projectiveCell O n G)) (cellMeasure O n (reducedFormCell O n μ G)) := by
  obtain ⟨hmaps, hsurjOn, hfibre⟩ := projectiveNormalize_alg O n G μ hGμ
  refine ⟨hmaps, hsurjOn, hfibre, ?_⟩
  set m := IsLocalRing.maximalIdeal O
  set nm := projectiveNormalize O n G μ
  set PC := projectiveCell O n G
  set D := reducedFormCell O n μ G
  set q := Nat.card (IsLocalRing.ResidueField O)
  have hq1 : 1 < q := Finite.one_lt_card
  have hG0 : G ≠ 0 := fun h => by simp [h] at hGμ
  obtain ⟨hPCm, hPCmass⟩ := projective_cell_mass O htop n G hG0
  obtain ⟨-, hDball, -, hDmeas, -, hDprob, hDmass⟩ :=
    normalized_form_cell_cylinder_mass O htop n μ G hGμ
  have hgen := finite_coordinate_borel_cylinders O m htop n
  have hB : ∀ (L : ℕ) (x : Fin n → O),
      {y : Fin n → O | adicCongr m L y x} = {y | ∀ j, y j - x j ∈ m ^ L} := fun L x => by
    ext y; exact finite_coordinate_adic_congruence O n m L y x
  -- the preimage of a ball around a point outside `D` is empty
  have hkey : ∀ L (x : Fin n → O), 1 ≤ L → x ∉ D →
      PC ∩ nm ⁻¹' {y | ∀ j, y j - x j ∈ m ^ L} = ∅ := fun L x hL hx => by
    refine Set.eq_empty_of_forall_notMem fun a ⟨ha, hyx⟩ => hx ?_
    change x ∈ reducedFormCell O n μ G
    rw [hDball _ (hmaps ha)]
    exact fun j => by
      simpa only [neg_sub] using m.neg_mem (Ideal.pow_le_self (by omega : L ≠ 0) (hyx j))
  have hPCB : ∀ L (x : Fin n → O), MeasurableSet (PC ∩ nm ⁻¹' {y | ∀ j, y j - x j ∈ m ^ L}) := by
    intro L x
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · have : {y : Fin n → O | ∀ j, y j - x j ∈ m ^ 0} = Set.univ := by ext y; simp
      rw [this, Set.preimage_univ, Set.inter_univ]; exact hPCm
    by_cases hx : x ∈ D
    · rw [projectiveNormalize_preimage_ball O n G μ L hL x hx]
      exact (unit_multiple_cylinder_mass O htop n L hL μ (insertOne μ x) (by simp [insertOne])).1
    · rw [hkey L x hL hx]; exact MeasurableSet.empty
  have hoff : ∀ a, a ∉ PC → nm a = 0 := fun a ha => if_neg ha
  have hnmm : Measurable nm := by
    change @Measurable _ _ _ (inferInstance : MeasurableSpace (Fin n → O)) nm
    rw [hgen]
    refine measurable_generateFrom ?_
    rintro s (rfl | ⟨L, x, rfl⟩)
    · simp
    rw [hB]
    have : nm ⁻¹' {y | ∀ j, y j - x j ∈ m ^ L} = (PC ∩ nm ⁻¹' {y | ∀ j, y j - x j ∈ m ^ L}) ∪
        (PCᶜ ∩ {_a | (0 : Fin n → O) ∈ {y : Fin n → O | ∀ j, y j - x j ∈ m ^ L}}) := by
      ext a
      by_cases ha : a ∈ PC
      · simp [ha]
      · simp [ha, hoff a ha]
    rw [this]
    exact (hPCB L x).union (hPCm.compl.inter (MeasurableSet.const _))
  have hμ0 : coefficientMeasure O (n+1) PC ≠ 0 := by
    rw [hPCmass]
    refine mul_ne_zero ?_ (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)))
    rw [← Nat.cast_one, ← ENNReal.natCast_sub]; exact_mod_cast (by omega : q - 1 ≠ 0)
  have hμt : coefficientMeasure O (n+1) PC ≠ ⊤ := by
    have := coefficient_measure_probability O htop (n+1)
    exact MeasureTheory.measure_ne_top _ _
  have : MeasureTheory.IsProbabilityMeasure (cellMeasure O (n+1) PC) := by
    constructor
    rw [cellMeasure, MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul,
      ENNReal.inv_mul_cancel hμ0 hμt]
  refine measurePreserving_cellMeasure_of_balls O htop _ n D hDmeas hDball nm hnmm PC
    (by rw [cellMeasure, MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.restrict_apply' hPCm, Set.compl_inter_self,
      MeasureTheory.measure_empty, smul_zero]) hmaps fun L hL x hx => ?_
  rw [cellMeasure, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply' hPCm,
    smul_eq_mul, Set.inter_comm, hDmass L x hL hx,
    projectiveNormalize_preimage_ball O n G μ L hL x hx,
    (unit_multiple_cylinder_mass O htop n L hL μ (insertOne μ x) (by simp [insertOne])).2, hPCmass]
  exact projective_mass_ratio q n L hq1 hL

end SurfaceBlowup
