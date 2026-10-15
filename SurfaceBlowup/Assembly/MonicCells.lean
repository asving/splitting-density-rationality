/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Assembly.TypeEvents

/-!
# Monic, projective and divisor cells

Residue-cell decompositions of spaces of polynomials over a complete DVR `O` with finite residue
field, and the laws of the factorization-type events on each cell, assuming the root cell law
`RootCellLaw`. Monic polynomials of degree `n` are partitioned into residue cells indexed by affine
divisors, primitive vectors into projective cells indexed by all divisors; each cell factors into
point cells and a cell at infinity, whose laws are descended from the root cell law.

## Main results

* `monic_cells_partition`, `projective_cells_partition`: the cell partitions.
* `product_law_of_factor_laws`: the law of a product of coprime cells.
* `point_cell_type_event`, `infinity_block_event_law`: laws of point cells and the cell at infinity.
* `divisor_form_cell_law`, `monic_cell_law`, `projective_cell_affine_type_event`: cell laws.
* `affine_type_event_primitive_density`: the primitive density of an affine type event.

Provenance: `Thm_SurfaceBlowupV2_{monic_cells_partition, point_chart_bijection,
product_cell_type_event_sets, product_cell_type_event_mass, product_law_of_factor_laws,
projective_divisor_count, projective_divisor_of_residue_vector, projective_cells_partition,
zero_cell_scaled, zero_cell_type_event_mass, point_cell_type_event, irreducible_cell_type_event,
infinity_block_event_law, divisor_form_cell_law, monic_cell_law,
projective_cell_affine_type_event, affine_type_event_primitive_density}`.
-/

namespace SurfaceBlowup

open scoped BigOperators ENNReal

/-! ### Normalized cell measures -/

/-- On a measurable cell `S` of finite positive mass, the coefficient measure of `E ∩ S` is the
mass of `S` times the normalized cell measure of `E`. -/
private theorem coefficientMeasure_inter_eq_mul (O : Type) [CommRing O] [IsDomain O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] {n : ℕ} {S : Set (Fin n → O)}
    (hS : MeasurableSet S) (h0 : coefficientMeasure O n S ≠ 0)
    (htop : coefficientMeasure O n S ≠ ⊤) (E : Set (Fin n → O)) :
    coefficientMeasure O n (E ∩ S) = coefficientMeasure O n S * cellMeasure O n S E := by
  rw [cellMeasure_apply_of_measurableSet O n S hS E, ← mul_assoc, ENNReal.mul_inv_cancel h0 htop,
    one_mul]

/-- If the cells `cell D` (`D ∈ S`) are measurable subsets of `P` and every point of `P` lies in
exactly one of them, then the measure of `E ∩ P` is the sum of the measures of `E ∩ cell D`. -/
private theorem measure_inter_eq_sum_cells {α ι : Type} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) {p : ι → Prop} (S : Finset ι) (hS : ∀ D, D ∈ S ↔ p D)
    (cell : ι → Set α) (P : Set α) (huniq : ∀ a ∈ P, ∃! D, p D ∧ a ∈ cell D)
    (hsub : ∀ D, p D → cell D ⊆ P) (hmeas : ∀ D, p D → MeasurableSet (cell D)) {E : Set α}
    (hE : MeasurableSet E) : μ (E ∩ P) = ∑ D ∈ S, μ (E ∩ cell D) := by
  have heq : E ∩ P = ⋃ D ∈ S, E ∩ cell D := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop, hS]
    refine ⟨fun ⟨haE, ha⟩ ↦ ?_, fun ⟨D, hD, haE, hc⟩ ↦ ⟨haE, hsub D hD hc⟩⟩
    obtain ⟨D, hD, -⟩ := huniq a ha
    exact ⟨D, hD.1, haE, hD.2⟩
  rw [heq]
  refine MeasureTheory.measure_biUnion_finset (fun D hD D' hD' hne ↦ Set.disjoint_left.2 ?_)
    fun D hD ↦ hE.inter (hmeas D ((hS D).1 hD))
  rintro a ⟨-, ha⟩ ⟨-, ha'⟩
  exact hne ((huniq a (hsub D ((hS D).1 hD) ha)).unique ⟨(hS D).1 hD, ha⟩ ⟨(hS D').1 hD', ha'⟩)

/-! ### Partitions into residue cells -/

/-- **Monic cell partition.** The monic polynomials of degree `n` over `O` are partitioned into the
residue cells of the affine divisors of degree `n` over the residue field: there are finitely many
such divisors, every coefficient vector lies in exactly one cell, each cell is measurable of mass
`q⁻ⁿ`, and the coefficient measure decomposes as a sum over cells. -/
theorem monic_cells_partition (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    (∃ S : Finset (ExceptionalDivisor (IsLocalRing.ResidueField O)), ∀ D, D ∈ S ↔ AffineDivisor
      (IsLocalRing.ResidueField O) n D) ∧ (∀ a : Fin n → O, ∃! D : ExceptionalDivisor
      (IsLocalRing.ResidueField O), AffineDivisor (IsLocalRing.ResidueField O) n D ∧ a ∈
      residueCell O n (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) ∧
      (∀ D : ExceptionalDivisor (IsLocalRing.ResidueField O), AffineDivisor
      (IsLocalRing.ResidueField O) n D → MeasurableSet (residueCell O n
      (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) ∧ coefficientMeasure O n
      (residueCell O n (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ n ∧ ∀ E : Set (Fin n → O),
      coefficientMeasure O n (E ∩ residueCell O n
      (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ n * cellMeasure O n
      (residueCell O n (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) E) ∧ ∀ S : Finset
      (ExceptionalDivisor (IsLocalRing.ResidueField O)),
      (∀ D, D ∈ S ↔ AffineDivisor (IsLocalRing.ResidueField O) n D) → ∀ E : Set (Fin n → O),
      MeasurableSet E → coefficientMeasure O n E = ∑ D ∈ S, coefficientMeasure O n
      (E ∩ residueCell O n (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) := by
  set k := IsLocalRing.ResidueField O
  have aux (D) (hD : AffineDivisor k n D) :
      (divisorAffinePolynomial k D).Monic ∧ (divisorAffinePolynomial k D).natDegree = n := by
    obtain ⟨hm, hn, -⟩ := divisor_vector_properties k n D hD.2
    exact ⟨hm, by rw [hn, hD.1, Nat.sub_zero]⟩
  -- unique cell
  have huniq : ∀ a : Fin n → O, ∃! D : ExceptionalDivisor k, AffineDivisor k n D ∧
      a ∈ residueCell O n (divisorAffinePolynomial k D) := by
    intro a
    obtain ⟨hm, hdeg, -, -⟩ := monic_poly_reconstruct O n a
    have hG : ((monicPolyO a).map (IsLocalRing.residue O)).Monic := hm.map _
    have hGn : ((monicPolyO a).map (IsLocalRing.residue O)).natDegree = n := by
      rw [hm.natDegree_map, hdeg]
    obtain ⟨D, ⟨hDa, hDp⟩, hDu⟩ := monic_polynomial_divisor k n _ hG hGn
    refine ⟨D, ⟨hDa, ?_⟩, ?_⟩
    · change _ = _; exact hDp.symm
    · rintro D' ⟨hD'a, hD'c⟩
      exact hDu D' ⟨hD'a, hD'c.symm⟩
  have hinj : ∀ D D' : ExceptionalDivisor k, AffineDivisor k n D → AffineDivisor k n D' →
      divisorAffinePolynomial k D = divisorAffinePolynomial k D' → D = D' := by
    intro D D' hD hD' h
    obtain ⟨hm, hn⟩ := aux D hD
    obtain ⟨E, -, hE⟩ := monic_polynomial_divisor k n _ hm hn
    exact (hE D ⟨hD, rfl⟩).trans (hE D' ⟨hD', h.symm⟩).symm
  have hcell : ∀ D : ExceptionalDivisor k, AffineDivisor k n D →
      MeasurableSet (residueCell O n (divisorAffinePolynomial k D)) ∧
      coefficientMeasure O n (residueCell O n (divisorAffinePolynomial k D)) =
        (Nat.card k : ℝ≥0∞)⁻¹ ^ n := by
    intro D hD
    obtain ⟨hm, hn⟩ := aux D hD
    obtain ⟨h1, h2, -⟩ := residue_cell_mass O htop n _ hm hn
    exact ⟨h1, h2⟩
  refine ⟨?_, huniq, ?_, ?_⟩
  · have hfin : Set.Finite {D : ExceptionalDivisor k | AffineDivisor k n D} := by
      have hT : Finite {F : Polynomial k // F.Monic ∧ F.natDegree = n} := by
        apply Nat.finite_of_card_ne_zero
        rw [monic_residue_polynomial_count k n]
        exact pow_ne_zero _ Nat.card_pos.ne'
      have : Finite {D : ExceptionalDivisor k // AffineDivisor k n D} :=
        Finite.of_injective
          (fun D => (⟨divisorAffinePolynomial k D.1, aux D.1 D.2⟩ :
            {F : Polynomial k // F.Monic ∧ F.natDegree = n}))
          (fun D D' h => Subtype.ext (hinj D D' D.2 D'.2 (congrArg Subtype.val h)))
      exact Set.finite_coe_iff.mp this
    exact ⟨hfin.toFinset, fun D => by rw [Set.Finite.mem_toFinset]; rfl⟩
  · intro D hD
    obtain ⟨h1, h2⟩ := hcell D hD
    refine ⟨h1, h2, fun E ↦ h2 ▸ coefficientMeasure_inter_eq_mul O h1 ?_ ?_ E⟩
    · exact h2 ▸ pow_ne_zero _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
    · exact h2 ▸ ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast Nat.card_pos.ne'))
  · intro S hS E hE
    simpa using measure_inter_eq_sum_cells (coefficientMeasure O n) S hS _ Set.univ
      (fun a _ ↦ huniq a) (fun _ _ ↦ Set.subset_univ _) (fun D hD ↦ (hcell D hD).1) hE

/-- The point chart is a bijection from the residue cell of `(Φ mod π)^r` onto the zero cell over
`O[X]/(Φ)`, and it identifies the congruence filtrations on both sides. -/
private theorem point_chart_bijection (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ) :
    Set.BijOn (pointChart O Φ r) (residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r))
      (zeroCell O Φ r) ∧ ∀ (L : ℕ), ∀ a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r),
      ∀ a' ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r),
      (∀ j, a j - a' j ∈ (IsLocalRing.maximalIdeal O) ^ L) ↔ ∀ j,
      pointChart O Φ r a j - pointChart O Φ r a' j ∈ (baseIdeal O Φ) ^ L := by
  have h1 := block_descent_bijection O Φ hΦ r
  have h2 := block_translation O Φ hΦ r
  refine ⟨h2.1.comp h1.1, fun L a ha a' ha' => ?_⟩
  exact (block_descent_congruence_iff O Φ hΦ r L a a' ha ha').trans
    (h2.2 L _ _)

/-! ### Product cells -/

/-- A point of a product of coprime residue cells has type `σ` after multiplying out iff its
factors have types `τ j` with `σ = ∑ j, τ j`. -/
private theorem factorProduct_mem_typeEvent_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (L : ℕ)
    (g : Fin L → Polynomial (IsLocalRing.ResidueField O))
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (σ : FactorType) (a : ∀ j, Fin (g j).natDegree → O)
    (ha : a ∈ Set.pi Set.univ fun j ↦ residueCell O (g j).natDegree (g j)) :
    factorProduct (fun j ↦ (g j).natDegree) a ∈ typeEvent O (∑ j, (g j).natDegree) σ ↔
      ∃ τ : Fin L → FactorType, (∀ j, a j ∈ typeEvent O (g j).natDegree (τ j)) ∧
        σ = ∑ j, τ j := by
  set d : Fin L → ℕ := fun j ↦ (g j).natDegree
  have hmon : ∀ j, (monicPolyO (a j)).Monic := fun j ↦ (monic_poly_reconstruct O (d j) (a j)).1
  have hprod : monicPolynomial O (factorProduct d a) = ∏ j, monicPolynomial O (a j) := by
    have hdeg : (∏ j, monicPolyO (a j)).natDegree = ∑ j, d j := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ ↦ hmon j]
      exact Finset.sum_congr rfl fun j _ ↦ (monic_poly_reconstruct O (d j) (a j)).2.1
    rw [← monicPolyO_map_fraction,
      show monicPolyO (factorProduct d a) = ∏ j, monicPolyO (a j) from
      (monic_poly_reconstruct O _ (factorProduct d a)).2.2.2 _
        (Polynomial.monic_prod_of_monic _ _ fun j _ ↦ hmon j) hdeg, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun j _ ↦ monicPolyO_map_fraction O (a j)
  refine (congrArg (HasPolynomialTypeF O · σ) hprod).to_iff.trans
    (coprime_family_type_iff O (Fin L) _ (fun j ↦ (monic_polynomial_degree O (d j) (a j)).1)
      (fun i j hij ↦ ?_) σ)
  rw [← monicPolyO_map_fraction, ← monicPolyO_map_fraction]
  refine coprime_of_coprime_residue_dvr O (BaseField O) _ _ (hmon i) (hmon j) ?_
  rw [show (monicPolyO (a i)).map (IsLocalRing.residue O) = g i from ha i (Set.mem_univ _),
    show (monicPolyO (a j)).map (IsLocalRing.residue O) = g j from ha j (Set.mem_univ _)]
  exact hc i j hij

/-- The trace on the product of coprime residue cells of the preimage of the type event `σ` is
the finite union, over factor types `τ ∈ W` adding up to `σ`, of products of factor events. -/
private theorem factorProduct_preimage_typeEvent_eq (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (L : ℕ)
    (g : Fin L → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ j, (g j).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (W : Fin L → Finset FactorType)
    (hW : ∀ j τ, (residueCell O (g j).natDegree (g j) ∩ typeEvent O (g j).natDegree
      τ).Nonempty → τ ∈ W j) (σ : FactorType) :
    factorProduct (fun j ↦ (g j).natDegree) ⁻¹' (residueCell O (∑ j, (g j).natDegree) (∏ j, g j) ∩
      typeEvent O (∑ j, (g j).natDegree) σ) ∩
        Set.pi Set.univ (fun j ↦ residueCell O (g j).natDegree (g j)) =
      ⋃ τ ∈ (Fintype.piFinset W).filter (fun τ : Fin L → FactorType ↦ σ = ∑ j, τ j),
        Set.pi Set.univ fun j ↦ residueCell O (g j).natDegree (g j) ∩
          typeEvent O (g j).natDegree (τ j) :=
  preimage_inter_pi_eq_biUnion _ _ _ _ (factor_product_bijection O (Fin L) g hg hc).mapsTo
    (fun j ↦ typeEvent O (g j).natDegree) W hW σ (factorProduct_mem_typeEvent_iff O L g hc σ · ·) _
    fun _ ↦ by rw [Finset.mem_filter, Fintype.mem_piFinset]

/-- A type event in a product of coprime residue cells is measurable. -/
private theorem measurableSet_product_cell_typeEvent (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (L : ℕ)
    (g : Fin L → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ j, (g j).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (W : Fin L → Finset FactorType)
    (hW : ∀ j τ, (residueCell O (g j).natDegree (g j) ∩ typeEvent O (g j).natDegree
      τ).Nonempty → τ ∈ W j)
    (hmeas : ∀ j τ, MeasurableSet (residueCell O (g j).natDegree (g j) ∩ typeEvent O
      (g j).natDegree τ)) (σ : FactorType) :
    MeasurableSet (residueCell O (∑ j, (g j).natDegree) (∏ j, g j) ∩
      typeEvent O (∑ j, (g j).natDegree) σ) := by
  set d : Fin L → ℕ := fun j ↦ (g j).natDegree
  have hbij := factor_product_bijection O (Fin L) g hg hc
  choose c hcmem using fun j ↦ (residue_cell_cylinder O (d j) (g j)).2.1 (hg j) rfl
  have hclosed : IsClosed (Set.pi Set.univ fun j ↦ residueCell O (d j) (g j)) := by
    convert (coordinate_cylinder_clopen O (IsLocalRing.maximalIdeal O) htop 1).2.2 (Fin L) d c
      using 3 with j
    rw [pow_one]; exact (residue_cell_cylinder O (d j) (g j)).1 (c j) (hcmem j)
  exact measurableSet_inter_of_bijOn hclosed
    (factor_product_continuous O (Fin L) d).1.continuousOn hbij
    (factorProduct_preimage_typeEvent_eq O L g hg hc W hW σ ▸
      Finset.measurableSet_biUnion _ fun (τ : Fin L → FactorType) _ ↦
        .univ_pi fun j ↦ hmeas j (τ j))

/-- **Product law.** If the coprime factor cells have laws `Dl j`, then the product cell has law
`lawProd (List.ofFn Dl)`. -/
theorem product_law_of_factor_laws (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (L : ℕ)
    (g : Fin L → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ j, (g j).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (Dl : Fin L → Law)
    (hnn : ∀ (j : Fin L) (τ : FactorType), 0 ≤ (lawCoeff (Dl j) τ).eval
      (Nat.card (IsLocalRing.ResidueField O)))
    (hlaw : ∀ (j : Fin L) (τ : FactorType), MeasurableSet
      (residueCell O (g j).natDegree (g j) ∩ typeEvent O (g j).natDegree τ) ∧ cellMeasure O
      (g j).natDegree (residueCell O (g j).natDegree (g j)) (typeEvent O (g j).natDegree τ) =
      densityValue (lawCoeff (Dl j) τ) (Nat.card (IsLocalRing.ResidueField O))) (σ : FactorType) :
    MeasurableSet (residueCell O (∑ j, (g j).natDegree) (∏ j, g j) ∩ typeEvent O
      (∑ j, (g j).natDegree) σ) ∧ cellMeasure O (∑ j, (g j).natDegree)
      (residueCell O (∑ j, (g j).natDegree) (∏ j, g j)) (typeEvent O (∑ j, (g j).natDegree) σ) =
      densityValue (lawCoeff (lawProd (List.ofFn Dl)) σ)
      (Nat.card (IsLocalRing.ResidueField O)) := by
  let W : Fin L → Finset FactorType := fun j =>
    (finite_types_of_degree (g j).natDegree).toFinset ∪ ((Dl j).map Prod.fst).toFinset
  have hW : ∀ j τ, (residueCell O (g j).natDegree (g j) ∩ typeEvent O (g j).natDegree τ).Nonempty →
      τ ∈ W j := by
    intro j τ ⟨a, _, ha⟩
    have h1 := polynomial_type_degree O _ τ ha
    have h2 := (monic_polynomial_degree O _ a).2
    simp only [W, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact Or.inl ⟨h1.1, h1.2.trans h2⟩
  have hmeas := fun j τ ↦ (hlaw j τ).1
  have hcell := fun j ↦ residue_cell_mass O htop _ (g j) (hg j) rfl
  have : ∀ j, MeasureTheory.IsProbabilityMeasure
      (cellMeasure O _ (residueCell O (g j).natDegree (g j))) := fun j ↦ (hcell j).2.2
  have hE := measurableSet_product_cell_typeEvent O htop L g hg hc W hW hmeas σ
  refine ⟨hE, ?_⟩
  rw [← cellMeasure_cell_inter (residue_cell_mass O htop _ (∏ j, g j)
      (Polynomial.monic_prod_of_monic _ _ fun j _ ↦ hg j)
      (Polynomial.natDegree_prod_of_monic _ _ fun j _ ↦ hg j)).1,
    measure_eq_sum_prod_of_preimage _ (factor_cells_measure_preserving O htop (Fin L) g hg hc) _
      (factor_cell_product_measure O htop (Fin L) g hg).2.1
      (fun j ↦ cellMeasure_cell_inter (hcell j).1) _ hmeas
      (fun _ _ _ _ h1 h2 ↦ polynomial_type_unique O _ _ _ h1 h2) hE _
      (factorProduct_preimage_typeEvent_eq O L g hg hc W hW σ),
    Finset.sum_congr rfl fun τ _ ↦ Finset.prod_congr rfl fun j _ ↦ (hlaw j (τ j)).2]
  exact sum_prod_densityValue_eq_lawProd Dl _ hnn W (fun _ ↦ Finset.subset_union_right) σ

/-! ### Projective cells -/

/-- The number of divisors of degree `n` with array `m` is `divisorCount 1 m` evaluated at the
residue field size. -/
private theorem projective_divisor_count (k : Type) [Field k] [Finite k] (n : ℕ) (m : Pattern n)
    (hm : m ∈ residuePatterns n) :
    Finite {D : ExceptionalDivisor k // exceptionalDegree k D = n ∧ HasArray k n D m} ∧
      ((Nat.card {D : ExceptionalDivisor k // exceptionalDegree k D = n ∧ HasArray k n D m} : ℕ) :
      ℚ) = (divisorCount 1 m).eval (Nat.card k) := by
  have hpt : ∀ δ : ℕ, 0 < δ → ((Nat.card {Q : ClosedDirection k // directionDegree k Q = δ} : ℕ) :
      ℚ) = (availablePoints 1 δ).eval (Nat.card k) := by
    intro δ hδ
    have h915 := nonboundary_direction_count k (State.single 1 1) δ hδ
    simp only at h915
    by_cases h1 : δ = 1
    · subst h1
      have hq : (Nat.card k : ℚ) ≠ 0 := by
        have : 0 < Nat.card k := Nat.card_pos
        exact_mod_cast this.ne'
      have hB :
          ((Nat.card {Q : ClosedDirection k // Q ∉ boundaryDirections k (State.single 1 1) ∧
          directionDegree k Q = 1} : ℕ) : ℚ) = Nat.card k := by
        rw [h915]; simp [availablePoints, Expr.eval]
      have hne : Nat.card {Q : ClosedDirection k // Q ∉ boundaryDirections k (State.single 1 1) ∧
          directionDegree k Q = 1} ≠ 0 := by
        intro h; rw [h] at hB; exact hq (by simpa using hB.symm)
      have := Nat.finite_of_card_ne_zero hne
      have e : {Q : ClosedDirection k // directionDegree k Q = 1} ≃ Option
          {Q : ClosedDirection k // Q ∉ boundaryDirections k (State.single 1 1) ∧ directionDegree k
          Q = 1} :=
        { toFun := fun Q => match Q with
            | ⟨none, _⟩ => none
            | ⟨some φ, h⟩ => some ⟨some φ, by simp [boundaryDirections, infinityDirection], h⟩
          invFun := fun o => match o with
            | none => ⟨none, rfl⟩
            | some Q => ⟨Q.1, Q.2.2⟩
          left_inv := by
            rintro ⟨Q, h⟩
            cases Q <;> rfl
          right_inv := by
            rintro (_ | ⟨Q, h⟩)
            · rfl
            · cases Q <;> simp [boundaryDirections, infinityDirection] at h ⊢ }
      rw [Nat.card_congr e, Nat.card_congr (Equiv.optionEquivSumPUnit.{0} _), Nat.card_sum,
          Nat.card_eq_fintype_card (α := PUnit), Fintype.card_punit, Nat.cast_add, hB]
      simp [availablePoints, Expr.eval]
    · have : ∀ Q : ClosedDirection k, directionDegree k Q = δ → Q ∉ boundaryDirections k
        (State.single 1 1) := by
        intro Q hQ hb
        obtain rfl : Q = infinityDirection k := hb
        exact h1 hQ.symm
      have e : Nat.card {Q : ClosedDirection k // directionDegree k Q = δ} = Nat.card
          {Q : ClosedDirection k // Q ∉ boundaryDirections k (State.single 1 1) ∧ directionDegree k
          Q = δ} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun Q => ⟨fun h => ⟨this Q h, h⟩, fun h => h.2⟩)
      rw [e, h915]
      simp [availablePoints, h1]
  have hc : ∀ δ : ℕ, 0 < δ → ((Nat.card {Q : ClosedDirection k // Q ∈
      (Set.univ : Set (ClosedDirection k)) ∧ directionDegree k Q = δ} : ℕ) : ℚ) =
      (availablePoints 1 δ).eval (Nat.card k) := by
    intro δ hδ
    simpa only [Set.mem_univ, true_and] using hpt δ hδ
  have h := divisor_count_eval_of_point_count k Set.univ 1 hc n m hm
  have e : ∀ D : ExceptionalDivisor k, ((∀ Q, D Q ≠ 0 → Q ∈ (Set.univ : Set (ClosedDirection k))) ∧
      exceptionalDegree k D = n ∧ HasArray k n D m) ↔
      (exceptionalDegree k D = n ∧ HasArray k n D m) := by
    intro D; simp
  have eq := Equiv.subtypeEquivRight e
  have := h.1
  exact ⟨Finite.of_equiv _ eq, by rw [← Nat.card_congr eq, h.2]⟩

section

open Polynomial

private lemma formPoly_coeff {A : Type} [CommRing A] {n : ℕ} (v : Fin (n + 1) → A) (j : ℕ) :
    (formPoly v).coeff j = if h : j < n+1 then v ⟨j, h⟩ else 0 := by
  unfold formPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      have : j ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    have : j ≠ (b : ℕ) := by omega
    simp [this]

private lemma formPoly_smul (k : Type) [Field k] {n : ℕ} (c : k) (w : Fin (n + 1) → k) :
    formPoly (c • w) = C c * formPoly w := by
  unfold formPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply, smul_eq_mul, C_mul, mul_assoc]

private lemma exceptionalDegree_add (k : Type) [Field k] (A B : ExceptionalDivisor k) :
    exceptionalDegree k (A + B) = exceptionalDegree k A + exceptionalDegree k B := by
  unfold exceptionalDegree
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

private lemma divisorAffinePolynomial_add (k : Type) [Field k] (A B : ExceptionalDivisor k) :
    divisorAffinePolynomial k (A + B) = divisorAffinePolynomial k A *
      divisorAffinePolynomial k B := by
  unfold divisorAffinePolynomial
  refine Finsupp.prod_add_index' (fun P => ?_) (fun P r s => ?_)
  · cases P <;> simp
  · cases P <;> simp [pow_add]

private lemma exceptionalDegree_single_none (k : Type) [Field k] (m : ℕ) :
    exceptionalDegree k (Finsupp.single (none : ClosedDirection k) m) = m := by
  unfold exceptionalDegree
  rw [Finsupp.sum_single_index] <;> simp [directionDegree]

private lemma divisorAffinePolynomial_single_none (k : Type) [Field k] (m : ℕ) :
    divisorAffinePolynomial k (Finsupp.single (none : ClosedDirection k) m) = 1 := by
  unfold divisorAffinePolynomial
  rw [Finsupp.prod_single_index]; simp

private lemma eq_erase_none_add_single (k : Type) [Field k] (D : ExceptionalDivisor k) :
    D = D.erase none + Finsupp.single none (D none) := by
  ext P
  cases P <;> simp

end

open Polynomial in
/-- Every nonzero residue vector is, up to scaling, the divisor vector of a unique divisor of
degree `n`. -/
private theorem projective_divisor_of_residue_vector (k : Type) [Field k] (n : ℕ)
    (v : Fin (n + 1) → k)
    (hv : v ≠ 0) :
    ∃! D : ExceptionalDivisor k, exceptionalDegree k D = n ∧ v ∈ scalarClass
      (divisorVector k n D) := by
  set H := formPoly v with hHdef
  have hvH : ∀ i : Fin (n+1), v i = H.coeff i := fun i => by
    rw [hHdef, formPoly_coeff, dif_pos i.isLt]
  have hH0 : H ≠ 0 := by
    intro h0; apply hv; funext i; rw [hvH i, h0]; simp
  have hdle : H.natDegree ≤ n := formPoly_natDegree_le v
  set c := H.leadingCoeff with hcdef
  have hc : c ≠ 0 := leadingCoeff_ne_zero.mpr hH0
  set H₀ := C c⁻¹ * H with hH₀def
  have hmon : H₀.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hc)
  have hH₀deg : H₀.natDegree = H.natDegree := natDegree_C_mul (inv_ne_zero hc)
  obtain ⟨D₀, ⟨hD₀aff, hD₀P⟩, hD₀u⟩ := monic_polynomial_divisor k _ H₀ hmon hH₀deg
  refine ⟨D₀ + Finsupp.single none (n - H.natDegree), ⟨?_, ?_⟩, ?_⟩
  · rw [exceptionalDegree_add, hD₀aff.2, exceptionalDegree_single_none]; omega
  · refine ⟨c, hc, funext fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, divisorVector, divisorAffinePolynomial_add,
        divisorAffinePolynomial_single_none, mul_one, hD₀P,
      hH₀def, coeff_C_mul]
    rw [hvH i, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  · rintro D' ⟨hdeg, c', hc', hv'⟩
    obtain ⟨hAmon, hAdeg, hinf, hform, -⟩ := divisor_vector_properties k n D' hdeg
    have hHA : H = C c' * divisorAffinePolynomial k D' := by
      rw [hHdef, hv', formPoly_smul, hform]
    have hcc : c = c' := by
      rw [hcdef, hHA, leadingCoeff_mul, leadingCoeff_C, hAmon.leadingCoeff, mul_one]
    have hH₀A : H₀ = divisorAffinePolynomial k D' := by
      rw [hH₀def, hHA, ← mul_assoc, ← C_mul, hcc, inv_mul_cancel₀ hc', C_1, one_mul]
    have hnone : D' none = n - H.natDegree := by
      have h1 := hAdeg
      rw [← hH₀A, hH₀deg] at h1
      change H.natDegree = n - D' none at h1
      have h3 : D' none ≤ n := hinf
      omega
    have hdec := eq_erase_none_add_single k D'
    have hE : AffineDivisor k H.natDegree (D'.erase none) := by
      refine ⟨Finsupp.erase_same, ?_⟩
      have h2 := hdeg
      rw [hdec, exceptionalDegree_add, exceptionalDegree_single_none] at h2
      omega
    have hEP : divisorAffinePolynomial k (D'.erase none) = H₀ := by
      rw [hH₀A]
      conv_rhs => rw [hdec]
      rw [divisorAffinePolynomial_add, divisorAffinePolynomial_single_none, mul_one]
    have := hD₀u _ ⟨hE, hEP⟩
    rw [hdec, this, hnone]

/-- **Projective cell partition.** The primitive coefficient vectors of length `n + 1` are
partitioned into the projective cells of the divisors of degree `n`, each measurable with an
explicit mass, and the coefficient measure decomposes as a sum over cells. -/
theorem projective_cells_partition (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    (∃ S : Finset (ExceptionalDivisor (IsLocalRing.ResidueField O)), ∀ D, D ∈ S ↔ exceptionalDegree
      (IsLocalRing.ResidueField O) D = n) ∧ (∀ a : Fin (n+1) → O, primitive O a → ∃! D :
      ExceptionalDivisor (IsLocalRing.ResidueField O), exceptionalDegree
      (IsLocalRing.ResidueField O) D = n ∧ a ∈ projectiveCell O n
      (divisorVector (IsLocalRing.ResidueField O) n D)) ∧
      (∀ D : ExceptionalDivisor (IsLocalRing.ResidueField O), exceptionalDegree
      (IsLocalRing.ResidueField O) D = n → MeasurableSet
      (projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D)) ∧ coefficientMeasure O
      (n+1) (projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D)) =
      ((Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞) - 1) *
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (n+1) ∧ ∀ E : Set (Fin (n+1) → O),
      coefficientMeasure O (n+1) (E ∩ projectiveCell O n
      (divisorVector (IsLocalRing.ResidueField O) n D)) = coefficientMeasure O (n+1)
      (projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D)) * cellMeasure O (n+1)
      (projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D)) E) ∧ ∀ S : Finset
      (ExceptionalDivisor (IsLocalRing.ResidueField O)),
      (∀ D, D ∈ S ↔ exceptionalDegree (IsLocalRing.ResidueField O) D = n) → ∀ E : Set
      (Fin (n+1) → O), MeasurableSet E → coefficientMeasure O (n+1)
      (E ∩ {a : Fin (n+1) → O | primitive O a}) = ∑ D ∈ S, coefficientMeasure O (n+1)
      (E ∩ projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D)) := by
  set k := IsLocalRing.ResidueField O
  have hprob := coefficient_measure_probability O htop (n+1)
  -- unique cell
  have huniq : ∀ a : Fin (n+1) → O, primitive O a → ∃! D : ExceptionalDivisor k,
      exceptionalDegree k D = n ∧ a ∈ projectiveCell O n (divisorVector k n D) := by
    intro a ha
    have hv := (primitive_iff_residue_ne_zero O n a).1 ha
    obtain ⟨D, ⟨hD1, hD2⟩, hDu⟩ := projective_divisor_of_residue_vector k n _ hv
    refine ⟨D, ⟨hD1, ha, hD2⟩, ?_⟩
    rintro D' ⟨h1, _, h2⟩
    exact hDu D' ⟨h1, h2⟩
  have hcell : ∀ D : ExceptionalDivisor k, exceptionalDegree k D = n →
      MeasurableSet (projectiveCell O n (divisorVector k n D)) ∧
      coefficientMeasure O (n+1) (projectiveCell O n (divisorVector k n D)) =
        ((Nat.card k : ℝ≥0∞) - 1) * (Nat.card k : ℝ≥0∞)⁻¹ ^ (n+1) := by
    intro D hD
    exact projective_cell_mass O htop n _
      (divisor_vector_properties k n D hD).2.2.2.2.2.2
  refine ⟨?_, huniq, ?_, ?_⟩
  · have hfin : {D : ExceptionalDivisor k | exceptionalDegree k D = n}.Finite := by
      refine Set.Finite.subset (Set.finite_univ.biUnion (t := fun m : Pattern n =>
        {D : ExceptionalDivisor k | exceptionalDegree k D = n ∧ HasArray k n D m ∧
          m ∈ residuePatterns n}) ?_) ?_
      · intro m _
        by_cases hm : m ∈ residuePatterns n
        · have := (projective_divisor_count k n m hm).1
          refine Set.Finite.subset (Set.finite_coe_iff.1 this) ?_
          intro D hD
          exact ⟨hD.1, hD.2.1⟩
        · refine Set.Finite.subset Set.finite_empty ?_
          intro D hD
          exact absurd hD.2.2 hm
      · intro D hD
        obtain ⟨m, hm1, hm2⟩ := (divisor_array_exists_unique k n D hD).1
        exact Set.mem_biUnion (Set.mem_univ m) ⟨hD, hm1, hm2⟩
    exact ⟨hfin.toFinset, fun D => by simp; rfl⟩
  · intro D hD
    obtain ⟨hmeas, hmass⟩ := hcell D hD
    refine ⟨hmeas, hmass,
      coefficientMeasure_inter_eq_mul O hmeas ?_ (MeasureTheory.measure_ne_top _ _)⟩
    have hq : 1 < Nat.card k := Finite.one_lt_card
    rw [hmass]
    refine mul_ne_zero (tsub_pos_of_lt (by exact_mod_cast hq)).ne'
      (pow_ne_zero _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)))
  · exact fun S hS E hE ↦ measure_inter_eq_sum_cells _ S hS _ _ huniq (fun _ _ _ ha ↦ ha.1)
      (fun D hD ↦ (hcell D hD).1) hE

/-! ### Point cells -/

/-- The zero cell over `O[X]/(Φ)` is the image of scaling by `π`; under this scaling its type
events are root events, and it is the first congruence neighbourhood of `0`. -/
private theorem zero_cell_scaled (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) [IsDomain (AdjoinRoot Φ)] (pi : O) (hpi : Irreducible pi) (r : ℕ)
    (τ : FactorType) :
    zeroCell O Φ r = (fun z : Fin r → AdjoinRoot Φ => algebraMap O (AdjoinRoot Φ) pi • z) ''
      Set.univ ∧ zeroCell O Φ r ∩ typeEvent (AdjoinRoot Φ) r τ =
      (fun z : Fin r → AdjoinRoot Φ => algebraMap O (AdjoinRoot Φ) pi • z) '' rootEvent
      (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi) r τ ∧
      (∀ b : Fin r → AdjoinRoot Φ, b ∈ zeroCell O Φ r ↔ ∀ j, b j - 0 ∈ (baseIdeal O Φ) ^ 1) := by
  have hI : baseIdeal O Φ = Ideal.span {algebraMap O (AdjoinRoot Φ) pi} := by
    unfold baseIdeal
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer pi).1 hpi, Ideal.map_span,
      Set.image_singleton]
    rfl
  have hcyl : ∀ b : Fin r → AdjoinRoot Φ, b ∈ zeroCell O Φ r ↔ ∀ j, b j ∈ baseIdeal O Φ := by
    intro b
    have h601 := (monic_poly_reconstruct (AdjoinRoot Φ) r b)
    obtain ⟨-, hdeg, hco, -⟩ := h601
    have h605 := (polynomial_congruence_and_product (AdjoinRoot Φ) (baseIdeal O Φ)).1
    change (monicPolyO b).map (baseReduce O Φ) = Polynomial.X ^ r ↔ _
    have : (Polynomial.X ^ r : Polynomial (residueExtension O Φ)) =
        (Polynomial.X ^ r : Polynomial (AdjoinRoot Φ)).map (baseReduce O Φ) := by simp
    rw [this]
    change (monicPolyO b).map (Ideal.Quotient.mk (baseIdeal O Φ)) =
        (Polynomial.X ^ r : Polynomial (AdjoinRoot Φ)).map (Ideal.Quotient.mk (baseIdeal O Φ)) ↔ _
    rw [h605]
    have hm : (monicPolyO b).Monic := (monic_poly_reconstruct (AdjoinRoot Φ) r b).1
    constructor
    · intro h j
      have := h j
      rw [hco j, Polynomial.coeff_X_pow] at this
      simpa [Fin.val_ne_iff.mp, j.2.ne] using this
    · intro h j
      by_cases hj : j < r
      · have := h ⟨j, hj⟩
        have e := hco ⟨j, hj⟩
        rw [e, Polynomial.coeff_X_pow, if_neg hj.ne]
        simpa using this
      · rcases (not_lt.1 hj).eq_or_lt with hr | hr
        · subst hr
          have h1 : (monicPolyO b).coeff r = 1 := by
            have := hm.coeff_natDegree
            rwa [hdeg] at this
          rw [Polynomial.coeff_X_pow, if_pos rfl, h1]
          simp
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hr),
            Polynomial.coeff_X_pow, if_neg hr.ne']
          simp
  have himg : ∀ b : Fin r → AdjoinRoot Φ, b ∈ zeroCell O Φ r ↔ ∃ z : Fin r → AdjoinRoot Φ,
      algebraMap O (AdjoinRoot Φ) pi • z = b := by
    intro b
    rw [hcyl]
    simp_rw [hI, Ideal.mem_span_singleton']
    constructor
    · intro h
      choose z hz using h
      exact ⟨z, funext fun j => by simp [mul_comm, ← hz j]⟩
    · rintro ⟨z, rfl⟩ j
      exact ⟨z j, by simp [mul_comm]⟩
  refine ⟨?_, ?_, ?_⟩
  · ext b; simp [himg b]
  · ext b
    constructor
    · rintro ⟨hb, ht⟩
      obtain ⟨z, rfl⟩ := (himg b).1 hb
      exact ⟨z, ht, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(himg _).2 ⟨z, rfl⟩, hz⟩
  · intro b
    rw [hcyl]; simp

/-- The zero cell over `O[X]/(Φ)` is measurable of mass `q^{-r deg Φ}`, and assuming the root cell
law its type events have the law of the single state `(1, r)` at the residue size `q^{deg Φ}`. -/
private theorem zero_cell_type_event_mass (hroot : RootCellLaw) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [TopologicalSpace (AdjoinRoot Φ)] [MeasurableSpace (AdjoinRoot Φ)]
    (hτ : ‹TopologicalSpace (AdjoinRoot Φ)› = unramifiedTopology O Φ hΦ.1)
    (hmeas : ‹MeasurableSpace (AdjoinRoot Φ)› = unramifiedMeasurableSpace O Φ hΦ.1)
    [IsDomain (AdjoinRoot Φ)] [IsTopologicalRing (AdjoinRoot Φ)] [CompactSpace (AdjoinRoot Φ)]
    [T2Space (AdjoinRoot Φ)] [SecondCountableTopology (AdjoinRoot Φ)] [BorelSpace (AdjoinRoot Φ)]
    (pi : O) (hpi : Irreducible pi) (r : ℕ) (hr : 0 < r) (τ : FactorType) :
    MeasurableSet (zeroCell O Φ r) ∧ coefficientMeasure (AdjoinRoot Φ) r (zeroCell O Φ r) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (Φ.natDegree * r) ∧ MeasurableSet
      (zeroCell O Φ r ∩ typeEvent (AdjoinRoot Φ) r τ) ∧ cellMeasure (AdjoinRoot Φ) r
      (zeroCell O Φ r) (typeEvent (AdjoinRoot Φ) r τ) = densityValue
      (lawCoeff (stateLaw (State.single 1 r)) τ) (Nat.card (IsLocalRing.ResidueField O) ^
      Φ.natDegree) := by
  obtain ⟨_, hloc, hcz, hdvr, hcomp, hfin, hcard, -, -, -, -, -, hadic⟩ :=
    unramified_extension_measure_package O htop Φ hΦ hτ hmeas
  obtain ⟨_, _, -, -, hirr, -⟩ := unramified_is_dvr O Φ hΦ
  have hpi' : Irreducible (algebraMap O (AdjoinRoot Φ) pi) := hirr pi hpi
  clear hirr
  have := hloc
  have := hcz
  have := hdvr
  have := hcomp
  have := hfin
  obtain ⟨hR1, hR2⟩ := hroot (AdjoinRoot Φ) hadic _ hpi' r hr τ
  obtain ⟨hz1, hz2, -⟩ := zero_cell_scaled O Φ pi hpi r τ
  obtain ⟨hU1, hU2⟩ := scaling_image_borel_mass (AdjoinRoot Φ) hadic _ hpi' r Set.univ
      MeasurableSet.univ
  obtain ⟨hT1, hT2⟩ := scaling_image_borel_mass (AdjoinRoot Φ) hadic _ hpi' r _ hR1
  have := coefficient_measure_probability (AdjoinRoot Φ) hadic r
  have hq : (Nat.card (IsLocalRing.ResidueField (AdjoinRoot Φ)) : ℝ≥0∞)⁻¹ ^ r
      = (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (Φ.natDegree * r) := by
    rw [hcard, pow_mul, Nat.cast_pow, ENNReal.inv_pow]
  have hne0 : (Nat.card (IsLocalRing.ResidueField (AdjoinRoot Φ)) : ℝ≥0∞)⁻¹ ^ r ≠ 0 :=
    pow_ne_zero _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  have hpos : Nat.card (IsLocalRing.ResidueField (AdjoinRoot Φ)) ≠ 0 := Nat.card_pos.ne'
  have hnet : (Nat.card (IsLocalRing.ResidueField (AdjoinRoot Φ)) : ℝ≥0∞)⁻¹ ^ r ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast hpos))
  rw [← hz1] at hU1 hU2
  unfold rootEvent at hz2
  rw [← hz2] at hT1 hT2
  refine ⟨hU1, ?_, hT1, ?_⟩
  · rw [hU2, MeasureTheory.measure_univ, mul_one, hq]
  · unfold cellMeasure
    rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply' hU1, smul_eq_mul,
      Set.inter_comm, hT2, hU2, MeasureTheory.measure_univ, mul_one, ← mul_assoc,
          ENNReal.inv_mul_cancel hne0 hnet,
      one_mul]
    rw [hR2, hcard]

/-- On the residue cell of `(Φ mod π)^r`, the type event of a scaled type `scaleType (deg Φ) τ₀`
is the preimage under the point chart of the type event `τ₀` of the zero cell. -/
private theorem point_cell_typeEvent_scaleType_eq (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] (r : ℕ) (τ₀ : FactorType) :
    typeEvent O (Φ.natDegree * r) (scaleType Φ.natDegree τ₀) ∩
        residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r) =
      pointChart O Φ r ⁻¹' (zeroCell O Φ r ∩ typeEvent (AdjoinRoot Φ) r τ₀) ∩
        residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r) := by
  have hδ : 0 < Φ.natDegree := hΦ.1.natDegree_map (IsLocalRing.residue O) ▸
    Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hΦ.2)
  have hinj := (scale_type_valid_degree_iff Φ.natDegree r hδ τ₀).2
  ext a
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨τ, hτ, he⟩ := (descended_block_type_iff O Φ hΦ r a h2 _).1 h1
    rw [hinj he]
    exact ⟨⟨(point_chart_bijection O Φ hΦ r).1.mapsTo h2, hτ⟩, h2⟩
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨(descended_block_type_iff O Φ hΦ r a h2 _).2 ⟨τ₀, h1, rfl⟩, h2⟩

/-- On the residue cell of `(Φ mod π)^r`, the type event of a type that is not of the form
`scaleType (deg Φ) τ` is empty. -/
private theorem point_cell_inter_typeEvent_eq_empty (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] (r : ℕ) (σ : FactorType)
    (hσ : ∀ τ, σ ≠ scaleType Φ.natDegree τ) :
    residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r) ∩ typeEvent O (Φ.natDegree * r) σ =
      ∅ := by
  refine Set.eq_empty_of_forall_notMem fun a ⟨ha, h⟩ ↦ ?_
  obtain ⟨τ, -, he⟩ := (descended_block_type_iff O Φ hΦ r a ha _).1 h
  exact hσ τ he

/-- **Point cell law.** Assuming the root cell law, the residue cell of `(Φ mod π)^r` has the law
`lawDescend (deg Φ) (stateLaw (single 1 r))`. -/
theorem point_cell_type_event (hroot : RootCellLaw) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (r : ℕ) (hr : 0 < r) (n : ℕ) (hn : Φ.natDegree * r = n) (σ : FactorType) :
    MeasurableSet (residueCell O n (residuePoly O Φ ^ r) ∩ typeEvent O n σ) ∧ cellMeasure O n
      (residueCell O n (residuePoly O Φ ^ r)) (typeEvent O n σ) = densityValue
      (lawCoeff (lawDescend Φ.natDegree (stateLaw (State.single 1 r))) σ)
      (Nat.card (IsLocalRing.ResidueField O)) := by
  -- strategy: transport cell measures along the point chart onto the zero cell over `O[X]/(Φ)`,
  -- where the root cell law applies; non-scaled types have empty events
  subst hn
  let tτ : TopologicalSpace (AdjoinRoot Φ) := unramifiedTopology O Φ hΦ.1
  let tm : MeasurableSpace (AdjoinRoot Φ) := unramifiedMeasurableSpace O Φ hΦ.1
  obtain ⟨hdom, hloc, hchar, hdvr, hcomp, hfin, hcard, htr, hcpt, ht2, hsc, hbor, hadic⟩ :=
    unramified_extension_measure_package O htop Φ hΦ rfl rfl
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hδ : 0 < Φ.natDegree := hΦ.1.natDegree_map (IsLocalRing.residue O) ▸
    Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hΦ.2)
  have hφmon : (residuePoly O Φ ^ r).Monic := (hΦ.1.map _).pow r
  have hφdeg : (residuePoly O Φ ^ r).natDegree = Φ.natDegree * r := by
    rw [(hΦ.1.map _).natDegree_pow, hΦ.1.natDegree_map, mul_comm]
  have hqinv0 : (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  obtain ⟨hCm, hCμ, -⟩ := residue_cell_mass O htop (Φ.natDegree * r) _ hφmon hφdeg
  obtain ⟨hZm, hZμ, -, -⟩ := zero_cell_type_event_mass hroot O htop Φ hΦ rfl rfl pi hpi r hr σ
  obtain ⟨hbij, hcong⟩ := point_chart_bijection O Φ hΦ r
  have hmax : IsLocalRing.maximalIdeal (AdjoinRoot Φ) = baseIdeal O Φ :=
    (unramified_is_dvr O Φ hΦ).2.2.2.1
  set C := residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r) with hC
  set Z := zeroCell O Φ r with hZ
  set T := pointChart O Φ r with hT
  have hmass : ∀ (L : ℕ), 1 ≤ L → ∀ a ∈ C,
      cellMeasure O (Φ.natDegree * r) C {a' | ∀ j, a' j - a j ∈ (IsLocalRing.maximalIdeal O) ^ L}
        = cellMeasure (AdjoinRoot Φ) r Z
            {b | ∀ j, b j - T a j ∈ (IsLocalRing.maximalIdeal (AdjoinRoot Φ)) ^ L} := by
    intro L hL a ha
    have hsub1 : {a' : Fin (Φ.natDegree * r) → O | ∀ j, a' j - a j ∈ (IsLocalRing.maximalIdeal O) ^
        L} ⊆ C := fun a' ha' ↦ by
      rw [hC, (residue_cell_cylinder O _ _).1 a ha]
      exact fun i ↦ Ideal.pow_le_self (by omega) (ha' i)
    have hsub2 : {b : Fin r → AdjoinRoot Φ | ∀ j, b j - T a j ∈
        (IsLocalRing.maximalIdeal (AdjoinRoot Φ)) ^ L} ⊆ Z := fun b hb ↦ by
      have h3 := (zero_cell_scaled O Φ pi hpi r σ).2.2
      have hTa := (h3 _).1 (hbij.mapsTo ha)
      refine (h3 b).2 fun j ↦ ?_
      have hbj := Ideal.pow_le_self (by omega : L ≠ 0) (hb j)
      rw [hmax] at hbj
      rw [show b j - 0 = (b j - T a j) + (T a j - 0) by ring, pow_one]
      exact Ideal.add_mem _ hbj (pow_one (baseIdeal O Φ) ▸ hTa j)
    rw [cellMeasure_apply_of_measurableSet _ _ _ hCm, cellMeasure_apply_of_measurableSet _ _ _ hZm,
      Set.inter_eq_left.mpr hsub1, Set.inter_eq_left.mpr hsub2, hCμ, hZμ,
      coefficient_cylinder_mass O htop, coefficient_cylinder_mass (AdjoinRoot Φ) hadic, hcard]
    congr 1
    rw [residueCard, Nat.cast_pow, ENNReal.inv_pow, ← pow_mul, ← mul_assoc]
  have htrans := cell_transport_preimage O htop (AdjoinRoot Φ) hadic (Φ.natDegree * r) r C Z
    hCm hZm (by rw [hCμ]; exact pow_ne_zero _ hqinv0) (by rw [hZμ]; exact pow_ne_zero _ hqinv0) T
    hbij (by rw [hmax]; exact hcong) hmass
  by_cases hσ : ∃ τ₀, σ = scaleType Φ.natDegree τ₀
  · obtain ⟨τ₀, rfl⟩ := hσ
    obtain ⟨-, -, hZTm, hZTμ⟩ := zero_cell_type_event_mass hroot O htop Φ hΦ rfl rfl pi hpi r hr τ₀
    have hset := point_cell_typeEvent_scaleType_eq O Φ hΦ r τ₀
    obtain ⟨hm1, hm2⟩ := htrans _ hZTm
    refine ⟨?_, ?_⟩
    · rw [Set.inter_comm, hset, Set.inter_comm]; exact hm1
    · rw [cellMeasure_apply_of_measurableSet _ _ _ hCm, hset, ←
        cellMeasure_apply_of_measurableSet _ _ _ hCm, hm2,
        cellMeasure_apply_of_measurableSet _ _ _ hZm]
      have e : zeroCell O Φ r ∩ typeEvent (AdjoinRoot Φ) r τ₀ ∩ Z = typeEvent (AdjoinRoot Φ) r τ₀ ∩
          Z := by
        rw [hZ]; ext x; simp only [Set.mem_inter_iff]; tauto
      rw [e, ← cellMeasure_apply_of_measurableSet _ _ _ hZm, hZTμ]
      simp only [densityValue]
      rw [(law_coeff_descend Φ.natDegree hδ _ τ₀ _).1]
      push_cast
      rfl
  · push Not at hσ
    have hset := point_cell_inter_typeEvent_eq_empty O Φ hΦ r σ hσ
    refine ⟨by rw [hset]; exact MeasurableSet.empty, ?_⟩
    rw [cellMeasure_apply_of_measurableSet _ _ _ hCm, Set.inter_comm, hset]
    simp only [densityValue]
    rw [(law_coeff_descend Φ.natDegree hδ _ σ _).2 σ hσ]
    simp

/-- The point cell law for a monic irreducible residue polynomial `φ`, obtained by lifting `φ` to
an unramified `Φ`. -/
private theorem irreducible_cell_type_event (hroot : RootCellLaw) (O : Type) [CommRing O]
    [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (φ : Polynomial (IsLocalRing.ResidueField O))
    (hφ : φ.Monic) (hirr : Irreducible φ) (r : ℕ) (hr : 0 < r) (n : ℕ) (hn : φ.natDegree * r = n)
    (σ : FactorType) :
    MeasurableSet (residueCell O n (φ ^ r) ∩ typeEvent O n σ) ∧ cellMeasure O n
      (residueCell O n (φ ^ r)) (typeEvent O n σ) = densityValue
      (lawCoeff (lawDescend φ.natDegree (stateLaw (State.single 1 r))) σ)
      (Nat.card (IsLocalRing.ResidueField O)) := by
  obtain ⟨Φ, hΦ, hres, hdeg⟩ := exists_unramified_lift O φ hφ hirr
  subst hres
  rw [← hdeg] at hn ⊢
  exact point_cell_type_event hroot O htop Φ hΦ r hr n hn σ

open Polynomial in
private theorem formPoly_eq_reverse {O : Type} [CommRing O] [Nontrivial O] (r : ℕ) (b : Fin r → O) :
    formPoly (insertOne (0 : Fin (r+1)) b) = (monicPolyO (b ∘ Fin.rev)).reverse := by
  obtain ⟨hm, hd, hc, -⟩ := monic_poly_reconstruct O r (b ∘ Fin.rev)
  ext i
  rw [formPoly_coeff, coeff_reverse, hd]
  by_cases hi : i ≤ r
  · rw [dif_pos (by omega), revAt_le hi]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp only [Nat.sub_zero]
      have h1 : (monicPolyO (b ∘ Fin.rev)).coeff r = 1 := by
        have := hm.coeff_natDegree; rwa [hd] at this
      rw [h1]; rfl
    · have := hc ⟨r - i, by omega⟩
      simp only at this
      rw [this]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have e : (⟨k+1, by omega⟩ : Fin (r+1)) = (⟨k, by omega⟩ : Fin r).succ := rfl
      rw [e, insertOne, Fin.insertNth_zero', Fin.cons_succ]
      simp only [Function.comp_apply]
      congr 1; ext; simp [Fin.rev]; omega
  · rw [dif_neg (by omega)]
    have : revAt r i = i := by simp only [revAt]; exact if_neg hi
    rw [this, coeff_eq_zero_of_natDegree_lt (by omega)]

open Polynomial in
private theorem infinityBlockEvent_eq_preimage (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (hr : 0 < r) (σ : FactorType) :
    infinityBlockEvent O r σ = (fun b : Fin r → O => b ∘ Fin.rev) ⁻¹'
      ({b' | b' ⟨0, hr⟩ ≠ 0} ∩ typeEvent O r σ) := by
  ext b
  obtain ⟨hm, hd, hc, -⟩ := monic_poly_reconstruct O r (b ∘ Fin.rev)
  set P := monicPolyO (b ∘ Fin.rev) with hP
  set ι := algebraMap O (BaseField O)
  have hF := formPoly_eq_reverse r b
  have hFr : (formPoly (insertOne (0 : Fin (r+1)) b)).coeff r = (b ∘ Fin.rev) ⟨0, hr⟩ := by
    rw [hF, coeff_reverse, hd, revAt_le le_rfl, Nat.sub_self]
    exact hc ⟨0, hr⟩
  have hmap : (formPoly (insertOne (0 : Fin (r+1)) b)).map ι = (P.map ι).reverse := by
    ext i
    rw [coeff_map, coeff_reverse, hm.natDegree_map, hd, coeff_map, hF, coeff_reverse, ← hP, hd]
  have h0 : (P.map ι).coeff 0 = ι ((b ∘ Fin.rev) ⟨0, hr⟩) := by
    rw [coeff_map]; exact congrArg ι (hc ⟨0, hr⟩)
  have hinj : Function.Injective ι := IsFractionRing.injective O (BaseField O)
  simp only [infinityBlockEvent, typeEvent, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff]
  rw [hFr, hmap, ← monicPolyO_map_fraction]
  constructor
  · rintro ⟨hne, ht⟩
    refine ⟨hne, ?_⟩
    have hne' : (P.map ι).coeff 0 ≠ 0 := by
      rw [h0]; exact fun e => hne (hinj (by rw [e, map_zero]))
    rw [reverse_polynomial_type_iff O (P.map ι) (hm.map ι) hne', h0]
    exact ht
  · rintro ⟨hne, ht⟩
    refine ⟨hne, ?_⟩
    have hne' : (P.map ι).coeff 0 ≠ 0 := by
      rw [h0]; exact fun e => hne (hinj (by rw [e, map_zero]))
    rw [reverse_polynomial_type_iff O (P.map ι) (hm.map ι) hne', h0] at ht
    exact ht

open MeasureTheory in
open MeasureTheory in
/-- Assuming the root cell law, the reduced form cell at infinity has law
`lawDescend 1 (stateLaw (single 1 r))` for its infinity block events. -/
theorem infinity_block_event_law (hroot : RootCellLaw) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (r : ℕ) (hr : 0 < r) (σ : FactorType) :
    MeasurableSet (reducedFormCell O r (0 : Fin (r+1))
      (Pi.single (0 : Fin (r+1)) (1 : IsLocalRing.ResidueField O)) ∩ infinityBlockEvent O r σ) ∧
      cellMeasure O r (reducedFormCell O r (0 : Fin (r+1))
      (Pi.single (0 : Fin (r+1)) (1 : IsLocalRing.ResidueField O))) (infinityBlockEvent O r σ) =
      densityValue (lawCoeff (lawDescend 1 (stateLaw (State.single 1 r))) σ)
      (Nat.card (IsLocalRing.ResidueField O)) := by
  set Z := reducedFormCell O r (0 : Fin (r+1)) (Pi.single (0 : Fin (r+1))
      (1 : IsLocalRing.ResidueField O)) with hZdef
  set CX := residueCell O r (Polynomial.X ^ r) with hCXdef
  set R : (Fin r → O) → (Fin r → O) := fun b => b ∘ Fin.rev with hRdef
  have hR : Measurable R := measurable_pi_iff.mpr fun j => measurable_pi_apply _
  have hZ : MeasurableSet Z :=
    (normalized_form_cell_cylinder_mass O htop r 0 _ (Pi.single_eq_same _ _)).2.2.2.1
  obtain ⟨-, hbij, -, hmp⟩ := form_cell_monic_identification O htop r
  have hRR : ∀ b, R (R b) = b := fun b => by
    funext j; simp [hRdef]
  have hCX : CX = R ⁻¹' Z := by
    ext b; constructor
    · intro hb
      obtain ⟨z, hz, rfl⟩ := hbij.surjOn hb
      change R (R z) ∈ Z
      rw [hRR]; exact hz
    · intro hb
      have : R (R b) ∈ CX := hbij.mapsTo hb
      rwa [hRR] at this
  have hCXm : MeasurableSet CX := hCX ▸ hR hZ
  obtain ⟨hT, hlaw⟩ := irreducible_cell_type_event hroot O htop Polynomial.X Polynomial.monic_X
    Polynomial.irreducible_X r hr r (by rw [Polynomial.natDegree_X, one_mul]) σ
  rw [Polynomial.natDegree_X] at hlaw
  obtain ⟨hHm0, hH0⟩ := coordinate_hyperplane_null O htop r ⟨0, hr⟩
  set H : Set (Fin r → O) := {b' | b' ⟨0, hr⟩ ≠ 0} with hHdef
  have hHm : MeasurableSet H := hHm0.compl
  set A := CX ∩ typeEvent O r σ ∩ H with hAdef
  have hA : MeasurableSet A := hT.inter hHm
  have hkey : infinityBlockEvent O r σ ∩ Z = R ⁻¹' A ∩ Z := by
    rw [infinityBlockEvent_eq_preimage O r hr σ]
    ext b
    simp only [Set.mem_inter_iff, Set.mem_preimage, hAdef]
    constructor
    · rintro ⟨⟨h1, h2⟩, hb⟩; exact ⟨⟨⟨hbij.mapsTo hb, h2⟩, h1⟩, hb⟩
    · rintro ⟨⟨⟨-, h2⟩, h1⟩, hb⟩; exact ⟨⟨h1, h2⟩, hb⟩
  refine ⟨?_, ?_⟩
  · rw [Set.inter_comm, hkey]; exact (hR hA).inter hZ
  rw [← cellMeasure_cell_inter hZ, Set.inter_comm Z, hkey, Set.inter_comm _ Z,
    cellMeasure_cell_inter hZ,
    hmp.measure_preimage hA.nullMeasurableSet, ← hlaw]
  have hnull : cellMeasure O r CX {b : Fin r → O | b ⟨0, hr⟩ = 0} = 0 := by
    have : (coefficientMeasure O r).restrict CX {b : Fin r → O | b ⟨0, hr⟩ = 0} = 0 :=
      le_antisymm ((Measure.restrict_le_self _).trans hH0.le) (zero_le)
    simp [cellMeasure, this]
  rw [← cellMeasure_cell_inter hCXm (typeEvent O r σ), Set.inter_comm CX,
    ← measure_inter_add_sdiff (typeEvent O r σ ∩ CX) hHm]
  have hdiff : cellMeasure O r CX (SDiff.sdiff (typeEvent O r σ ∩ CX) H) = 0 :=
    measure_mono_null (fun b hb => by simpa [hHdef] using hb.2) hnull
  rw [hdiff, add_zero, hAdef, Set.inter_comm CX]

section
variable {k : Type} [Field k]

private noncomputable def blockPoly : ClosedDirection k → ℕ → Polynomial k
  | none, _ => 1
  | some φ, r => φ.val ^ r

private def blockDeg : ClosedDirection k → ℕ → ℕ
  | none, r => r
  | some φ, r => φ.val.natDegree * r

private def blockNu : (Q : ClosedDirection k) → (r : ℕ) → Fin (blockDeg Q r + 1)
  | none, _ => 0
  | some _, _ => Fin.last _

private noncomputable def blockG (Q : ClosedDirection k) (r : ℕ) : Fin (blockDeg Q r + 1) → k :=
  fun i => (blockPoly Q r).coeff i

private lemma blockDeg_eq_mul (Q : ClosedDirection k) (r : ℕ) :
    blockDeg Q r = directionDegree k Q * r := by
  cases Q <;> simp [blockDeg, directionDegree]

private lemma blockPoly_natDegree_le (Q : ClosedDirection k) (r : ℕ) :
    (blockPoly Q r).natDegree ≤ blockDeg Q r := by
  cases Q with
  | none => simp [blockPoly]
  | some φ => simp [blockPoly, blockDeg, φ.2.1.natDegree_pow, mul_comm]

private lemma formPoly_coeff_eq_self (n : ℕ) (P : Polynomial k) (h : P.natDegree ≤ n) :
    formPoly (fun i : Fin (n+1) => P.coeff i) = P := by
  unfold formPoly
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (P.coeff i) * Polynomial.X ^ i) (n+1)]
  conv_rhs => rw [P.as_sum_range' (n+1) (by omega)]
  simp [Polynomial.C_mul_X_pow_eq_monomial]

private lemma formPoly_blockG (Q : ClosedDirection k) (r : ℕ) :
    formPoly (blockG Q r) = blockPoly Q r :=
  formPoly_coeff_eq_self _ _ (blockPoly_natDegree_le Q r)

private lemma blockPoly_isCoprime (a b : ClosedDirection k) (ra rb : ℕ) (hne : a ≠ b) :
    IsCoprime (blockPoly a ra) (blockPoly b rb) := by
  cases a with
  | none => simp [blockPoly, isCoprime_one_left]
  | some φ =>
    cases b with
    | none => simp [blockPoly, isCoprime_one_right]
    | some ψ =>
      exact (distinct_monic_irreducible_coprime k φ.1 ψ.1 φ.2.1 ψ.2.1 φ.2.2 ψ.2.2
        (fun h => hne (congrArg some (Subtype.ext h)))).pow

private lemma blockPoly_some_natDegree (φ : AffineDirection k) (r : ℕ) :
    (blockPoly (some φ) r).natDegree = blockDeg (some φ) r := by
  simp [blockPoly, blockDeg, φ.2.1.natDegree_pow, mul_comm]

private lemma blockPoly_natDegree_or (a b : ClosedDirection k) (ra rb : ℕ) (hne : a ≠ b) :
    (blockPoly a ra).natDegree = blockDeg a ra ∨ (blockPoly b rb).natDegree = blockDeg b rb := by
  cases a with
  | none =>
    cases b with
    | none => exact absurd rfl hne
    | some ψ => exact Or.inr (blockPoly_some_natDegree ψ rb)
  | some φ => exact Or.inl (blockPoly_some_natDegree φ ra)

private lemma blockG_single (r : ℕ) : blockG (none : ClosedDirection k) r = Pi.single 0 1 := by
  funext i
  simp only [blockG, blockPoly, Polynomial.coeff_one, Pi.single_apply]
  by_cases h : i = 0
  · subst h; simp
  · have : (i : ℕ) ≠ 0 := fun h' => h (Fin.ext h')
    simp [h, this]

private lemma blockG_nu (a : ClosedDirection k) (r : ℕ) : blockG a r (blockNu a r) = 1 := by
  cases a with
  | none => rw [blockG_single]; simp [blockNu]
  | some φ =>
    simp only [blockG, blockNu, Fin.val_last]
    rw [← blockPoly_some_natDegree φ r]
    exact (φ.2.1.pow r)

private lemma block_class (a : ClosedDirection k) (r : ℕ) :
    if a.isNone = true then (blockNu a r = 0 ∧ blockG a r = Pi.single 0 1) else blockNu a r =
      Fin.last _ := by
  cases a with
  | none => simp [blockNu, blockG_single]
  | some φ => simp [blockNu]

end

private lemma block_law (hroot : RootCellLaw) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (a : ClosedDirection (IsLocalRing.ResidueField O))
    (r : ℕ) (hr : 0 < r) (τ : FactorType) :
    MeasurableSet (reducedFormCell O (blockDeg a r) (blockNu a r) (blockG a r) ∩
      (if a.isNone = true then infinityBlockEvent O (blockDeg a r) τ else typeEvent O
      (blockDeg a r) τ)) ∧ cellMeasure O (blockDeg a r) (reducedFormCell O (blockDeg a r)
      (blockNu a r) (blockG a r)) (if a.isNone = true then infinityBlockEvent O (blockDeg a r) τ
      else typeEvent O (blockDeg a r) τ) = densityValue (lawCoeff
      (lawDescend (directionDegree _ a) (stateLaw (State.single 1 r))) τ)
      (Nat.card (IsLocalRing.ResidueField O)) := by
  cases a with
  | none =>
    simp only [Option.isNone_none, if_true]
    rw [blockG_single]
    exact infinity_block_event_law hroot O htop r hr τ
  | some φ =>
    simp only [Option.isNone_some, Bool.false_eq_true, if_false]
    have hcell := (form_cell_monic_identification O htop 0).1 (blockDeg (some φ) r)
        (blockG (some φ) r)
    rw [formPoly_blockG] at hcell
    change MeasurableSet (reducedFormCell O _ (Fin.last _) _ ∩ _) ∧ cellMeasure O _
        (reducedFormCell O _ (Fin.last _) _) _ = _
    rw [hcell]
    exact irreducible_cell_type_event hroot O htop φ.1 φ.2.1 φ.2.2 r hr _ rfl τ

private lemma block_law_coeff_nonneg (k : Type) [Field k] [Finite k] (a : ClosedDirection k) (r : ℕ)
    (hr : 0 < r) (τ : FactorType) :
    0 ≤ (lawCoeff (lawDescend (directionDegree _ a) (stateLaw (State.single 1 r))) τ).eval
      (Nat.card k) :=
  (state_law_coeff_nonneg _ (finite_field_card_primePower k) (State.single 1 r) ⟨one_pos, hr⟩ τ).2
    _ (directionDegree_pos _ a)

/-! ### Divisor cells -/

/-- **Divisor cell law.** Assuming the root cell law, the reduced form cell of a divisor `D` with
array `m` has law `arrayLaw m`. -/
theorem divisor_form_cell_law (hroot : RootCellLaw) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (D : ExceptionalDivisor (IsLocalRing.ResidueField O))
    (hD : exceptionalDegree (IsLocalRing.ResidueField O) D = n) (m : Pattern n)
    (hm : HasArray (IsLocalRing.ResidueField O) n D m) (σ : FactorType) :
    MeasurableSet (reducedFormCell O n
      (⟨n - D (infinityDirection (IsLocalRing.ResidueField O)),
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ : Fin (n+1))
      (divisorVector (IsLocalRing.ResidueField O) n D) ∩ insertOne
      (⟨n - D (infinityDirection (IsLocalRing.ResidueField O)),
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ : Fin (n+1)) ⁻¹'
      affineTypeEvent O n σ) ∧ cellMeasure O n (reducedFormCell O n
      (⟨n - D (infinityDirection (IsLocalRing.ResidueField O)),
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ : Fin (n+1))
      (divisorVector (IsLocalRing.ResidueField O) n D)) (insertOne
      (⟨n - D (infinityDirection (IsLocalRing.ResidueField O)),
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ : Fin (n+1)) ⁻¹'
      affineTypeEvent O n σ) = densityValue (lawCoeff (arrayLaw m) σ)
      (Nat.card (IsLocalRing.ResidueField O)) := by
  obtain ⟨e, he⟩ := array_enumeration (IsLocalRing.ResidueField O) n D hD m hm
  let Q : Fin (otherChildren 1 m).length → ClosedDirection (IsLocalRing.ResidueField O) :=
    fun j => (e j).val
  have hQinj : Function.Injective Q := fun i j h => e.injective (Subtype.ext h)
  have hr : ∀ j, 0 < D (Q j) := fun j => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (e j).2)
  let d : Fin (otherChildren 1 m).length → ℕ := fun j => blockDeg (Q j) (D (Q j))
  let ν : ∀ j, Fin (d j + 1) := fun j => blockNu (Q j) (D (Q j))
  let g : ∀ j, Fin (d j + 1) → IsLocalRing.ResidueField O := fun j => blockG (Q j) (D (Q j))
  have hsum : ∑ j, d j = n := by
    refine Eq.trans ?_ hD
    unfold exceptionalDegree Finsupp.sum
    rw [← Finset.sum_coe_sort D.support]
    rw [← Equiv.sum_comp e]
    simp only [d, Q, blockDeg_eq_mul]
  have hpoly : ∏ j, formPoly (g j) = divisorAffinePolynomial (IsLocalRing.ResidueField O) D := by
    have : divisorAffinePolynomial (IsLocalRing.ResidueField O) D = D.prod
        (fun P r => blockPoly P r) := by
      unfold divisorAffinePolynomial
      congr 1; funext P r; cases P <;> rfl
    rw [this]
    unfold Finsupp.prod
    rw [← Finset.prod_coe_sort D.support, ← Equiv.prod_comp e]
    simp only [g, formPoly_blockG, Q]
  have hprod : formProd d g = divisorVector (IsLocalRing.ResidueField O) (∑ j, d j) D := by
    funext i
    simp only [formProd, divisorVector, hpoly]
  have hD' : exceptionalDegree (IsLocalRing.ResidueField O) D = ∑ j, d j := hD.trans hsum.symm
  have hμ : formProd d g ⟨(∑ j, d j) - D (infinityDirection (IsLocalRing.ResidueField O)),
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ = 1 := by
    rw [hprod]
    exact (divisor_vector_properties _ _ D hD').2.2.2.2.1
  have hc : FormsCoprime d g := by
    constructor
    · intro i j hij
      simp only [g, formPoly_blockG]
      exact blockPoly_isCoprime _ _ _ _ (fun h => hij (hQinj h))
    · intro i j hij
      simp only [g, d, formPoly_blockG]
      exact blockPoly_natDegree_or _ _ _ _ (fun h => hij (hQinj h))
  let Dl : Fin (otherChildren 1 m).length → Law := fun j =>
    lawDescend (directionDegree _ (Q j)) (stateLaw (State.single 1 (D (Q j))))
  have R := form_product_type_event_law O htop _ d ν g (fun j => blockG_nu _ _) hc _ hμ
    (fun j => (Q j).isNone) (fun j => block_class _ _)
    (fun i j hi hj => hQinj (by
      simp only [Option.isNone_iff_eq_none] at hi hj; rw [hi, hj]))
    Dl (fun j τ => block_law_coeff_nonneg _ _ _ (hr j) τ)
        (fun j τ => block_law hroot O htop _ _ (hr j) τ) σ
  have hlist : List.ofFn Dl = (otherChildren 1 m).map fun z => lawDescend z.1 (stateLaw z.2) := by
    conv_rhs => rw [← List.ofFn_get (otherChildren 1 m), List.map_ofFn]
    exact congrArg List.ofFn (funext fun j ↦ by simp only [Function.comp_apply, he j, Dl, Q])
  rwa [hlist, hprod, hsum] at R

/-- **Monic cell law.** Assuming the root cell law, the residue cell of an affine divisor with
array `m` has law `arrayLaw m`. -/
theorem monic_cell_law (hroot : RootCellLaw) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (D : ExceptionalDivisor (IsLocalRing.ResidueField O))
    (hD : AffineDivisor (IsLocalRing.ResidueField O) n D) (m : Pattern n)
    (hm : HasArray (IsLocalRing.ResidueField O) n D m) (σ : FactorType) :
    MeasurableSet (residueCell O n (divisorAffinePolynomial (IsLocalRing.ResidueField O) D) ∩
      typeEvent O n σ) ∧ cellMeasure O n (residueCell O n
      (divisorAffinePolynomial (IsLocalRing.ResidueField O) D)) (typeEvent O n σ) = densityValue
      (lawCoeff (arrayLaw m) σ) (Nat.card (IsLocalRing.ResidueField O)) := by
  set k := IsLocalRing.ResidueField O
  obtain ⟨e, he⟩ := array_enumeration k n D hD.2 m hm
  have hsome : ∀ j, ∃ a : AffineDirection k, (e j).val = some a := fun j ↦
    Option.ne_none_iff_exists'.1 fun h ↦ Finsupp.mem_support_iff.1 (h ▸ (e j).2 :
      none ∈ D.support) hD.1
  choose φ hφ using hsome
  have hr : ∀ j, 0 < D (e j) := fun j ↦ Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 (e j).2)
  let g : Fin (otherChildren 1 m).length → Polynomial k := fun j => (φ j).val ^ D (e j)
  let Dl : Fin (otherChildren 1 m).length → Law := fun j => lawDescend (φ j).val.natDegree
      (stateLaw (State.single 1 (D (e j))))
  have hg : ∀ j, (g j).Monic := fun j => (φ j).property.1.pow _
  have hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j) := by
    intro i j hij
    have hne : (φ i).val ≠ (φ j).val := fun h ↦
      hij (e.injective (Subtype.ext (by rw [hφ i, hφ j, Subtype.ext h])))
    exact (distinct_monic_irreducible_coprime k _ _ (φ i).property.1 (φ j).property.1
      (φ i).property.2 (φ j).property.2 hne).pow
  have hnn : ∀ (j : Fin (otherChildren 1 m).length) (τ : FactorType), 0 ≤ (lawCoeff (Dl j) τ).eval
      (Nat.card k) := by
    intro j τ
    exact (state_law_coeff_nonneg _ (finite_field_card_primePower k) (State.single 1 (D (e j)))
        (show 0 < 1 ∧ 0 < D (e j) from ⟨Nat.one_pos, hr j⟩) τ).2 _
      (Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_irreducible (φ j).property.2))
  have hlaw : ∀ (j : Fin (otherChildren 1 m).length) (τ : FactorType), MeasurableSet
      (residueCell O (g j).natDegree (g j) ∩ typeEvent O (g j).natDegree τ) ∧ cellMeasure O
      (g j).natDegree (residueCell O (g j).natDegree (g j)) (typeEvent O (g j).natDegree τ) =
      densityValue (lawCoeff (Dl j) τ) (Nat.card k) := by
    intro j τ
    exact irreducible_cell_type_event hroot O htop (φ j).val (φ j).property.1 (φ j).property.2
      (D (e j)) (hr j) (g j).natDegree (by simp only [g, Polynomial.natDegree_pow]; ring) τ
  have hprod : ∏ j, g j = divisorAffinePolynomial k D := by
    unfold divisorAffinePolynomial Finsupp.prod
    rw [← Finset.prod_coe_sort D.support, ← e.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [g, hφ j]
  have hsum : ∑ j, (g j).natDegree = n := by
    refine Eq.trans ?_ hD.2
    unfold exceptionalDegree Finsupp.sum
    rw [← Finset.sum_coe_sort D.support, ← e.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g, hφ j, directionDegree, Polynomial.natDegree_pow]
    ring
  have hlist : List.ofFn Dl = (otherChildren 1 m).map fun z => lawDescend z.1 (stateLaw z.2) := by
    conv_rhs => rw [← List.ofFn_get (otherChildren 1 m), List.map_ofFn]
    exact congrArg List.ofFn (funext fun j ↦ by
      simp only [Function.comp_apply, he j, Dl, hφ, directionDegree])
  have key := product_law_of_factor_laws O htop _ g hg hc Dl hnn hlaw σ
  rwa [hprod, hsum, hlist] at key

/-- Assuming the root cell law, the projective cell of a divisor with array `m` has law
`arrayLaw m` for affine type events. -/
theorem projective_cell_affine_type_event (hroot : RootCellLaw) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (D : ExceptionalDivisor (IsLocalRing.ResidueField O))
    (hD : exceptionalDegree (IsLocalRing.ResidueField O) D = n) (m : Pattern n)
    (hm : HasArray (IsLocalRing.ResidueField O) n D m) (σ : FactorType) :
    MeasurableSet (projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D) ∩
      affineTypeEvent O n σ) ∧ cellMeasure O (n+1) (projectiveCell O n
      (divisorVector (IsLocalRing.ResidueField O) n D)) (affineTypeEvent O n σ) = densityValue
      (lawCoeff (arrayLaw m) σ) (Nat.card (IsLocalRing.ResidueField O)) := by
  obtain ⟨_, _, _, _, hGμ, _, hG0⟩ := divisor_vector_properties (IsLocalRing.ResidueField O) n D hD
  set G := divisorVector (IsLocalRing.ResidueField O) n D with hG
  set μ : Fin (n+1) := ⟨n - D (infinityDirection (IsLocalRing.ResidueField O)), by omega⟩ with hμ
  obtain ⟨hPCm, _⟩ := projective_cell_mass O htop n G hG0
  obtain ⟨hmaps, _, _, hmp⟩ := projective_cell_normalization_pushforward O htop n G μ hGμ
  obtain ⟨hEm, hEv⟩ := divisor_form_cell_law hroot O htop n D hD m hm σ
  have hscale := (affine_type_event_unit_scaling O n σ).2 G μ hGμ
  have hset : projectiveCell O n G ∩ affineTypeEvent O n σ
      = projectiveCell O n G ∩ (projectiveNormalize O n G μ ⁻¹'
          (reducedFormCell O n μ G ∩ insertOne μ ⁻¹' affineTypeEvent O n σ)) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, hmaps ha, (hscale a ha).2 hb⟩
    · rintro ⟨ha, _, hb⟩
      exact ⟨ha, (hscale a ha).1 hb⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact hPCm.inter (hmp.measurable hEm)
  · have hDc := (normalized_form_cell_cylinder_mass O htop n μ G hGμ).2.2.2.1
    rw [← cellMeasure_cell_inter hPCm, hset, cellMeasure_cell_inter hPCm,
      hmp.measure_preimage hEm.nullMeasurableSet, cellMeasure_cell_inter hDc]
    exact hEv

/-- **Primitive density.** Assuming the root cell law, the relative density of the affine type
event `σ` among primitive coefficient vectors is `densityValue (projectiveExpr n σ) q`. -/
theorem affine_type_event_primitive_density (hroot : RootCellLaw) (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    MeasurableSet (affineTypeEvent O n σ ∩ {a : Fin (n+1) → O | primitive O a}) ∧
      coefficientMeasure O (n+1) (affineTypeEvent O n σ ∩ {a : Fin (n+1) → O | primitive O a}) /
      coefficientMeasure O (n+1) {a : Fin (n+1) → O | primitive O a} = densityValue
      (projectiveExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) := by
  classical
  set k := IsLocalRing.ResidueField O
  set q := Nat.card k
  set μ := coefficientMeasure O (n+1)
  set A := affineTypeEvent O n σ
  set Pr := {a : Fin (n+1) → O | primitive O a}
  obtain ⟨⟨S, hS⟩, hpart, hcell, hsum⟩ := projective_cells_partition O htop n
  set PC : ExceptionalDivisor k → Set (Fin (n+1) → O) := fun D ↦
    projectiveCell O n (divisorVector k n D)
  have hPCsub : ∀ D, PC D ⊆ Pr := fun D a ha ↦ ha.1
  have hlawD := fun D (hD : D ∈ S) m hm ↦
    projective_cell_affine_type_event hroot O htop n D ((hS D).1 hD) m hm σ
  have hmeas : MeasurableSet (A ∩ Pr) := by
    have hunion : A ∩ Pr = ⋃ D ∈ S, PC D ∩ A := by
      ext a
      simp only [Set.mem_inter_iff, Set.mem_iUnion]
      refine ⟨fun ⟨hA, hP⟩ ↦ ?_, fun ⟨D, _, ha, hA⟩ ↦ ⟨hA, hPCsub D ha⟩⟩
      obtain ⟨D, ⟨hD, ha⟩, -⟩ := hpart a hP
      exact ⟨D, (hS D).2 hD, ha, hA⟩
    rw [hunion]
    refine Finset.measurableSet_biUnion S fun D hD ↦ ?_
    obtain ⟨⟨m, hm, -⟩, -⟩ := divisor_array_exists_unique k n D ((hS D).1 hD)
    exact (hlawD D hD m hm).1
  refine ⟨hmeas, ?_⟩
  -- the measure side: a sum over arrays weighted by divisor counts
  let c : Pattern n → ℝ≥0∞ := fun m ↦ densityValue (lawCoeff (arrayLaw m) σ) q
  set ν := densityValue (Expr.inv (projectiveNormalizer n)) q
  have hcellD : ∀ D ∈ S, μ (A ∩ Pr ∩ PC D) * (μ Pr)⁻¹ =
      ν * ∑ m ∈ residuePatterns n, if HasArray k n D m then c m else 0 := by
    intro D hD
    obtain ⟨⟨m₀, hm₀, hm₀R⟩, huniq⟩ := divisor_array_exists_unique k n D ((hS D).1 hD)
    rw [Finset.sum_eq_single_of_mem m₀ hm₀R fun m _ hne ↦ if_neg fun h ↦ hne (huniq _ _ h hm₀),
      if_pos hm₀, Set.inter_assoc, Set.inter_eq_right.2 (hPCsub D),
      (hcell D ((hS D).1 hD)).2.2 A, (hlawD D hD m₀ hm₀).2, mul_right_comm, ← div_eq_mul_inv,
      projective_cell_conditional_density O htop n (divisorVector k n D)
        (divisor_vector_properties k n D ((hS D).1 hD)).2.2.2.2.2.2]
  have hmass : μ (A ∩ Pr) / μ Pr =
      ν * ∑ m ∈ residuePatterns n, ((S.filter fun D ↦ HasArray k n D m).card : ℝ≥0∞) * c m := by
    have := hsum S hS (A ∩ Pr) hmeas
    rw [Set.inter_assoc, Set.inter_self] at this
    rw [div_eq_mul_inv, this, Finset.sum_mul, Finset.sum_congr rfl hcellD, ← Finset.mul_sum,
      Finset.sum_comm]
    refine congrArg (ν * ·) (Finset.sum_congr rfl fun m _ ↦ ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ∀ m ∈ residuePatterns n, ((S.filter fun D ↦ HasArray k n D m).card : ℚ) =
      (divisorCount 1 m).eval (q : ℚ) := by
    intro m hm
    rw [← (projective_divisor_count k n m hm).2,
      Nat.subtype_card (S.filter fun D ↦ HasArray k n D m) fun D ↦ by rw [Finset.mem_filter, hS]]
  -- the law side
  have hlaw : (projectiveExpr n σ).eval (q : ℚ) = (Expr.inv (projectiveNormalizer n)).eval (q : ℚ) *
      ∑ m ∈ residuePatterns n, (divisorCount 1 m).eval (q : ℚ) *
        (lawCoeff (arrayLaw m) σ).eval (q : ℚ) := by
    rw [projectiveExpr, globalLaw, law_coeff_scale, (law_coeff_flatMap _ _ _ [] [] σ _).2.2,
      ← Finset.sum_map_toList]
    simp only [if_true]
    congr 2
    exact List.map_congr_left fun m _ ↦ by rw [law_coeff_scale]; rfl
  have hPN : 0 ≤ (Expr.inv (projectiveNormalizer n)).eval (q : ℚ) := by
    change 0 ≤ ((projectiveNormalizer n).eval (q : ℚ))⁻¹
    rw [(projective_normalizer_eval _ n).1]
    positivity
  have hl : ∀ m : Pattern n, 0 ≤ (lawCoeff (arrayLaw m) σ).eval (q : ℚ) := by
    refine fun m ↦ (law_coeff_nonneg_closure (q : ℚ)).2.2.1 _ (fun L hL τ ↦ ?_) σ
    simp only [List.mem_map, otherChildren, List.mem_flatMap, List.mem_replicate] at hL
    obtain ⟨z, ⟨ij, -, -, rfl⟩, rfl⟩ := hL
    exact (state_law_coeff_nonneg q (finite_field_card_primePower k) _
      (show State.Valid (.single 1 _) from ⟨Nat.one_pos, Nat.succ_pos _⟩) τ).2 _ (Nat.succ_pos _)
  rw [hmass]
  change ν * _ = ENNReal.ofReal (((projectiveExpr n σ).eval (q : ℚ) : ℚ) : ℝ)
  rw [hlaw, Rat.cast_mul, ENNReal.ofReal_mul (by exact_mod_cast hPN), Rat.cast_sum,
    ENNReal.ofReal_sum_of_nonneg fun m hm ↦ by
      have := hl m; rw [← hcard m hm]; push_cast; positivity]
  refine congrArg (ν * ·) (Finset.sum_congr rfl fun m hm ↦ ?_)
  rw [← hcard m hm, Rat.cast_mul, ENNReal.ofReal_mul (by positivity), Rat.cast_natCast,
    ENNReal.ofReal_natCast]

end SurfaceBlowup
