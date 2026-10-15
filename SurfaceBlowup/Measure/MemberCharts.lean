/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.CechStability
import SurfaceBlowup.Formula.TypeTransport
import SurfaceBlowup.Recursion.Members

/-!
# Charts of concrete members and the inseparable locus

For a concrete member of the recursion we describe its coordinate charts: translations of the
coordinates, the coset decomposition of a cell in a chart, and the pushforward of Haar measure along
a product of child charts. We show that the inseparable locus of monic polynomials is Haar-null,
and compute the cokernel length `binom(d, 2)` of the child-order map of a blown-up curve.

## Main results

* `member_chart_translate`: translating chart coordinates recenters the generator and preserves the
  coefficient measure.
* `member_coefficient_measure_map_product_coordinates`: a measurable linear isomorphism onto the
  child coordinate spaces maps Haar measure to the product of Haar measures.
* `monic_inseparable_null`: the inseparable locus of monic polynomials is Haar-null.
* `member_cell_chart_coset_decomposition`: the preimage of a cell in a chart is a finite disjoint
  union of coordinate cosets.
* `member_product_chart_pushforward`: the pushforward of Haar measure along a product of child
  charts.
* `child_order_index_and_kernel`, `concrete_curve_order_index`: the child-order map has kernel
  `(f)` and cokernel of length `binom(d, 2)`.

Provenance: `Thm_SurfaceBlowupV2_*`: `member_chart_translate`, `member_children_degree_sum`,
`member_coefficient_measure_map_product_coordinates`, `member_cell_chart_coset_decomposition`,
`member_product_chart_pushforward`, `curve_order_limit_cokernel_length`,
`child_order_index_and_kernel`, `concrete_curve_order_index`; `Thm_Gen_InseparableNull`.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-- Translating chart coordinates by `z₀` recenters the generator at `f + π Σ z₀ᵢ bᵢ`, maps cosets
  to translated cosets, and preserves the coefficient measure and measurability. -/
theorem member_chart_translate (m : ConcreteMember) (f : m.toMeasured.R)
    (b : Fin m.toMeasured.s.degree → m.toMeasured.R) (Mlev : ℕ)
    (z₀ : Fin m.toMeasured.s.degree → m.toMeasured.O) :
    (∀ z, coordinateIdeal m.toMeasured.S.pi f b (z₀ + z) =
      coordinateIdeal m.toMeasured.S.pi (f + m.toMeasured.S.pi • coordinateLift b z₀) b z) ∧
      coordinateCoset m.toMeasured.S.pi Mlev z₀ =
      (fun z => z₀ + z) '' Set.range (coordinateScale m.toMeasured.S.pi Mlev) ∧
        ∀ A : Set (Fin m.toMeasured.s.degree → m.toMeasured.O),
        coefficientMeasure m.toMeasured.O m.toMeasured.s.degree ((fun z => z₀ + z) '' A) =
        coefficientMeasure m.toMeasured.O m.toMeasured.s.degree A ∧
        (MeasurableSet A → MeasurableSet ((fun z => z₀ + z) '' A)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    unfold coordinateIdeal normalizedIdeal normalizedGenerator coordinateLift
    congr 2
    simp only [Pi.smul_apply, Pi.add_apply, smul_add, add_smul, Finset.sum_add_distrib,
      Finset.smul_sum, smul_eq_mul, mul_smul, ← add_assoc]
  · ext z
    rw [Set.mem_image]
    simp only [coordinateCoset, Set.mem_ofPred_eq, Set.mem_range, coordinateScale]
    rw [finite_coordinate_adic_congruence]
    constructor
    · intro h
      choose y hy using fun i ↦ Ideal.mem_span_singleton'.1
        (by simpa only [Ideal.span_singleton_pow] using h i)
      refine ⟨(m.toMeasured.S.pi ^ Mlev) • y, ⟨y, rfl⟩, ?_⟩
      ext i
      simp [mul_comm _ (y i), hy i]
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
      exact ⟨y i, by simp [mul_comm]⟩
  · intro A
    have := (coefficient_space_strict_instances m.toMeasured.O m.toMeasured.htop
      m.toMeasured.S.pi m.toMeasured.S.pi_irreducible m.toMeasured.s.degree).2.1
    rw [Set.image_add_left]
    exact ⟨MeasureTheory.measure_preimage_add _ _ _, fun hA ↦ measurable_const_add _ hA⟩

/-- The degrees of the children of a cell, weighted by their multiplicities `δ_j`, sum to the degree
  of the parent state. -/
theorem member_children_degree_sum (m : ConcreteMember) (c : m.toMeasured.cellIndex) :
    ∑ j, m.toMeasured.childDelta c j * (m.toMeasured.childState c j).degree =
      m.toMeasured.s.degree := by
  rw [← children_degree_identity m.toMeasured.s (m.shape.valid m.ha) c.1.1 c.1.2]
  exact Fin.sum_univ_fun_getElem _ fun z : ℕ × State ↦ z.1 * z.2.degree

/-- A measurable linear isomorphism onto the product of child coordinate spaces maps the parent
  coefficient measure to the product of child coefficient measures. -/
theorem member_coefficient_measure_map_product_coordinates (m : ConcreteMember)
    (c : m.toMeasured.cellIndex) (mc : m.toMeasured.childIdx c → ConcreteMember)
    [∀ j, Algebra m.toMeasured.O (mc j).toMeasured.O]
    (ρ : (Fin m.toMeasured.s.degree → m.toMeasured.O) ≃ₗ[m.toMeasured.O]
      (∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O))
    (hρ : Measurable ρ) :
    MeasureTheory.Measure.map ρ (coefficientMeasure m.toMeasured.O m.toMeasured.s.degree) =
      MeasureTheory.Measure.pi
      (fun j => coefficientMeasure (mc j).toMeasured.O (mc j).toMeasured.s.degree) := by
  classical
  have hm := coefficient_space_strict_instances m.toMeasured.O m.toMeasured.htop
    m.pi m.hpi m.toMeasured.s.degree
  have hc := fun j => coefficient_space_strict_instances (mc j).toMeasured.O (mc j).toMeasured.htop
    (mc j).pi (mc j).hpi (mc j).toMeasured.s.degree
  have := hm.2.1
  have := hm.2.2.1
  have : ∀ j, MeasureTheory.Measure.IsAddHaarMeasure
      (coefficientMeasure (mc j).toMeasured.O (mc j).toMeasured.s.degree) := fun j => (hc j).2.1
  have : ∀ j, MeasureTheory.IsProbabilityMeasure
      (coefficientMeasure (mc j).toMeasured.O (mc j).toMeasured.s.degree) := fun j => (hc j).2.2.1
  set ν := MeasureTheory.Measure.pi
      (fun j => coefficientMeasure (mc j).toMeasured.O (mc j).toMeasured.s.degree)
  set μ' := MeasureTheory.Measure.map ρ (coefficientMeasure m.toMeasured.O m.toMeasured.s.degree)
  have : MeasureTheory.IsProbabilityMeasure μ' :=
    MeasureTheory.Measure.isProbabilityMeasure_map hρ.aemeasurable
  have : μ'.IsAddLeftInvariant :=
    MeasureTheory.isAddLeftInvariant_map (ρ.toLinearMap.toAddMonoidHom.toAddHom) hρ ρ.surjective
  have key := MeasureTheory.Measure.isAddInvariant_eq_smul_of_compactSpace μ' ν
  have h1 := congrArg (fun μ => μ Set.univ) key
  simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.measure_univ] at h1
  rw [ENNReal.smul_def, smul_eq_mul, mul_one, eq_comm, ENNReal.coe_eq_one] at h1
  rw [key, h1, one_smul]

/-! ### The inseparable locus is Haar-null -/

section InseparableNull

open MeasureTheory Polynomial

section Res
variable {K : Type} [Field K]

/-- The resultant of `f` and `f'` computed in formal degrees `(n, n - 1)` is a power of the leading
  coefficient times the usual resultant. -/
private theorem resultant_deriv_eq (f : K[X]) (n : ℕ) (hn : f.natDegree = n) :
    resultant f (derivative f) n (n-1) =
      f.coeff n ^ (n - 1 - (derivative f).natDegree) * resultant f (derivative f) := by
  have hd : (derivative f).natDegree ≤ n - 1 := hn ▸ natDegree_derivative_le f
  have := resultant_add_right_deg (f := f) (g := derivative f) (m := n)
    (n := (derivative f).natDegree) (n - 1 - (derivative f).natDegree) le_rfl
  rw [Nat.add_sub_cancel' hd] at this
  rw [this, ← hn]

/-- A nonzero polynomial of degree `n` whose resultant with its derivative in degrees `(n, n - 1)`
  is nonzero is separable. -/
theorem separable_of_resultant (f : K[X]) (n : ℕ) (hn : f.natDegree = n) (hf : f ≠ 0)
    (h : resultant f (derivative f) n (n - 1) ≠ 0) : f.Separable := by
  rw [resultant_deriv_eq f n hn] at h
  have h2 : resultant f (derivative f) ≠ 0 := right_ne_zero_of_mul h
  rw [Ne, resultant_eq_zero_iff] at h2
  push Not at h2
  exact h2 (Or.inl hf)

/-- A nonzero separable polynomial of degree `n` has nonzero resultant with its derivative in
  degrees `(n, n - 1)`. -/
theorem resultant_ne_zero_of_separable (f : K[X]) (n : ℕ) (hn : f.natDegree = n) (hf : f ≠ 0)
    (hs : f.Separable) : resultant f (derivative f) n (n-1) ≠ 0 := by
  rw [resultant_deriv_eq f n hn]
  refine mul_ne_zero (pow_ne_zero _ ?_) (resultant_ne_zero f _ hs)
  rw [← hn]; exact leadingCoeff_ne_zero.mpr hf
end Res

/-- The generic monic polynomial `X^n + Σ aᵢ Xⁱ` over `ℤ[a₀, …, a_{n-1}]`. -/
private noncomputable def genericMonic (n : ℕ) : Polynomial (MvPolynomial (Fin n) ℤ) :=
  X ^ n + ∑ i : Fin n, C (MvPolynomial.X i) * X ^ i.val
/-- The generic polynomial `Σ_{i ≤ n} aᵢ Xⁱ` over `ℤ[a₀, …, a_n]`. -/
private noncomputable def genericAffine (n : ℕ) : Polynomial (MvPolynomial (Fin (n+1)) ℤ) :=
  ∑ i : Fin (n+1), C (MvPolynomial.X i) * X ^ i.val
/-- The discriminant-type resultant of the generic monic polynomial and its derivative. -/
private noncomputable def discMonic (n : ℕ) : MvPolynomial (Fin n) ℤ :=
  resultant (genericMonic n) (derivative (genericMonic n)) n (n-1)
/-- The discriminant-type resultant of the generic polynomial of degree `n` and its derivative. -/
noncomputable def discAffine (n : ℕ) : MvPolynomial (Fin (n+1)) ℤ :=
  resultant (genericAffine n) (derivative (genericAffine n)) n (n-1)

variable (O : Type) [CommRing O] [IsDomain O]

/-- Specialization `ℤ[a] → Frac O` sending the generic coefficients to `a`. -/
private noncomputable def specHom {m : ℕ} (a : Fin m → O) :
    MvPolynomial (Fin m) ℤ →+* BaseField O :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) fun i ↦ algebraMap O (BaseField O) (a i)

omit [IsDomain O] in
/-- The monic polynomial with coefficients `a` is the specialization of the generic monic
  polynomial. -/
private theorem monicPolynomial_eq_map {n : ℕ} (a : Fin n → O) :
    monicPolynomial O a = (genericMonic n).map (specHom O a) := by
  simp [monicPolynomial, genericMonic, specHom, Polynomial.map_sum]

omit [IsDomain O] in
/-- The polynomial with coefficients `a` is the specialization of the generic polynomial. -/
private theorem affinePolynomial_eq_map {n : ℕ} (a : Fin (n + 1) → O) :
    affinePolynomial O a = (genericAffine n).map (specHom O a) := by
  simp [affinePolynomial, genericAffine, specHom, Polynomial.map_sum]

omit [IsDomain O] in
/-- Specialization agrees with evaluating the polynomial mapped to `O`, then passing to `Frac O`. -/
private theorem specHom_eq {m : ℕ} (a : Fin m → O) (D : MvPolynomial (Fin m) ℤ) :
    specHom O a D = algebraMap O (BaseField O)
      (MvPolynomial.eval a (MvPolynomial.map (Int.castRingHom O) D)) := by
  induction D using MvPolynomial.induction_on with
  | C z => simp [specHom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.map_X, map_mul, map_mul, MvPolynomial.eval_X, ← hp]
    simp [specHom]

omit [IsDomain O] in
/-- The resultant of a monic polynomial with its derivative is the evaluation of `discMonic` at its
  coefficients. -/
private theorem monic_resultant_eq {n : ℕ} (a : Fin n → O) :
    resultant (monicPolynomial O a) (derivative (monicPolynomial O a)) n (n-1) =
      algebraMap O (BaseField O)
        (MvPolynomial.eval a (MvPolynomial.map (Int.castRingHom O) (discMonic n))) := by
  rw [← specHom_eq, monicPolynomial_eq_map, derivative_map, resultant_map_map]; rfl

omit [IsDomain O] in
/-- The resultant of a polynomial with its derivative is the evaluation of `discAffine` at its
  coefficients. -/
theorem affine_resultant_eq {n : ℕ} (a : Fin (n + 1) → O) :
    resultant (affinePolynomial O a) (derivative (affinePolynomial O a)) n (n-1) =
      algebraMap O (BaseField O)
        (MvPolynomial.eval a (MvPolynomial.map (Int.castRingHom O) (discAffine n))) := by
  rw [← specHom_eq, affinePolynomial_eq_map, derivative_map, resultant_map_map]; rfl

/-- Over a domain there is a separable monic polynomial of every degree over the fraction field. -/
theorem exists_separable_monic (n : ℕ) : ∃ a : Fin n → O, (monicPolynomial O a).Separable := by
  rcases n with _ | k
  · exact ⟨Fin.elim0, by simp [monicPolynomial]⟩
  by_cases h : ((k+1 : ℕ) : BaseField O) = 0
  · rcases k with _ | k
    · simp at h
    refine ⟨Pi.single 1 (-1), ?_⟩
    have he : monicPolynomial O (Pi.single (1 : Fin (k+2)) (-1 : O)) = X ^ (k+2) - X := by
      simp [monicPolynomial, Fin.sum_univ_succ, Pi.single_apply, sub_eq_add_neg,
        Fin.succ_succ_ne_one]
      ring
    rw [he]
    have hd : derivative (X ^ (k+2) - X : Polynomial (BaseField O)) = -1 := by
      simp only [derivative_sub, derivative_X_pow, derivative_X]
      rw [show ((k+2 : ℕ) : BaseField O) = 0 by exact_mod_cast h]
      simp
    rw [Polynomial.Separable, hd]
    exact isCoprime_one_right.neg_right
  · refine ⟨Pi.single 0 (-1), ?_⟩
    have he : monicPolynomial O (Pi.single (0 : Fin (k+1)) (-1 : O)) = X ^ (k+1) - 1 := by
      simp [monicPolynomial, Fin.sum_univ_succ, Pi.single_apply, sub_eq_add_neg]
    rw [he]
    exact (X_pow_sub_one_separable_iff).2 h

variable [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]

/-- The zero locus of a polynomial that does not vanish identically on `O^m` is null for the
  coefficient measure. -/
theorem coefficientMeasure_zero_null (htop : IsAdic (IsLocalRing.maximalIdeal O)) (m : ℕ)
    (P : MvPolynomial (Fin m) O) (a₀ : Fin m → O) (h₀ : MvPolynomial.eval a₀ P ≠ 0) :
    coefficientMeasure O m {a | MvPolynomial.eval a P = 0} = 0 := by
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := coefficient_measure_probability O htop 1
  set ν := (coefficientMeasure O 1).map (LinearEquiv.funUnique (Fin 1) O O) with hν
  have h := coefficient_measure_pi_one O htop pi hpi m
  rw [h.1]
  have : MeasureTheory.Measure.IsAddLeftInvariant (coefficientMeasure O 1) := by
    unfold coefficientMeasure
    infer_instance
  have : NullSingletonClass ν := ⟨fun x => by
    rw [hν, Measure.map_apply h.2.2.2.2.1 (measurableSet_singleton x)]
    have hpre : (LinearEquiv.funUnique (Fin 1) O O) ⁻¹' {x} =
        (fun b : Fin 1 → O => (fun _ => -x) + b) ⁻¹' {b : Fin 1 → O | b 0 = 0} := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, LinearEquiv.funUnique_apply,
        Set.mem_ofPred_eq, Pi.add_apply]
      rw [show (default : Fin 1) = 0 from rfl, neg_add_eq_zero, eq_comm]
    rw [hpre, measure_preimage_add]
    exact (coordinate_hyperplane_null O htop 1 0).2⟩
  exact mvPolynomial_zero_null ν m P (fun hP => h₀ (by rw [hP, map_zero]))

/-- The coefficients of inseparable monic polynomials form a null set for the coefficient measure.
-/
theorem monic_inseparable_null (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    coefficientMeasure O n {a | ¬ (monicPolynomial O a).Separable} = 0 := by
  obtain ⟨a₀, h₀⟩ := exists_separable_monic O n
  have hdeg := fun a => monic_polynomial_degree O n a
  refine measure_mono_null (fun a ha => ?_) (coefficientMeasure_zero_null O htop n
    (MvPolynomial.map (Int.castRingHom O) (discMonic n)) a₀ ?_)
  · simp only [Set.mem_ofPred_eq] at ha ⊢
    by_contra hne
    apply ha
    refine separable_of_resultant _ n (hdeg a).2 (hdeg a).1.ne_zero ?_
    rw [monic_resultant_eq]
    exact fun h => hne ((IsFractionRing.injective O (BaseField O)) (by rw [h, map_zero]))
  · have := resultant_ne_zero_of_separable _ n (hdeg a₀).2 (hdeg a₀).1.ne_zero h₀
    rw [monic_resultant_eq] at this
    exact fun h => this (by rw [h, map_zero])

end InseparableNull

open scoped Classical in
/-- Coordinate cosets of level `M ≥ cellDegree` give a finite measurable partition of the coordinate
  space, and the preimage of a cell in any chart is the union of the cosets whose representatives
  lie in the cell. -/
theorem member_cell_chart_coset_decomposition (m : ConcreteMember) (c : m.toMeasured.cellIndex)
    (Mlev : ℕ) (hM : m.toMeasured.cellDegree c ≤ Mlev) :
    ∃ reps : Finset (Fin m.s.degree → m.O),
      (∀ z : Fin m.s.degree → m.O, ∃! z₀, z₀ ∈ reps ∧ adicCongr (Ideal.span {m.S.pi}) Mlev z z₀) ∧
      (∀ z₀ : Fin m.s.degree → m.O, MeasurableSet (coordinateCoset m.S.pi Mlev z₀)) ∧
      (reps : Set (Fin m.s.degree → m.O)).PairwiseDisjoint
      (fun z₀ => coordinateCoset m.S.pi Mlev z₀) ∧ ∀ i : m.atlas.ι,
        coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b ⁻¹' m.toMeasured.cell c =
        ⋃ z₀ ∈ reps.filter
        (fun z₀ => coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b z₀ ∈
        m.toMeasured.cell c), coordinateCoset m.S.pi Mlev z₀ := by
  obtain ⟨reps, hreps⟩ :=
      coordinate_coset_representatives_exist m.O m.S.pi
      (by rw [m.hS_pi]; exact m.hpi) m.s.degree Mlev
  have hmax : Ideal.span {m.S.pi} = IsLocalRing.maximalIdeal m.O := by
    rw [m.hS_pi]; exact ((m.hpi).maximalIdeal_eq).symm
  have hmeas : ∀ z₀ : Fin m.s.degree → m.O, MeasurableSet (coordinateCoset m.S.pi Mlev z₀) := by
    intro z₀
    have h := finite_coordinate_borel_cylinders m.O (IsLocalRing.maximalIdeal m.O) m.htop m.s.degree
    have : @MeasurableSet _
        (adicCylinderSpace (IsLocalRing.maximalIdeal m.O) (Fin m.s.degree → m.O))
        (coordinateCoset m.S.pi Mlev z₀) := MeasurableSpace.measurableSet_generateFrom
      (.inr ⟨Mlev, z₀, by unfold coordinateCoset; rw [hmax]⟩)
    rwa [← h] at this
  refine ⟨reps, hreps, hmeas, fun z₁ h₁ z₂ h₂ hne ↦ Set.disjoint_left.2 fun z hz1 hz2 ↦ ?_, ?_⟩
  · obtain ⟨w, _, hw⟩ := hreps z
    exact hne ((hw z₁ ⟨h₁, hz1⟩).trans (hw z₂ ⟨h₂, hz2⟩).symm)
  intro i
  obtain ⟨hinj, -, -⟩ := concrete_member_charts m i
  have hf : Ideal.span {(m.atlas.chart i).f} ∈ surfaceStateSet m.O m.R m.S m.s :=
    m.atlas.cover.symm.subset <| Set.mem_iUnion.2
      ⟨i, ⟨_, rfl⟩, by rw [Ideal.map_span, Set.image_singleton]⟩
  obtain ⟨hpart, -⟩ := fixed_tangent_cell_chart_partition m.O m.R m.S m.s m.s.degree
    (m.atlas.chart i).b (m.atlas.chart i).f hf hinj (m.toMeasured.cellDegree c) Mlev hM c.2.1 reps
    hreps
  have hstate : ∀ z₀, coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b z₀ ∈
      surfaceStateSet m.O m.R m.S m.s := fun z₀ ↦ by
    change Ideal.span {_ + coordinateLift _ _} ∈ _
    rw [coordinateLift_smul_eq_mul]
    exact surface_state_vertical_perturbation m.O m.R m.S m.s (m.atlas.chart i).f _ hf
  rw [Finset.filter_congr fun z₀ _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨hstate z₀, h⟩⟩]
  have h2 := congrArg
    (fun T ↦ coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b ⁻¹' T) hpart
  simp only [Set.preimage_inter_range] at h2
  refine h2.trans ?_
  simp only [Set.preimage_iUnion₂, Set.preimage_image_eq _ hinj]
  rfl

private theorem member_chart_measurableEmbedding (m : ConcreteMember) (g : m.toMeasured.R)
    (hg : Ideal.span {g} ∈ m.toMeasured.stateSet)
    (bc : Fin m.toMeasured.s.degree → m.toMeasured.R)
    (E : m.toMeasured.R ≃ₗ[m.toMeasured.O]
      ((Fin m.toMeasured.s.degree → m.toMeasured.O) × m.toMeasured.R))
    (hE : ∀ w, E.symm w = divisionMap g bc w) :
    @MeasurableEmbedding _ _ inferInstance m.toMeasured.measurableSpaceIdeal
      (coordinateIdeal m.toMeasured.S.pi g bc) := by
  have hreg := (concrete_member_state_generator_regular m g hg).2.2
  have hvp := surface_vertical_parameter m.toMeasured.O m.toMeasured.R m.toMeasured.S
  have hpi' : Irreducible m.toMeasured.S.pi := by
    change Irreducible m.S.pi
    rw [m.hS_pi]; exact m.hpi
  have := concrete_member_division_module_isAdicComplete m
  exact coordinate_ideal_measurableEmbedding m.toMeasured.O m.toMeasured.htop m.toMeasured.R
    m.toMeasured.S.pi hpi' hvp.1 hvp.2 _ g bc ⟨⟨E, hE⟩, hreg⟩

/-- The product of child coordinate-ideal maps is a measurable embedding, and pushes the product
  state measure back to `Π_j q_j^(-deg_j)` times the product coefficient measure. -/
theorem member_product_chart_pushforward (ι : Type) [Fintype ι] (mc : ι → ConcreteMember)
    (g : ∀ j, (mc j).toMeasured.R) (hg : ∀ j, Ideal.span {g j} ∈ (mc j).toMeasured.stateSet)
    (bc' : ∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.R)
    (E' : ∀ j, (mc j).toMeasured.R ≃ₗ[(mc j).toMeasured.O]
      ((Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O) × (mc j).toMeasured.R))
    (hE' : ∀ j w, (E' j).symm w = divisionMap (g j) (bc' j) w) :
    (letI : ∀ j, MeasurableSpace (Ideal (mc j).toMeasured.R) :=
      fun j => (mc j).toMeasured.measurableSpaceIdeal; MeasurableEmbedding
        (fun (w : ∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O) (j : ι)
        => coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) (w j)) ∧
        ∀ Y : Set (∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O), MeasurableSet Y →
        MeasureTheory.Measure.pi (fun j => (mc j).toMeasured.μ)
        ((fun (w : ∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O) (j : ι)
        => coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) (w j)) '' Y) =
        (∏ j, ((mc j).toMeasured.q : ℝ≥0∞)⁻¹ ^ (mc j).toMeasured.s.degree) *
        MeasureTheory.Measure.pi
        (fun j => coefficientMeasure (mc j).toMeasured.O (mc j).toMeasured.s.degree) Y) := by
  set Ψ : (∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O) → ∀ j,
      Ideal (mc j).toMeasured.R :=
    fun w j ↦ coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) (w j)
  have hemb : MeasurableEmbedding Ψ :=
    measurableEmbedding_pi ι _ _ _
      (fun j => member_chart_measurableEmbedding (mc j) (g j) (hg j) (bc' j) (E' j) (hE' j))
  refine ⟨hemb, fun Y hY ↦ ?_⟩
  have : ∀ j, MeasureTheory.IsFiniteMeasure (mc j).toMeasured.μ :=
    fun j => (concrete_member_measure_finite_support (mc j)).1
  have : ∀ j, MeasureTheory.IsProbabilityMeasure
      (coefficientMeasure (mc j).toMeasured.O (mc j).toMeasured.s.degree) :=
    fun j => coefficient_measure_probability _ (mc j).toMeasured.htop _
  set C : ℝ≥0∞ := ∏ j, ((mc j).toMeasured.q : ℝ≥0∞)⁻¹ ^ (mc j).toMeasured.s.degree
  have hC0 : C ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦
    pow_ne_zero _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  have hCt : C ≠ ⊤ := ENNReal.prod_ne_top fun j _ ↦ ENNReal.pow_ne_top <| ENNReal.inv_ne_top.2 <|
    Nat.cast_ne_zero.2
      (Finite.one_lt_card (α := IsLocalRing.ResidueField (mc j).toMeasured.O)).ne_bot
  set κ := MeasureTheory.Measure.comap Ψ
      (MeasureTheory.Measure.pi (fun j => (mc j).toMeasured.μ))
  have hκapp : ∀ Z, MeasurableSet Z → κ Z =
      MeasureTheory.Measure.pi (fun j => (mc j).toMeasured.μ) (Ψ '' Z) :=
    fun Z hZ => MeasureTheory.Measure.comap_apply Ψ hemb.injective
      (fun s hs => hemb.measurableSet_image' hs) _ hZ
  have hbox : ∀ s : ∀ j, Set (Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O),
      Ψ '' Set.pi Set.univ s =
        Set.pi Set.univ (fun j => coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) '' s j) := by
    intro s
    ext y
    refine ⟨fun ⟨w, hw, hwy⟩ j _ ↦ hwy ▸ ⟨w j, hw j trivial, rfl⟩, fun hy ↦ ?_⟩
    choose w hw using fun j ↦ hy j trivial
    exact ⟨w, fun j _ ↦ (hw j).1, funext fun j ↦ (hw j).2⟩
  have hpi : MeasureTheory.Measure.pi
      (fun j => coefficientMeasure (mc j).toMeasured.O (mc j).toMeasured.s.degree)
      = C⁻¹ • κ := by
    apply MeasureTheory.Measure.pi_eq
    intro s hs
    rw [MeasureTheory.Measure.smul_apply, smul_eq_mul, hκapp _ (MeasurableSet.univ_pi hs), hbox,
      MeasureTheory.Measure.pi_pi, Finset.prod_congr rfl fun j _ ↦
        (concrete_member_division_chart_measure (mc j) (g j) (hg j) (bc' j) (E' j) (hE' j)).2.2 _
          (hs j), Finset.prod_mul_distrib, ← mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, one_mul]
  rw [← hκapp _ hY, hpi, MeasureTheory.Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hC0 hCt, one_mul]

/-! ### The child-order map of a blown-up curve -/

section ChildOrder

variable (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (t x : R)
  (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
  (hregSwap : RegularParameterPair R x t) [(Ideal.span ({t,x} : Set R)).IsMaximal]
  (hres : Function.Surjective (algebraMap O (R ⧸ Ideal.span {t,x})))
  [IsAdicComplete (Ideal.span {t,x}) R]

include hreg hregSwap hres

/-- The cokernel of the map from the surface to the curve-order limit has length `binom(d, 2)`. -/
private theorem curve_order_limit_cokernel_length (d : ℕ) (G : GluedGenerators R t x beta d)
    (hregF : ∀ j : ℕ, Function.Injective
      (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j =>
        Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
          ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    (σ : R →ₗ[R] CurveOrderLimit R t x beta G)
    (hσ : ∀ r : R, ∃ p : curveThreads R t x beta G, σ r = curveLimitMk R t x beta G p ∧ ∀ j : ℕ,
      p.val j = surfaceToChartPair R t x r) :
    Module.length O (CurveOrderLimit R t x beta G ⧸ LinearMap.range (σ.restrictScalars O)) =
      (chooseTwo d : ℕ∞) := by
  set J := max (d - 1) 1
  have hJ : d - 1 ≤ J := le_max_left _ _
  have hpres := fun j ↦ actual_cech_preserves_exceptional_lattices R t x beta d j
  obtain ⟨π, hπ⟩ := curve_limit_level_map_exists R t x beta d G J
  obtain ⟨δ, -, hδs, hδk⟩ := curve_sections_connecting_map_exists O R t x hreg beta hregSwap d G J
    (hpres J) (hregF J)
  let Θ := δ ∘ₗ (π.restrictScalars O)
  have hker : LinearMap.ker Θ = LinearMap.range (σ.restrictScalars O) := by
    ext u
    simp only [LinearMap.mem_ker, LinearMap.mem_range, LinearMap.restrictScalars_apply]
    constructor
    · intro hu
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      obtain ⟨r, hr⟩ := (hδk _).1 (show δ (π (curveLimitMk R t x beta G p)) = 0 from hu)
      rw [hπ p] at hr
      exact curve_limit_range_of_stable_level R t x beta d G hreg hregSwap hregF f hf J hJ σ hσ p
        ⟨r, (Submodule.Quotient.eq _).1 hr⟩
    · rintro ⟨r, rfl⟩
      obtain ⟨p, hp1, hp2⟩ := hσ r
      change δ (π (σ r)) = 0
      exact (hδk _).2 ⟨r, by rw [hp1, hπ p, hp2]⟩
  rw [((Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective Θ
    (hδs.comp (curve_limit_level_map_surjective R t x beta d G hreg J π hπ)))).length_eq]
  exact actual_finite_cech_coefficient_triangular O R t x hreg beta hregSwap hres d J hJ hpres

/-- The child-order map has kernel `(f)` and cokernel of length `binom(d, 2)`. -/
theorem child_order_index_and_kernel [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (D : TwoChartCurveData R t x beta) (d : ℕ)
    (G : GluedGenerators R t x beta d)
    (hregF : ∀ j : ℕ, Function.Injective
      (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j =>
        Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
          ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    (hclosed : (⨅ j : ℕ, (Ideal.span {f} ⊔ (Ideal.span {t,x})^j)) = Ideal.span {f})
    [∀ p : AllPoints D, IsLocalRing (localRing D p)]
    [∀ p : AllPoints D, IsNoetherianRing (localRing D p)]
    [∀ p : AllPoints D, IsAdicComplete (IsLocalRing.maximalIdeal (localRing D p)) (localRing D p)]
    [∀ p : AllPoints D, Algebra O (localRing D p)]
    (E : CurveOrderLimit R t x beta G ≃ₗ[O] childOrder D) (σ : R →ₗ[R] CurveOrderLimit R t x beta G)
    (hσ : ∀ r : R, ∃ p : curveThreads R t x beta G, σ r = curveLimitMk R t x beta G p ∧ ∀ j : ℕ,
      p.val j = surfaceToChartPair R t x r)
    (hE : ∀ (p : curveThreads R t x beta G) (r : R),
      (∀ j : ℕ, p.val j = surfaceToChartPair R t x r) → E (curveLimitMk R t x beta G p) =
      childOrderMap D r)
    (φ : R →ₗ[O] childOrder D) (hφ : ∀ r : R, φ r = childOrderMap D r) :
    RingHom.ker (childOrderMap D) = Ideal.span {f} ∧
      Module.length O ((childOrder D) ⧸ LinearMap.range φ) = (chooseTwo d : ℕ∞) := by
  have key : ∀ r : R, childOrderMap D r = E (σ r) := fun r ↦ by
    obtain ⟨p, hp1, hp2⟩ := hσ r
    rw [hp1, hE p r hp2]
  have hker := surface_to_curve_limit_kernel R t x beta d G hreg hregSwap hregF f hf hclosed σ hσ
  refine ⟨Ideal.ext fun r ↦ ?_, ?_⟩
  · rw [RingHom.mem_ker, key, LinearEquiv.map_eq_zero_iff, ← LinearMap.mem_ker, hker]
  · have hrange : (LinearMap.range (σ.restrictScalars O)).map
        (E : CurveOrderLimit R t x beta G →ₗ[O] childOrder D) = LinearMap.range φ := by
      ext y
      simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.coe_restrictScalars]
      constructor
      · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
        exact ⟨r, by rw [hφ, key]; rfl⟩
      · rintro ⟨r, rfl⟩
        exact ⟨σ r, ⟨r, rfl⟩, by rw [hφ, key]; rfl⟩
    rw [← curve_order_limit_cokernel_length O R t x hreg beta hregSwap hres d G hregF f hf σ hσ]
    exact (LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ E hrange)).symm

end ChildOrder

section ConcreteIndex

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
  (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)

-- Abbreviations for the concrete surface and its two parameters.
local notation "𝒮" => ConcreteSurface O pi u a b
local notation "𝒯" => surfaceT O pi u a b
local notation "𝒳" => surfaceX O pi u a b

include hpi ha in
/-- For a concrete surface, the child-order map is `O`-linear with kernel `(f)` and cokernel of
  length `binom(d, 2)`, where `d` is the curve degree. -/
theorem concrete_curve_order_index (beta : BlowupRestriction 𝒮 𝒯 𝒳)
    (D : TwoChartCurveData 𝒮 𝒯 𝒳 beta) (f : 𝒮) (G : GluedGenerators 𝒮 𝒯 𝒳 beta (curveDataDegree D))
    (hf : ∀ j : ℕ, surfaceToCechInput 𝒮 𝒯 𝒳 j f =
      (cechInputLattice 𝒮 𝒯 𝒳 j).mkQ (gluedFunctionPair 𝒮 𝒯 𝒳 G j))
    (hG : ∀ j : ℕ,
      Ideal.span {Ideal.Quotient.mk ((chartExceptional 𝒮 𝒯 𝒳)^j) (G.left j)} =
        leftLevelKernel D j ∧
      Ideal.span {Ideal.Quotient.mk ((chartExceptional 𝒮 𝒳 𝒯)^j) (G.right j)} =
        rightLevelKernel D j) :
    (letI : ∀ p : AllPoints D, Algebra O (localRing D p) :=
      fun p => ((localFromSurface D p).comp (algebraMap O 𝒮)).toAlgebra;
        ∃ φ : 𝒮 →ₗ[O] childOrder D, (∀ r : 𝒮, φ r = childOrderMap D r) ∧
        RingHom.ker (childOrderMap D) = Ideal.span {f} ∧
        Module.length O (childOrder D ⧸ LinearMap.range φ) =
        (chooseTwo (curveDataDegree D) : ℕ∞)) := by
  let _ : ∀ p : AllPoints D, Algebra O (localRing D p) := fun p ↦
    ((localFromSurface D p).comp (algebraMap O 𝒮)).toAlgebra
  have hreg := concrete_surface_regular_pair_tx O pi hpi.ne_zero u a b ha
  have hregSwap := concrete_surface_regular_pair_xt O pi hpi.ne_zero u a b ha
  have : (Ideal.span ({𝒯, 𝒳} : Set 𝒮)).IsMaximal :=
    concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha
  have : IsAdicComplete (Ideal.span ({𝒯, 𝒳} : Set 𝒮)) 𝒮 :=
    concrete_surface_isAdicComplete_parameterIdeal O pi u a b
  have := blowupChart_concrete_isNoetherianRing O pi u a b 𝒯 𝒳
  have := blowupChart_concrete_isNoetherianRing O pi u a b 𝒳 𝒯
  have := concrete_surface_isLocalRing O pi u a b hpi.not_isUnit ha
  have := concrete_surface_isNoetherianRing O pi u a b
  have hclosed : (⨅ j : ℕ, (Ideal.span {f} ⊔ (Ideal.span ({𝒯, 𝒳} : Set 𝒮))^j)) =
      Ideal.span {f} := by
    have := ideal_closed_noetherian_local 𝒮 (Ideal.span {f})
    rwa [concrete_surface_maximalIdeal_eq O pi hpi u a b ha] at this
  have h3 := (two_chart_datum_concrete_instances O pi hpi u a b ha beta D).2.2
  have : ∀ p : AllPoints D, IsNoetherianRing (localRing D p) := fun p ↦ (h3 p).1
  have : ∀ p : AllPoints D, IsLocalRing (localRing D p) := fun p ↦ (h3 p).2.choose
  have : ∀ p : AllPoints D,
      IsAdicComplete (IsLocalRing.maximalIdeal (localRing D p)) (localRing D p) :=
    fun p ↦ (h3 p).2.choose_spec.1
  obtain ⟨σ, hσ⟩ := surface_to_curve_limit_exists 𝒮 𝒯 𝒳 beta _ G
  obtain ⟨E, hE⟩ := child_order_equiv_linear 𝒮 𝒯 𝒳 beta D _ G hG
    (fun p ↦ (h3 p).2.choose_spec.2) O fun p o ↦ rfl
  let φ : 𝒮 →ₗ[O] childOrder D :=
    { toFun := fun r ↦ childOrderMap D r
      map_add' := fun r s ↦ map_add _ r s
      map_smul' := fun o r ↦ by
        rw [RingHom.id_apply, Algebra.smul_def o r, map_mul, Algebra.smul_def]
        congr 1 }
  refine ⟨φ, fun r ↦ rfl, child_order_index_and_kernel O 𝒮 𝒯 𝒳 hreg beta hregSwap ?_ D _ G
    (two_chart_left_generators_regular_on_overlap 𝒮 𝒯 𝒳 beta D _ G hG hreg hregSwap) f hf hclosed
    E σ hσ hE φ fun r ↦ rfl⟩
  intro y
  obtain ⟨e, he'⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨MvPowerSeries.constantCoeff s, e.injective ?_⟩
  have h2 := he' (MvPowerSeries.C (MvPowerSeries.constantCoeff s))
  simp only [MvPowerSeries.constantCoeff_C] at h2
  exact h2.trans (he' s).symm

end ConcreteIndex

end SurfaceBlowup
