/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Algebra.AlgebraType
import SurfaceBlowup.Unramified.Extension
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The primitive locus, state measures, and integral closures

Mass computations for the coefficient measure (the primitive locus of `O^(n+1)`, total masses of
state measures, the Haar property of the unramified coefficient measure), lifting lemmas for
generators of residue cells, and the structure of the integral closure of a complete DVR with
finite residue field in a finite extension of its fraction field (complete, local, a DVR),
with the `p`-adic specializations.

## Main results

* `primitive_locus_mass`: the primitive vectors of `O^(n+1)` have mass `1 - q^(-(n+1))`.
* `state_measure_total_mass`: an atlas with `N` charts has total state mass `N q^(-n)`.
* `unramified_coefficient_measure_haar`: the unramified coefficient measure is a Haar probability
  measure with the expected cylinder masses.
* `integral_closure_is_local`, `integral_closure_is_dvr`, `integral_closure_own_adic_complete`.
* `polynomial_type_degree`: a polynomial type is valid and has the polynomial's degree.

Provenance: `Thm_SurfaceBlowupV2_*`: `primitive_locus_mass`, `scaled_normalization_identity`,
`state_measure_total_mass`, `units_lift_from_local_quotient`,
`residue_ideal_has_fixed_generator_lift`, `unramified_coefficient_measure_haar`,
`integral_closure_{adic_complete, finite_reduction, is_local, is_dvr, own_adic_complete}`,
`irreducible_factor_invariant_degree`, `polynomial_type_degree`,
`padicIntegers_{isDVR, maximal_adic_complete, residueField_finite}`,
`quotient_ring_length_intrinsic`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-- The primitive vectors of `O^(n+1)` (some coordinate a unit) have coefficient measure
`1 - q^(-(n+1))`. -/
theorem primitive_locus_mass (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    coefficientMeasure O (n+1) {a | primitive O a} =
      1-(Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(n+1) := by
  have h1 := coefficient_cylinder_mass O htop (n+1) 1 0
  have h0 := coefficient_cylinder_mass O htop (n+1) 0 0
  simp only [pow_zero, mul_zero, Ideal.one_eq_top, Submodule.mem_top, implies_true,
    Set.ofPred_true, Pi.zero_apply, sub_zero, mul_one, pow_one] at h1 h0
  have hS : {a : Fin (n+1) → O | primitive O a} =
      {b : Fin (n+1) → O | ∀ i, b i ∈ IsLocalRing.maximalIdeal O}ᶜ := by
    ext a
    simp [primitive, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hopen : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
    simpa using (isAdic_iff.mp htop).1 1
  have hm : MeasurableSet {b : Fin (n+1) → O | ∀ i, b i ∈ IsLocalRing.maximalIdeal O} := by
    have : {b : Fin (n+1) → O | ∀ i, b i ∈ IsLocalRing.maximalIdeal O} =
        Set.univ.pi fun _ ↦ ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
      ext; simp
    rw [this]
    exact MeasurableSet.univ_pi fun _ ↦ hopen.measurableSet
  rw [hS]
  have hne : (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (n+1) ≠ ⊤ :=
    ENNReal.pow_ne_top <| ENNReal.inv_ne_top.mpr <|
      Nat.cast_ne_zero.2 (Nat.card_pos (α := IsLocalRing.ResidueField O)).ne'
  have hadd := measure_add_measure_compl (μ := coefficientMeasure O (n+1)) hm
  rw [h1, h0, add_comm] at hadd
  exact ENNReal.eq_sub_of_add_eq hne hadd

/-- The normalization identity `(1 + π v)(f + π ∑ zᵢ bᵢ) = f + π E⁻¹(s + remainder s)` for a
division chart. -/
theorem scaled_normalization_identity (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (pi : O) (f : R) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    (hE : ∀ s, E.symm s = divisionMap f b s) (s : (Fin n → O) × R) :
    (1 + pi • s.2) * (f + pi • coordinateLift b s.1) =
      f + pi • E.symm (adicPerturb (coordinateRemainder pi b E) s) := by
  simp only [adicPerturb, coordinateRemainder, map_add, map_smul, LinearEquiv.symm_apply_apply]
  rw [hE, divisionMap]
  simp only [Algebra.smul_def]
  ring

/-- An atlas whose chart maps are measurable has total state mass `#charts · q^(-n)`. -/
theorem state_measure_total_mass (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) [CommRing R] [Algebra O R]
    [MeasurableSpace (Ideal R)] (pi : O) (n : ℕ) (X : Set (Ideal R))
    (A : IdealAtlas O R pi n X)
    (hA : ∀ i, Measurable (coordinateIdeal pi (A.chart i).f (A.chart i).b)) :
    stateMeasure O R pi n (Nat.card (IsLocalRing.ResidueField O)) A Set.univ =
      (Fintype.card A.ι : ℝ≥0∞) * (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^n := by
  unfold stateMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  have h : ∀ i : A.ι, chartMeasure O R pi n (A.chart i) Set.univ = 1 := fun i =>
    chart_measure_total_mass O R htop pi n (A.chart i) (hA i)
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  rw [mul_comm]

/-- Units of `R/I` lift to units of `R` when `I` lies in the maximal ideal of the local ring `R`. -/
theorem units_lift_from_local_quotient (R : Type) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) (v : (R ⧸ I)ˣ) :
    ∃ u : Rˣ, Ideal.Quotient.mk I (u : R) = (v : R ⧸ I) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v : R ⧸ I)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((v⁻¹ : (R ⧸ I)ˣ) : R ⧸ I)
  have hab : a * b - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hb, map_one]
    simp
  have hunit : IsUnit a := by
    by_contra h
    have ham : a ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).2 h
    have h1 : a * b - (a * b - 1) ∈ IsLocalRing.maximalIdeal R :=
      Ideal.sub_mem _ (Ideal.mul_mem_right b _ ham) (hI hab)
    simp at h1
  exact ⟨hunit.unit, by simpa using ha⟩

/-- Every ideal in the residue cell of a regular `f` has a generator of the form `f + π h`. -/
theorem residue_ideal_has_fixed_generator_lift (R : Type) [CommRing R] [IsLocalRing R] (pi f : R)
    (hp : pi ∈ IsLocalRing.maximalIdeal R)
    (hf : Function.Injective
      (fun x : R ⧸ Ideal.span {pi} => x * Ideal.Quotient.mk (Ideal.span {pi}) f))
    (J : Ideal R) (hJ : J ∈ residueIdealCell pi f) :
    ∃ h : R, J = Ideal.span {f + pi*h} := by
  obtain ⟨⟨g, rfl⟩, hmap⟩ := hJ
  rw [Ideal.map_span, Set.image_singleton] at hmap
  obtain ⟨v, hv⟩ := regular_principal_generators_associated _ _ _ hf hmap.symm
  have hle : Ideal.span {pi} ≤ IsLocalRing.maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).2 hp
  obtain ⟨u, hu⟩ := units_lift_from_local_quotient R _ hle v
  have hmem : g - (u : R) * f ∈ Ideal.span {pi} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu, ← hv, sub_self]
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨(↑u⁻¹ : R) * k, ?_⟩
  have : f + pi * ((↑u⁻¹ : R) * k) = (↑u⁻¹ : R) * g := by
    have hg : g = (u : R) * f + k * pi := by rw [hk]; ring
    rw [hg, mul_add, ← mul_assoc (↑u⁻¹ : R), Units.inv_mul, one_mul]; ring
  rw [this, eq_comm]
  exact Ideal.span_singleton_mul_left_unit (Units.isUnit _) _

/-- The unramified coefficient measure on `O[X]/(Φ)` is an additive Haar probability measure,
and the ball `x + (base ideal)^L` has mass `q^(-δL)`. -/
theorem unramified_coefficient_measure_haar (O : Type) [CommRing O] [IsDomain O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] (Φ : Polynomial O) (hm : Φ.Monic)
    [TopologicalSpace (AdjoinRoot Φ)]
    (hτ : ‹TopologicalSpace (AdjoinRoot Φ)› = unramifiedTopology O Φ hm)
    [MeasurableSpace (AdjoinRoot Φ)]
    (hmeas : ‹MeasurableSpace (AdjoinRoot Φ)› = unramifiedMeasurableSpace O Φ hm)
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (htop : IsAdic (IsLocalRing.maximalIdeal O)) :
    Measure.IsAddHaarMeasure (unramifiedCoefficientMeasure O Φ hm) ∧
      IsProbabilityMeasure (unramifiedCoefficientMeasure O Φ hm) ∧ ∀ (L : ℕ) (x : AdjoinRoot Φ),
      unramifiedCoefficientMeasure O Φ hm {y | y - x ∈ (baseIdeal O Φ) ^ L} =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (Φ.natDegree * L) := by
  obtain ⟨hTR, hC, hT2, hSC, hB, hce, hces, hme, hmes⟩ :=
    power_coordinates_transport O Φ hm hτ hmeas
  set e := powerCoordinates O Φ hm
  have hprob := coefficient_measure_probability O htop Φ.natDegree
  have hμ : Measure.IsAddHaarMeasure (coefficientMeasure O Φ.natDegree) := by
    unfold coefficientMeasure
    apply Measure.IsAddHaarMeasure.smul
    · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
    · exact ENNReal.inv_ne_top.mpr
        (Measure.IsOpenPosMeasure.open_pos _ isOpen_univ Set.univ_nonempty)
  refine ⟨Measure.isAddHaarMeasure_map_of_isFiniteMeasure (coefficientMeasure O Φ.natDegree)
      e.symm.toLinearMap.toAddMonoidHom hces e.symm.surjective,
    Measure.isProbabilityMeasure_map hmes.aemeasurable, fun L x ↦ ?_⟩
  let E : AdjoinRoot Φ ≃ᵐ (Fin Φ.natDegree → O) :=
    { toEquiv := e.toEquiv, measurable_toFun := hme, measurable_invFun := hmes }
  rw [show unramifiedCoefficientMeasure O Φ hm =
    Measure.map E.symm (coefficientMeasure O Φ.natDegree) from rfl, MeasurableEquiv.map_apply]
  have hset : E.symm ⁻¹' {y | y - x ∈ (baseIdeal O Φ) ^ L} =
      {b | ∀ i, b i - e x i ∈ (IsLocalRing.maximalIdeal O) ^ L} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [base_ideal_coordinates O Φ hm L]
    have key : ∀ z i, (AdjoinRoot.powerBasis' hm).basis.repr z i = e z i := fun z i => rfl
    have hEv : E.symm v = e.symm v := rfl
    simp only [map_sub, Finsupp.coe_sub, Pi.sub_apply, key, hEv, LinearEquiv.apply_symm_apply]
    rfl
  rw [hset]
  exact coefficient_cylinder_mass O htop Φ.natDegree L (e x)

/-- The integral closure of a complete DVR in a finite extension (assumed `O`-finite) is
`𝔪_O`-adically complete. -/
private theorem integral_closure_adic_complete (O K L : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L]
    [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Module.Finite O (integralClosure O L)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] :
    IsAdicComplete (IsLocalRing.maximalIdeal O) (integralClosure O L) := by
  obtain ⟨h1, h2, -⟩ := integral_closure_finite_free O K L
  exact finite_free_adic_complete O (integralClosure O L) _

/-- The integral closure has finite reduction modulo `𝔪_O`. -/
private theorem integral_closure_finite_reduction (O K L : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L]
    [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Module.Finite O (integralClosure O L)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] :
    Finite (integralClosure O L ⧸
      (IsLocalRing.maximalIdeal O).map (algebraMap O (integralClosure O L))) := by
  obtain ⟨h1, h2, -⟩ := integral_closure_finite_free O K L
  have : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
  have hfin := finite_free_residue_quotient O (integralClosure O L)
    (IsLocalRing.maximalIdeal O)
  rw [Ideal.smul_top_eq_map] at hfin
  exact Finite.of_equiv _ (Submodule.Quotient.restrictScalarsEquiv O _).toEquiv

/-- The integral closure of a complete DVR with finite residue field in a finite extension
(assumed `O`-finite) is a local ring. -/
theorem integral_closure_is_local (O K L : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L]
    [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Module.Finite O (integralClosure O L)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] :
    IsLocalRing (integralClosure O L) := by
  have h1 := integral_closure_adic_complete O K L
  have h2 := integral_closure_finite_reduction O K L
  have : IsAdicComplete ((IsLocalRing.maximalIdeal O).map
      (algebraMap O (integralClosure O L))) (integralClosure O L) :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr h1
  exact complete_domain_finite_quotient_local (integralClosure O L)
    ((IsLocalRing.maximalIdeal O).map (algebraMap O (integralClosure O L)))

/-- The integral closure of a complete DVR with finite residue field in a finite extension
(assumed `O`-finite) is a DVR. -/
theorem integral_closure_is_dvr (O K L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L] [Algebra O L]
    [IsScalarTower O K L] [FiniteDimensional K L] [Module.Finite O (integralClosure O L)]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] :
    IsDiscreteValuationRing (integralClosure O L) := by
  have := integral_closure_is_local O K L
  have hD := integral_closure_is_dedekind O K L
  have hN : IsNoetherianRing (integralClosure O L) := inferInstance
  exact ((IsDiscreteValuationRing.TFAE (R := integralClosure O L)
    (integral_closure_not_field O K L)).out 0 2).mpr hD

/-- The integral closure is complete for its own maximal ideal. -/
theorem integral_closure_own_adic_complete (O K L : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L]
    [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Module.Finite O (integralClosure O L)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (hlocal : IsLocalRing (integralClosure O L)) :
    letI : IsLocalRing (integralClosure O L) := hlocal
    IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure O L)) (integralClosure O L) := by
  have : IsLocalRing (integralClosure O L) := hlocal
  have : IsDiscreteValuationRing (integralClosure O L) :=
    integral_closure_is_dvr O K L
  have hc := integral_closure_adic_complete O K L
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro a b h
    have h2 : algebraMap O L a = algebraMap O L b := by
      simpa using congrArg (fun x : integralClosure O L => (x : L)) h
    simp only [IsScalarTower.algebraMap_apply O K L] at h2
    exact IsFractionRing.injective O K ((algebraMap K L).injective h2)
  have : Algebra.IsIntegral O (integralClosure O L) := integralClosure.AlgebraIsIntegral
  have : FaithfulSMul O (integralClosure O L) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h512 := dvr_extension_maximalIdeal_map_eq_pow O (integralClosure O L) hinj
  have hI : (IsLocalRing.maximalIdeal O).map (algebraMap O (integralClosure O L)) ≤
      IsLocalRing.maximalIdeal (integralClosure O L) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap]
    by_contra hn
    have hu : IsUnit (algebraMap O (integralClosure O L) x) := by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hn
    exact (IsLocalRing.mem_maximalIdeal x).1 hx ((isUnit_map_iff _ x).1 hu)
  have h1 := (IsAdicComplete.map_algebraMap_iff (S := integralClosure O L)
    (I := IsLocalRing.maximalIdeal O) (M := integralClosure O L)).2 hc
  exact (adic_complete_iff_of_pow_le (integralClosure O L) (integralClosure O L) _ _
    _ (le_of_eq h512.symm) hI).1 h1

/-- For a monic irreducible `g` with `O`-finite integral closure, the factor invariants `(f, e)`
are positive with `f e = deg g`. -/
private theorem irreducible_factor_invariant_degree (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (g : Polynomial (BaseField O)) (hg : g.Monic)
    (hirr : Irreducible g) (hfin : Module.Finite O (integralClosure O (AdjoinRoot g))) :
    0 < (factorInvariant O g).1 ∧ 0 < (factorInvariant O g).2 ∧
      (factorInvariant O g).1 * (factorInvariant O g).2 = g.natDegree := by
  have : Fact (Irreducible g) := ⟨hirr⟩
  have : Module.Finite (BaseField O) (AdjoinRoot g) := hg.finite_adjoinRoot
  have hloc := integral_closure_is_local O (BaseField O) (AdjoinRoot g)
  have h := integral_closure_invariants_degree O (BaseField O) (AdjoinRoot g) hloc
  have hdeg : Module.finrank (BaseField O) (AdjoinRoot g) = g.natDegree :=
    finrank_quotient_span_eq_natDegree
  unfold factorInvariant
  rw [dif_pos hloc]
  exact ⟨h.1, h.2.1, h.2.2.trans hdeg⟩

/-- A polynomial type of `F` is a valid factor type of degree `deg F`. -/
theorem polynomial_type_degree (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (F : Polynomial (BaseField O)) (σ : FactorType) (hF : HasPolynomialTypeF O F σ) :
    ValidType σ ∧ typeDegree σ=F.natDegree := by
  obtain ⟨gs, hgs, -, rfl, rfl, hfin⟩ := hF
  constructor
  · intro z hz
    rw [Multiset.mem_coe, List.mem_map] at hz
    obtain ⟨g, hg, rfl⟩ := hz
    have := irreducible_factor_invariant_degree O g (hgs g hg).1 (hgs g hg).2 (hfin g hg)
    exact ⟨this.1, this.2.1⟩
  · induction gs with
    | nil => simp [typeDegree]
    | cons g gs ih =>
      have hg := hgs g (by simp)
      have ht : ∀ h ∈ gs, h.Monic ∧ Irreducible h := fun h hh => hgs h (by simp [hh])
      have hm : gs.prod.Monic := by
        simpa using Polynomial.monic_multiset_prod_of_monic (gs : Multiset _) id
          (fun h hh => (ht h (by simpa using hh)).1)
      have := irreducible_factor_invariant_degree O g hg.1 hg.2 (hfin g (by simp))
      have ih' := ih ht (fun h hh => hfin h (by simp [hh]))
      simp only [typeDegree, List.map_cons, ← Multiset.cons_coe, Multiset.map_cons,
        Multiset.sum_cons, List.prod_cons] at ih' ⊢
      rw [Polynomial.Monic.natDegree_mul hg.1 hm, ih', this.2.2]

/-- The ring of integers of a finite extension of `ℚ_[p]` is a DVR. -/
theorem padicIntegers_isDVR (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra ℚ_[p] K]
    [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] :
    IsDiscreteValuationRing (padicIntegers p K) := by
  have : Algebra.IsSeparable ℚ_[p] K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).toEquiv.symm
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
  exact integral_closure_is_dvr ℤ_[p] ℚ_[p] K

/-- The ring of integers of a finite extension of `ℚ_[p]` is complete for its maximal ideal. -/
theorem padicIntegers_maximal_adic_complete (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (hdvr : IsDiscreteValuationRing (padicIntegers p K)) :
    letI := hdvr
    IsAdicComplete (IsLocalRing.maximalIdeal (padicIntegers p K)) (padicIntegers p K) := by
  have := hdvr
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod p) PadicInt.residueField.toEquiv.symm
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
  exact integral_closure_own_adic_complete ℤ_[p] ℚ_[p] K inferInstance

/-- The ring of integers of a finite extension of `ℚ_[p]` has finite residue field. -/
theorem padicIntegers_residueField_finite (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (hdvr : IsDiscreteValuationRing (padicIntegers p K)) :
    letI := hdvr; Finite (IsLocalRing.ResidueField (padicIntegers p K)) := by
  have := hdvr
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv _ PadicInt.residueField.symm.toEquiv
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
  have h1 : Finite (integralClosure ℤ_[p] K ⧸
      (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (integralClosure ℤ_[p] K))) :=
    integral_closure_finite_reduction ℤ_[p] ℚ_[p] K
  have h2 := (integral_local_extension_unique_prime ℤ_[p] (padicIntegers p K)).1
  have hle : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (padicIntegers p K)) ≤
      IsLocalRing.maximalIdeal (padicIntegers p K) := by
    rw [Ideal.map_le_iff_le_comap, h2]
  exact Finite.of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)

/-- The length of a quotient ring over itself depends only on its ring isomorphism class. -/
theorem quotient_ring_length_intrinsic (S S' : Type) [CommRing S] [CommRing S'] (I : Ideal S)
    (J : Ideal S') (e : (S ⧸ I) ≃+* (S' ⧸ J)) :
    Module.length S (S ⧸ I) = Module.length S' (S' ⧸ J) := by
  rw [Module.length_eq_of_surjective (R := S ⧸ I) (M := S ⧸ I) Ideal.Quotient.mk_surjective,
    Module.length_eq_of_surjective (R := S' ⧸ J) (M := S' ⧸ J) Ideal.Quotient.mk_surjective]
  have : RingHomSurjective (e : (S ⧸ I) →+* (S' ⧸ J)) := ⟨e.surjective⟩
  let f : (S ⧸ I) →ₛₗ[(e : (S ⧸ I) →+* (S' ⧸ J))] (S' ⧸ J) :=
    ⟨(e : (S ⧸ I) →+* (S' ⧸ J)).toAddMonoidHom, by intro c x; simp⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

end SurfaceBlowup
