/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Unramified.FrobeniusDescent

/-!
# Types under unramified base change

Let `O → Oδ` be an unramified extension of complete DVRs of degree `δ` (in the applications
`Oδ = O[X]/(Φ)` for an unramified lift `Φ`). This file compares invariants and types over `O` and
over `Oδ`: the invariant `(e, f)` of a field over `Oδ` becomes `(e, δ f)` over `O`, so algebra types
descend by `scaleType δ`; the Frobenius of `Oδ` extends to the fraction fields with fixed field
`K = Frac O`, making `Kδ/K` finite separable; polynomial types ascend from `O` to `Oδ`; and a
Frobenius-invariant product of conjugates of a typed polynomial over `Oδ` descends to `O` with the
scaled type.

## Main results

* `SurfaceBlowup.field_invariant_unramified_tower`, `SurfaceBlowup.algebra_type_unramified_descent`
* `SurfaceBlowup.frobenius_fraction_extension`, `SurfaceBlowup.unramified_fraction_isSeparable`
* `SurfaceBlowup.factor_invariant_unramified_scale`, `SurfaceBlowup.polynomial_type_map_unramified`
* `SurfaceBlowup.descended_polynomial_type`

Provenance: Thm_SurfaceBlowupV2_{field_invariant_unramified_tower,
algebra_type_unramified_descent, factor_invariant_unramified_scale, frobenius_fraction_extension,
descended_polynomial_type}; Thm_Gen_UnramifiedAscent.
-/

namespace SurfaceBlowup

open Polynomial

/-! ### Invariants in an unramified tower -/

/-- `K`-isomorphic finite extensions of `K = Frac O` (one with finite closure) have the same
invariants, and the other one also has finite closure. -/
private theorem fieldInvariant_congr (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (L L' : Type) [Field L] [Field L']
    [Algebra (BaseField O) L] [Algebra O L] [IsScalarTower O (BaseField O) L]
    [FiniteDimensional (BaseField O) L] [Algebra (BaseField O) L'] [Algebra O L']
    [IsScalarTower O (BaseField O) L'] [FiniteDimensional (BaseField O) L']
    (e : L ≃ₐ[BaseField O] L') [Module.Finite O (integralClosure O L)] :
    fieldInvariant O L = fieldInvariant O L' ∧ Module.Finite O (integralClosure O L') := by
  obtain ⟨φ, -⟩ := integral_closure_algEquiv O L L' (e.restrictScalars O)
  exact ⟨field_invariant_algEquiv O L L' e inferInstance, .equiv φ.toLinearEquiv⟩

/-- In an unramified tower `O → Oδ` of degree `δ`, the invariant `(e, f)` of a finite extension
`L` over `Oδ` becomes `(e, δ f)` over `O`. -/
theorem field_invariant_unramified_tower (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ)
    (pi : O) (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi))
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (L : Type)
    [Field L] [Algebra O L] [Algebra Oδ L] [IsScalarTower O Oδ L] [Algebra (BaseField O) L]
    [IsScalarTower O (BaseField O) L] [FiniteDimensional (BaseField O) L] [Algebra (BaseField Oδ) L]
    [IsScalarTower Oδ (BaseField Oδ) L] [FiniteDimensional (BaseField Oδ) L]
    (hfinδ : Module.Finite Oδ (integralClosure Oδ L)) :
    fieldInvariant O L = ((fieldInvariant Oδ L).1, δ * (fieldInvariant Oδ L).2) := by
  -- `Oδ` is again complete with finite residue field
  have hmap : (IsLocalRing.maximalIdeal O).map (algebraMap O Oδ) = IsLocalRing.maximalIdeal Oδ := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer pi).1 hpi,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hpiδ, Ideal.map_span,
      Set.image_singleton]
  have : IsAdicComplete (IsLocalRing.maximalIdeal Oδ) Oδ := by
    rw [← hmap]
    exact (IsAdicComplete.map_algebraMap_iff _ _).2
      (finite_free_adic_complete O Oδ (IsLocalRing.maximalIdeal O))
  have : Finite (IsLocalRing.ResidueField Oδ) := by
    have : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
      inferInstanceAs (Finite (IsLocalRing.ResidueField O))
    have := finite_free_residue_quotient O Oδ (IsLocalRing.maximalIdeal O)
    have hle : (IsLocalRing.maximalIdeal O • ⊤ : Submodule O Oδ) ≤
        LinearMap.ker (Ideal.Quotient.mkₐ O (IsLocalRing.maximalIdeal Oδ)).toLinearMap := by
      refine Submodule.smul_le.2 fun r hr n _ ↦ ?_
      rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (hmap ▸ Ideal.mem_map_of_mem _ hr)
    refine Finite.of_surjective ((IsLocalRing.maximalIdeal O • ⊤ : Submodule O Oδ).liftQ _ hle)
      fun y ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  -- compare the two (equal) integral closures, both DVRs
  have := closure_finite_descent O Oδ L hfinδ
  have h1 := integral_closure_is_local O (BaseField O) L
  have h2 := integral_closure_is_local Oδ (BaseField Oδ) L
  have := integral_closure_is_dvr O (BaseField O) L
  have := integral_closure_is_dvr Oδ (BaseField Oδ) L
  obtain ⟨-, _, -⟩ := integral_closure_finite_free Oδ (BaseField Oδ) L
  have : Algebra.IsIntegral O Oδ := Algebra.IsIntegral.of_finite O Oδ
  have : Algebra.IsIntegral O (integralClosure Oδ L) := .trans Oδ
  obtain ⟨hr, hi⟩ := dvr_algEquiv_ramification_inertia O _ _
    (algebraMap_injective_of_tower O _ L) (algebraMap_injective_of_tower O _ L)
    (integralClosureTowerEquiv O Oδ L)
  unfold fieldInvariant
  rw [dif_pos h1, dif_pos h2]
  rw [hr, hi, ramificationIdx_unramified_tower O Oδ (integralClosure Oδ L) δ hrank pi hpi hpiδ,
    inertiaDeg_unramified_tower O Oδ (integralClosure Oδ L) δ hrank pi hpi hpiδ]

/-- Algebra types descend along an unramified extension `O → Oδ` of degree `δ`, scaled by `δ`. -/
theorem algebra_type_unramified_descent (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ)
    (pi : O) (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi))
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (B : Type)
    [CommRing B] [Algebra O B] [Algebra Oδ B] [IsScalarTower O Oδ B] (σ : FactorType)
    (h : HasAlgebraType Oδ B σ) :
    HasAlgebraType O B (scaleType δ σ) := by
  obtain ⟨ι, hι, L, hF, hK, hO, hT, hFD, e, rfl, hfinL⟩ := h
  obtain ⟨hK', hO', hT', hT'', hFD', E, -⟩ :=
    unramified_generic_fibre_witness O Oδ δ hrank pi hpi hpiδ B ι L e
  refine ⟨ι, hι, L, hF, hK', hO', hT', hFD', E, ?_,
    fun i ↦ closure_finite_descent O Oδ (L i) (hfinL i)⟩
  unfold scaleType
  rw [← Multiset.coe_mapAddMonoidHom, map_sum]
  simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_singleton,
    field_invariant_unramified_tower O Oδ δ hrank pi hpi hpiδ _ (hfinL _)]

/-! ### Frobenius on the fraction field -/

/-- The Frobenius iterates of `Oδ = O[X]/(Φ)` extend to automorphisms `τ i` of `Kδ = Frac Oδ`
fixing `K`; `τ` is a group action of `ℕ` with `τ δ = id`, and the fixed field of `τ 1` is `K`. -/
theorem frobenius_fraction_extension (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
    (hι : ∀ c : O, ι (algebraMap O (BaseField O) c) =
      algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c)) :
    ∃ τ : ℕ → (BaseField (AdjoinRoot Φ) ≃+* BaseField (AdjoinRoot Φ)),
      (∀ (i : ℕ) (x : AdjoinRoot Φ), τ i (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) x) =
        algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (frobeniusIter O Φ i x))
      ∧ (∀ (i : ℕ) (y : BaseField O), τ i (ι y) = ι y)
      ∧ τ 0 = RingEquiv.refl (BaseField (AdjoinRoot Φ)) ∧ (∀ i : ℕ, τ (i + 1) = (τ i).trans (τ 1))
      ∧ (∀ z : BaseField (AdjoinRoot Φ), τ Φ.natDegree z = z)
      ∧ (∀ z : BaseField (AdjoinRoot Φ), τ 1 z = z → ∃ y : BaseField O, ι y = z) := by
  obtain ⟨hid, hbij⟩ := frobenius_pow_degree_eq_id O Φ hΦ
  have bij : ∀ i, Function.Bijective (frobeniusIter O Φ i) := fun i ↦ by
    induction i with
    | zero => exact Function.bijective_id
    | succ i ih =>
      change Function.Bijective (⇑(unramifiedFrobenius O Φ) ∘ ⇑(frobeniusIter O Φ i))
      exact hbij.comp ih
  set K := BaseField (AdjoinRoot Φ)
  let τ : ℕ → (K ≃+* K) := fun i ↦ IsFractionRing.ringEquivOfRingEquiv
    (RingEquiv.ofBijective (frobeniusIter O Φ i).toRingHom (bij i))
  have h1 : ∀ (i : ℕ) (x : AdjoinRoot Φ),
      τ i (algebraMap (AdjoinRoot Φ) K x) = algebraMap (AdjoinRoot Φ) K (frobeniusIter O Φ i x) :=
    fun i x ↦ IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have ext : ∀ f g : K ≃+* K,
      (∀ x : AdjoinRoot Φ, f (algebraMap _ _ x) = g (algebraMap _ _ x)) → f = g := fun f g h ↦
    RingEquiv.toRingHom_injective
      (IsLocalization.ringHom_ext (nonZeroDivisors (AdjoinRoot Φ)) (RingHom.ext h))
  refine ⟨τ, h1, fun i y ↦ ?_, ext _ _ fun x ↦ by rw [h1]; rfl,
    fun i ↦ ext _ _ fun x ↦ by rw [RingEquiv.trans_apply, h1, h1, h1]; rfl,
    fun z ↦ by rw [ext (τ Φ.natDegree) (RingEquiv.refl _) fun x ↦ by rw [h1, hid]; rfl]; rfl,
    fun z hz ↦ ?_⟩
  · refine RingHom.congr_fun (?_ : (τ i).toRingHom.comp ι = ι) y
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (RingHom.ext fun c ↦ ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [hι, h1, AlgHom.commutes]
  · -- write `z = a' / ϖᵏ` with `ϖ ∈ O` a uniformizer; then `a'` is Frobenius-fixed, so in `O`
    obtain ⟨_, _, hdvr, -, hirr, -⟩ := unramified_is_dvr O Φ hΦ
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := AdjoinRoot Φ) z
    obtain ⟨k, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hs) (hirr ϖ hϖ)
    have hdK : algebraMap (AdjoinRoot Φ) K (algebraMap O (AdjoinRoot Φ) (ϖ ^ k)) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero (by
        rw [map_pow]; exact pow_ne_zero _ (hirr ϖ hϖ).ne_zero))
    set a' := a * ↑u⁻¹ with ha'
    have hz' : algebraMap (AdjoinRoot Φ) K a / algebraMap (AdjoinRoot Φ) K s =
        algebraMap (AdjoinRoot Φ) K a' /
          algebraMap (AdjoinRoot Φ) K (algebraMap O (AdjoinRoot Φ) (ϖ ^ k)) := by
      rw [div_eq_div_iff (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs) hdK, ← map_mul,
        ← map_mul, hu, ha', map_pow]
      rw [mul_assoc, Units.inv_mul_cancel_left]
    rw [hz'] at hz ⊢
    rw [map_div₀, h1, h1, AlgHom.commutes] at hz
    obtain ⟨c, hc⟩ := frobenius_fixed_ring O Φ hΦ a'
      (IsFractionRing.injective (AdjoinRoot Φ) K ((div_left_inj' hdK).mp hz))
    exact ⟨algebraMap O (BaseField O) c / algebraMap O (BaseField O) (ϖ ^ k),
      by rw [map_div₀, hι, hι, hc]⟩

/-! ### Ascent and descent of polynomial types -/

section Ascent

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
  (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) [IsDomain (AdjoinRoot Φ)]
  (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
  (hι : ∀ c : O, ι (algebraMap O (BaseField O) c) =
    algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c))

include hΦ hι in
/-- The unramified fraction-field extension `Kδ/K` is finite and separable (it is Galois: the
Frobenius `τ 1` already has fixed field `K`). -/
theorem unramified_fraction_isSeparable :
    letI := ι.toAlgebra
    FiniteDimensional (BaseField O) (BaseField (AdjoinRoot Φ)) ∧
      Algebra.IsSeparable (BaseField O) (BaseField (AdjoinRoot Φ)) := by
  let := ι.toAlgebra
  obtain ⟨ι0, hι0, -, huniq, hfin0, -⟩ := unramified_fraction_field_lift O Φ hΦ
  obtain rfl : ι = ι0 := huniq ι hι
  have hfd : FiniteDimensional (BaseField O) (BaseField (AdjoinRoot Φ)) := hfin0
  obtain ⟨τ, -, hτι, -, -, -, hfix⟩ := frobenius_fraction_extension O Φ hΦ ι hι
  let σ1 : BaseField (AdjoinRoot Φ) ≃ₐ[BaseField O] BaseField (AdjoinRoot Φ) :=
    AlgEquiv.ofRingEquiv (f := τ 1) (hτι 1)
  have : IsGalois (BaseField O) (BaseField (AdjoinRoot Φ)) :=
    IsGalois.of_fixedField_eq_bot _ _ <| eq_bot_iff.2 fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hfix x ((IntermediateField.mem_fixedField_iff _ _).1 hx σ1
        (Subgroup.mem_top σ1))
      exact IntermediateField.algebraMap_mem _ y
  exact ⟨hfd, inferInstance⟩

/-- For a monic irreducible `H` over `K` whose root field is `K`-isomorphic to the root field of a
monic irreducible `g` over `Kδ` (with finite `Oδ`-closure), the factor invariant of `H` is that
of `g` with inertia degree scaled by `δ = deg Φ`, and `H` has finite `O`-closure. -/
theorem factor_invariant_unramified_scale (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
    (hι : ∀ c : O, ι (algebraMap O (BaseField O) c) =
      algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c))
    (g : Polynomial (BaseField (AdjoinRoot Φ))) (hg : g.Monic) (hgi : Irreducible g)
    (H : Polynomial (BaseField O)) (hH : H.Monic) (hHi : Irreducible H)
    (hiso : letI := ι.toAlgebra; Nonempty (AdjoinRoot H ≃ₐ[BaseField O] AdjoinRoot g))
    (hfinδ : Module.Finite (AdjoinRoot Φ) (integralClosure (AdjoinRoot Φ) (AdjoinRoot g))) :
    factorInvariant O H = ((factorInvariant (AdjoinRoot Φ) g).1,
      Φ.natDegree * (factorInvariant (AdjoinRoot Φ) g).2) ∧
      Module.Finite O (integralClosure O (AdjoinRoot H)) := by
  let _ := ι.toAlgebra
  set K := BaseField O
  set Oδ := AdjoinRoot Φ
  set Kδ := BaseField Oδ
  set L := AdjoinRoot g
  obtain ⟨_, _, hdvrδ, -, hirrδ, _, _, -⟩ := unramified_is_dvr O Φ hΦ
  obtain ⟨hfree, hfin, hrank⟩ := unramified_free_module O Φ hΦ.1
  obtain ⟨hfd, -⟩ := unramified_fraction_isSeparable O Φ hΦ ι hι
  have : Fact (Irreducible g) := ⟨hgi⟩
  have : Fact (Irreducible H) := ⟨hHi⟩
  have : IsScalarTower O K Kδ := .of_algebraMap_eq fun c ↦ (hι c).symm
  have : IsScalarTower O K L := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply O Kδ L, IsScalarTower.algebraMap_apply K Kδ L,
      IsScalarTower.algebraMap_apply O K Kδ]
  have : IsScalarTower O Oδ L := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply O Kδ L, IsScalarTower.algebraMap_apply Oδ Kδ L,
      IsScalarTower.algebraMap_apply O Oδ Kδ]
  have : Module.Finite K (AdjoinRoot H) := hH.finite_adjoinRoot
  have : Module.Finite Kδ L := hg.finite_adjoinRoot
  have : Module.Finite K L := .trans Kδ L
  have : Module.Finite O (integralClosure O L) := closure_finite_descent O Oδ L hfinδ
  obtain ⟨e⟩ : Nonempty (AdjoinRoot H ≃ₐ[K] L) := hiso
  obtain ⟨hinv, hfinH⟩ := fieldInvariant_congr O L (AdjoinRoot H) e.symm
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine ⟨?_, hfinH⟩
  change fieldInvariant O (AdjoinRoot H) =
    ((fieldInvariant Oδ L).1, Φ.natDegree * (fieldInvariant Oδ L).2)
  rw [← hinv, field_invariant_unramified_tower O Oδ Φ.natDegree hrank pi hpi (hirrδ pi hpi) L hfinδ]

include hΦ hι in
/-- An irreducible factor type over `O` ascends to a type over `Oδ`. -/
private theorem polynomial_type_map_irreducible (g : Polynomial (BaseField O)) (hgm : g.Monic)
    (hgi : Irreducible g) (hfin : Module.Finite O (integralClosure O (AdjoinRoot g))) :
    ∃ τ' : FactorType, HasPolynomialTypeF (AdjoinRoot Φ) (g.map ι) τ' := by
  let := ι.toAlgebra
  obtain ⟨hfd, hsep⟩ := unramified_fraction_isSeparable O Φ hΦ ι hι
  have : Fact (Irreducible g) := ⟨hgi⟩
  obtain ⟨-, hfinδ, -⟩ := unramified_free_module O Φ hΦ.1
  have : IsScalarTower O (BaseField O) (BaseField (AdjoinRoot Φ)) :=
    .of_algebraMap_eq fun c ↦ by
      rw [IsScalarTower.algebraMap_apply O (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))]
      exact (hι c).symm
  refine squarefree_monic_has_polynomial_type (AdjoinRoot Φ) _ (hgm.map _)
    (squarefree_map_of_isSeparable _ _ g) fun h hh ↦ ?_
  exact closure_finite_ascent_root O (AdjoinRoot Φ) (BaseField O) (BaseField (AdjoinRoot Φ)) g hgm
    hgi hfin h (UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh)
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh)

include hΦ hι in
/-- A polynomial with a type over `O` has a type over the unramified extension `Oδ`. -/
theorem polynomial_type_map_unramified (F : Polynomial (BaseField O)) (σ : FactorType)
    (hF : HasPolynomialTypeF O F σ) :
    ∃ τ' : FactorType, HasPolynomialTypeF (AdjoinRoot Φ) (F.map ι) τ' := by
  obtain ⟨gs, hgs, hpw, rfl, -, hfin⟩ := hF
  induction gs with
  | nil => exact ⟨0, [], by simp, by simp, by simp, by simp, by simp⟩
  | cons g t ih =>
    rw [List.pairwise_cons] at hpw
    obtain ⟨τ1, h1⟩ := polynomial_type_map_irreducible O Φ hΦ ι hι g (hgs g (by simp)).1
      (hgs g (by simp)).2 (hfin g (by simp))
    obtain ⟨τ2, h2⟩ := ih (fun x hx ↦ hgs x (by simp [hx])) hpw.2
      (fun x hx ↦ hfin x (by simp [hx]))
    have hc : ∀ l : List (Polynomial (BaseField O)), (∀ x ∈ l, IsCoprime g x) →
        IsCoprime g l.prod := by
      intro l
      induction l with
      | nil => exact fun _ ↦ isCoprime_one_right
      | cons x l ih2 => exact fun h ↦
        (h x (by simp)).mul_right (ih2 fun y hy ↦ h y (by simp [hy]))
    have hct : IsCoprime g t.prod := hc t fun x hx ↦
      distinct_monic_irreducible_coprime _ g x (hgs g (by simp)).1 (hgs x (by simp [hx])).1
        (hgs g (by simp)).2 (hgs x (by simp [hx])).2 (hpw.1 x hx)
    rw [List.prod_cons, Polynomial.map_mul]
    exact ⟨_, polynomial_type_mul_coprime _ _ _ _ _ h1 h2 (hct.map (mapRingHom ι))⟩

end Ascent

/-- Descent of polynomial types: if `F` over `Oδ` has type `σ` with pairwise coprime Frobenius
conjugates, and `G ∈ O[X]` maps to the conjugate product of `F`, then `G` has type
`scaleType δ σ` over `O`, where `δ = deg Φ`. -/
theorem descended_polynomial_type (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) [IsDomain (AdjoinRoot Φ)]
    (F : Polynomial (AdjoinRoot Φ)) (σ : FactorType)
    (hσ : HasPolynomialTypeF (AdjoinRoot Φ)
      (F.map (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) σ)
    (hcop : ∀ i j : Fin Φ.natDegree, i ≠ j → IsCoprime
      ((fun i : Fin Φ.natDegree ↦ (F.map (frobeniusIter O Φ i).toRingHom).map
        (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) i)
      ((fun i : Fin Φ.natDegree ↦ (F.map (frobeniusIter O Φ i).toRingHom).map
        (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) j)) (G : Polynomial O)
    (hG : G.map (algebraMap O (AdjoinRoot Φ)) = conjugateProduct O Φ F) :
    HasPolynomialTypeF O (G.map (algebraMap O (BaseField O))) (scaleType Φ.natDegree σ) := by
  obtain ⟨gs, hgs, hd, hprod, hσeq, hfinδ⟩ := hσ
  obtain ⟨ι, hι, hinj, -, hfin⟩ := unramified_fraction_field_lift O Φ hΦ
  obtain ⟨τ, hτ, hτι, hτ0, hrec, hτδ, hfix⟩ := frobenius_fraction_extension O Φ hΦ ι hι
  obtain ⟨H, hHmi, hHinj, hHorb, hHdeg, hHprod⟩ := invariant_orbit_factors O Φ hΦ ι τ hτ hτι hτ0
    hrec hτδ hfix hinj F gs hgs hd hprod hcop
  have hcomp : ι.comp (algebraMap O (BaseField O)) =
      (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))).comp (algebraMap O (AdjoinRoot Φ)) :=
    RingHom.ext hι
  have hGprod : ∏ a, H a = G.map (algebraMap O (BaseField O)) := by
    apply Polynomial.map_injective ι hinj
    rw [hHprod, ← hG, Polynomial.map_map, Polynomial.map_map, hcomp]
  have hδpos : 0 < Φ.natDegree := Nat.pos_of_ne_zero fun h ↦ by
    have h2 := hΦ.2
    rw [eq_one_of_monic_natDegree_zero hΦ.1 h, residuePoly, Polynomial.map_one] at h2
    exact h2.not_isUnit isUnit_one
  have hinv : ∀ a, factorInvariant O (H a) =
      (fun z : ℕ × ℕ ↦ (z.1, Φ.natDegree * z.2)) (factorInvariant (AdjoinRoot Φ) (gs.get a)) ∧
      Module.Finite O (integralClosure O (AdjoinRoot (H a))) := by
    intro a
    have hga := hgs (gs.get a) (List.get_mem _ _)
    have hdiv : gs.get a ∣ (H a).map ι := by
      rw [hHorb a]
      conv_lhs => rw [← show (gs.get a).map (τ (⟨0, hδpos⟩ : Fin Φ.natDegree)).toRingHom =
        gs.get a by simp [hτ0]]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    exact factor_invariant_unramified_scale O Φ hΦ ι hι (gs.get a) hga.1 hga.2 (H a)
      (hHmi a).1 (hHmi a).2 (root_field_algEquiv_conjugate_orbit O Φ ι hfin (gs.get a)
        hga.1 hga.2 (H a) (hHmi a).1 (hHmi a).2 hdiv (hHdeg a)) (hfinδ _ (List.get_mem _ _))
  refine ⟨List.ofFn H, fun g hg ↦ ?_, List.nodup_ofFn.mpr hHinj, by rw [List.prod_ofFn, hGprod],
    ?_, fun g hg ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hg
    exact hHmi a
  · rw [hσeq, List.map_ofFn]
    conv_lhs => rw [← List.ofFn_get gs]
    rw [List.map_ofFn, scaleType, Multiset.map_coe, List.map_ofFn]
    exact congrArg _ (congrArg _ (funext fun a ↦ (hinv a).1.symm))
  · obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hg
    exact (hinv a).2

end SurfaceBlowup
