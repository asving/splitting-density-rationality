/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Measure.PrimitiveLocus
import SurfaceBlowup.Unramified.FactorCells

/-!
# Invariance of factor invariants and uniqueness of algebra types

Over a complete DVR `O` with finite residue field and fraction field `K = BaseField O`, the
invariants `(e, f)` of the integral closure of `O` in a finite extension `L/K` depend only on the
`K`-isomorphism class of `L`. Consequences: polynomial types are invariant under normalized
reversal `g ↦ g(0)⁻¹ · reverse g`, algebra types are unique, and a monic `F ∈ O[X]` has polynomial
type `σ` over `K` exactly when `O[X]/(F)` has algebra type `σ`.

## Main results

* `SurfaceBlowup.field_invariant_algEquiv`, `SurfaceBlowup.factor_invariant_algEquiv`
* `SurfaceBlowup.reverse_normalized_irreducible`, `SurfaceBlowup.reverse_polynomial_type_iff`
* `SurfaceBlowup.algebra_type_unique`, `SurfaceBlowup.polynomial_type_iff_algebra_type`

Provenance: Thm_SurfaceBlowupV2_{factor_invariant_algEquiv, reverse_normalized_irreducible,
reverse_polynomial_type_iff, field_invariant_algEquiv, algebra_type_unique,
polynomial_type_iff_algebra_type}.
-/

namespace SurfaceBlowup

open Polynomial

/-! ### Invariance under isomorphism -/

/-- The invariants `(e, f)` of the integral closure of `O` in a finite extension `L/K` (assumed
finite over `O`) depend only on the `K`-isomorphism class of `L`. -/
theorem field_invariant_algEquiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (L L' : Type) [Field L] [Field L']
    [Algebra (BaseField O) L] [Algebra O L] [IsScalarTower O (BaseField O) L]
    [FiniteDimensional (BaseField O) L] [Algebra (BaseField O) L'] [Algebra O L']
    [IsScalarTower O (BaseField O) L'] [FiniteDimensional (BaseField O) L']
    (e : L ≃ₐ[BaseField O] L') (hfin : Module.Finite O (integralClosure O L)) :
    fieldInvariant O L = fieldInvariant O L' := by
  obtain ⟨φ, -⟩ := integral_closure_algEquiv O L L' (e.restrictScalars O)
  have : Module.Finite O (integralClosure O L') := .equiv φ.toLinearEquiv
  have h1 := integral_closure_is_local O (BaseField O) L
  have h2 := integral_closure_is_local O (BaseField O) L'
  have := integral_closure_is_dvr O (BaseField O) L
  have := integral_closure_is_dvr O (BaseField O) L'
  obtain ⟨hr, hi⟩ := dvr_algEquiv_ramification_inertia O _ _
    (algebraMap_injective_of_tower O _ L) (algebraMap_injective_of_tower O _ L') φ
  unfold fieldInvariant
  rw [dif_pos h1, dif_pos h2, hr, hi]

/-- `K`-isomorphic root fields of monic irreducibles `g, g'` (with finite closure) have the same
factor invariant. -/
theorem factor_invariant_algEquiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (g g' : Polynomial (BaseField O)) (hg : g.Monic)
    (hirr : Irreducible g) (hg' : g'.Monic) (hirr' : Irreducible g')
    (e : AdjoinRoot g ≃ₐ[BaseField O] AdjoinRoot g')
    (hfin : Module.Finite O (integralClosure O (AdjoinRoot g))) :
    factorInvariant O g = factorInvariant O g' := by
  have : Fact (Irreducible g) := ⟨hirr⟩
  have : Fact (Irreducible g') := ⟨hirr'⟩
  have : Module.Finite (BaseField O) (AdjoinRoot g) := hg.finite_adjoinRoot
  have : Module.Finite (BaseField O) (AdjoinRoot g') := hg'.finite_adjoinRoot
  exact field_invariant_algEquiv O _ _ e hfin

/-! ### Normalized reversal -/

section Reverse

variable {K : Type} [Field K]

/-- The normalized reversal `f(0)⁻¹ · reverse f`. -/
private noncomputable def rho (f : K[X]) : K[X] := C (f.coeff 0)⁻¹ * f.reverse

private theorem rho_mul (f g : K[X]) : rho (f * g) = rho f * rho g := by
  unfold rho
  rw [mul_coeff_zero, reverse_mul_of_domain, mul_inv, C_mul]
  ring

private theorem rho_prod (gs : List K[X]) : rho gs.prod = (gs.map rho).prod := by
  induction gs with
  | nil => simp [rho, reverse]
  | cons g gs ih => rw [List.prod_cons, rho_mul, ih, List.map_cons, List.prod_cons]

private theorem reverse_reverse_of (f : K[X]) (h0 : f.coeff 0 ≠ 0) : f.reverse.reverse = f := by
  have hd : f.reverse.natDegree = f.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero h0, Nat.sub_zero]
  ext n
  rw [coeff_reverse, coeff_reverse, hd, revAt_invol]

private theorem rho_coeff_zero {f : K[X]} (hf : f.Monic) : (rho f).coeff 0 = (f.coeff 0)⁻¹ := by
  rw [rho, coeff_C_mul, coeff_zero_reverse, hf.leadingCoeff, mul_one]

private theorem rho_rho (f : K[X]) (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) : rho (rho f) = f := by
  rw [rho, rho_coeff_zero hf, inv_inv, rho, reverse_mul_of_domain, reverse_reverse_of f h0,
    show (C (f.coeff 0)⁻¹).reverse = C (f.coeff 0)⁻¹ by simp [reverse], ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ h0, C_1, one_mul]

end Reverse

/-- For a monic irreducible `g` with `g(0) ≠ 0` and finite closure, its normalized reversal
`h = g(0)⁻¹ · reverse g` is monic irreducible of the same degree with `h(0) = g(0)⁻¹`, has the
same factor invariant and finite closure, and normalized reversal of `h` gives back `g`. -/
theorem reverse_normalized_irreducible (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (g : Polynomial (BaseField O)) (hg : g.Monic)
    (hgi : Irreducible g) (h0 : g.coeff 0 ≠ 0)
    (hfin : Module.Finite O (integralClosure O (AdjoinRoot g))) :
    (C (g.coeff 0)⁻¹ * g.reverse).Monic
      ∧ Irreducible (C (g.coeff 0)⁻¹ * g.reverse)
      ∧ (C (g.coeff 0)⁻¹ * g.reverse).natDegree = g.natDegree
      ∧ (C (g.coeff 0)⁻¹ * g.reverse).coeff 0 = (g.coeff 0)⁻¹
      ∧ factorInvariant O (C (g.coeff 0)⁻¹ * g.reverse) = factorInvariant O g
      ∧ C ((C (g.coeff 0)⁻¹ * g.reverse).coeff 0)⁻¹ * (C (g.coeff 0)⁻¹ * g.reverse).reverse =
        g
      ∧ Module.Finite O (integralClosure O (AdjoinRoot (C (g.coeff 0)⁻¹ * g.reverse))) := by
  set K := BaseField O
  set c := g.coeff 0
  set h := C c⁻¹ * g.reverse with hh
  have hr : 0 < g.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hgi)
  have hrevdeg : g.reverse.natDegree = g.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero h0, Nat.sub_zero]
  have hdeg : h.natDegree = g.natDegree := by rw [hh, natDegree_C_mul (inv_ne_zero h0), hrevdeg]
  have hmon : h.Monic := by
    rw [Monic, hh, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff,
      trailingCoeff_eq_coeff_zero h0, inv_mul_cancel₀ h0]
  have hcoeff0 : h.coeff 0 = c⁻¹ := rho_coeff_zero hg
  have hgrev : g.reverse = C c * h := by
    rw [hh, ← mul_assoc, ← C_mul, mul_inv_cancel₀ h0, C_1, one_mul]
  -- the root field `K[X]/(h)` is isomorphic to `K[X]/(g)`, via the inverse of the root of `h`
  have hne : h ≠ 0 := hmon.ne_zero
  have : Nontrivial (AdjoinRoot h) := AdjoinRoot.nontrivial h (by
    rw [degree_eq_natDegree hne, hdeg]; exact_mod_cast hr.ne')
  set L := AdjoinRoot h
  set β : L := AdjoinRoot.root h
  have hβ : h.eval₂ (algebraMap K L) β = 0 := AdjoinRoot.eval₂_root h
  have hβinv : β * (-(algebraMap K L c) * (divX h).eval₂ (algebraMap K L) β) = 1 := by
    have e1 := congrArg (fun p ↦ p.eval₂ (algebraMap K L) β) (X_mul_divX_add h)
    simp only [eval₂_add, eval₂_mul, eval₂_X, eval₂_C, hβ, hcoeff0] at e1
    calc β * (-(algebraMap K L c) * (divX h).eval₂ (algebraMap K L) β)
        = -(algebraMap K L c) * (β * (divX h).eval₂ (algebraMap K L) β) := by ring
      _ = algebraMap K L (c * c⁻¹) := by rw [eq_neg_of_add_eq_zero_left e1, map_mul]; ring
      _ = 1 := by rw [mul_inv_cancel₀ h0, map_one]
  let _ : Invertible β := invertibleOfRightInverse _ _ hβinv
  have hgβ : g.eval₂ (algebraMap K L) (⅟β) = 0 := by
    have : Invertible (⅟β) := invertibleInvOf
    rw [← eval₂_reverse_eq_zero_iff, invOf_invOf, hgrev, eval₂_mul, hβ, mul_zero]
  have : Fact (Irreducible g) := ⟨hgi⟩
  let φ : AdjoinRoot g →ₐ[K] L := AdjoinRoot.liftAlgHom g (Algebra.ofId K L) (⅟β) hgβ
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have : FiniteDimensional K (AdjoinRoot g) := (AdjoinRoot.powerBasis hg.ne_zero).finite
  have : FiniteDimensional K L := (AdjoinRoot.powerBasis hne).finite
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap) (by
      rw [(AdjoinRoot.powerBasis hg.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
        (AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg])).mp hinj
  let e : AdjoinRoot g ≃ₐ[K] L := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hirr : Irreducible h := (Ideal.irreducible_iff_isMaximal_span_singleton hne).mpr
    (Ideal.Quotient.maximal_of_isField _
      (MulEquiv.isField (Field.toIsField (AdjoinRoot g)) e.symm.toMulEquiv))
  obtain ⟨φ', -⟩ := integral_closure_algEquiv O _ _ (e.restrictScalars O)
  exact ⟨hmon, hirr, hdeg, hcoeff0, (factor_invariant_algEquiv O g h hg hgi hmon hirr e hfin).symm,
    rho_rho g hg h0, .equiv φ'.toLinearEquiv⟩

private theorem rev_type_forward (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (P : Polynomial (BaseField O)) (h0 : P.coeff 0 ≠ 0)
    (τ : FactorType) : HasPolynomialTypeF O P τ → HasPolynomialTypeF O (rho P) τ := by
  rintro ⟨gs, hmem, hpw, hprod, hτ, hfin⟩
  have hg0 : ∀ g ∈ gs, g.coeff 0 ≠ 0 := fun g hg hz ↦ by
    obtain ⟨Q, hQ⟩ := List.dvd_prod hg
    exact h0 (by rw [hprod, hQ, mul_coeff_zero, hz, zero_mul])
  have hrev : ∀ g ∈ gs, _ := fun g hg ↦
    reverse_normalized_irreducible O g (hmem g hg).1 (hmem g hg).2 (hg0 g hg) (hfin g hg)
  refine ⟨gs.map rho, ?_, ?_, by rw [hprod, rho_prod], ?_, ?_⟩
  · simp only [List.mem_map]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨(hrev g hg).1, (hrev g hg).2.1⟩
  · refine List.Nodup.map_on (fun a ha b hb hab ↦ ?_) hpw
    rw [← (hrev a ha).2.2.2.2.2.1, ← (hrev b hb).2.2.2.2.2.1]
    exact congrArg rho hab
  · rw [hτ, List.map_map]
    exact congrArg _ (List.map_congr_left fun g hg ↦ ((hrev g hg).2.2.2.2.1).symm)
  · simp only [List.mem_map]
    rintro _ ⟨g, hg, rfl⟩
    exact (hrev g hg).2.2.2.2.2.2

/-- A monic `P` with `P(0) ≠ 0` has type `τ` iff its normalized reversal does. -/
theorem reverse_polynomial_type_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (P : Polynomial (BaseField O)) (hP : P.Monic)
    (h0 : P.coeff 0 ≠ 0) (τ : FactorType) :
    HasPolynomialTypeF O P τ ↔ HasPolynomialTypeF O (Polynomial.C (P.coeff 0)⁻¹ * P.reverse) τ :=
  ⟨rev_type_forward O P h0 τ, fun h ↦ rho_rho P hP h0 ▸
    rev_type_forward O (rho P) (by rw [rho_coeff_zero hP]; exact inv_ne_zero h0) τ h⟩

/-! ### Uniqueness of algebra types -/

/-- A `K`-algebra isomorphism between finite products of fields `∏ Lᵢ ≃ ∏ L'ⱼ` yields an injection
`φ : ι → ι'` with `Lᵢ ≃ L'_{φ i}`. -/
private theorem pi_field_matching (K : Type) [Field K] (ι ι' : Type) [Finite ι] [Finite ι']
    (L : ι → Type) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    (L' : ι' → Type) [∀ i, Field (L' i)] [∀ i, Algebra K (L' i)]
    (f : (∀ i, L i) ≃ₐ[K] (∀ j, L' j)) :
    ∃ φ : ι → ι', Function.Injective φ ∧ ∀ i, Nonempty (L i ≃ₐ[K] L' (φ i)) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite ι'
  have hs : ∀ i, Function.Surjective ((Pi.evalAlgHom K L i).comp f.symm.toAlgHom) :=
    fun i x ↦ ⟨f (Pi.single i x), by simp⟩
  have hker : ∀ i, ∃ j, RingHom.ker ((Pi.evalAlgHom K L i).comp f.symm.toAlgHom) =
      RingHom.ker (Pi.evalAlgHom K L' j) := fun i ↦
    (pi_field_maximal_ideals ι' L' _).1.1 (RingHom.ker_isMaximal_of_surjective _ (hs i))
  choose φ hφ using hker
  refine ⟨φ, fun i i' h ↦ ?_, fun i ↦ ?_⟩
  · have h1 := hφ i
    rw [h] at h1
    apply (pi_field_maximal_ideals ι L ⊥).2 i i'
    ext x
    simpa [RingHom.mem_ker] using Ideal.ext_iff.1 (h1.trans (hφ i').symm) (f x)
  · exact ⟨(Ideal.quotientKerAlgEquivOfSurjective (hs i)).symm.trans
      ((Ideal.quotientEquivAlgOfEq K (hφ i)).trans
        (Ideal.quotientKerAlgEquivOfSurjective fun x ↦ ⟨Pi.single (φ i) x, by simp⟩))⟩

/-- The algebra type of an `O`-algebra, if it exists, is unique. -/
theorem algebra_type_unique (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (B : Type) [CommRing B] [Algebra O B] (σ τ : FactorType) (hσ : HasAlgebraType O B σ)
    (hτ : HasAlgebraType O B τ) : σ = τ := by
  obtain ⟨ι, _, L, _, _, _, _, _, e, rfl, hfinL⟩ := hσ
  obtain ⟨ι', _, L', _, _, _, _, _, e', rfl, -⟩ := hτ
  obtain ⟨φ, hφi, hφ⟩ := pi_field_matching _ ι ι' L L' (e.symm.trans e')
  obtain ⟨ψ, hψi, -⟩ := pi_field_matching _ ι' ι L' L (e'.symm.trans e)
  have hb : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).2
    ⟨hφi, le_antisymm (Fintype.card_le_of_injective φ hφi) (Fintype.card_le_of_injective ψ hψi)⟩
  refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans (Fintype.sum_bijective φ hb _ _ fun _ ↦ rfl)
  obtain ⟨g⟩ := hφ i
  rw [field_invariant_algEquiv O (L i) (L' (φ i)) g (hfinL i)]

/-! ### Polynomial types versus algebra types -/

private theorem sum_singleton_get {α β : Type} (f : α → β) (l : List α) :
    ∑ i : Fin l.length, ({f (l.get i)} : Multiset β) = ((l.map f : List β) : Multiset β) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    refine (Fin.sum_univ_succ
      (fun i : Fin (l.length + 1) ↦ ({f ((a :: l).get i)} : Multiset β))).trans ?_
    rw [show ∑ i : Fin l.length, ({f ((a :: l).get i.succ)} : Multiset β) = _ from ih]
    rfl

private theorem type_forward (O : Type) [CommRing O] [IsDomain O] (F : Polynomial O)
    (σ : FactorType) (h : HasPolynomialTypeF O (F.map (algebraMap O (BaseField O))) σ) :
    HasAlgebraType O (AdjoinRoot F) σ := by
  obtain ⟨gs, hgs, hd, hprod, hσ, hfinG⟩ := h
  obtain ⟨e₁, -⟩ := polynomial_quotient_product_equiv (BaseField O) gs hgs hd
  obtain ⟨e₀, -⟩ := adjoinRoot_base_change O F
  rw [hprod] at e₀
  have : ∀ i : Fin gs.length, Fact (Irreducible (gs.get i)) :=
    fun i ↦ ⟨(hgs _ (List.get_mem gs i)).2⟩
  refine ⟨Fin gs.length, inferInstance, fun i ↦ AdjoinRoot (gs.get i),
    fun i ↦ AdjoinRoot.instField, fun i ↦ inferInstance, fun i ↦ inferInstance,
    fun i ↦ inferInstance, fun i ↦ (hgs _ (List.get_mem gs i)).1.finite_adjoinRoot, e₀.trans e₁,
    ?_, fun i ↦ hfinG _ (List.get_mem gs i)⟩
  rw [hσ, ← sum_singleton_get]
  rfl

/-- For monic `F ∈ O[X]`, the image of `F` in `K[X]` has polynomial type `σ` iff `O[X]/(F)` has
algebra type `σ`. -/
theorem polynomial_type_iff_algebra_type (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (F : Polynomial O) (hF : F.Monic) (σ : FactorType) :
    HasPolynomialTypeF O (F.map (algebraMap O (BaseField O))) σ ↔
      HasAlgebraType O (AdjoinRoot F) σ := by
  classical
  open UniqueFactorizationMonoid in
  refine ⟨type_forward O F σ, fun h ↦ ?_⟩
  obtain ⟨e₀, -⟩ := adjoinRoot_base_change O F
  -- `K[X]/(F)` is reduced (a product of fields), so the image `G` of `F` is squarefree
  set G := F.map (algebraMap O (BaseField O))
  have hGm : G.Monic := hF.map _
  have h0 : G ≠ 0 := hGm.ne_zero
  have hsq : Squarefree G := by
    obtain ⟨ι, _, L, _, _, _, _, _, e, -, -⟩ := h
    exact squarefree_of_isReduced_adjoinRoot _ _ h0
      (isReduced_of_injective (e₀.symm.trans e).toRingHom (e₀.symm.trans e).injective)
  -- closure finiteness of each irreducible factor is read off by matching factors with the `Lᵢ`
  have hmon : ∀ g ∈ normalizedFactors G, g.Monic := fun g hg ↦ by
    rw [← normalize_normalized_factor g hg]
    exact monic_normalize (irreducible_of_normalized_factor g hg).ne_zero
  set l := (normalizedFactors G).toList with hl
  have hlm : ∀ g ∈ l, g.Monic ∧ Irreducible g := fun g hg ↦ by
    rw [hl, Multiset.mem_toList] at hg
    exact ⟨hmon g hg, irreducible_of_normalized_factor g hg⟩
  have hlnd : l.Pairwise (fun g h ↦ g ≠ h) := by
    change l.Nodup
    rw [hl, ← Multiset.coe_nodup, Multiset.coe_toList]
    exact (squarefree_iff_nodup_normalizedFactors h0).1 hsq
  have hlprod : G = l.prod := by
    rw [hl, Multiset.prod_toList]
    exact (eq_of_monic_of_associated (by simpa using monic_multiset_prod_of_monic _ id hmon) hGm
      (prod_normalizedFactors h0)).symm
  obtain ⟨e₁, -⟩ := polynomial_quotient_product_equiv (BaseField O) l hlm hlnd
  rw [hlprod] at e₀
  obtain ⟨ι, _, L, _, _, _, _, _, e, -, hfinL⟩ := id h
  have : ∀ i : Fin l.length, Fact (Irreducible (l.get i)) := fun i ↦ ⟨(hlm _ (List.get_mem l i)).2⟩
  obtain ⟨φ, -, hφ⟩ := pi_field_matching (BaseField O) (Fin l.length) ι
    (fun i ↦ AdjoinRoot (l.get i)) L (e₁.symm.trans (e₀.symm.trans e))
  have hfac : ∀ g ∈ normalizedFactors G, Module.Finite O (integralClosure O (AdjoinRoot g)) := by
    intro g hg
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 (show g ∈ l by rwa [hl, Multiset.mem_toList])
    obtain ⟨ψ⟩ := hφ j
    obtain ⟨χ, -⟩ := integral_closure_algEquiv O _ _ (ψ.restrictScalars O)
    have := hfinL (φ j)
    exact .equiv χ.symm.toLinearEquiv
  obtain ⟨τ, hτ⟩ := squarefree_monic_has_polynomial_type O G hGm hsq hfac
  rwa [algebra_type_unique O (AdjoinRoot F) σ τ h (type_forward O F τ hτ)]

end SurfaceBlowup
