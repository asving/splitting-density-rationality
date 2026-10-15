/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Formula.LawAlgebra
import Mathlib.RingTheory.Henselian

/-!
# Algebra types and integral closures over a discrete valuation ring

For a domain `O` with fraction field `K = BaseField O`, an `O`-algebra `B` *has algebra type* `σ`
when its generic fibre `K ⊗_O B` is a finite product of finite field extensions `Lᵢ/K` with finite
`O`-integral closures, `σ` being the multiset of the invariants `(e, f)` of these closures. This
file sets up that notion and the order defect `δ_O(B)`, and proves the closure-finiteness and
base-change facts used to compute types: transfer of closure finiteness along finite extensions of
`O` and finite separable extensions of fields, types of squarefree monic polynomials, invariance
of algebra types under isomorphism and products, and the structure of integral closures in finite
extensions of `K` (finite free of the right rank, Dedekind, not a field).

## Main definitions

* `SurfaceBlowup.fieldInvariant`, `SurfaceBlowup.HasAlgebraType`
* `SurfaceBlowup.GenericClosure`, `SurfaceBlowup.orderImage`, `SurfaceBlowup.orderDefect`

## Main results

* `SurfaceBlowup.closure_finite_descent`, `SurfaceBlowup.closure_finite_ascent`,
  `SurfaceBlowup.closure_finite_ascent_root`, `SurfaceBlowup.closure_finite_of_separable`
* `SurfaceBlowup.HasPolynomialTypeF.to_original`,
  `SurfaceBlowup.hasPolynomialTypeF_iff_of_separable`
* `SurfaceBlowup.squarefree_monic_has_polynomial_type`, `SurfaceBlowup.polynomial_type_dvd`
* `SurfaceBlowup.algebra_type_pi`, `SurfaceBlowup.integral_closure_finite_free`,
  `SurfaceBlowup.integral_closure_is_dedekind`, `SurfaceBlowup.unramified_generic_fibre_witness`

Provenance: Def_SurfaceBlowupV2_{AlgebraType, OrderDefect}; Thm_Gen_{ClosureTransfer, Ascent,
SepHelpers, TypeDvd}; Thm_SurfaceBlowupV2_{adjoinRoot_base_change, algebra_type_{algEquiv,
of_generic_fibre_equiv, pi}, integral_closure_{algEquiv, finite_free, invariants_degree,
is_dedekind, not_field}, pi_field_maximal_ideals, unramified_{fraction_base_change,
generic_fibre_witness}}.
-/

noncomputable section

namespace SurfaceBlowup

open scoped TensorProduct
open Polynomial IsLocalRing

/-! ### Definitions -/

section Definitions

variable (O : Type) [CommRing O] [IsDomain O]

/-- The invariants (e,f) of the maximal ideal of the integral closure of O in an O-algebra L (a
field in the applications), with the junk value (0,0) when that closure is not local. -/
noncomputable def fieldInvariant (L : Type) [CommRing L] [Algebra O L] : ℕ × ℕ := by
  classical
  let B := integralClosure O L
  exact if h : IsLocalRing B then
    letI : IsLocalRing B := h
    ((maximalIdeal B).ramificationIdx O, (maximalIdeal B).inertiaDeg O)
  else (0,0)

/-- `HasAlgebraType O B σ`: the generic fibre K ⊗_O B (K = FractionRing O) is isomorphic as a
K-algebra to a finite product of finite field extensions L_i of K whose O-integral closures are
finite O-modules, and σ is the multiset of their invariants. -/
def HasAlgebraType (B : Type) [CommRing B] [Algebra O B] (σ : FactorType) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i))
    (_ : ∀ i, Algebra (BaseField O) (L i)) (_ : ∀ i, Algebra O (L i))
    (_ : ∀ i, IsScalarTower O (BaseField O) (L i)) (_ : ∀ i, FiniteDimensional (BaseField O) (L i))
    (_ : (BaseField O ⊗[O] B) ≃ₐ[BaseField O] (∀ i, L i)),
    σ = ∑ i, ({fieldInvariant O (L i)} : FactorType) ∧
      ∀ i, Module.Finite O (integralClosure O (L i))

/-- The integral closure of O in the generic fibre K ⊗_O B (K = BaseField O), as a type: a `def`
copy of the coerced subalgebra, so that the module quotient defining `orderDefect` can be formed. -/
def GenericClosure (B : Type) [CommRing B] [Algebra O B] : Type :=
  ↥(integralClosure O (BaseField O ⊗[O] B))

/-- The ring structure of `GenericClosure O B`, inherited from the subalgebra. -/
instance (B : Type) [CommRing B] [Algebra O B] : CommRing (GenericClosure O B) :=
  inferInstanceAs (CommRing ↥(integralClosure O (BaseField O ⊗[O] B)))

/-- The `O`-algebra structure of `GenericClosure O B`, inherited from the subalgebra. -/
instance (B : Type) [CommRing B] [Algebra O B] : Algebra O (GenericClosure O B) :=
  inferInstanceAs (Algebra O ↥(integralClosure O (BaseField O ⊗[O] B)))

/-- The inclusion of the closure into the generic fibre (the subalgebra's `val`). -/
def genericClosureVal (B : Type) [CommRing B] [Algebra O B] :
    GenericClosure O B →ₐ[O] BaseField O ⊗[O] B :=
  (integralClosure O (BaseField O ⊗[O] B)).val

/-- The O-submodule of the closure formed by the elements 1 ⊗ b, b ∈ B (the image of the order B
in its generic fibre): the preimage of the range of includeRight under the inclusion. -/
def orderImage (B : Type) [CommRing B] [Algebra O B] : Submodule O (GenericClosure O B) :=
  Submodule.comap (genericClosureVal O B).toLinearMap
    (LinearMap.range (Algebra.TensorProduct.includeRight : B →ₐ[O] BaseField O ⊗[O] B).toLinearMap)

/-- δ_O(B): the O-length (an ℕ∞) of the integral closure of O in K ⊗_O B modulo the image of B.
It is finite when K ⊗_O B is a product of fields and B is finite free; ⊤ is a legitimate value. -/
noncomputable def orderDefect (B : Type) [CommRing B] [Algebra O B] : ℕ∞ :=
  Module.length O (GenericClosure O B ⧸ orderImage O B)

end Definitions

/-! ### Transfer of closure finiteness -/

/-- Over a finite (hence integral) extension `O → Oδ`, the integral closures of `O` and of `Oδ` in
`L` coincide. -/
def integralClosureTowerEquiv (O Oδ L : Type) [CommRing O] [CommRing Oδ] [Algebra O Oδ]
    [Module.Finite O Oδ] [CommRing L] [Algebra O L] [Algebra Oδ L] [IsScalarTower O Oδ L] :
    integralClosure O L ≃ₐ[O] integralClosure Oδ L := by
  have : Algebra.IsIntegral O Oδ := Algebra.IsIntegral.of_finite O Oδ
  exact
  { toFun := fun x ↦ ⟨x.1, x.2.tower_top⟩
    invFun := fun x ↦ ⟨x.1, isIntegral_trans _ x.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }

/-- `O` embeds into any `O`-subring `S` of a field `L` over `K = Frac O`. -/
theorem algebraMap_injective_of_tower (O : Type) [CommRing O] [IsDomain O] (S L : Type)
    [CommRing S] [Field L] [Algebra O S] [Algebra S L] [Algebra (BaseField O) L] [Algebra O L]
    [IsScalarTower O S L] [IsScalarTower O (BaseField O) L] :
    Function.Injective (algebraMap O S) := by
  refine Function.Injective.of_comp (f := algebraMap S L) ?_
  rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq O (BaseField O) L, RingHom.coe_comp]
  exact (algebraMap (BaseField O) L).injective.comp (IsFractionRing.injective O (BaseField O))

/-- Closure finiteness descends along a finite extension `O → Oδ`: the two integral closures
coincide, and finite over `Oδ` finite over `O` is finite over `O`. -/
theorem closure_finite_descent (O Oδ L : Type) [CommRing O] [CommRing Oδ] [Algebra O Oδ]
    [Module.Finite O Oδ] [CommRing L] [Algebra O L] [Algebra Oδ L] [IsScalarTower O Oδ L]
    (h : Module.Finite Oδ (integralClosure Oδ L)) : Module.Finite O (integralClosure O L) :=
  have : Module.Finite O (integralClosure Oδ L) := .trans Oδ _
  .equiv (integralClosureTowerEquiv O Oδ L).symm.toLinearEquiv

/-- Closure finiteness ascends along a finite extension `O → Oδ` acting on the same ring. -/
theorem closure_finite_ascent (O Oδ L : Type) [CommRing O] [CommRing Oδ] [Algebra O Oδ]
    [Module.Finite O Oδ] [CommRing L] [Algebra O L] [Algebra Oδ L] [IsScalarTower O Oδ L]
    (h : Module.Finite O (integralClosure O L)) : Module.Finite Oδ (integralClosure Oδ L) :=
  have := Module.Finite.equiv (integralClosureTowerEquiv O Oδ L).toLinearEquiv
  .of_restrictScalars_finite O Oδ _

private theorem faithfulSMul_of_isFractionRing (O K L : Type) [CommRing O] [IsDomain O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L] [Algebra O L]
    [IsScalarTower O K L] : FaithfulSMul O L := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq O K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)

/-- The integral closure of a DVR `O` in a finite extension `L` of `K = Frac O`, assumed finite
over `O`, is a Dedekind domain. -/
theorem integral_closure_is_dedekind (O K L : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L]
    [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Module.Finite O (integralClosure O L)] :
    IsDedekindDomain (integralClosure O L) := by
  have := faithfulSMul_of_isFractionRing O K L
  have hN : IsNoetherianRing (integralClosure O L) :=
    isNoetherian_of_tower O (isNoetherian_of_isNoetherianRing_of_finite O (integralClosure O L))
  have : IsFractionRing (integralClosure O L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension O K L (integralClosure O L)
  have : Algebra.IsIntegral O (integralClosure O L) := IsIntegralClosure.isIntegral_algebra O L
  exact { hN, Ring.DimensionLEOne.of_isIntegral O (integralClosure O L),
    (isIntegrallyClosed_iff L).mpr fun {x} hx ↦
      ⟨IsIntegralClosure.mk' (integralClosure O L) x (isIntegral_trans (R := O) _ hx),
        IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain (integralClosure O L) }

/-- Finiteness of the integral closure is stable under a finite separable extension on top: if
the closure `C` of `O` in `L` is finite over `O` and `M/L` is finite separable, the closure of `O`
in `M` is finite over `O` (it sits inside the closure of the Dedekind domain `C` in `M`). -/
private theorem closure_finite_of_separable_tower (O K L M : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L]
    [Algebra K L] [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L] [Field M]
    [Algebra L M] [Algebra O M] [IsScalarTower O L M] [FiniteDimensional L M]
    [Algebra.IsSeparable L M] (hL : Module.Finite O (integralClosure O L)) :
    Module.Finite O (integralClosure O M) := by
  have := integral_closure_is_dedekind O K L
  have : IsFractionRing (integralClosure O L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension O K L (integralClosure O L)
  have := IsIntegralClosure.finite (integralClosure O L) L M
    (integralClosure (integralClosure O L) M)
  have : IsScalarTower O (integralClosure O L) M := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply O L M,
      IsScalarTower.algebraMap_apply (integralClosure O L) L M]
    rfl
  have := Module.Finite.trans (R := O) (integralClosure O L)
    (integralClosure (integralClosure O L) M)
  have : IsNoetherian O (integralClosure (integralClosure O L) M) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  let f : integralClosure O M →ₗ[O] integralClosure (integralClosure O L) M :=
    { toFun := fun x ↦ ⟨x.1, x.2.tower_top⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact .of_injective f fun x y h ↦ Subtype.ext (show x.1 = y.1 from congrArg (fun z ↦ z.1) h)

/-! ### Base change of root fields -/

/-- Base change of `R[X]/(g)` along `R → A`: `A ⊗_R R[X]/(g) ≃ A[X]/(g)`, compatibly with `mk`. -/
private theorem adjoinRoot_tensor (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (g : R[X]) :
    ∃ e : A ⊗[R] AdjoinRoot g ≃ₐ[A] AdjoinRoot (g.map (algebraMap R A)), ∀ P : R[X],
      e (1 ⊗ₜ AdjoinRoot.mk g P) = AdjoinRoot.mk _ (P.map (algebraMap R A)) := by
  have hmap : ∀ P : R[X], (polyEquivTensor' R A).symm (1 ⊗ₜ P) = P.map (algebraMap R A) :=
    fun P ↦ by simp [polyEquivTensor_symm_apply_tmul_eq_smul]
  have hI : Ideal.span {g.map (algebraMap R A)} =
      ((Ideal.span {g}).map (Algebra.TensorProduct.includeRight (A := A) (R := R))).map
        ((polyEquivTensor' R A).symm : A ⊗[R] R[X] →+* A[X]) := by
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, ← hmap]
    rfl
  refine ⟨(Algebra.TensorProduct.tensorQuotientEquiv A R[X] A (Ideal.span {g})).trans
    (Ideal.quotientEquivAlg _ _ (polyEquivTensor' R A).symm hI), fun P ↦ ?_⟩
  change Ideal.Quotient.mk _ ((polyEquivTensor' R A).symm (1 ⊗ₜ P)) = _
  rw [hmap]
  rfl

/-- Base change of `O[X]/(F)` to the fraction field `K` of `O` is `K[X]/(F)`, compatibly with
`mk`. -/
theorem adjoinRoot_base_change (O : Type) [CommRing O] [IsDomain O] (F : Polynomial O) :
    ∃ e : TensorProduct O (BaseField O) (AdjoinRoot F) ≃ₐ[BaseField O]
      AdjoinRoot (F.map (algebraMap O (BaseField O))), ∀ P : Polynomial O,
      e (TensorProduct.tmul O (1 : BaseField O) (AdjoinRoot.mk F P)) =
        AdjoinRoot.mk (F.map (algebraMap O (BaseField O))) (P.map (algebraMap O (BaseField O))) :=
  adjoinRoot_tensor O (BaseField O) F

section Fields

variable (K K' : Type) [Field K] [Field K'] [Algebra K K']

/-- A nonzero `q` with `K'[X]/(q)` reduced is squarefree. -/
theorem squarefree_of_isReduced_adjoinRoot (q : K'[X]) (hq : q ≠ 0)
    (hred : IsReduced (AdjoinRoot q)) : Squarefree q := by
  rintro g ⟨h, rfl⟩
  have hgh : g * h ≠ 0 := by rintro h0; apply hq; rw [mul_assoc, h0, mul_zero]
  have h0 := (show IsNilpotent (AdjoinRoot.mk (g * g * h) (g * h)) from
    ⟨2, by rw [← map_pow, AdjoinRoot.mk_eq_zero]; exact ⟨h, by ring⟩⟩).eq_zero
  rw [AdjoinRoot.mk_eq_zero, mul_assoc] at h0
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hgh).1 (by simpa using h0))

/-- Along a finite separable extension `K'/K`, the image of an irreducible polynomial stays
squarefree (`K' ⊗_K K[X]/(g)` is formally unramified over the field `K[X]/(g)`, hence reduced). -/
theorem squarefree_map_of_isSeparable [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    (g : K[X]) [Fact (Irreducible g)] : Squarefree (g.map (algebraMap K K')) := by
  have : Algebra.FormallyUnramified K K' := .of_isSeparable K K'
  have hred : IsReduced (TensorProduct K (AdjoinRoot g) K') :=
    Algebra.FormallyUnramified.isReduced_of_field (AdjoinRoot g) _
  obtain ⟨e, -⟩ := adjoinRoot_tensor K K' g
  let c := (Algebra.TensorProduct.comm K K' (AdjoinRoot g)).toRingEquiv
  exact squarefree_of_isReduced_adjoinRoot K' _ (map_ne_zero (Fact.out : Irreducible g).ne_zero)
    (isReduced_of_injective (c.toRingHom.comp e.symm.toRingEquiv.toRingHom)
      (c.injective.comp e.symm.injective))

/-- The root-field map `K[X]/(g) → K'[X]/(h)` for `h ∣ g` over `K'`. -/
private def rootHom (g : K[X]) (h : K'[X]) (hdvd : h ∣ g.map (algebraMap K K')) :
    AdjoinRoot g →ₐ[K] AdjoinRoot h :=
  AdjoinRoot.liftAlgHom g (Algebra.ofId K (AdjoinRoot h)) (AdjoinRoot.root h) (by
    change g.eval₂ (algebraMap K (AdjoinRoot h)) _ = 0
    rwa [IsScalarTower.algebraMap_eq K K' (AdjoinRoot h), ← eval₂_map, ← aeval_def,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero])

/-- `K'[X]/(h)` is separable over `K[X]/(g)` when `K'/K` is separable: it is generated over
`K[X]/(g)` by the separable elements of `K'`. -/
private theorem rootHom_isSeparable [Algebra.IsSeparable K K'] (g : K[X]) [Fact (Irreducible g)]
    (h : K'[X]) [Fact (Irreducible h)] (hdvd : h ∣ g.map (algebraMap K K')) :
    letI := (rootHom K K' g h hdvd).toRingHom.toAlgebra
    Algebra.IsSeparable (AdjoinRoot g) (AdjoinRoot h) := by
  let := (rootHom K K' g h hdvd).toRingHom.toAlgebra
  have : IsScalarTower K (AdjoinRoot g) (AdjoinRoot h) :=
    .of_algebraMap_eq fun x ↦ ((rootHom K K' g h hdvd).commutes x).symm
  rw [← separableClosure.eq_top_iff, eq_top_iff]
  rintro x -
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on with
    | C a =>
      rw [AdjoinRoot.mk_C]
      exact mem_separableClosure_iff.2 <| ((Algebra.IsSeparable.isSeparable K a).map
        (IsScalarTower.toAlgHom K K' (AdjoinRoot h)) (RingHom.injective _)).tower_top _
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
      refine mul_mem ih ?_
      rw [show AdjoinRoot.root h = rootHom K K' g h hdvd (AdjoinRoot.root g) from
        (AdjoinRoot.liftAlgHom_root _ _ _ _).symm]
      exact IntermediateField.algebraMap_mem _ _

end Fields

/-- The ascent step: let `O → Oδ` be finite, `K = Frac O`, and `Kδ/K` finite separable (with
compatible structures). If `g` is monic irreducible over `K` with finite `O`-closure of
`K[X]/(g)`, and `h` is an irreducible factor of `g` over `Kδ`, then the `Oδ`-closure of
`Kδ[X]/(h)` is finite over `Oδ`. -/
theorem closure_finite_ascent_root (O Oδ K Kδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [Algebra O Oδ] [Module.Finite O Oδ]
    [Field K] [Algebra O K] [IsFractionRing O K] [Field Kδ] [Algebra K Kδ] [Algebra O Kδ]
    [Algebra Oδ Kδ] [IsScalarTower O K Kδ] [IsScalarTower O Oδ Kδ] [FiniteDimensional K Kδ]
    [Algebra.IsSeparable K Kδ] (g : K[X]) (hgm : g.Monic) (hgi : Irreducible g)
    (hfin : Module.Finite O (integralClosure O (AdjoinRoot g)))
    (h : Kδ[X]) (hhi : Irreducible h) (hdvd : h ∣ g.map (algebraMap K Kδ)) :
    Module.Finite Oδ (integralClosure Oδ (AdjoinRoot h)) := by
  have : Fact (Irreducible g) := ⟨hgi⟩
  have : Fact (Irreducible h) := ⟨hhi⟩
  have : FiniteDimensional K (AdjoinRoot g) := hgm.finite_adjoinRoot
  have : FiniteDimensional Kδ (AdjoinRoot h) := (AdjoinRoot.powerBasis hhi.ne_zero).finite
  have : FiniteDimensional K (AdjoinRoot h) := Module.Finite.trans Kδ _
  let := (rootHom K Kδ g h hdvd).toRingHom.toAlgebra
  have : IsScalarTower K (AdjoinRoot g) (AdjoinRoot h) :=
    .of_algebraMap_eq fun x ↦ ((rootHom K Kδ g h hdvd).commutes x).symm
  have : FiniteDimensional (AdjoinRoot g) (AdjoinRoot h) := .of_restrictScalars_finite K _ _
  have := rootHom_isSeparable K Kδ g h hdvd
  have : IsScalarTower O (AdjoinRoot g) (AdjoinRoot h) := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply O K (AdjoinRoot h),
      IsScalarTower.algebraMap_apply O K (AdjoinRoot g),
      IsScalarTower.algebraMap_apply K (AdjoinRoot g) (AdjoinRoot h)]
  exact closure_finite_ascent O Oδ (AdjoinRoot h)
    (closure_finite_of_separable_tower O K (AdjoinRoot g) (AdjoinRoot h) hfin)

/-- `K[X]/(g)` is separable over `K` when `g` is irreducible and separable. -/
private theorem adjoinRoot_isSeparable {K : Type} [Field K] (g : K[X]) [Fact (Irreducible g)]
    (hs : g.Separable) : Algebra.IsSeparable K (AdjoinRoot g) := by
  have hx : IsSeparable K (AdjoinRoot.root g) :=
    hs.of_dvd (minpoly.dvd K _ (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]))
  have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot g)).2 hx
  refine ⟨fun y ↦ IntermediateField.isSeparable_of_mem_isSeparable K (AdjoinRoot g)
    (L := IntermediateField.adjoin K {AdjoinRoot.root g}) ?_⟩
  have : y ∈ Algebra.adjoin K {AdjoinRoot.root g} := by rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
  exact IntermediateField.algebra_adjoin_le_adjoin K _ this

/-- For `g` irreducible and separable over `Frac O`, the integral closure of `O` in `K[X]/(g)` is
a finite `O`-module. -/
theorem closure_finite_of_separable (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (g : (FractionRing O)[X]) (hirr : Irreducible g)
    (hs : g.Separable) : Module.Finite O (integralClosure O (AdjoinRoot g)) := by
  have : Fact (Irreducible g) := ⟨hirr⟩
  have : Module.Finite (FractionRing O) (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have := adjoinRoot_isSeparable g hs
  exact IsIntegralClosure.finite O (FractionRing O) (AdjoinRoot g) _

/-- A route-F polynomial type is a polynomial type (forget the closure-finiteness witnesses). -/
theorem HasPolynomialTypeF.to_original {O : Type} [CommRing O] [IsDomain O]
    {F : (BaseField O)[X]} {σ : FactorType} (h : HasPolynomialTypeF O F σ) :
    HasPolynomialType O F σ :=
  let ⟨gs, h1, h2, hF, hσ, _⟩ := h; ⟨gs, h1, h2, hF, hσ⟩

/-- For separable `F` the route-F and original polynomial types agree: every factor is
separable, so its closure is finite by `closure_finite_of_separable`. -/
theorem hasPolynomialTypeF_iff_of_separable (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {F : (BaseField O)[X]} {σ : FactorType} (hs : F.Separable) :
    HasPolynomialTypeF O F σ ↔ HasPolynomialType O F σ :=
  ⟨HasPolynomialTypeF.to_original, fun ⟨gs, h1, h2, hF, hσ⟩ => ⟨gs, h1, h2, hF, hσ, fun g hg =>
    closure_finite_of_separable O g (h1 g hg).2 (hs.of_dvd (hF ▸ List.dvd_prod hg))⟩⟩

/-! ### Polynomial types -/

section TypeDvd

open UniqueFactorizationMonoid

open scoped Classical in
/-- A squarefree monic polynomial whose irreducible factors have finite closures has a type. -/
theorem squarefree_monic_has_polynomial_type (O : Type) [CommRing O] [IsDomain O]
    (F : Polynomial (BaseField O)) (hF : F.Monic) (hsq : Squarefree F)
    (hfin : ∀ g ∈ normalizedFactors F, Module.Finite O (integralClosure O (AdjoinRoot g))) :
    ∃ σ : FactorType, HasPolynomialTypeF O F σ := by
  have h0 : F ≠ 0 := hF.ne_zero
  have hmon : ∀ g ∈ normalizedFactors F, g.Monic := fun g hg ↦ by
    rw [← normalize_normalized_factor g hg]
    exact monic_normalize (irreducible_of_normalized_factor g hg).ne_zero
  have hprod : (normalizedFactors F).toList.prod = F := by
    rw [Multiset.prod_toList]
    exact eq_of_monic_of_associated (by simpa using monic_multiset_prod_of_monic _ id hmon) hF
      (prod_normalizedFactors h0)
  refine ⟨_, (normalizedFactors F).toList, fun g hg ↦ ?_, ?_, hprod.symm, rfl,
    fun g hg ↦ hfin g (Multiset.mem_toList.1 hg)⟩
  · rw [Multiset.mem_toList] at hg
    exact ⟨hmon g hg, irreducible_of_normalized_factor g hg⟩
  · change List.Nodup _
    rw [← Multiset.coe_nodup, Multiset.coe_toList]
    exact (squarefree_iff_nodup_normalizedFactors h0).1 hsq

/-- A monic divisor of a polynomial with a type has a type. -/
theorem polynomial_type_dvd (O : Type) [CommRing O] [IsDomain O]
    (F G : Polynomial (BaseField O)) (σ : FactorType)
    (hF : HasPolynomialTypeF O F σ) (hG : G.Monic) (hdvd : G ∣ F) :
    ∃ τ : FactorType, HasPolynomialTypeF O G τ := by
  classical
  obtain ⟨gs, hgs, hpw, rfl, -, hfin⟩ := hF
  have hNF : normalizedFactors gs.prod = (gs : Multiset _) := by
    rw [← Multiset.prod_coe, normalizedFactors_prod_eq _ fun g hg ↦ (hgs g hg).2]
    exact (Multiset.map_congr rfl fun g hg ↦ (hgs g hg).1.normalize_eq_self).trans
      (Multiset.map_id _)
  have hF0 : gs.prod ≠ 0 := fun h0 ↦ (hgs 0 (List.prod_eq_zero_iff.1 h0)).2.ne_zero rfl
  have hle : normalizedFactors G ≤ (gs : Multiset _) :=
    hNF ▸ (dvd_iff_normalizedFactors_le_normalizedFactors hG.ne_zero hF0).1 hdvd
  exact squarefree_monic_has_polynomial_type O G hG
    ((squarefree_iff_nodup_normalizedFactors hG.ne_zero).2
      (Multiset.nodup_of_le hle (Multiset.coe_nodup.2 hpw)))
    fun g hg ↦ hfin g (Multiset.mem_coe.1 (Multiset.mem_of_le hle hg))

end TypeDvd

/-! ### Algebra types -/

/-- Algebra types are invariant under `O`-algebra isomorphism. -/
theorem algebra_type_algEquiv (O : Type) [CommRing O] [IsDomain O] (B B' : Type) [CommRing B]
    [CommRing B'] [Algebra O B] [Algebra O B'] (e : B ≃ₐ[O] B') (σ : FactorType)
    (h : HasAlgebraType O B σ) : HasAlgebraType O B' σ := by
  obtain ⟨ι, hι, L, hF, hA, hA2, hT, hD, e₀, hσ⟩ := h
  exact ⟨ι, hι, L, hF, hA, hA2, hT, hD,
    (Algebra.TensorProduct.congr AlgEquiv.refl e).symm.trans e₀, hσ⟩

/-- Algebra types only depend on the generic fibre: an isomorphism `K ⊗_O A ≃ K ⊗_O B` transports
the type of `B` to `A`. -/
theorem algebra_type_of_generic_fibre_equiv (O : Type) [CommRing O] [IsDomain O] (A B : Type)
    [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
    (e : TensorProduct O (BaseField O) A ≃ₐ[BaseField O] TensorProduct O (BaseField O) B)
    (σ : FactorType) (h : HasAlgebraType O B σ) : HasAlgebraType O A σ := by
  obtain ⟨ι, i1, L, i2, i3, i4, i5, i6, g, hg⟩ := h
  exact ⟨ι, i1, L, i2, i3, i4, i5, i6, e.trans g, hg⟩

/-- The type of a finite product of algebras is the sum of their types. -/
theorem algebra_type_pi (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (B : Fin n → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)] (σ : Fin n → FactorType)
    (h : ∀ j, HasAlgebraType O (B j) (σ j)) : HasAlgebraType O (∀ j, B j) (∑ j, σ j) := by
  choose ι hι L hF hKL hOL hST hFD e hσ using h
  let K := BaseField O
  let Lp : (Σ j, ι j) → Type := fun p ↦ L p.1 p.2
  let c : (∀ p : (Σ j, ι j), Lp p) ≃ₐ[K] ∀ j, ∀ i, L j i :=
    { toEquiv := Equiv.piCurry (fun j i ↦ L j i)
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  refine ⟨Σ j, ι j, inferInstance, Lp, fun p ↦ hF p.1 p.2, fun p ↦ hKL p.1 p.2,
    fun p ↦ hOL p.1 p.2, fun p ↦ hST p.1 p.2, fun p ↦ hFD p.1 p.2,
    ((Algebra.TensorProduct.piRight O K K B).trans (AlgEquiv.piCongrRight e)).trans c.symm,
    ?_, fun p ↦ (hσ p.1).2 p.2⟩
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun j _ ↦ (hσ j).1

/-! ### Integral closures in finite extensions -/

/-- An `O`-algebra isomorphism `L ≃ L'` restricts to the integral closures of `O`. -/
theorem integral_closure_algEquiv (O L L' : Type) [CommRing O] [CommRing L] [CommRing L']
    [Algebra O L] [Algebra O L'] (e : L ≃ₐ[O] L') :
    ∃ φ : integralClosure O L ≃ₐ[O] integralClosure O L',
      ∀ x : integralClosure O L, (φ x : L') = e x :=
  ⟨(e.subalgebraMap (integralClosure O L)).trans
    (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e)), fun _ ↦ rfl⟩

/-- If the integral closure of a DVR `O` in a finite extension `L/K` is finite over `O`, it is
free of rank `[L : K]`. -/
theorem integral_closure_finite_free (O K L : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L]
    [Algebra K L] [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L]
    [hfin : Module.Finite O (integralClosure O L)] :
    Module.Finite O (integralClosure O L) ∧ Module.Free O (integralClosure O L) ∧
      Module.finrank O (integralClosure O L) = Module.finrank K L := by
  have := faithfulSMul_of_isFractionRing O K L
  have : Module.IsTorsionFree O L := .trans_faithfulSMul O K L
  have : Module.IsTorsionFree O (integralClosure O L) := IsIntegralClosure.isTorsionFree O L
  have : IsNoetherian O (integralClosure O L) := isNoetherian_of_isNoetherianRing_of_finite _ _
  refine ⟨hfin, inferInstance, ?_⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure O L) (nonZeroDivisors O)) L :=
    IsIntegralClosure.isLocalization O K L (integralClosure O L)
  rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis
    (Module.Basis.localizationLocalization K (nonZeroDivisors O) L
      (Module.Free.chooseBasis O (integralClosure O L)))]

/-- Over a complete DVR with finite residue field, if the (finite) integral closure of `O` in
`L` is local, its ramification index and inertia degree are positive with `e · f = [L : K]`. -/
theorem integral_closure_invariants_degree (O K L : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L]
    [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Module.Finite O (integralClosure O L)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (hlocal : IsLocalRing (integralClosure O L)) :
    letI : IsLocalRing (integralClosure O L) := hlocal;
      0 < (IsLocalRing.maximalIdeal (integralClosure O L)).ramificationIdx O ∧
      0 < (IsLocalRing.maximalIdeal (integralClosure O L)).inertiaDeg O ∧
      (IsLocalRing.maximalIdeal (integralClosure O L)).ramificationIdx O *
        (IsLocalRing.maximalIdeal (integralClosure O L)).inertiaDeg O = Module.finrank K L := by
  obtain ⟨-, _, hrank⟩ := integral_closure_finite_free O K L
  refine ⟨Ideal.ramificationIdx_pos _ _, Ideal.inertiaDeg_pos _ _, ?_⟩
  rw [finite_flat_local_ramification_degree O (integralClosure O L), hrank]

/-- The integral closure of a DVR `O` in a finite extension of `K = Frac O`, assumed finite over
`O`, is not a field. -/
theorem integral_closure_not_field (O K L : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L]
    [Algebra K L] [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Module.Finite O (integralClosure O L)] : ¬ IsField (integralClosure O L) := fun h ↦ by
  have := faithfulSMul_of_isFractionRing O K L
  exact IsDiscreteValuationRing.not_isField O (isField_of_isIntegral_of_isField
    (fun a b hab ↦ FaithfulSMul.algebraMap_injective O L (congrArg Subtype.val hab)) h)

/-- The maximal ideals of a finite product of fields `∏ Lᵢ` are exactly the kernels of the
projections, and distinct projections have distinct kernels. -/
theorem pi_field_maximal_ideals (ι : Type) [Finite ι] (L : ι → Type) [∀ i, Field (L i)]
    (m : Ideal (∀ i, L i)) :
    (m.IsMaximal ↔ ∃ i, m = RingHom.ker (Pi.evalRingHom L i)) ∧ ∀ i j : ι,
      RingHom.ker (Pi.evalRingHom L i) = RingHom.ker (Pi.evalRingHom L j) → i = j := by
  have := Fintype.ofFinite ι
  classical
  have hmax : ∀ i, (RingHom.ker (Pi.evalRingHom L i)).IsMaximal := fun i ↦
    RingHom.ker_isMaximal_of_surjective _ (Function.surjective_eval i)
  refine ⟨⟨fun hm ↦ ?_, fun ⟨i, hi⟩ ↦ hi ▸ hmax i⟩, fun i j h ↦ ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, (Pi.single i (1 : L i) : ∀ i, L i) ∉ m := by
      by_contra! hc
      apply hm.ne_top
      rw [Ideal.eq_top_iff_one, show (1 : ∀ i, L i) = ∑ i, Pi.single i (1 : L i) by
        ext k; simp [Finset.sum_apply]]
      exact Ideal.sum_mem _ fun i _ ↦ hc i
    refine ⟨i, ((hmax i).eq_of_le hm.ne_top fun x (hx : x i = 0) ↦ ?_).symm⟩
    have hxe : x = ∑ j ∈ Finset.univ.erase i, x * (Pi.single j (1 : L j) : ∀ i, L i) := by
      ext k
      rw [← Finset.mul_sum, Pi.mul_apply, Finset.sum_apply]
      by_cases hk : k = i
      · subst hk; simp [hx]
      · rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb; simp [hb]
        · simp [hk]
    rw [hxe]
    refine Ideal.sum_mem _ fun j hj ↦ Ideal.mul_mem_left _ _ ?_
    have h0 : (Pi.single i (1 : L i) : ∀ i, L i) * Pi.single j (1 : L j) = 0 := by
      ext k; by_cases hk : k = i
      · subst hk; simp [Ne.symm (Finset.ne_of_mem_erase hj)]
      · simp [hk]
    exact (hm.isPrime.mem_or_mem (h0 ▸ m.zero_mem)).resolve_left hi
  · by_contra hij
    have : (Pi.single j (1 : L j) : ∀ i, L i) ∈ RingHom.ker (Pi.evalRingHom L i) := by
      simp [RingHom.mem_ker, Ne.symm hij]
    simp [h, RingHom.mem_ker] at this

/-! ### Unramified base change -/

/-- For a finite free extension of DVRs `O → Oδ` of rank `δ` in which a uniformizer stays
irreducible, `K ⊗_O Oδ` is a field of degree `δ` over `K` and a fraction field of `Oδ`. -/
theorem unramified_fraction_base_change (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ)
    (pi : O) (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi)) :
    IsField (TensorProduct O (BaseField O) Oδ) ∧ Module.finrank (BaseField O)
      (TensorProduct O (BaseField O) Oδ) = δ
      ∧ (letI : Algebra Oδ (TensorProduct O (BaseField O) Oδ) := Algebra.TensorProduct.rightAlgebra;
        IsFractionRing Oδ (TensorProduct O (BaseField O) Oδ)) := by
  have hinj : Function.Injective (algebraMap O Oδ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hpi
    rw [map_mul, map_pow] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact (Units.map (algebraMap O Oδ : O →* Oδ) u).ne_zero h
    · exact hpiδ.ne_zero (pow_eq_zero_iff'.mp h).1
  let : Algebra Oδ (TensorProduct O (BaseField O) Oδ) := Algebra.TensorProduct.rightAlgebra
  have hle : Algebra.algebraMapSubmonoid Oδ (nonZeroDivisors O) ≤ nonZeroDivisors Oδ := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha))
  have : IsDomain (TensorProduct O (BaseField O) Oδ) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (TensorProduct O (BaseField O) Oδ) hle
  have hfield : IsField (TensorProduct O (BaseField O) Oδ) :=
    isField_of_isIntegral_of_isField' (R := BaseField O) (Field.toIsField _)
  refine ⟨hfield, by rw [Module.finrank_baseChange, hrank], ?_⟩
  let := hfield.toField
  have : FaithfulSMul Oδ (TensorProduct O (BaseField O) Oδ) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid Oδ (nonZeroDivisors O)) z
  refine ⟨x, s, (eq_div_iff ?_).2 (IsLocalization.mk'_spec _ x s)⟩
  exact (map_ne_zero_iff _ (IsLocalization.injective _ hle)).mpr (nonZeroDivisors.ne_zero (hle s.2))

/-- In the unramified situation of `unramified_fraction_base_change`, a presentation of the
`Oδ`-generic fibre of an `Oδ`-algebra `B` as a product of fields `Lᵢ` induces compatible
`K`- and `O`-structures on the `Lᵢ` and a presentation of the `O`-generic fibre of `B`. -/
theorem unramified_generic_fibre_witness (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ)
    (pi : O) (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi))
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (B : Type)
    [CommRing B] [Algebra O B] [Algebra Oδ B] [IsScalarTower O Oδ B] (ι : Type)
    (L : ι → Type) [∀ i, Field (L i)] [∀ i, Algebra (BaseField Oδ) (L i)] [∀ i, Algebra Oδ (L i)]
    [∀ i, IsScalarTower Oδ (BaseField Oδ) (L i)] [∀ i, FiniteDimensional (BaseField Oδ) (L i)]
    (e : TensorProduct Oδ (BaseField Oδ) B ≃ₐ[BaseField Oδ] (∀ i, L i)) :
    ∃ (_ : ∀ i, Algebra (BaseField O) (L i)) (_ : ∀ i, Algebra O (L i))
      (_ : ∀ i, IsScalarTower O (BaseField O) (L i)) (_ : ∀ i, IsScalarTower O Oδ (L i))
      (_ : ∀ i, FiniteDimensional (BaseField O) (L i))
      (_ : TensorProduct O (BaseField O) B ≃ₐ[BaseField O] (∀ i, L i)), True := by
  obtain ⟨-, -, hfr⟩ := unramified_fraction_base_change O Oδ δ hrank pi hpi hpiδ
  let K := BaseField O
  let Kδ := BaseField Oδ
  let rA : Algebra Oδ (K ⊗[O] Oδ) := Algebra.TensorProduct.rightAlgebra
  have : IsFractionRing Oδ (K ⊗[O] Oδ) := hfr
  let χ : K ⊗[O] Oδ ≃ₐ[Oδ] Kδ := IsLocalization.algEquiv (nonZeroDivisors Oδ) (K ⊗[O] Oδ) Kδ
  let χ' : Oδ ⊗[O] K ≃ₐ[Oδ] Kδ :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm O Oδ K).toRingEquiv.trans χ.toRingEquiv)
      fun d ↦ χ.commutes d
  let φ : K →+* Kδ := χ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom
  let aKKδ : Algebra K Kδ := φ.toAlgebra
  have : Module.Finite K Kδ := .equiv
    { χ.toRingEquiv with
      map_smul' := fun k x ↦ by
        change χ (k • x) = φ k * χ x
        rw [Algebra.smul_def (R := K) k x, map_mul]
        rfl : K ⊗[O] Oδ ≃ₗ[K] Kδ }
  let E : K ⊗[O] B ≃+* (∀ i, L i) :=
    (Algebra.TensorProduct.comm O K B).toRingEquiv.trans <|
    (Algebra.TensorProduct.cancelBaseChange O Oδ Oδ B K).symm.toRingEquiv.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := Oδ) (A₁ := B)) χ').toRingEquiv.trans <|
    (Algebra.TensorProduct.comm Oδ B Kδ).toRingEquiv.trans e.toRingEquiv
  let aK : ∀ i, Algebra K (L i) := fun i ↦ ((algebraMap Kδ (L i)).comp φ).toAlgebra
  let aO : ∀ i, Algebra O (L i) := fun i ↦
    ((algebraMap Oδ (L i)).comp (algebraMap O Oδ)).toAlgebra
  have : ∀ i, IsScalarTower K Kδ (L i) := fun i ↦ .of_algebraMap_eq' rfl
  have t2 : ∀ i, IsScalarTower O Oδ (L i) := fun i ↦ .of_algebraMap_eq' rfl
  have t3 : ∀ i, IsScalarTower O K (L i) := fun i ↦ .of_algebraMap_eq fun c ↦ by
    change algebraMap Oδ (L i) (algebraMap O Oδ c) =
      algebraMap Kδ (L i) (χ (algebraMap O K c ⊗ₜ[O] 1))
    have h1 : algebraMap O K c ⊗ₜ[O] (1 : Oδ) = algebraMap Oδ (K ⊗[O] Oδ) (algebraMap O Oδ c) := by
      change _ = (1 : K) ⊗ₜ[O] algebraMap O Oδ c
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [h1, χ.commutes]
    exact IsScalarTower.algebraMap_apply Oδ Kδ (L i) _
  refine ⟨aK, aO, t3, t2, fun i ↦ Module.Finite.trans Kδ (L i),
    AlgEquiv.ofRingEquiv (f := E) fun x ↦ ?_, trivial⟩
  funext i
  change e (Algebra.TensorProduct.comm Oδ B Kδ
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := Oδ) (A₁ := B)) χ'
      ((Algebra.TensorProduct.cancelBaseChange O Oδ Oδ B K).symm ((1 : B) ⊗ₜ[O] x)))) i =
    algebraMap Kδ (L i) (χ (x ⊗ₜ[O] 1))
  rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
  simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.comm_tmul]
  change e (algebraMap Kδ (Kδ ⊗[Oδ] B) (χ (x ⊗ₜ[O] 1))) i = _
  rw [e.commutes]
  rfl

end SurfaceBlowup
