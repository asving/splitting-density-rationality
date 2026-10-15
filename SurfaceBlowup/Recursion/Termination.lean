/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Measure.MemberCharts
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# Termination of the recursion

Inputs for the termination step of Theorem 8.1. We construct the index map of a curve on a
concrete surface, control division charts under perturbation, attach homogeneous tangent divisors
and allowed patterns to initial forms, compute the volume of the state set of a concrete member,
build the child member at the point at infinity, and prove that the recursion terminates outside
the return and bad-exit events. We also show that order defects decrease along unramified towers
and add over products.

## Main results

* `concrete_index_map_reindexed`: the reindexed index map with cokernel length `d(d-1)/2`.
* `allowed_pattern_of_divisor`: a tangent divisor has an allowed pattern.
* `concrete_member_volume`: the volume of the state set of a concrete member.
* `child_ideal_set_map_iff_stateSet`, `infinity_point_child_member`: child members.
* `etale_type_event_eq_term`, `nonterminating_subset_return_or_bad`: termination.
* `order_defect_le_of_tower`, `order_defect_pi`: order defects.

Provenance: `Thm_SurfaceBlowupV2_{concrete_index_map_reindexed,
division_data_vertical_perturbation, division_quotient_basis_equiv,
divisor_affine_polynomial_normalized_factors, divisor_degree_pattern_weight,
allowed_pattern_of_divisor, equiv_of_fiber_card_eq, full_rank_free_submodule_finite_length,
global_function_of_two_chart_curve_data, has_multiplicity_initial_form,
homogeneous_divisor_of_polynomial, homogeneous_divisor_boundary_multiplicities,
ideal_atlas_reindex, concrete_member_volume, ideal_data_along_ringEquiv,
child_ideal_set_map_iff_stateSet, infinity_point_child_member, initial_form_has_tangent_divisor,
length_le_length_restrict, list_get_fiber_card_count, mem_integralClosure_pi_iff,
integralClosure_pi_equiv, generic_closure_free_of_type, nonself_cell_child_rank_lt,
etale_terminates_of_invariant, etale_type_event_eq_term, nonterminating_subset_return_or_bad,
order_defect_le_of_tower, order_defect_pi}`.
-/

namespace SurfaceBlowup

open IsLocalRing MeasureTheory
open scoped BigOperators ENNReal

/-! ### Index maps and division charts -/

/-- The index map of a curve on a concrete surface, reindexed along an enumeration `e` of the
points of its two-chart curve data: an injective `O`-algebra map from `R/(f)` into the product of
the local curve orders, with cokernel of length `d(d-1)/2`. -/
theorem concrete_index_map_reindexed (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b) beta) (f : ConcreteSurface O pi u a b)
    (G : GluedGenerators (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
    beta (curveDataDegree D)) (hf : ∀ j : ℕ, surfaceToCechInput (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b) j f = (cechInputLattice (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b) j).mkQ (gluedFunctionPair
    (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b) G j))
    (hG : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b))^j) (G.left j)} = leftLevelKernel D j ∧ Ideal.span
    {Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
    (surfaceT O pi u a b))^j) (G.right j)} = rightLevelKernel D j) (n : ℕ) (e : Fin n ≃ AllPoints D)
    (B : Fin n → Type) [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)]
    (eB : ∀ j, B j ≃+* (localRing D (e j) ⧸ Ideal.span {localCurve D (e j)}))
    (hB : ∀ (j : Fin n) (c : O), (eB j) (algebraMap O (B j) c) = Ideal.Quotient.mk
    (Ideal.span {localCurve D (e j)}) (localFromSurface D (e j)
    (algebraMap O (ConcreteSurface O pi u a b) c))) :
    ∃ ψ : ((ConcreteSurface O pi u a b) ⧸ Ideal.span {f}) →ₐ[O] ∀ j, B j, Function.Injective ψ ∧
      Module.length O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) =
      (chooseTwo (curveDataDegree D) : ℕ∞) ∧ ∀ (r : (ConcreteSurface O pi u a b)) (j : Fin n),
      (eB j) (ψ (Ideal.Quotient.mk (Ideal.span {f}) r) j) = Ideal.Quotient.mk
      (Ideal.span {localCurve D (e j)}) (localFromSurface D (e j) r) := by
  obtain ⟨φ, hφ, hker, hlen⟩ := concrete_curve_order_index O pi hpi u a b ha beta D f G hf hG
  let _ : ∀ p : AllPoints D, Algebra O (localRing D p) := fun p =>
    ((localFromSurface D p).comp (algebraMap O (ConcreteSurface O pi u a b))).toAlgebra
  set χ := childOrderMap D with hχ
  let E : childOrder D ≃+* ∀ j, B j :=
    (RingEquiv.piCongrLeft (fun p => localRing D p ⧸ Ideal.span {localCurve D p}) e).symm.trans
      (RingEquiv.piCongrRight fun j => (eB j).symm)
  have hE : ∀ x j, E x j = (eB j).symm (x (e j)) := fun x j => rfl
  have hχapp : ∀ r p, χ r p = Ideal.Quotient.mk (Ideal.span {localCurve D p})
      (localFromSurface D p r) :=
    fun r p => rfl
  have hEalg : ∀ (c : O) (j : Fin n), E (algebraMap O (childOrder D) c) j = algebraMap O (B j)
      c := by
    intro c j
    rw [hE]
    apply (eB j).injective
    rw [RingEquiv.apply_symm_apply, hB]
    rfl
  have hsub : Ideal.span {f} ≤ RingHom.ker (E.toRingHom.comp χ) := by
    intro r hr
    rw [← hker] at hr
    simp only [RingHom.mem_ker, RingHom.comp_apply] at hr ⊢
    rw [hr, map_zero]
  let ψ₀ : ConcreteSurface O pi u a b ⧸ Ideal.span {f} →+* ∀ j, B j :=
    Ideal.Quotient.lift (Ideal.span {f}) (E.toRingHom.comp χ) (fun r hr => hsub hr)
  have hψ₀ : ∀ r, ψ₀ (Ideal.Quotient.mk _ r) = E (χ r) := fun r => rfl
  let ψ : (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) →ₐ[O] ∀ j, B j :=
    { ψ₀ with
      commutes' := by
        intro c
        change ψ₀ (Ideal.Quotient.mk _ (algebraMap O _ c)) = _
        rw [hψ₀]
        funext j
        rw [Pi.algebraMap_apply, ← hEalg]
        congr 2 }
  have hψ : ∀ r, ψ (Ideal.Quotient.mk _ r) = E (χ r) := fun r => rfl
  let L : childOrder D ≃ₗ[O] ∀ j, B j :=
    { E.toAddEquiv with
      map_smul' := by
        intro c x
        funext j
        change E (c • x) j = c • E x j
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, Pi.mul_apply, hEalg] }
  have hL : ∀ x, L x = E x := fun x => rfl
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hψ, hψ] at hxy
    rw [Ideal.Quotient.eq, ← hker, RingHom.mem_ker, map_sub, E.injective hxy, sub_self]
  · have hrange : LinearMap.range ψ.toLinearMap = (LinearMap.range φ).map L.toLinearMap := by
      ext y
      simp only [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨q, rfl⟩
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
        exact ⟨φ r, ⟨r, rfl⟩, by rw [hφ]; rfl⟩
      · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
        exact ⟨Ideal.Quotient.mk _ r, by rw [hφ]; rfl⟩
    rw [← hlen]
    exact (Submodule.Quotient.equiv _ _ L hrange.symm).symm.length_eq
  · intro r j
    rw [hψ, hE, RingEquiv.apply_symm_apply]
    rfl

/-- Division data survive a vertical perturbation `f ↦ f + π h` of the divisor. -/
theorem division_data_vertical_perturbation (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) (pi : O) (f : R) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    (hE : ∀ w, E.symm w = divisionMap f b w) [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)]
    (h : R) :
    ∃ E' : R ≃ₗ[O] ((Fin n → O) × R), ∀ w, E'.symm w = divisionMap (f + pi • h) b w := by
  set M := (Fin n → O) × R
  let r0 : M →ₗ[O] M := E.toLinearMap ∘ₗ (LinearMap.mulRight O h) ∘ₗ LinearMap.snd O (Fin n → O) R
  let rL : M →ₗ[O] M := pi • r0
  have hr : RaisesAdicOrder (Ideal.span {pi}) (rL : M → M) := by
    intro j x y hxy
    have h1 := linear_map_preserves_adic_congruence O M M (Ideal.span {pi}) r0 j x y hxy
    unfold adicCongr at h1 ⊢
    have : rL x - rL y = pi • (r0 x - r0 y) := by
      simp [rL, smul_sub]
    rw [this, pow_succ', Submodule.mul_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self pi) h1
  have hbij := adic_perturb_bijective O M (Ideal.span {pi}) (rL : M → M) hr
  let L : M →ₗ[O] R := E.symm.toLinearMap ∘ₗ (LinearMap.id + rL)
  have hL : ∀ w, L w = divisionMap (f + pi • h) b w := by
    intro w
    simp only [L, rL, r0, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply, LinearEquiv.coe_coe, map_add, map_smul, LinearEquiv.symm_apply_apply,
      LinearMap.mulRight_apply]
    rw [hE]
    unfold divisionMap
    rw [add_mul, smul_mul_assoc, mul_comm h]
    abel
  have hLb : Function.Bijective L := by
    have : (L : M → R) = E.symm ∘ adicPerturb (rL : M → M) := by
      funext w; simp [L, adicPerturb]
    rw [this]
    exact E.symm.bijective.comp hbij
  refine ⟨(LinearEquiv.ofBijective L hLb).symm, fun w => ?_⟩
  rw [LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply, hL]

/-- Division data for `f` give coordinates on `R/(f)`, inverse to the coordinate lift. -/
theorem division_quotient_basis_equiv (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (f : R) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    (hE : ∀ w, E.symm w = divisionMap f b w) :
    ∃ EB : (R ⧸ Ideal.span {f}) ≃ₗ[O] (Fin n → O), ∀ z : Fin n → O, EB.symm z = Ideal.Quotient.mk
      (Ideal.span {f}) (coordinateLift b z) := by
  obtain ⟨EC, hEC⟩ := division_equiv_child_coordinates O R n f b E hE
  refine ⟨EC, fun z => ?_⟩
  have h : E.symm (z, 0) = coordinateLift b z := by
    rw [hE]; simp [divisionMap]
  have h2 : E (coordinateLift b z) = (z, 0) := by rw [← h]; exact E.apply_symm_apply _
  rw [LinearEquiv.symm_apply_eq, hEC, h2]

/-! ### Tangent divisors and allowed patterns -/

open scoped Classical in
/-- The affine polynomial of an exceptional divisor is monic, and the multiplicity of each affine
direction among its normalized factors is the divisor's multiplicity. -/
theorem divisor_affine_polynomial_normalized_factors (k : Type) [Field k]
    (D : ExceptionalDivisor k) :
    (divisorAffinePolynomial k D).Monic ∧ ∀ φ : AffineDirection k, Multiset.count φ.val
      (UniqueFactorizationMonoid.normalizedFactors (divisorAffinePolynomial k D)) = D (some φ) := by
  let g : ClosedDirection k → ℕ → Polynomial k := fun P r =>
    match P with | none => 1 | some phi => phi.val ^ r
  have hg : ∀ P r, (g P r).Monic := by
    intro P r
    cases P with
    | none => exact Polynomial.monic_one
    | some phi => exact phi.property.1.pow r
  have hg0 : ∀ P r, g P r ≠ 0 := fun P r => (hg P r).ne_zero
  have hprod : divisorAffinePolynomial k D = ∏ P ∈ D.support, g P (D P) := rfl
  have key : ∀ s : Finset (ClosedDirection k),
      UniqueFactorizationMonoid.normalizedFactors (∏ P ∈ s, g P (D P)) =
        ∑ P ∈ s, UniqueFactorizationMonoid.normalizedFactors (g P (D P)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        UniqueFactorizationMonoid.normalizedFactors_mul (hg0 _ _)
          (Finset.prod_ne_zero_iff.mpr fun i _ => hg0 _ _), ih]
  have hnf : ∀ ψ : AffineDirection k, ∀ r,
      UniqueFactorizationMonoid.normalizedFactors (g (some ψ) r) = r • {ψ.val} := by
    intro ψ r
    change UniqueFactorizationMonoid.normalizedFactors (ψ.val ^ r) = _
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible ψ.property.2,
      (Polynomial.Monic.normalize_eq_self ψ.property.1)]
  refine ⟨?_, ?_⟩
  · rw [hprod]
    exact Polynomial.monic_prod_of_monic _ _ fun P _ => hg _ _
  · intro φ
    rw [hprod, key, Multiset.count_sum']
    rw [Finset.sum_eq_single (some φ)]
    · rw [hnf]; simp
    · intro P _ hP
      cases P with
      | none => simp [g]
      | some ψ =>
        rw [hnf]
        have : ψ.val ≠ φ.val := fun h => hP (by rw [Subtype.val_injective h])
        simp [Ne.symm this]
    · intro h
      rw [Finsupp.notMem_support_iff.mp h]
      simp [g]

/-- The contact conditions of a state `s` on an exceptional divisor `Dv` of degree `d`: `d` is at
most the contact `c` (and, for a crossing state, at most the second contact `h`), and `Dv` meets the
direction at infinity (resp. the zero direction) exactly when `d < c` (resp. `d < h`). -/
abbrev DivisorContactCondition (k : Type) [Field k] (s : State) (Dv : ExceptionalDivisor k)
    (d : ℕ) : Prop :=
  match s with
  | State.single _ c => d ≤ c ∧ (0 < Dv (infinityDirection k) ↔ d < c)
  | State.crossing _ _ c h => d ≤ c ∧ (0 < Dv (infinityDirection k) ↔ d < c) ∧ d ≤ h ∧
      (0 < Dv (zeroDirection k) ↔ d < h)

/-- The degree of an exceptional divisor splits as its boundary multiplicities plus the weighted
count of interior points by (degree, multiplicity). -/
private theorem divisor_degree_pattern_weight (k : Type) [Field k] [Finite k] (s : State)
    (Dv : ExceptionalDivisor k) (n : ℕ) (hdeg : ∀ Q, 0 < Dv Q → directionDegree k Q ≤ n)
    (hmult : ∀ Q, Dv Q ≤ n) :
    exceptionalDegree k Dv = Dv (infinityDirection k) +
      (match s with
        | State.single _ _ => (0 : ℕ)
        | State.crossing _ _ _ _ => Dv (zeroDirection k)) +
      ∑ ij : Fin n × Fin n, (ij.1.val + 1) * (ij.2.val + 1) *
        Nat.card {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧
          directionDegree k Q = ij.1.val + 1 ∧ Dv Q = ij.2.val + 1} := by
  classical
  have hpos : ∀ Q, 1 ≤ directionDegree k Q := by
    intro Q
    rcases Q with _ | φ
    · simp [directionDegree]
    · exact φ.2.2.natDegree_pos
  obtain ⟨B, hB, hBsum⟩ : ∃ B : Finset (ClosedDirection k),
      (∀ Q, Q ∈ boundaryDirections k s ↔ Q ∈ B) ∧
      ∑ Q ∈ B, directionDegree k Q * Dv Q = Dv (infinityDirection k) +
        (match s with
          | State.single _ _ => (0 : ℕ)
          | State.crossing _ _ _ _ => Dv (zeroDirection k)) := by
    cases s with
    | single _ _ =>
      exact ⟨{infinityDirection k}, fun Q => by simp [boundaryDirections],
        by simp [infinityDirection, directionDegree]⟩
    | crossing _ _ _ _ =>
      refine ⟨{infinityDirection k, zeroDirection k}, fun Q => by simp [boundaryDirections], ?_⟩
      rw [Finset.sum_pair (by simp [infinityDirection, zeroDirection])]
      simp [infinityDirection, zeroDirection, directionDegree]
  set f : ClosedDirection k → ℕ := fun Q => directionDegree k Q * Dv Q with hf
  have hdegsum : exceptionalDegree k Dv = ∑ Q ∈ Dv.support, f Q := rfl
  rw [hdegsum, ← Finset.sum_filter_add_sum_filter_not Dv.support (fun Q => Q ∈ B)]
  congr 1
  · rw [← hBsum]
    apply Finset.sum_subset
    · intro Q hQ; exact (Finset.mem_filter.1 hQ).2
    · intro Q _ hQ
      have : Dv Q = 0 := by
        by_contra h
        exact hQ (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 h, by assumption⟩)
      simp [f, this]
  · rcases n with _ | m
    · have : ∀ Q, Dv Q = 0 := fun Q => Nat.le_zero.1 (hmult Q)
      simp [this]
    · set g : ClosedDirection k → Fin (m+1) × Fin (m+1) :=
        fun Q => (⟨(directionDegree k Q - 1) % (m+1), Nat.mod_lt _ (Nat.succ_pos _)⟩,
          ⟨(Dv Q - 1) % (m+1), Nat.mod_lt _ (Nat.succ_pos _)⟩)
      rw [← Finset.sum_fiberwise_of_maps_to (s := Dv.support.filter (fun Q => Q ∉ B))
        (t := Finset.univ) (g := g) (fun _ _ => Finset.mem_univ _)]
      apply Finset.sum_congr rfl
      intro ij _
      have hmem : ∀ Q, Q ∈ (Dv.support.filter (fun Q => Q ∉ B)).filter (fun Q => g Q = ij) ↔
          (Q ∉ boundaryDirections k s ∧ directionDegree k Q = ij.1.val + 1 ∧ Dv Q = ij.2.val +
              1) := by
        intro Q
        simp only [Finset.mem_filter, Finsupp.mem_support_iff, hB, g, Prod.ext_iff, Fin.ext_iff]
        have h1 := hpos Q
        constructor
        · rintro ⟨⟨hne, hnb⟩, ha, hb⟩
          have hd := hdeg Q (Nat.pos_of_ne_zero hne)
          have hm := hmult Q
          rw [Nat.mod_eq_of_lt (by omega)] at ha hb
          exact ⟨hnb, by omega, by omega⟩
        · rintro ⟨hnb, ha, hb⟩
          refine ⟨⟨by omega, hnb⟩, ?_, ?_⟩
          · rw [ha, Nat.add_sub_cancel, Nat.mod_eq_of_lt ij.1.2]
          · rw [hb, Nat.add_sub_cancel, Nat.mod_eq_of_lt ij.2.2]
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun Q => (hmem Q).symm)),
        Nat.card_eq_finsetCard, Finset.sum_congr rfl (g := fun _ => (ij.1.val + 1) *
            (ij.2.val + 1)),
        Finset.sum_const, smul_eq_mul, mul_comm]
      intro Q hQ
      obtain ⟨_, ha, hb⟩ := (hmem Q).1 hQ
      simp [f, ha, hb]

private theorem card_le_of_weighted_sum_eq {ι : Type} [Fintype ι] (w c : ι → ℕ)
    (hw : ∀ i, 0 < w i) (e x y : ℕ) (hid : e = x + y + ∑ i, w i * c i) (i : ι) : c i ≤ e := by
  have := Finset.single_le_sum (f := fun i ↦ w i * c i) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)
  have := Nat.le_mul_of_pos_left (c i) (hw i)
  omega

/-- An exceptional divisor of degree `d` satisfying the contact conditions of the state has an
allowed tangent pattern of degree `d`. -/
theorem allowed_pattern_of_divisor (k : Type) [Field k] [Finite k] (s : State) (hs : s.Valid)
    (Dv : ExceptionalDivisor k) (d : ℕ) (hd : 0 < d) (hdeg : exceptionalDegree k Dv = d)
    (hQ : ∀ Q, 0 < Dv Q → directionDegree k Q ≤ d) (hmult : ∀ Q, Dv Q ≤ d)
    (hcontact : DivisorContactCondition k s Dv d) :
    ∃ P : TangentPattern s.degree, P.d.val = d ∧ Allowed s P ∧ HasPattern k s Dv P := by
  have hdn : d ≤ s.degree := by
    revert hs hcontact
    cases s with
    | single a c =>
      rintro ⟨ha, -⟩ ⟨h1, -⟩
      change d ≤ a * c
      nlinarith
    | crossing a b c h =>
      rintro ⟨ha, -⟩ ⟨h1, -⟩
      change d ≤ a * c + b * h
      nlinarith
  have hid := divisor_degree_pattern_weight k s Dv s.degree
      (fun Q hQ' => (hQ Q hQ').trans hdn) (fun Q => (hmult Q).trans hdn)
  have hcb := card_le_of_weighted_sum_eq _ _ (fun _ ↦ by positivity) _ _ _ hid
  rw [hdeg] at hid hcb
  have hcb' : ∀ ij : Fin s.degree × Fin s.degree, Nat.card {Q : ClosedDirection k //
      Q ∉ boundaryDirections k s ∧ directionDegree k Q = ij.1.val + 1 ∧ Dv Q = ij.2.val + 1}
      ≤ s.degree := fun ij => (hcb ij).trans hdn
  clear hcb
  revert hcontact hid hcb' hdn
  cases s with
  | single a c =>
    intro hcontact hdn hid hcb
    obtain ⟨h1, h2⟩ := hcontact
    refine ⟨⟨⟨d, by omega⟩,
      ⟨Dv (infinityDirection k), by have := hmult (infinityDirection k); omega⟩,
      ⟨0, by omega⟩, fun ij => ⟨_, hcb ij |> Nat.lt_succ_of_le⟩⟩, rfl, ?_, ?_⟩
    · refine ⟨hd, ?_, h1, rfl, h2⟩
      simp only [patternWeight]
      simp only at hid
      omega
    · exact ⟨hdeg, rfl, trivial, fun ij => rfl⟩
  | crossing a b c h =>
    intro hcontact hdn hid hcb
    obtain ⟨h1, h2, h3, h4⟩ := hcontact
    refine ⟨⟨⟨d, by omega⟩,
      ⟨Dv (infinityDirection k), by have := hmult (infinityDirection k); omega⟩,
      ⟨Dv (zeroDirection k), by have := hmult (zeroDirection k); omega⟩,
      fun ij => ⟨_, hcb ij |> Nat.lt_succ_of_le⟩⟩, rfl, ?_, ?_⟩
    · refine ⟨hd, ?_, h1, h3, h2, h4⟩
      simp only [patternWeight]
      simp only at hid
      omega
    · exact ⟨hdeg, rfl, rfl, fun ij => rfl⟩

/-! ### Auxiliary algebra -/

/-- Two finite types over `γ` with fibres of equal cardinality are equivalent over `γ`. -/
theorem equiv_of_fiber_card_eq (α β γ : Type) [Finite α] [Finite β] (f : α → γ) (g : β → γ)
    (h : ∀ c : γ, Nat.card {x : α // f x = c} = Nat.card {y : β // g y = c}) :
    ∃ e : α ≃ β, ∀ x, g (e x) = f x := by
  have e : ∀ c, {x : α // f x = c} ≃ {y : β // g y = c} := fun c => by
    haveI : Fintype {x : α // f x = c} := Fintype.ofFinite _
    haveI : Fintype {y : β // g y = c} := Fintype.ofFinite _
    exact Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using h c)
  exact ⟨Equiv.ofFiberEquiv e, fun x => Equiv.ofFiberEquiv_map e x⟩

/-- Over a DVR with finite residue field, a free submodule of full rank in a finite free module has
quotient of finite length. -/
theorem full_rank_free_submodule_finite_length (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (N : Type) [AddCommGroup N] [Module O N]
    [Module.Finite O N] [Module.Free O N] (M : Submodule O N) [Module.Finite O M] [Module.Free O M]
    (hrank : Module.finrank O M = Module.finrank O N) :
    Module.length O (N ⧸ M) ≠ ⊤ := by
  have hr := rank_quotient_add_rank_of_isDomain M
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, hrank] at hr
  norm_cast at hr
  have h0 : Module.finrank O (N ⧸ M) = 0 := by omega
  have htor : Module.IsTorsion O (N ⧸ M) := (Module.finrank_eq_zero_iff_isTorsion).mp h0
  obtain ⟨a, haI, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htor
  have ha : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  set I := (⊤ : Submodule O (N ⧸ M)).annihilator
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hle : (maximalIdeal O) ^ k ≤ I := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    have := I.mul_mem_left (↑u⁻¹ : O) haI
    simpa [← mul_assoc] using this
  have hQ : Finite (O ⧸ (maximalIdeal O) ^ k) := by
    apply Nat.finite_of_card_ne_zero
    rw [residue_quotient_card]
    have : Nat.card (ResidueField O) ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    exact pow_ne_zero _ this
  have hI : Finite (O ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  let _ := (Module.isTorsionBySet_annihilator_top O (N ⧸ M)).module
  have : Module.Finite (O ⧸ I) (N ⧸ M) := Module.Finite.of_restrictScalars_finite O _ _
  have : Finite (N ⧸ M) := Module.finite_of_finite (O ⧸ I)
  exact Module.length_ne_top

/-! ### Initial forms and homogeneous divisors -/

/-- Two-chart curve data with normalized level generators come from a global function `f` and
glued generators. -/
theorem global_function_of_two_chart_curve_data (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsLocalRing R] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] [IsAdicComplete (Ideal.span {t,x}) R]
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t) (d : ℕ)
    (FA : ℕ → BlowupChart R t x) (hFA : ∀ j : ℕ, leftLevelKernel D j = Ideal.span
    {Ideal.Quotient.mk ((Ideal.span {chartBase R t x t})^j) (FA j)}) (FB : ℕ → BlowupChart R x t)
    (hFB : ∀ j : ℕ, rightLevelKernel D j = Ideal.span {Ideal.Quotient.mk
    ((Ideal.span {chartBase R x t x})^j) (FB j)}) (hnorm : ∃ u : Rˣ,
    (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (FA 1) - algebraMap R
    (BlowupOverlap R t x) (u : R) * ((overlapSlope R t x)^d * beta.right (FB 1)) ∈
    (Ideal.span {overlapException R t x})) :
    ∃ f : R, ∃ G : GluedGenerators R t x beta d, (∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j)) ∧ ∀ j : ℕ, Ideal.span
      {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧ Ideal.span
      {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D j := by
  obtain ⟨G, hG⟩ := glued_generators_of_two_chart_curve_data R t x beta D hreg hregSwap d FA hFA FB
      hFB hnorm
  obtain ⟨f, hf, _⟩ := glued_function_exists_unique R t x beta d G hreg hregSwap
  exact ⟨f, G, hf, hG⟩

/-- An element of exact order `d` is a degree-`d` form in `t, x` with some coefficient a unit. -/
theorem has_multiplicity_initial_form (R : Type) [CommRing R] [IsLocalRing R] (t x : R)
    (hmax : maximalIdeal R = Ideal.span {t, x}) (d : ℕ) (f : R) (hf : f ∈ (maximalIdeal R) ^ d)
    (hf' : f ∉ (maximalIdeal R) ^ (d + 1)) :
    ∃ c : Fin (d+1) → R, f = (∑ i : Fin (d+1), c i * t^(d - i.val) * x^i.val) ∧ ∃ i₀ : Fin (d+1), c
      i₀ ∉ maximalIdeal R := by
  rw [hmax] at hf
  obtain ⟨c, hc⟩ := monomial_span_pow R t x d f hf
  refine ⟨c, hc, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hf'
  rw [hc]
  refine Ideal.sum_mem _ fun i _ => ?_
  have ht : t ∈ maximalIdeal R := hmax ▸ Ideal.subset_span (by simp)
  have hx : x ∈ maximalIdeal R := hmax ▸ Ideal.subset_span (by simp)
  have h1 : t^(d - i.val) * x^i.val ∈ (maximalIdeal R)^d := by
    have := Ideal.mul_mem_mul (Ideal.pow_mem_pow ht (d - i.val)) (Ideal.pow_mem_pow hx i.val)
    rwa [← pow_add, Nat.sub_add_cancel (by omega)] at this
  rw [mul_assoc, pow_succ']
  exact Ideal.mul_mem_mul (hcon i) h1

open scoped Classical in
/-- A nonzero polynomial `H` of degree at most `d` has a homogeneous divisor of degree `d`: the
point at infinity with multiplicity `d - deg H` plus the normalized factors of `H`. -/
theorem homogeneous_divisor_of_polynomial (k : Type) [Field k] (d : ℕ) (H : Polynomial k)
    (hH : H ≠ 0) (hdeg : H.natDegree ≤ d) :
    ∃ Dv : ExceptionalDivisor k, HasHomogeneousDivisor k d H Dv ∧ Dv (infinityDirection k) = d -
      H.natDegree ∧ (∀ φ : AffineDirection k, Dv (some φ) = Multiset.count φ.val
      (UniqueFactorizationMonoid.normalizedFactors H)) ∧ exceptionalDegree k Dv = d := by
  set F := UniqueFactorizationMonoid.normalizedFactors H with hF
  have hmon : ∀ ψ ∈ F, ψ.Monic := fun ψ hψ =>
    Polynomial.normalize_eq_self_iff_monic
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor ψ hψ).ne_zero |>.mp
      (UniqueFactorizationMonoid.normalize_normalized_factor ψ hψ)
  have hirr : ∀ ψ ∈ F, Irreducible ψ := fun ψ hψ =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor ψ hψ
  let g : {ψ // ψ ∈ F} → ClosedDirection k := fun ψ => some ⟨ψ.1, hmon ψ.1 ψ.2, hirr ψ.1 ψ.2⟩
  let M : Multiset (ClosedDirection k) := F.attach.map g
  have hMmap : M.map (Option.map Subtype.val) = F.map some := by
    simp only [M, Multiset.map_map]
    conv_rhs => rw [← Multiset.attach_map_val F, Multiset.map_map]
    rfl
  have hMsum : Multiset.toFinsupp M = (M.map fun Q => Finsupp.single Q 1).sum := by
    induction M using Multiset.induction_on with
    | empty => simp
    | cons a s ih => rw [← Multiset.singleton_add, Multiset.toFinsupp_add, ih]; simp
  have hprod : F.prod = Polynomial.C H.leadingCoeff⁻¹ * H := by
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hH, normalize_apply,
      Polynomial.coe_normUnit, mul_comm]
    simp [hH]
  have hdegF : F.prod.natDegree = H.natDegree := by
    rw [hprod, Polynomial.natDegree_C_mul (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hH))]
  refine ⟨Finsupp.single none (d - H.natDegree) + Multiset.toFinsupp M, ⟨hH, hdeg, ?_, ?_⟩, ?_, ?_,
      ?_⟩
  · simp [M, g]
  · have key : ∀ (f : ClosedDirection k → ℕ → Polynomial k), (∀ P, f P 0 = 1) →
        (∀ P a b, f P (a + b) = f P a * f P b) → ∀ L : Multiset (Finsupp (ClosedDirection k) ℕ),
          L.sum.prod f = (L.map fun G => G.prod f).prod := by
      intro f hf0 hfa L
      induction L using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        rw [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, Finsupp.prod_add_index' hf0
            hfa, ih]
    have hP : divisorAffinePolynomial k (Finsupp.single none (d - H.natDegree) + Multiset.toFinsupp
        M) = F.prod := by
      unfold divisorAffinePolynomial
      rw [Finsupp.prod_add_index' (fun P => by cases P <;> simp)
          (fun P a b => by cases P <;> simp [pow_add]),
        Finsupp.prod_single_index (by simp), hMsum,
        key _ (fun P => by cases P <;> simp) (fun P a b => by cases P <;> simp [pow_add])]
      simp only [M, Multiset.map_map, Function.comp_def]
      rw [one_mul]
      conv_rhs => rw [← Multiset.attach_map_val F]
      congr 1
      apply Multiset.map_congr rfl
      intro ψ _
      rw [Finsupp.prod_single_index (by simp [g])]
      simp [g]
    rw [hP, hprod, ← mul_assoc, ← Polynomial.C_mul,
      mul_inv_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hH), Polynomial.C_1, one_mul]
  · simp [infinityDirection, M, g]
  · intro φ
    simp only [Finsupp.add_apply, Finsupp.single_apply, reduceCtorEq, if_false, zero_add,
      Multiset.toFinsupp_apply]
    rw [← Multiset.count_map_eq_count' (Option.map Subtype.val) M
      (Option.map_injective Subtype.val_injective), hMmap]
    exact Multiset.count_map_eq_count' _ _ (Option.some_injective _) _
  · unfold exceptionalDegree
    have h0 : ∀ P : ClosedDirection k, directionDegree k P * 0 = 0 := fun _ => mul_zero _
    have ha : ∀ (P : ClosedDirection k) (a b : ℕ),
        directionDegree k P * (a + b) = directionDegree k P * a + directionDegree k P * b :=
      fun _ _ _ => mul_add _ _ _
    rw [Finsupp.sum_add_index' h0 ha, Finsupp.sum_single_index (by simp), hMsum,
      Finsupp.multiset_sum_sum_index _ _ h0 ha]
    simp only [directionDegree, one_mul, Multiset.map_map, Function.comp_apply, mul_zero,
      Finsupp.sum_single_index, mul_one, Multiset.attach_map_val', M, g]
    rw [← Polynomial.natDegree_multiset_prod_of_monic F hmon, hdegF]
    omega

open scoped Classical in
/-- Boundary multiplicities of the homogeneous divisor of `H`: positive at infinity iff `H_d = 0`,
positive at zero iff `H_0 = 0`, and all multiplicities and degrees of support points at most `d`. -/
theorem homogeneous_divisor_boundary_multiplicities (k : Type) [Field k] (d : ℕ) (H : Polynomial k)
    (hH : H ≠ 0) (hdeg : H.natDegree ≤ d) (Dv : ExceptionalDivisor k)
    (hinf : Dv (infinityDirection k) = d - H.natDegree) (haff : ∀ φ : AffineDirection k, Dv (some φ)
    = Multiset.count φ.val (UniqueFactorizationMonoid.normalizedFactors H)) :
    (0 < Dv (infinityDirection k) ↔ H.coeff d = 0) ∧ (0 < Dv (zeroDirection k) ↔ H.coeff 0 = 0) ∧
      (∀ Q : ClosedDirection k, Dv Q ≤ d) ∧ ∀ Q : ClosedDirection k, 0 < Dv Q → directionDegree k Q
      ≤ d := by
  obtain ⟨D', -, hi', ha', hd'⟩ := homogeneous_divisor_of_polynomial k d H hH hdeg
  have heq : Dv = D' := by
    ext Q
    cases Q with
    | none => exact hinf.trans hi'.symm
    | some φ => exact (haff φ).trans (ha' φ).symm
  subst heq
  have hdpos : ∀ Q : ClosedDirection k, 1 ≤ directionDegree k Q := by
    intro Q
    cases Q with
    | none => simp [directionDegree]
    | some φ => exact φ.property.2.natDegree_pos
  have hle : ∀ Q : ClosedDirection k, directionDegree k Q * Dv Q ≤ d := by
    intro Q
    by_cases h : Dv Q = 0
    · simp [h]
    · rw [← hd']
      exact Finset.single_le_sum (f := fun P => directionDegree k P * Dv P)
        (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hinf]
    constructor
    · intro h
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · intro h
      by_contra hc
      have : H.natDegree = d := by omega
      have := Polynomial.leadingCoeff_ne_zero.mpr hH
      apply this
      rw [Polynomial.leadingCoeff]
      simpa [‹H.natDegree = d›] using h
  · have h1 : Dv (zeroDirection k) = Multiset.count Polynomial.X
      (UniqueFactorizationMonoid.normalizedFactors H) :=
      haff ⟨Polynomial.X, Polynomial.monic_X, Polynomial.irreducible_X⟩
    rw [h1, Multiset.count_pos, ← Polynomial.X_dvd_iff]
    constructor
    · exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
    · intro h
      obtain ⟨q, hq, hass⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hH
        (Polynomial.irreducible_X : Irreducible (Polynomial.X : Polynomial k)) h
      have hn := UniqueFactorizationMonoid.normalize_normalized_factor q hq
      have : normalize q = normalize (Polynomial.X : Polynomial k) := normalize_eq_normalize_iff.mpr
          ⟨hass.symm.dvd, hass.dvd⟩
      rw [hn, (Polynomial.normalize_eq_self_iff_monic Polynomial.X_ne_zero).mpr Polynomial.monic_X]
          at this
      rw [← this]; exact hq
  · intro Q
    exact le_trans (Nat.le_mul_of_pos_left _ (hdpos Q)) (hle Q)
  · intro Q _
    have := hle Q
    have hp : 0 < Dv Q := ‹_›
    exact le_trans (Nat.le_mul_of_pos_right _ hp) this

/-! ### Atlases and volumes of concrete members -/

/-- Any two ideal atlases of the same set have the same residue cells, up to reindexing. -/
private theorem ideal_atlas_reindex (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (pi : O)
    (n : ℕ)
    (X : Set (Ideal R)) (A B : IdealAtlas O R pi n X) :
    ∃ e : A.ι ≃ B.ι, ∀ i, residueIdealCell (algebraMap O R pi) (A.chart i).f = residueIdealCell
      (algebraMap O R pi) (B.chart (e i)).f := by
  have self_mem : ∀ p f : R, Ideal.span {f} ∈ residueIdealCell p f := by
    intro p f
    refine ⟨⟨f, rfl⟩, ?_⟩
    rw [Ideal.map_span]; simp
  have eq_of_mem : ∀ p f g : R, ∀ J, J ∈ residueIdealCell p f → J ∈ residueIdealCell p g →
      residueIdealCell p f = residueIdealCell p g := by
    intro p f g J hf hg
    have h : Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) f} = Ideal.span
        {Ideal.Quotient.mk (Ideal.span {p}) g} := hf.2.symm.trans hg.2
    ext K
    simp only [residueIdealCell, Set.mem_ofPred_eq, h]
  have ex : ∀ i, ∃ j, Ideal.span {(A.chart i).f} ∈ residueIdealCell (algebraMap O R pi)
      (B.chart j).f := by
    intro i
    have : Ideal.span {(A.chart i).f} ∈ X :=
      (Set.ext_iff.1 A.cover _).2 (Set.mem_iUnion.2 ⟨i, self_mem _ _⟩)
    exact Set.mem_iUnion.1 ((Set.ext_iff.1 B.cover _).1 this)
  choose e he using ex
  have hcell : ∀ i, residueIdealCell (algebraMap O R pi) (A.chart i).f = residueIdealCell
      (algebraMap O R pi) (B.chart (e i)).f :=
    fun i => eq_of_mem _ _ _ _ (self_mem _ _) (he i)
  have inj : Function.Injective e := by
    intro i i' h
    by_contra hne
    have h1 : Disjoint (residueIdealCell (algebraMap O R pi) (A.chart i).f)
        (residueIdealCell (algebraMap O R pi) (A.chart i').f) := A.disjoint hne
    have h2 : residueIdealCell (algebraMap O R pi) (A.chart i).f = residueIdealCell
        (algebraMap O R pi) (A.chart i').f := by
      rw [hcell i, hcell i', h]
    rw [h2] at h1
    exact Set.disjoint_left.1 h1 (self_mem _ _) (self_mem _ _)
  have surj : Function.Surjective e := by
    intro j
    have : Ideal.span {(B.chart j).f} ∈ X :=
      (Set.ext_iff.1 B.cover _).2 (Set.mem_iUnion.2 ⟨j, self_mem _ _⟩)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ((Set.ext_iff.1 A.cover _).1 this)
    refine ⟨i, ?_⟩
    by_contra hne
    have h1 : Disjoint (residueIdealCell (algebraMap O R pi) (B.chart (e i)).f)
        (residueIdealCell (algebraMap O R pi) (B.chart j).f) := B.disjoint fun h ↦ hne h
    have h2 := eq_of_mem _ _ _ _ hi (self_mem _ _)
    have h3 : residueIdealCell (algebraMap O R pi) (B.chart (e i)).f = residueIdealCell
        (algebraMap O R pi) (B.chart j).f := by
      rw [← hcell i, h2]
    rw [h3] at h1
    exact Set.disjoint_left.1 h1 (self_mem _ _) (self_mem _ _)
  exact ⟨Equiv.ofBijective e ⟨inj, surj⟩, hcell⟩

/-- Transport of a state-measure computation between two atlases of the same set, the first one
built on a parameter `p` propositionally equal to `pi`. -/
private theorem stateMeasure_univ_of_atlas (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (maximalIdeal O)) [CommRing R] [Algebra O R] [IsDomain R] [IsLocalRing R]
    (p pi : O) (hp : p = pi) (hpi : Irreducible pi) (hp0 : algebraMap O R pi ≠ 0)
    (hpm : algebraMap O R pi ∈ maximalIdeal R) (n : ℕ) (X : Set (Ideal R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (A : IdealAtlas O R p n X)
    (A' : IdealAtlas O R pi n X) (V : ℝ≥0∞)
    (hA' : (letI := idealChartSigma O R pi
      stateMeasure O R pi n (Nat.card (ResidueField O)) A' Set.univ = V)) :
    letI := idealChartSigma O R p
    stateMeasure O R p n (Nat.card (ResidueField O)) A Set.univ = V := by
  subst hp
  let _ := idealChartSigma O R p
  obtain ⟨e, he⟩ := ideal_atlas_reindex O R p n X A A'
  rwa [state_measure_atlas_independent O R htop p hpi n X A A' (fun j ↦
    coordinate_ideal_measurable_chart_sigma O htop R p hpi hp0 hpm n _ _
      (A'.chart j).isDivisionChart) e he hp0 hpm]

/-- The state measure of the state set of a concrete member is the state volume density. -/
theorem concrete_member_volume (m : ConcreteMember) :
    m.toMeasured.μ m.toMeasured.stateSet = densityValue (stateVolume m.s) m.toMeasured.q := by
  rw [← Set.univ_inter m.toMeasured.stateSet, ← (concrete_member_measure_finite_support m).2]
  obtain ⟨O, htop, pi, hpi, u, a0, b0, ha, S, hS_pi, hS_t, hS_x, hS_a, hS_b, s, shape, atlas⟩ := m
  have hq : 2 ≤ Nat.card (ResidueField O) := Finite.one_lt_card_iff_nontrivial.2 inferInstance
  cases s with
  | single a c =>
    obtain ⟨rfl, rfl, hc⟩ := shape
    obtain ⟨e, he⟩ := concrete_surface_special_fiber_equiv O pi hpi u a 0
    obtain ⟨A', hA'⟩ := concrete_single_state_volume O pi hpi u a ha S hS_pi hS_t hS_a hS_b e he c
        hc htop
    obtain ⟨hp0, hpm⟩ := surface_vertical_parameter O (ConcreteSurface O pi u a 0) S
    rw [hS_pi] at hp0 hpm
    have := division_coordinate_module_isAdicComplete O pi hpi u a 0 ha (a*c)
    refine (stateMeasure_univ_of_atlas O _ htop S.pi pi hS_pi hpi hp0 hpm (a*c) _ atlas A'
      _ hA').trans ?_
    exact (density_value_arith _ hq (.const 1) (.const 1) (by simp [Expr.eval])
      (by simp [Expr.eval]) c (State.single 1 1) ⟨Nat.one_pos, Nat.one_pos⟩).2.2.1.symm
  | crossing a b c h =>
    obtain ⟨rfl, rfl, hb, hc, hh⟩ := shape
    obtain ⟨e, he⟩ := concrete_surface_special_fiber_equiv O pi hpi u a b
    obtain ⟨A', hA'⟩ := concrete_crossing_state_volume O pi hpi u a b ha hb S hS_pi hS_t hS_x hS_a
        hS_b e he c h hc hh htop
    obtain ⟨hp0, hpm⟩ := surface_vertical_parameter O (ConcreteSurface O pi u a b) S
    rw [hS_pi] at hp0 hpm
    have := division_coordinate_module_isAdicComplete O pi hpi u a b ha (a*c+b*h)
    refine (stateMeasure_univ_of_atlas O _ htop S.pi pi hS_pi hpi hp0 hpm (a*c+b*h) _
      atlas A' _ hA').trans ?_
    have hq1 : (1 : ℚ) ≤ (Nat.card (ResidueField O) : ℚ) := by exact_mod_cast (by omega)
    have hdv := density_value_arith _ hq eminusOne (.inv (.pow .var (c+h)))
      (by simp [eminusOne, Expr.sub, Expr.neg, Expr.eval]; linarith)
      (by simp only [Expr.eval, expression_pow_eval]; positivity) (c+h) (State.single 1 1)
      ⟨Nat.one_pos, Nat.one_pos⟩
    have hem : densityValue eminusOne (Nat.card (ResidueField O)) =
        (Nat.card (ResidueField O) : ℝ≥0∞) - 1 := by
      simp only [densityValue, eminusOne, Expr.sub, Expr.neg, Expr.eval]
      push_cast
      rw [show ((Nat.card (ResidueField O) : ℝ) + -1 * 1) =
        (Nat.card (ResidueField O) : ℝ) - 1 by ring,
        ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    change _ = densityValue (stateVolume (.crossing a b c h)) (Nat.card (ResidueField O))
    rw [stateVolume, hdv.1, hdv.2.2.1, hem]

/-! ### Child members -/

/-- Principality and contact lengths of ideals are transported by ring isomorphisms. -/
private theorem ideal_data_along_ringEquiv (S S' : Type) [CommRing S] [CommRing S'] (Eq : S ≃+* S')
    (I : Ideal S) (e : S) :
    ((∃ g : S, I = Ideal.span {g}) ↔ ∃ g' : S', Ideal.map (Eq : S →+* S') I = Ideal.span {g'}) ∧
      Module.length S (S ⧸ (I ⊔ Ideal.span {e})) = Module.length S'
      (S' ⧸ (Ideal.map (Eq : S →+* S') I ⊔ Ideal.span {Eq e})) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨g, rfl⟩
    exact ⟨Eq g, by rw [Ideal.map_span]; simp⟩
  · rintro ⟨g', h⟩
    refine ⟨Eq.symm g', ?_⟩
    have := congrArg (Ideal.map (Eq.symm : S' →+* S)) h
    rw [Ideal.map_span] at this
    simp only [Set.image_singleton] at this
    change I = Ideal.span {(Eq.symm : S' →+* S) g'}
    rw [← this, Ideal.map_map]
    have : (Eq.symm : S' →+* S).comp (Eq : S →+* S') = RingHom.id S := by ext; simp
    rw [this, Ideal.map_id]
  · rw [module_length_quotient_ringEquiv S S' Eq (I ⊔ Ideal.span {e}), Ideal.map_sup,
      Ideal.map_span]
    rw [Set.image_singleton]
    rfl

/-- An ideal of the completed local ring at the point of a child lies in the child ideal set iff
its image in the child member lies in the child's state set. -/
theorem child_ideal_set_map_iff_stateSet (m : ConcreteMember) (c : m.cellIndex)
    (D : CellChildData m c) (j : m.toMeasured.childIdx c) (I : Ideal
    (divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j))) :
    I ∈ childIdealSet m.R m.S.t m.S.x D.e c.2.1 D.hinf m.s (m.toMeasured.cellDegree c) (D.point j) ↔
      Ideal.map (D.Eq j : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) →+*
      (D.mc j).R) I ∈ (D.mc j).toMeasured.stateSet := by
  have hE := ideal_data_along_ringEquiv _ _ (D.Eq j) I
    (divisorException m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j))
  have hB := (ideal_data_along_ringEquiv _ _ (D.Eq j) I
    (divisorBoundary m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j))).2
  rw [D.hEq_e j] at hE
  have hB' : (D.asg.pt j = infinityDirection (ResidueField m.R) ∨ D.asg.pt j = zeroDirection
      (ResidueField m.R)) →
      Module.length (divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j))
          (divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) ⧸
          (I ⊔ Ideal.span {divisorBoundary m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j)})) =
        idealContact (D.mc j).R (Ideal.map (D.Eq j : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1
            D.hinf (D.point j) →+* (D.mc j).R) I) (D.mc j).S.x := by
    intro h; rw [hB, D.hEq_b j h]; rfl
  obtain ⟨hP, hE⟩ := hE
  have hs : (D.mc j).s = pointChildState (ResidueField m.R) m.s (m.toMeasured.cellDegree c) c.2.1
      (D.asg.pt j) :=
    (D.child j).hstate.trans (D.asg.state j)
  have hshape := (D.mc j).shape
  have hvalid := (D.mc j).shape.valid (D.mc j).ha
  have hSa := (D.mc j).hS_a
  have hSb := (D.mc j).hS_b
  change _ ↔ _ ∈ surfaceStateSet (D.mc j).O (D.mc j).R (D.mc j).S (D.mc j).s
  unfold childIdealSet surfaceStateSet
  simp only [Set.mem_ofPred_eq]
  change _ = idealContact (D.mc j).R _ (D.mc j).S.t at hE
  rw [hP, hE]
  have hQ : (D.point j).val = D.asg.pt j := rfl
  rw [hQ, hs]
  rw [hs] at hshape hvalid
  generalize idealContact (D.mc j).R (Ideal.map (D.Eq j : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1
      D.hinf (D.point j) →+* (D.mc j).R) I) (D.mc j).S.t = CT at *
  generalize idealContact (D.mc j).R (Ideal.map (D.Eq j : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1
      D.hinf (D.point j) →+* (D.mc j).R) I) (D.mc j).S.x = CX at *
  generalize Module.length (divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j))
      (divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) ⧸
      (I ⊔ Ideal.span {divisorBoundary m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j)})) = LB at *
  generalize (∃ g', Ideal.map (D.Eq j : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf
      (D.point j) →+* (D.mc j).R) I = Ideal.span {g'}) = PP at *
  rw [hSa, hSb]
  clear hB hE hP hs
  generalize D.asg.pt j = Q at *
  generalize m.toMeasured.cellDegree c = d at *
  simp only [hvalid, true_and]
  clear hvalid hSa hSb hQ I
  generalize c.2.1 = Dv at *
  generalize m.s = s0 at *
  generalize (D.mc j).a = A at *
  generalize (D.mc j).b = B at *
  rcases Q with _ | φ
  · obtain rfl := hB' (Or.inl rfl)
    cases s0 <;>
    · simp only [pointChildState, infinityDirection, if_true, StateShape, stateContactT,
        stateContactX] at hshape ⊢
      obtain ⟨rfl, rfl, -⟩ := hshape
      simp [zeroDirection]
  have hne : (some φ : ClosedDirection (ResidueField m.R)) ≠ infinityDirection _ := by
    simp [infinityDirection]
  cases s0 with
  | single a0 c0 =>
    simp only [pointChildState, if_neg hne, StateShape, stateContactT, stateContactX] at hshape ⊢
    obtain ⟨rfl, rfl, -⟩ := hshape
    simp
  | crossing a0 b0 c0 h0 =>
    by_cases hz : (some φ : ClosedDirection (ResidueField m.R)) = zeroDirection _
    · obtain rfl := hB' (Or.inr hz)
      simp only [pointChildState, if_neg hne, if_pos hz, StateShape, stateContactT,
        stateContactX] at hshape ⊢
      obtain ⟨rfl, rfl, -⟩ := hshape
      simp [hz, zeroDirection]
    · simp only [pointChildState, if_neg hne, if_neg hz, StateShape, stateContactT,
        stateContactX] at hshape ⊢
      obtain ⟨rfl, rfl, -⟩ := hshape
      simp [hz]

/-- The completed local ring at the point at infinity of a concrete surface is a concrete member
of shape `(a + b, a)` over the same coefficient ring, with the expected boundary parameters. -/
theorem infinity_point_child_member (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (htop : IsAdic (maximalIdeal O)) (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    [hinf : (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)).IsPrime] (s' : State) (hs' : StateShape (a + b) a s') :
    ∃ mc : ConcreteMember, ∃ (_ : Algebra O mc.O) (_ : Module.Finite O mc.O)
      (_ : Module.Free O mc.O), Module.finrank O mc.O = 1 ∧ Nat.card (ResidueField mc.O) = Nat.card
      (ResidueField O) ^ 1 ∧ mc.pi = algebraMap O mc.O pi ∧ mc.a = a + b ∧ mc.b = a ∧ mc.s = s' ∧
      (∃ pc : mc.O ≃ₗ[O] (Fin 1 → O), Continuous pc ∧ Continuous pc.symm ∧ Measurable pc ∧
      Measurable pc.symm ∧ IsProbabilityMeasure (Measure.map pc.symm (coefficientMeasure O 1)) ∧ ∀ r
      : ℕ, coefficientMeasure mc.O r = Measure.pi (fun _ : Fin r => Measure.map pc.symm
      (coefficientMeasure O 1))) ∧ ∃ Eq : CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b)
      (surfaceX O pi u a b) (surfaceT O pi u a b)) (infinityPoint (ConcreteSurface O pi u a b)
      (surfaceT O pi u a b) (surfaceX O pi u a b)) ≃+* mc.R, Eq
      ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
      (surfaceT O pi u a b)) (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))) ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
      (surfaceT O pi u a b)) (surfaceX O pi u a b))) = mc.S.t ∧ Eq
      ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
      (surfaceT O pi u a b)) (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))) (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
      (surfaceT O pi u a b))) = mc.S.x ∧ ∀ c : O, Eq ((completedPointMap
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
      (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))
      ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
      (algebraMap O (ConcreteSurface O pi u a b) c))) = algebraMap O mc.R c := by
  obtain ⟨Eq, h1, h2, h3⟩ := x_chart_infinity_completion_equiv O pi hpi u a b ha
    (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) rfl
  obtain ⟨i1, i2, S, hSpi, hSt, hSx, hSa, hSb, ⟨atlas⟩⟩ :=
    concrete_member_data_exists O pi hpi (xSubstUnit O u) (a + b) a (by omega) s' hs'
  have := coefficient_measure_probability O htop 1
  obtain ⟨-, hm2, hm3, hm4, hm5, hm6⟩ := coefficient_measure_pi_one O htop pi hpi 0
  refine ⟨⟨O, htop, pi, hpi, xSubstUnit O u, a + b, a, by omega, S, hSpi, hSt, hSx, hSa, hSb, s',
      hs', atlas⟩, Algebra.id O, Module.Finite.self O, Module.Free.self O, Module.finrank_self O,
      by simp, by simp, rfl, rfl, rfl,
      ⟨(LinearEquiv.funUnique (Fin 1) O O).symm, hm4, hm3, hm6, hm5, by simpa using hm2,
        fun r ↦ by simpa using (coefficient_measure_pi_one O htop pi hpi r).1⟩,
      Eq, ?_, by simpa [hSx] using h2, fun c ↦ by simpa using h3 c⟩
  have := h1 (axisX O)
  rw [(chartSubst_apply_generators O 0).2.2.2.2.2.1] at this
  simpa [hSt, surfaceT, surfaceX] using this

/-- A homogeneous divisor of the initial form of `f` is a tangent divisor of `(f)`. -/
theorem initial_form_has_tangent_divisor (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (d : ℕ) (f : R) (c : Fin (d + 1) → R)
    (hc : f = (∑ i : Fin (d + 1), c i * S.t ^ (d - i.val) * S.x ^ i.val))
    (H : Polynomial (ResidueField R)) (hH : H = ∑ i : Fin (d + 1), Polynomial.C (residue R (c i)) *
    Polynomial.X ^ i.val) (Dv : ExceptionalDivisor (ResidueField R))
    (hDv : HasHomogeneousDivisor (ResidueField R) d H Dv) :
    HasTangentDivisor O R S (Ideal.span {f}) d Dv := by
  refine ⟨f, H, rfl, hDv, ?_⟩
  have hco : ∀ i : Fin (d+1), H.coeff i.val = residue R (c i) := by
    intro i
    rw [hH, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : i.val ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [this]
    · simp
  unfold tangentLift
  rw [hc]
  refine initial_form_lift_independent O R S d c
    (fun i => residueRepresentative R (H.coeff i.val)) fun i ↦ ?_
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hco i]
  have : residue R (residueRepresentative R (residue R (c i))) = residue R (c i) :=
    Function.rightInverse_invFun IsLocalRing.residue_surjective _
  rw [this, sub_self]

/-! ### Lengths, fibres and integral closures -/

/-- Restricting scalars along `O → Oδ` does not decrease length. -/
private theorem length_le_length_restrict (O Oδ M : Type) [CommRing O] [CommRing Oδ] [Algebra O Oδ]
    [AddCommGroup M] [Module O M] [Module Oδ M] [IsScalarTower O Oδ M] :
    Module.length Oδ M ≤ Module.length O M := by
  have h := Submodule.length_le_length_restrictScalars O (⊤ : Submodule Oδ M)
  rw [Submodule.restrictScalars_top] at h
  rwa [(Submodule.topEquiv (R := Oδ) (M := M)).length_eq,
    (Submodule.topEquiv (R := O) (M := M)).length_eq] at h

/-- The number of positions of a list holding `v` is the count of `v`. -/
theorem list_get_fiber_card_count (β : Type) [DecidableEq β] (l : List β) (v : β) :
    Nat.card {j : Fin l.length // l.get j = v} = l.count v := by
  have key : ∀ l : List β, l.count v = ∑ j : Fin l.length, if l.get j = v then 1 else 0 := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.count_cons, ih]
      erw [Fin.sum_univ_succ]
      by_cases h : a = v <;> simp [h, Nat.add_comm]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, key]

/-- An element of a finite product is integral iff each coordinate is integral. -/
private theorem mem_integralClosure_pi_iff (O : Type) [CommRing O] (ι : Type) [Finite ι]
    (C : ι → Type)
    [∀ i, CommRing (C i)] [∀ i, Algebra O (C i)] (x : ∀ i, C i) :
    x ∈ integralClosure O (∀ i, C i) ↔ ∀ i, x i ∈ integralClosure O (C i) := by
  have := Fintype.ofFinite ι
  simp only [mem_integralClosure_iff]
  constructor
  · intro h i
    exact h.map (Pi.evalAlgHom O C i)
  · intro h
    choose p hp hx using h
    refine ⟨∏ i, p i, Polynomial.monic_prod_of_monic _ _ (fun i _ => hp i), ?_⟩
    have h1 : Polynomial.aeval x (∏ j, p j) = 0 := by
      funext i
      have : Polynomial.aeval x (∏ j, p j) = ∏ j, Polynomial.aeval x (p j) := map_prod _ _ _
      rw [this, Finset.prod_apply]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom O C i) x (p i)
      simp only [Pi.evalAlgHom_apply] at this
      rw [← this, Polynomial.aeval_def]
      exact hx i
    rwa [Polynomial.aeval_def] at h1

/-- The integral closure in a finite product is the product of the integral closures. -/
private theorem integralClosure_pi_equiv (O : Type) [CommRing O] (ι : Type) [Finite ι]
    (C : ι → Type)
    [∀ i, CommRing (C i)] [∀ i, Algebra O (C i)] :
    ∃ e : integralClosure O (∀ i, C i) ≃ₗ[O] (∀ i, integralClosure O (C i)), ∀
      (x : integralClosure O (∀ i, C i)) (i : ι), ((e x i : integralClosure O (C i)) : C i) =
      (x : ∀ i, C i) i := by
  refine ⟨{ toFun := fun x i => ⟨(x : ∀ i, C i) i, (mem_integralClosure_pi_iff O ι C x.1).1 x.2 i⟩
            map_add' := fun x y => rfl
            map_smul' := fun r x => rfl
            invFun := fun y => ⟨fun i => (y i : C i), (mem_integralClosure_pi_iff O ι C _).2
                (fun i => (y i).2)⟩
            left_inv := fun x => rfl
            right_inv := fun y => rfl }, fun x i => rfl⟩

/-- If `B` has an algebra type, its generic closure is finite free of rank the generic rank. -/
theorem generic_closure_free_of_type (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (B : Type) [CommRing B] [Algebra O B] (σ : FactorType)
    (h : HasAlgebraType O B σ) :
    Module.Finite O (GenericClosure O B) ∧ Module.Free O (GenericClosure O B) ∧ Module.finrank O
      (GenericClosure O B) = Module.finrank (BaseField O) (TensorProduct O (BaseField O) B) := by
  obtain ⟨ι, _, L, _, _, _, _, _, e, -, hsepL⟩ := h
  have : ∀ i, Module.Finite O (integralClosure O (L i)) := hsepL
  have hL := fun i => integral_closure_finite_free O (BaseField O) (L i)
  have : ∀ i, Module.Finite O (integralClosure O (L i)) := fun i => (hL i).1
  have : ∀ i, Module.Free O (integralClosure O (L i)) := fun i => (hL i).2.1
  obtain ⟨e₁, -⟩ := integralClosure_pi_equiv O ι L
  obtain ⟨φ, -⟩ := integral_closure_algEquiv O _ _ (e.restrictScalars O)
  let E : GenericClosure O B ≃ₗ[O] (∀ i, integralClosure O (L i)) :=
    φ.toLinearEquiv.trans e₁
  refine ⟨Module.Finite.equiv E.symm, Module.Free.of_equiv E.symm, ?_⟩
  rw [E.finrank_eq, Module.finrank_pi_fintype, e.toLinearEquiv.finrank_eq,
    Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun i _ => (hL i).2.2

/-! ### Termination of the recursion -/

/-- Children of a non-self cell have strictly smaller state rank. -/
private theorem nonself_cell_child_rank_lt (U : SurfaceUniverse) (i : U.ι) (c : (U.M i).cellIndex)
    (hc : ¬ (U.M i).IsSelfCell c) (j : (U.M i).childIdx c) :
    (U.M (U.child i c j)).s.rank < (U.M i).s.rank := by
  rw [U.child_state]
  exact nonself_child_rank_lt _ (U.M i).valid _ c.1.2 hc _
    (List.get_mem _ _)

/-- If types propagate to children and an invariant `δ` is non-increasing along the recursion and
strictly decreasing on self cells, every ideal with a type terminates. -/
private theorem etale_terminates_of_invariant (U : SurfaceUniverse) (hE1 : U.ChildTypesExist)
    (δ : ∀ i : U.ι, Ideal (U.M i).R → ℕ) (hE2 : U.InvariantDecreases δ) (i : U.ι)
    (J : Ideal (U.M i).R) (hJ : J ∈ (U.M i).stateSet) (σ : FactorType)
    (hσ : HasAlgebraType (U.M i).O ((U.M i).R ⧸ J) σ) :
    U.Terminates i J := by
  have key : ∀ n r : ℕ, ∀ (i : U.ι) (J : Ideal (U.M i).R), δ i J = n → (U.M i).s.rank = r →
      J ∈ (U.M i).stateSet → (∃ σ, HasAlgebraType (U.M i).O ((U.M i).R ⧸ J) σ) →
      U.Terminates i J := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IHδ =>
    intro r
    induction r using Nat.strong_induction_on with
    | _ r IHr =>
    intro i J hn hr hJ ⟨σ, hσ⟩
    cases ht : (U.M i).s.terminal with
    | true => exact SurfaceUniverse.Terminates.leaf i J hJ ht
    | false =>
      rw [U.cells_cover i ht, Set.mem_iUnion] at hJ
      obtain ⟨c, hc⟩ := hJ
      refine SurfaceUniverse.Terminates.node i c J hc ht (fun j => ?_)
      have hτ := hE1 i ht c J hc σ hσ j
      have hmem := cell_child_mem_stateSet U i ht c J hc j
      have hδ := hE2 i ht c J hc ⟨σ, hσ⟩ j
      by_cases hself : (U.M i).IsSelfCell c
      · exact IHδ _ (hn ▸ hδ.2 hself) _ _ _ rfl rfl hmem hτ
      · have hrank := nonself_cell_child_rank_lt U i c hself j
        rcases lt_or_eq_of_le hδ.1 with h | h
        · exact IHδ _ (hn ▸ h) _ _ _ rfl rfl hmem hτ
        · exact IHr _ (hr ▸ hrank) _ _ (h.trans hn) rfl hmem hτ
  exact key _ _ i J rfl rfl hJ ⟨σ, hσ⟩

/-- Under the hypotheses of `etale_terminates_of_invariant`, the type events consist of
terminating ideals. -/
theorem etale_type_event_eq_term (U : SurfaceUniverse) (hE1 : U.ChildTypesExist)
    (δ : ∀ i : U.ι, Ideal (U.M i).R → ℕ) (hE2 : U.InvariantDecreases δ) (i : U.ι) (σ : FactorType) :
    U.typeEvent i σ = U.termTypeEvent i σ :=
  Set.Subset.antisymm (fun J hJ ↦ ⟨hJ, etale_terminates_of_invariant U hE1 δ hE2 i J hJ.1 σ hJ.2⟩)
    Set.inter_subset_left

private theorem childList_of_isSelfCell (U : SurfaceUniverse) (i : U.ι) (c : (U.M i).cellIndex)
    (hc : (U.M i).IsSelfCell c) : (U.M i).childList c = [(1, (U.M i).s)] := by
  obtain ⟨_, _, _, h⟩ := hc
  exact h

private theorem child_state_of_isSelfCell (U : SurfaceUniverse) (i : U.ι) (c : (U.M i).cellIndex)
    (hc : (U.M i).IsSelfCell c) (j : (U.M i).childIdx c) :
    (U.M (U.child i c j)).s = (U.M i).s := by
  rw [U.child_state]
  have h := childList_of_isSelfCell U i c hc
  unfold MeasuredSurface.childState
  have : ∀ (L : List (ℕ × State)) (hL : L = [(1, (U.M i).s)]) (j : Fin L.length), (L.get j).2 =
      (U.M i).s := by
    intro L hL j
    subst hL
    have hj := j.2
    simp only [List.length_cons, List.length_nil] at hj
    have : j = ⟨0, by simp⟩ := Fin.ext (by simp only; omega)
    subst this; rfl
  exact this _ h j

private theorem childIdx_subsingleton_of_isSelfCell (U : SurfaceUniverse) (i : U.ι)
    (c : (U.M i).cellIndex)
    (hc : (U.M i).IsSelfCell c) (j j' : (U.M i).childIdx c) : j = j' := by
  have hl : ((U.M i).childList c).length = 1 := by rw [childList_of_isSelfCell U i c hc]; rfl
  exact Fin.ext (by have := j.2; have := j'.2; omega)

private theorem exists_child_mem_nonterminatingSet (U : SurfaceUniverse) (i : U.ι)
    (hnt : (U.M i).s.terminal = false)
    (c : (U.M i).cellIndex) (J : Ideal (U.M i).R) (hJc : J ∈ (U.M i).cell c)
    (hJ : J ∉ U.terminatingSet i) : ∃ j, U.Φ i c J j ∈ U.nonterminatingSet (U.child i c j) := by
  by_contra hcon
  push Not at hcon
  refine hJ (SurfaceUniverse.Terminates.node i c J hJc hnt fun j ↦ ?_)
  by_contra h
  exact hcon j ⟨cell_child_mem_stateSet U i hnt c J hJc j, h⟩

private theorem mem_returnEvent_succ_or_badExitEvent (U : SurfaceUniverse) (k : ℕ) : ∀ (i : U.ι),
    (U.M i).s.terminal = false →
    ∀ J, J ∈ U.nonterminatingSet i → J ∈ U.returnEvent k i →
      J ∈ U.returnEvent (k+1) i ∪ U.badExitEvent k i := by
  induction k with
  | zero =>
    intro i hnt J hJ _
    have hJs := hJ.1
    rw [U.cells_cover i hnt, Set.mem_iUnion] at hJs
    obtain ⟨c, hJc⟩ := hJs
    have hmem := (U.Φ_bij i hnt c).mapsTo hJc
    rw [Set.mem_univ_pi] at hmem
    by_cases hc : (U.M i).IsSelfCell c
    · left
      simp only [SurfaceUniverse.returnEvent, Set.mem_iUnion]
      exact ⟨⟨c, hc⟩, hJc, Set.mem_univ_pi.2 hmem⟩
    · right
      obtain ⟨j₀, hj₀⟩ := exists_child_mem_nonterminatingSet U i hnt c J hJc hJ.2
      simp only [SurfaceUniverse.badExitEvent, Set.mem_iUnion]
      refine ⟨⟨c, hc⟩, j₀, hJc, Set.mem_univ_pi.2 (fun j => ?_)⟩
      by_cases hj : j = j₀
      · subst hj; simp [hj₀]
      · simp [Function.update_of_ne hj]
  | succ k ih =>
    intro i hnt J hJ hJr
    simp only [SurfaceUniverse.returnEvent, Set.mem_iUnion] at hJr
    obtain ⟨⟨c, hc⟩, hJc, hJpi⟩ := hJr
    rw [Set.mem_preimage, Set.mem_univ_pi] at hJpi
    obtain ⟨j₀, hj₀⟩ := exists_child_mem_nonterminatingSet U i hnt c J hJc hJ.2
    have hnt' : (U.M (U.child i c j₀)).s.terminal = false := by
      rw [child_state_of_isSelfCell U i c hc]; exact hnt
    rcases ih _ hnt' _ hj₀ (hJpi j₀) with h | h
    · left
      simp only [SurfaceUniverse.returnEvent, Set.mem_iUnion]
      refine ⟨⟨c, hc⟩, hJc, Set.mem_univ_pi.2 (fun j => ?_)⟩
      obtain rfl := childIdx_subsingleton_of_isSelfCell U i c hc j j₀
      simpa [SurfaceUniverse.returnEvent] using h
    · right
      simp only [SurfaceUniverse.badExitEvent, Set.mem_iUnion]
      refine ⟨⟨c, hc⟩, hJc, Set.mem_univ_pi.2 (fun j => ?_)⟩
      obtain rfl := childIdx_subsingleton_of_isSelfCell U i c hc j j₀
      exact h

/-- A nonterminating ideal either returns infinitely often or eventually exits through a bad
cell; in a crossing state it exits through a bad cell at once. -/
theorem nonterminating_subset_return_or_bad (U : SurfaceUniverse) (i : U.ι)
    (hnt : (U.M i).s.terminal = false) :
    (∀ a c : ℕ, (U.M i).s = State.single a c → U.nonterminatingSet i ⊆ (⋂ k, U.returnEvent k i) ∪ ⋃
      k, U.badExitEvent k i) ∧ (∀ a b c h : ℕ, (U.M i).s = State.crossing a b c h →
      U.nonterminatingSet i ⊆ U.badExitEvent 0 i) := by
  classical
  constructor
  · intro a c _ J hJ
    by_cases hall : J ∈ ⋂ k, U.returnEvent k i
    · exact Or.inl hall
    · right
      rw [Set.mem_iInter] at hall
      push Not at hall
      have hex : ∃ n, J ∉ U.returnEvent n i := hall
      have hn0 : Nat.find hex ≠ 0 := fun h0 ↦ (h0 ▸ Nat.find_spec hex) hJ.1
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hin : J ∈ U.returnEvent m i := by
        by_contra hc
        have := Nat.find_min' hex hc
        omega
      have hnot : J ∉ U.returnEvent (m+1) i := by
        rw [← Nat.succ_eq_add_one, ← hm]; exact Nat.find_spec hex
      rcases mem_returnEvent_succ_or_badExitEvent U m i hnt J hJ hin with h | h
      · exact absurd h hnot
      · exact Set.mem_iUnion.2 ⟨m, h⟩
  · intro a b c h hs J hJ
    rcases mem_returnEvent_succ_or_badExitEvent U 0 i hnt J hJ hJ.1 with h' | h'
    · exfalso
      simp only [SurfaceUniverse.returnEvent, Set.mem_iUnion] at h'
      obtain ⟨⟨c', ⟨a', c'', hs', _⟩⟩, _⟩ := h'
      rw [hs] at hs'
      cases hs'
    · exact h'

/-! ### Order defects -/

open scoped TensorProduct in
/-- The order defect does not increase under an unramified extension of the coefficient DVR. -/
theorem order_defect_le_of_tower (O Oδ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ] [Algebra O Oδ] [Module.Finite O Oδ]
    [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ) (pi : O) (hpi : Irreducible pi)
    (hpiδ : Irreducible (algebraMap O Oδ pi)) (B : Type) [CommRing B] [Algebra O B] [Algebra Oδ B]
    [IsScalarTower O Oδ B] :
    orderDefect Oδ B ≤ orderDefect O B := by
  obtain ⟨-, -, hfr⟩ := unramified_fraction_base_change O Oδ δ hrank pi hpi hpiδ
  -- fraction field of Oδ as Oδ ⊗[O] K
  have hfr' : IsFractionRing Oδ (Oδ ⊗[O] BaseField O) := by
    let _i : Algebra Oδ (BaseField O ⊗[O] Oδ) := Algebra.TensorProduct.rightAlgebra
    refine IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors Oδ)
      (AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm O (BaseField O) Oδ).toRingEquiv) ?_)
    intro x
    change (Algebra.TensorProduct.comm O (BaseField O) Oδ) (1 ⊗ₜ x) = _
    simp
  let ψ : BaseField Oδ ≃ₐ[Oδ] Oδ ⊗[O] BaseField O :=
    IsLocalization.algEquiv (nonZeroDivisors Oδ) (BaseField Oδ) (Oδ ⊗[O] BaseField O)
  let Θ : BaseField Oδ ⊗[Oδ] B ≃+* BaseField O ⊗[O] B :=
    ((((Algebra.TensorProduct.congr ψ (AlgEquiv.refl (R := Oδ) (A₁ := B))).trans
      (Algebra.TensorProduct.comm Oδ _ B)).trans
      (Algebra.TensorProduct.cancelBaseChange O Oδ Oδ B (BaseField O))).toRingEquiv.trans
      (Algebra.TensorProduct.comm O B (BaseField O)).toRingEquiv)
  have hΘ : ∀ b : B, Θ (1 ⊗ₜ b) = 1 ⊗ₜ b := by
    intro b
    simp [Θ, Algebra.TensorProduct.one_def]
  let f : Oδ →+* BaseField O ⊗[O] B :=
    (Algebra.TensorProduct.includeRight : B →ₐ[O] BaseField O ⊗[O] B).toRingHom.comp
        (algebraMap Oδ B)
  let alg : Algebra Oδ (BaseField O ⊗[O] B) := f.toAlgebra
  have hf : ∀ o, Θ (algebraMap Oδ (BaseField Oδ ⊗[Oδ] B) o) = algebraMap Oδ (BaseField O ⊗[O] B)
      o := by
    intro o
    rw [Algebra.TensorProduct.algebraMap_apply', hΘ]
    rfl
  have : IsScalarTower O Oδ (BaseField O ⊗[O] B) := IsScalarTower.of_algebraMap_eq (fun a => by
    change _ = (1 : BaseField O) ⊗ₜ algebraMap Oδ B (algebraMap O Oδ a)
    rw [Algebra.TensorProduct.algebraMap_apply', ← IsScalarTower.algebraMap_apply])
  let Θa : BaseField Oδ ⊗[Oδ] B ≃ₐ[Oδ] BaseField O ⊗[O] B := AlgEquiv.ofRingEquiv (f := Θ) hf
  have : Algebra.IsIntegral O Oδ := Algebra.IsIntegral.of_finite O Oδ
  have hint : ∀ z, IsIntegral Oδ z ↔ IsIntegral O (Θ z) := by
    intro z
    rw [← isIntegral_algEquiv Θa]
    exact ⟨fun h => isIntegral_trans _ h, fun h => h.tower_top⟩
  let : Module O (GenericClosure Oδ B) := Module.compHom _ (algebraMap O Oδ)
  have : IsScalarTower O Oδ (GenericClosure Oδ B) := ⟨fun a b x => by
    change (a • b) • x = (algebraMap O Oδ a) • (b • x)
    rw [Algebra.smul_def a b, mul_smul]⟩
  let θ : GenericClosure Oδ B ≃ₗ[O] GenericClosure O B :=
  { toFun := fun z => (⟨Θ (z : ↥(integralClosure Oδ (BaseField Oδ ⊗[Oδ] B))).1,
        (hint _).1 (z : ↥(integralClosure Oδ (BaseField Oδ ⊗[Oδ] B))).2⟩ :
        ↥(integralClosure O (BaseField O ⊗[O] B)))
    invFun := fun w => (⟨Θ.symm (w : ↥(integralClosure O (BaseField O ⊗[O] B))).1,
        (hint _).2 (by simpa [mem_integralClosure_iff] using
          (w : ↥(integralClosure O (BaseField O ⊗[O] B))).2)⟩ :
        ↥(integralClosure Oδ (BaseField Oδ ⊗[Oδ] B)))
    map_add' := fun z w => Subtype.ext (map_add Θ _ _)
    map_smul' := fun a z => by
      apply Subtype.ext
      change Θ (algebraMap O Oδ a • (z : ↥(integralClosure Oδ (BaseField Oδ ⊗[Oδ] B))).1) = a • _
      rw [← algebraMap_smul Oδ a (Θ _)]
      exact map_smul Θa _ _
    left_inv := fun z => Subtype.ext (Θ.symm_apply_apply _)
    right_inv := fun w => Subtype.ext (Θ.apply_symm_apply _) }
  have hmap : ((orderImage Oδ B).restrictScalars O).map (θ : GenericClosure Oδ B →ₗ[O]
      GenericClosure O B)
      = orderImage O B := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext w
    change Θ.symm (w : ↥(integralClosure O (BaseField O ⊗[O] B))).1 ∈ LinearMap.range _ ↔
      (w : ↥(integralClosure O (BaseField O ⊗[O] B))).1 ∈ LinearMap.range _
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      have := congrArg Θ hb
      simp only [RingEquiv.apply_symm_apply] at this
      rw [← this]
      exact (hΘ b).symm
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      change (1 : BaseField Oδ) ⊗ₜ b = _
      rw [← Θ.symm_apply_apply ((1 : BaseField Oδ) ⊗ₜ b), hΘ]
      exact congrArg Θ.symm hb
  calc orderDefect Oδ B = Module.length Oδ (GenericClosure Oδ B ⧸ orderImage Oδ B) := rfl
    _ ≤ Module.length O (GenericClosure Oδ B ⧸ orderImage Oδ B) :=
      length_le_length_restrict O Oδ _
    _ = Module.length O (GenericClosure Oδ B ⧸ (orderImage Oδ B).restrictScalars O) :=
      (Submodule.Quotient.restrictScalarsEquiv O (orderImage Oδ B)).length_eq.symm
    _ = orderDefect O B := (Submodule.Quotient.equiv _ _ θ hmap).length_eq

/-- The order defect of a finite product is the sum of the order defects. -/
theorem order_defect_pi (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (B : Fin n → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)] :
    orderDefect O (∀ j, B j) = ∑ j, orderDefect O (B j) := by
  let K := BaseField O
  let p : TensorProduct O K (∀ j, B j) ≃ₐ[O] ∀ j, TensorProduct O K (B j) :=
    (Algebra.TensorProduct.piRight O K K B).restrictScalars O
  obtain ⟨φ, hφ⟩ := integral_closure_algEquiv O _ _ p
  obtain ⟨e₁, he₁⟩ := integralClosure_pi_equiv O (Fin n) (fun j => TensorProduct O K (B j))
  let E : GenericClosure O (∀ j, B j) ≃ₗ[O] ∀ j, GenericClosure O (B j) :=
    φ.toLinearEquiv.trans e₁
  have hE : ∀ (x : GenericClosure O (∀ j, B j)) (j : Fin n),
      genericClosureVal O (B j) (E x j) = p (genericClosureVal O (∀ j, B j) x) j := by
    intro x j
    have := he₁ (φ x) j
    rwa [hφ x] at this
  have hmap : (orderImage O (∀ j, B j)).map E.toLinearMap
      = Submodule.pi Set.univ (fun j => orderImage O (B j)) := by
    have hmem : ∀ (C : Type) [CommRing C] [Algebra O C] (z : GenericClosure O C),
        z ∈ orderImage O C ↔ ∃ c : C, (1 : K) ⊗ₜ[O] c = genericClosureVal O C z := by
      intro C _ _ z
      simp [orderImage, Submodule.mem_comap, LinearMap.mem_range,
        K]
    ext y
    simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨x, hx, rfl⟩ j
      obtain ⟨b, hb⟩ := (hmem _ x).1 hx
      refine (hmem _ _).2 ⟨b j, ?_⟩
      rw [show (E.toLinearMap x) j = E x j from rfl, hE, ← hb]
      rfl
    · intro hy
      choose b hb using fun j => (hmem _ (y j)).1 (hy j)
      refine ⟨E.symm y, (hmem _ _).2 ⟨b, ?_⟩, by simp⟩
      apply p.injective
      funext j
      rw [← hE, LinearEquiv.apply_symm_apply, ← hb j]
      rfl
  unfold orderDefect
  rw [(Submodule.Quotient.equiv _ _ E hmap).length_eq, (Submodule.quotientPi _).length_eq,
    Module.length_pi_of_fintype]

end SurfaceBlowup
