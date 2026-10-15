/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Formula.PatternCounts
import SurfaceBlowup.Recursion.Termination

/-!
# Order defects and child data for the blowup recursion

The order defect `orderDefect O A` (the `O`-length of the generic closure of `A` modulo the
image of `A`) controls termination of the blowup recursion. This file proves its additivity
along finite-cokernel injections into products and its monotonicity in the children; the
combinatorics matching children of a tangent pattern with points of an exceptional divisor;
and the explicit completed local rings (child data) at points of the exceptional line of the
`t`-chart, including the one-chart atlas for repeated-root states.

## Main results

* `order_defect_children_sum`, `order_defect_child_le`, `etale_invariant_children`:
  `δ(A) = Σⱼ δ(Bⱼ) + ℓ` and the resulting strict decrease of the order defect.
* `cell_assignment_exists`, `concrete_member_divisor_count`: children ↔ divisor points, and
  the count of divisors with a given tangent pattern.
* `series_quotient_equiv_adjoinRoot`, `repeated_root_chart_type`,
  `repeated_root_one_chart_atlas`: the repeated-root chart.
* `t_chart_rational_point_child_data`, `t_chart_nonrational_point_child_data`,
  `cell_child_Phi_eq_map`: child data at closed points of the exceptional line.

Provenance: `Thm_SurfaceBlowupV2_` nodes `order_defect_{transport,children_sum,child_le}`,
`order_image_free`, `order_defect_ne_top_of_type`, `etale_invariant_children`,
`otherChildren_count`, `cell_assignment_exists`, `pattern_divisors_finite`,
`concrete_member_divisor_count`, `pi_field_quotient_equiv`, `root_cell_clauses_reindex`,
`scaled_strict_map_measurable`, `series_quotient_equiv_adjoinRoot`,
`repeated_root_{chart_type,one_chart_atlas}`, `strict_transform_map_along_point_equiv`,
`divisor_strict_transform_map_along_equiv`, `cell_child_Phi_eq_map`,
`t_chart_{nonrational,rational}_point_child_data`.
-/

open scoped BigOperators ENNReal TensorProduct

namespace SurfaceBlowup

/-! ### Order defects -/

private theorem length_quotient_map_add (O : Type) [CommRing O] (N C : Type) [AddCommGroup N]
    [Module O N]
    [AddCommGroup C] [Module O C] (j : N →ₗ[O] C) (hj : Function.Injective j) (P : Submodule O N) :
    Module.length O (C ⧸ P.map j) = Module.length O (N ⧸ P) +
        Module.length O (C ⧸ LinearMap.range j) := by
  have hle : P.map j ≤ LinearMap.range j := by
    rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩
  let f : (N ⧸ P) →ₗ[O] (C ⧸ P.map j) := P.mapQ (P.map j) j (fun x hx ↦ ⟨x, hx, rfl⟩)
  let g : (C ⧸ P.map j) →ₗ[O] (C ⧸ LinearMap.range j) := Submodule.factor hle
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H y =>
    rw [LinearMap.mem_ker] at hx
    change Submodule.Quotient.mk (j y) = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨z, hz, hzy⟩ := hx
    rw [hj hzy] at hz
    simpa using hz
  · exact Submodule.factor_surjective hle
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H c =>
    change Submodule.Quotient.mk c = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    · rintro ⟨y, hy⟩
      induction y using Submodule.Quotient.induction_on with
      | H y =>
      change Submodule.Quotient.mk (j y) = Submodule.Quotient.mk c at hy
      rw [Submodule.Quotient.eq] at hy
      obtain ⟨z, _, hz⟩ := hy
      refine ⟨y - z, ?_⟩
      rw [map_sub, hz]; abel

private noncomputable def genericInclusion (O : Type) [CommRing O] [IsDomain O] (B : Type)
    [CommRing B]
    [Algebra O B]
    [Module.Finite O B] : B →ₗ[O] GenericClosure O B where
  toFun b := (⟨(1 : BaseField O) ⊗ₜ[O] b,
    (Algebra.IsIntegral.isIntegral (R := O) b).map
      (Algebra.TensorProduct.includeRight : B →ₐ[O] BaseField O ⊗[O] B)⟩ :
      integralClosure O (BaseField O ⊗[O] B))
  map_add' _ _ := Subtype.ext (TensorProduct.tmul_add _ _ _)
  map_smul' _ _ := Subtype.ext (TensorProduct.tmul_smul _ _ _)

private theorem orderImage_eq_range (O : Type) [CommRing O] [IsDomain O] (B : Type) [CommRing B]
    [Algebra O B]
    [Module.Finite O B] : orderImage O B = LinearMap.range (genericInclusion O B) := by
  ext x
  exact ⟨fun ⟨b, hb⟩ ↦ ⟨b, Subtype.ext hb⟩, fun ⟨b, hb⟩ ↦ ⟨b, hb ▸ rfl⟩⟩

private theorem genericInclusion_injective (O : Type) [CommRing O] [IsDomain O] (B : Type)
    [CommRing B] [Algebra O B]
    [Module.Finite O B] [Module.Free O B] : Function.Injective (genericInclusion O B) := by
  intro x y h
  have h2 : (1 : BaseField O) ⊗ₜ[O] x = (1 : BaseField O) ⊗ₜ[O] y := congrArg Subtype.val h
  have hinj : Function.Injective (LinearMap.rTensor B (Algebra.linearMap O (BaseField O))) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O (BaseField O))
  exact (TensorProduct.lid O B).symm.injective (hinj (by simpa using h2))


/-- If `ψ : A →ₐ[O] N` is injective with `N` finite free and `ψ` becomes bijective after base
change to the fraction field, then `orderDefect O A = orderDefect O N + ℓ`, where `ℓ` is the
`O`-length of the cokernel of `ψ`. -/
private theorem order_defect_transport (O : Type) [CommRing O] [IsDomain O] (A N : Type)
    [CommRing A]
    [CommRing N] [Algebra O A] [Algebra O N] [Module.Finite O A] [Module.Finite O N]
    [Module.Free O N] (ψ : A →ₐ[O] N)
    (hbij : Function.Bijective
        (Algebra.TensorProduct.map (AlgHom.id (BaseField O) (BaseField O)) ψ))
    (ℓ : ℕ) (hℓ : Module.length O (N ⧸ LinearMap.range ψ.toLinearMap) = ℓ) :
    orderDefect O A = orderDefect O N + ℓ := by
  let Ψ := AlgEquiv.ofBijective _ hbij
  let φ : GenericClosure O A ≃ₐ[O] GenericClosure O N := (Ψ.restrictScalars O).mapIntegralClosure
  have hφ : ∀ a, φ (genericInclusion O A a) = genericInclusion O N (ψ a) := by
    intro a
    apply Subtype.ext
    change Ψ ((1 : BaseField O) ⊗ₜ[O] a) = (1 : BaseField O) ⊗ₜ[O] ψ a
    simp [Ψ]
  have hS : (orderImage O A).map φ.toLinearEquiv.toLinearMap
      = (LinearMap.range ψ.toLinearMap).map (genericInclusion O N) := by
    rw [orderImage_eq_range, LinearMap.range_eq_map, LinearMap.range_eq_map, ← Submodule.map_comp,
      ← Submodule.map_comp]
    congr 1
  have h1 : orderDefect O A = Module.length O (GenericClosure O N ⧸
      (LinearMap.range ψ.toLinearMap).map (genericInclusion O N)) := by
    unfold orderDefect
    rw [← hS]
    exact (Submodule.Quotient.equiv _ _ φ.toLinearEquiv rfl).length_eq
  rw [h1, length_quotient_map_add O N _ (genericInclusion O N) (genericInclusion_injective O N), hℓ,
    orderDefect, orderImage_eq_range, add_comm]

/-- Additivity of the order defect over a DVR: for an injection `ψ : A → ∏ⱼ Bⱼ` with cokernel
of length `ℓ`, `orderDefect O A = Σⱼ orderDefect O (Bⱼ) + ℓ`. -/
theorem order_defect_children_sum (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (n : ℕ) (B : Fin n → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)] [∀ j, Module.Finite O (B j)]
    [∀ j, Module.Free O (B j)] (ψ : A →ₐ[O] ∀ j, B j) (hinj : Function.Injective ψ) (ℓ : ℕ)
    (hℓ : Module.length O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = ℓ) :
    orderDefect O A = ∑ j, orderDefect O (B j) + ℓ := by
  have h := baseChange_bijective_of_finite_cokernel O A (∀ j, B j) ψ.toLinearMap hinj ℓ hℓ
  have hbij : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id (BaseField O) (BaseField O)) ψ) := by
    have : ⇑(Algebra.TensorProduct.map (AlgHom.id (BaseField O) (BaseField O)) ψ) =
      ⇑(LinearMap.baseChange (BaseField O) ψ.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    exact this ▸ h
  rw [order_defect_transport O A (∀ j, B j) ψ hbij ℓ hℓ,
    order_defect_pi]

/-- If `A ↪ ∏ⱼ Bⱼ` has cokernel of length `ℓ` and `A` has finite order defect, then each `Bⱼ` has
finite order defect at most that of `A`, strictly smaller when `ℓ ≥ 1`. -/
theorem order_defect_child_le (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (n : ℕ) (B : Fin n → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)] [∀ j, Module.Finite O (B j)]
    [∀ j, Module.Free O (B j)] (ψ : A →ₐ[O] ∀ j, B j) (hinj : Function.Injective ψ) (ℓ : ℕ)
    (hℓ : Module.length O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = ℓ)
    (hA : orderDefect O A ≠ ⊤) :
    ∀ j, orderDefect O (B j) ≤ orderDefect O A ∧ orderDefect O (B j) ≠ ⊤ ∧
    (1 ≤ ℓ → orderDefect O (B j) < orderDefect O A) := by
  intro j
  have h := order_defect_children_sum O A n B ψ hinj ℓ hℓ
  have h1 : orderDefect O (B j) ≤ ∑ j', orderDefect O (B j') :=
    Finset.single_le_sum (f := fun j' ↦ orderDefect O (B j')) (fun _ _ ↦ zero_le)
      (Finset.mem_univ j)
  have h2 : orderDefect O (B j) ≤ orderDefect O A := h ▸ h1.trans le_self_add
  have hS : ∑ j', orderDefect O (B j') ≠ ⊤ := ne_top_of_le_ne_top hA (h ▸ le_self_add)
  refine ⟨h2, ne_top_of_le_ne_top hA h2, fun hl ↦ ?_⟩
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hS
  refine lt_of_le_of_lt h1 ?_
  rw [h, ← hm]
  have : m < m + ℓ := by omega
  exact_mod_cast this

/-- For a finite free `O`-algebra `B`: `B → K ⊗[O] B` is injective, the order image of `B` is
finite free of rank `rank B`, and `K ⊗[O] B` has `K`-dimension `rank B` (`K = BaseField O`). -/
private theorem order_image_free (O : Type) [CommRing O] [IsDomain O] (B : Type) [CommRing B]
    [Algebra O B]
    [Module.Finite O B] [Module.Free O B] :
    Function.Injective
      (Algebra.TensorProduct.includeRight : B →ₐ[O] TensorProduct O (BaseField O) B) ∧
    Module.Finite O (orderImage O B) ∧ Module.Free O (orderImage O B) ∧
    Module.finrank O (orderImage O B) = Module.finrank O B ∧
    Module.finrank (BaseField O) (TensorProduct O (BaseField O) B) = Module.finrank O B := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : B →ₐ[O] TensorProduct O (BaseField O) B) :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective O (FractionRing O))
  have hint : ∀ b : B,
      (Algebra.TensorProduct.includeRight : B →ₐ[O] TensorProduct O (BaseField O) B) b ∈
      integralClosure O (TensorProduct O (BaseField O) B) := fun b ↦
    (IsIntegral.of_finite O b).map _
  let ρ : B →ₗ[O] GenericClosure O B :=
    LinearMap.codRestrict (integralClosure O (TensorProduct O (BaseField O) B)).toSubmodule
      (Algebra.TensorProduct.includeRight :
        B →ₐ[O] TensorProduct O (BaseField O) B).toLinearMap hint
  have hρ : Function.Injective ρ := fun x y h ↦ hinj (congrArg Subtype.val h)
  have hrange : LinearMap.range ρ = orderImage O B := by
    ext z
    exact ⟨fun ⟨b, hb⟩ ↦ ⟨b, hb ▸ rfl⟩, fun ⟨b, hb⟩ ↦ ⟨b, Subtype.ext hb⟩⟩
  let e : B ≃ₗ[O] orderImage O B :=
    (LinearEquiv.ofInjective ρ hρ).trans (LinearEquiv.ofEq _ _ hrange)
  exact ⟨hinj, Module.Finite.equiv e, Module.Free.of_equiv e, (LinearEquiv.finrank_eq e).symm,
    Module.finrank_baseChange⟩

/-- A finite free algebra admitting a factorization type, over a DVR with finite residue field,
has finite order defect. -/
private theorem order_defect_ne_top_of_type (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
    [Module.Free O B] (σ : FactorType) (h : HasAlgebraType O B σ) :
    orderDefect O B ≠ ⊤ := by
  obtain ⟨_, _, hr⟩ := generic_closure_free_of_type O B σ h
  obtain ⟨_, _, _, hr2, hr3⟩ := order_image_free O B
  exact full_rank_free_submodule_finite_length O (GenericClosure O B) (orderImage O B)
    (by rw [hr2, hr, hr3])

/-- The order defects of the children `Bⱼ`, measured over their own DVRs `Oⱼ` (in which `π` stays
a uniformizer), are at most the order defect of `A`, and strictly smaller when `ℓ ≥ 1`. -/
theorem etale_invariant_children (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (n : ℕ) (Oj : Fin n → Type) [∀ j, CommRing (Oj j)]
    [∀ j, IsDomain (Oj j)] [∀ j, IsDiscreteValuationRing (Oj j)] [∀ j, Algebra O (Oj j)]
    [∀ j, Module.Finite O (Oj j)] [∀ j, Module.Free O (Oj j)] (δ : Fin n → ℕ)
    (hrank : ∀ j, Module.finrank O (Oj j) = δ j) (pi : O) (hpi : Irreducible pi)
    (hpiδ : ∀ j, Irreducible (algebraMap O (Oj j) pi)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Free O A] (B : Fin n → Type) [∀ j, CommRing (B j)]
    [∀ j, Algebra O (B j)] [∀ j, Module.Finite O (B j)] [∀ j, Module.Free O (B j)]
    [∀ j, Algebra (Oj j) (B j)] [∀ j, IsScalarTower O (Oj j) (B j)] (ψ : A →ₐ[O] ∀ j, B j)
    (hinj : Function.Injective ψ) (ℓ : ℕ)
    (hℓ : Module.length O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = ℓ) (σ : FactorType)
    (hσ : HasAlgebraType O A σ) :
    ∀ j, (orderDefect (Oj j) (B j)).toNat ≤ (orderDefect O A).toNat ∧
    (1 ≤ ℓ → (orderDefect (Oj j) (B j)).toNat < (orderDefect O A).toNat) := by
  have hA : orderDefect O A ≠ ⊤ := order_defect_ne_top_of_type O A σ hσ
  intro j
  have h₁ := order_defect_le_of_tower O (Oj j) (δ j) (hrank j) pi hpi (hpiδ j) (B j)
  obtain ⟨h₂, _, h₃⟩ := order_defect_child_le O A n B ψ hinj ℓ hℓ hA j
  refine ⟨ENat.toNat_le_toNat (h₁.trans h₂) hA, fun h ↦ ?_⟩
  have hlt := h₁.trans_lt (h₃ h)
  have hne := ne_top_of_lt hlt
  rw [← ENat.natCast_toNat_eq_self.2 hne, ← ENat.natCast_toNat_eq_self.2 hA] at hlt
  exact_mod_cast hlt

/-! ### Children of a tangent pattern and exceptional divisors -/

/-- Multiplicities in `otherChildren w mm`: the child `(δ, single w r)` occurs `mm (δ-1, r-1)`
times (zero outside the index range), and no other single or crossing state occurs. -/
private theorem otherChildren_count (n : ℕ) (w : ℕ) (mm : Pattern n) (δ r : ℕ) :
    (otherChildren w mm).count (δ, State.single w r) =
        (if h : 1 ≤ δ ∧ δ ≤ n ∧ 1 ≤ r ∧ r ≤ n then
          (mm (⟨δ - 1, by omega⟩, ⟨r - 1, by omega⟩)).val else 0) ∧
    (∀ w' r', w' ≠ w → (otherChildren w mm).count (δ, State.single w' r') = 0) ∧
    ∀ (a' b' c' h' : ℕ), (otherChildren w mm).count (δ, State.crossing a' b' c' h') = 0 := by
  have key : ∀ v : ℕ × State, (otherChildren w mm).count v =
      ∑ ij : Fin n × Fin n,
        if (ij.1.val+1, State.single w (ij.2.val+1)) = v then (mm ij).val else 0 := by
    intro v
    unfold otherChildren
    rw [List.count_flatMap]
    rw [← Finset.sum_map_toList Finset.univ
      (fun ij : Fin n × Fin n ↦
        if (ij.1.val+1, State.single w (ij.2.val+1)) = v then (mm ij).val else 0)]
    congr 1
    apply List.map_congr_left
    intro ij _
    simp only [Function.comp, List.count_replicate]
    by_cases h : (ij.1.val+1, State.single w (ij.2.val+1)) = v <;> simp [h]
  refine ⟨?_, ?_, ?_⟩
  · rw [key]
    split_ifs with h
    · rw [Finset.sum_eq_single (⟨δ - 1, by omega⟩, ⟨r - 1, by omega⟩)]
      · rw [if_pos]
        simp [Prod.ext_iff]; omega
      · rintro ⟨i, j⟩ _ hne
        rw [if_neg]
        intro he
        simp only [Prod.mk.injEq, State.single.injEq] at he
        apply hne
        ext <;> simp <;> omega
      · simp
    · apply Finset.sum_eq_zero
      rintro ⟨i, j⟩ _
      rw [if_neg]
      intro he
      simp only [Prod.mk.injEq, State.single.injEq] at he
      have := i.2; have := j.2
      apply h; omega
  · intro w' r' hw
    rw [key]
    refine Finset.sum_eq_zero fun ij _ ↦ if_neg fun he ↦ ?_
    simp only [Prod.mk.injEq, State.single.injEq] at he
    exact hw he.2.1.symm
  · intro a b c h
    rw [key]
    exact Finset.sum_eq_zero fun ij _ ↦ if_neg (by simp)

open scoped Classical in
private lemma natCard_subtype_eq_filter_card {α : Type} (T : Finset α) (p : α → Prop)
    (h : ∀ x, p x → x ∈ T) :
    Nat.card {x // p x} = (T.filter p).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x ↦ by
    simp only [Finset.mem_filter]; exact ⟨fun hp ↦ ⟨h x hp, hp⟩, fun hp ↦ hp.2⟩))

private lemma directionDegree_mul_le (k : Type) [Field k] (Dv : ExceptionalDivisor k)
    (Q : ClosedDirection k) : directionDegree k Q * Dv Q ≤ exceptionalDegree k Dv := by
  unfold exceptionalDegree Finsupp.sum
  by_cases hQ : Q ∈ Dv.support
  · exact Finset.single_le_sum (f := fun P ↦ directionDegree k P * Dv P)
      (fun _ _ ↦ Nat.zero_le _) hQ
  · simp [Finsupp.notMem_support_iff.mp hQ]

open scoped Classical in
private lemma otherChildren_count_eq_card (k : Type) [Field k] (s : State)
    (P : TangentPattern s.degree)
    (Dv : ExceptionalDivisor k)
    (hDv : HasPattern k s Dv P) (w : ℕ)
    (hw : ∀ Q, Q ∉ boundaryDirections k s → pointChildState k s P.d.val Dv Q =
        State.single w (Dv Q))
    (c : ℕ × State) :
    (otherChildren w P.other).count c =
      (Dv.support.filter (fun Q ↦ (directionDegree k Q, pointChildState k s P.d.val Dv Q) = c ∧
        Q ∉ boundaryDirections k s)).card := by
  have hfc : Dv.support.filter
      (fun Q ↦ (directionDegree k Q, pointChildState k s P.d.val Dv Q) = c ∧
        Q ∉ boundaryDirections k s) = Dv.support.filter (fun Q ↦ Q ∉ boundaryDirections k s ∧
        (directionDegree k Q, State.single w (Dv Q)) = c) :=
    Finset.filter_congr fun Q _ ↦ by
      by_cases h : Q ∈ boundaryDirections k s <;> simp [h, hw Q, and_comm]
  rw [hfc]
  have hOC := otherChildren_count s.degree w P.other
  obtain ⟨δ, st⟩ := c
  have hempty : ∀ (p : ClosedDirection k → Prop) [DecidablePred p],
      (∀ Q, Dv Q ≠ 0 → ¬ p Q) → (Dv.support.filter p).card = 0 := fun p _ hp ↦
    Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun Q hQ ↦
      hp Q (Finsupp.mem_support_iff.mp hQ))
  rcases st with ⟨w', r⟩ | ⟨a', b', c', h'⟩
  · by_cases hww : w' = w
    · subst hww
      rw [(hOC δ r).1]
      split_ifs with hc
      · have := hDv.2.2.2 (⟨δ - 1, by omega⟩, ⟨r - 1, by omega⟩)
        rw [natCard_subtype_eq_filter_card Dv.support _
          (fun Q hQ ↦ Finsupp.mem_support_iff.mpr (by simp at hQ; omega))] at this
        rw [← this]
        congr 1
        ext Q
        simp only [Finset.mem_filter, Prod.mk.injEq, State.single.injEq, true_and]
        exact ⟨fun ⟨h1, h2, _, _⟩ ↦ ⟨h1, h2, by omega⟩,
          fun ⟨h1, h2, _⟩ ↦ ⟨h1, h2, by omega, by omega⟩⟩
      · refine (hempty _ ?_).symm
        rintro Q hQ ⟨_, h2⟩
        simp only [Prod.mk.injEq, State.single.injEq, true_and] at h2
        have h5 := directionDegree_mul_le k Dv Q
        rw [hDv.1] at h5
        have := Nat.le_mul_of_pos_left (Dv Q) (directionDegree_pos k Q)
        have := Nat.le_mul_of_pos_right (directionDegree k Q) (Nat.pos_of_ne_zero hQ)
        have := P.d.isLt
        have := directionDegree_pos k Q
        exact hc (by omega)
    · rw [(hOC δ r).2.1 w' r hww]
      refine (hempty _ ?_).symm
      rintro Q _ ⟨_, h2⟩
      simp only [Prod.mk.injEq, State.single.injEq] at h2
      exact hww h2.2.1.symm
  · rw [(hOC δ 0).2.2 a' b' c' h']
    exact (hempty _ fun Q _ ⟨_, h2⟩ ↦ by simp at h2).symm

private lemma beq_inst_eq : (instBEqOfDecidableEq : BEq (ℕ × State)) = instBEqProd :=
  lawful_beq_subsingleton _ _

/-- For a divisor `Dv` with the allowed tangent pattern `P`, the children of `(s, P)` can be
matched bijectively with the support points of `Dv`, respecting degrees and child states. -/
theorem cell_assignment_exists (k : Type) [Field k] [Finite k] (s : State) (hs : s.Valid)
    (P : TangentPattern s.degree) (hP : Allowed s P) (Dv : ExceptionalDivisor k)
    (hDv : HasPattern k s Dv P) :
    Nonempty (CellAssignment k s P Dv) := by
  classical
  let g' : ClosedDirection k → ℕ × State :=
    fun Q ↦ (directionDegree k Q, pointChildState k s P.d.val Dv Q)
  let g : {Q // 0 < Dv Q} → ℕ × State := fun Q ↦ g' Q.1
  have : Finite {Q // 0 < Dv Q} :=
    (Dv.support.finite_toSet.subset fun Q hQ ↦
      Finsupp.mem_support_iff.2 (Nat.pos_iff_ne_zero.1 hQ)).to_subtype
  have hlist (b : Prop) [Decidable b] (x c : ℕ × State) :
      (if b then [] else [x]).count c = if (¬ b ∧ x = c) then 1 else 0 := by
    by_cases hb : b <;> by_cases hx : x = c <;> simp [hb, hx]
  have hnz : zeroDirection k ≠ infinityDirection k := by simp [zeroDirection, infinityDirection]
  have key : ∀ c, (children s P).count c = (Dv.support.filter (fun Q ↦ g' Q = c)).card := by
    intro c
    rw [← Finset.card_filter_add_card_filter_not (s := Dv.support.filter (fun Q ↦ g' Q = c))
      (fun Q ↦ Q ∈ boundaryDirections k s), Finset.filter_filter, Finset.filter_filter]
    have hB := otherChildren_count_eq_card k s P Dv hDv s.weight ?_ c
    rotate_left
    · intro Q hQ
      cases s <;> simp_all [pointChildState, boundaryDirections, State.weight]
    rw [← hB]
    have hA : ∀ (T : Finset (ClosedDirection k)), (∀ Q, Q ∈ boundaryDirections k s ↔ Q ∈ T) →
        (Dv.support.filter (fun Q ↦ g' Q = c ∧ Q ∈ boundaryDirections k s)).card =
          ∑ Q ∈ T, if (0 < Dv Q ∧ g' Q = c) then 1 else 0 := by
      intro T hT
      rw [← Finset.card_filter]
      congr 1
      ext Q
      simp only [Finset.mem_filter, Finsupp.mem_support_iff, hT, Nat.pos_iff_ne_zero]
      tauto
    obtain ⟨hdeg, hrt, hrx, -⟩ := hDv
    cases s with
    | single a c0 =>
      rw [hA {infinityDirection k} (by intro Q; simp [boundaryDirections])]
      simp only [children, List.count_append, hlist, Finset.sum_singleton]
      congr 1
      simp only [g', pointChildState, if_true, hrt]
      simp only [infinityDirection, directionDegree] at hrt ⊢
      simp only [Nat.pos_iff_ne_zero]
    | crossing a b c0 h0 =>
      rw [hA {infinityDirection k, zeroDirection k} (by intro Q; simp [boundaryDirections]),
        Finset.sum_pair hnz.symm]
      simp only [children, List.count_append, hlist]
      simp only at hrx
      congr 1
      have hzi : zeroDirection k = infinityDirection k ↔ False := ⟨hnz, False.elim⟩
      simp only [g', pointChildState, if_true, hzi, if_false, hrt, hrx]
      simp only [infinityDirection, directionDegree, zeroDirection, Polynomial.natDegree_X,
        Nat.pos_iff_ne_zero]
  obtain ⟨e, he⟩ := equiv_of_fiber_card_eq (Fin (children s P).length) {Q // 0 < Dv Q} (ℕ × State)
    (children s P).get g (fun c ↦ by
      rw [list_get_fiber_card_count]
      refine Eq.trans (by rw [beq_inst_eq]) ((key c).trans ?_)
      rw [Nat.card_congr
          (Equiv.subtypeSubtypeEquivSubtypeInter (fun Q ↦ 0 < Dv Q) (fun Q ↦ g' Q = c)),
        natCard_subtype_eq_filter_card Dv.support _
          (fun Q hQ ↦ Finsupp.mem_support_iff.mpr (by omega))]
      congr 1
      ext Q
      simp only [Finset.mem_filter, Finsupp.mem_support_iff, Nat.pos_iff_ne_zero]
      tauto)
  exact ⟨{ pt := fun j ↦ (e j).1
           inj := fun i j hij ↦ e.injective (Subtype.ext hij)
           supp := fun Q ↦ ⟨fun hQ ↦ ⟨e.symm ⟨Q, hQ⟩, by simp⟩, by rintro ⟨j, rfl⟩; exact (e j).2⟩
           deg := fun j ↦ congrArg Prod.fst (he j)
           state := fun j ↦ (congrArg Prod.snd (he j)).symm }⟩

/-- Over a finite field there are only finitely many exceptional divisors with a given tangent
pattern. -/
private theorem pattern_divisors_finite (k : Type) [Field k] [Finite k] (s : State)
    (P : TangentPattern s.degree) :
    Finite (patternDivisors k s P) := by
  set n := P.d.val with hn
  have hpos := directionDegree_pos k
  have key : ∀ D : patternDivisors k s P, ∀ Q, directionDegree k Q * D.1 Q ≤ n :=
    fun D Q ↦ (directionDegree_mul_le k D.1 Q).trans_eq D.2.1
  have hTfin : Finite {Q : ClosedDirection k // directionDegree k Q ≤ n} := by
    let f : {Q : ClosedDirection k // directionDegree k Q ≤ n} → Option (Fin (n+1) → k) :=
      fun Q ↦ Option.map (fun φ : AffineDirection k ↦ fun i : Fin (n+1) ↦ φ.val.coeff i) Q.1
    refine Finite.of_injective f ?_
    rintro ⟨_ | φ, hQ⟩ ⟨_ | ψ, hQ'⟩ h
    · rfl
    all_goals simp only [f, Option.map_some, Option.map_none, reduceCtorEq,
      Option.some.injEq] at h
    refine Subtype.ext (congrArg some (Subtype.ext (Polynomial.ext fun i ↦ ?_)))
    by_cases hi : i < n + 1
    · exact congrFun h ⟨i, hi⟩
    · simp only [directionDegree] at hQ hQ'
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  have := hTfin
  refine Finite.of_injective
    (fun (D : patternDivisors k s P) (Q : {Q : ClosedDirection k // directionDegree k Q ≤ n}) ↦
      (⟨min (D.1 Q.1) n, by omega⟩ : Fin (n+1))) ?_
  intro D D' h
  apply Subtype.ext
  apply Finsupp.ext
  intro Q
  have hb : ∀ E : patternDivisors k s P, E.1 Q ≤ n := by
    intro E
    have := key E Q
    have := hpos Q
    nlinarith
  by_cases hQ : directionDegree k Q ≤ n
  · have := congrFun h ⟨Q, hQ⟩
    simp only [Fin.mk.injEq] at this
    have := hb D; have := hb D'
    omega
  · have z : ∀ E : patternDivisors k s P, E.1 Q = 0 := by
      intro E
      by_contra hne
      have := key E Q
      have : 1 ≤ E.1 Q := Nat.pos_of_ne_zero hne
      nlinarith
    rw [z D, z D']

/-- For a concrete member the pattern-divisor sets are finite, and for nonterminal states the
number of divisors with an allowed pattern `P` is `tangentCount s P` evaluated at `q`. -/
theorem concrete_member_divisor_count (m : ConcreteMember) :
    (∀ P : TangentPattern m.s.degree,
        Finite (patternDivisors (IsLocalRing.ResidueField m.R) m.s P)) ∧
    (m.s.terminal = false → ∀ P : TangentPattern m.s.degree, Allowed m.s P →
        ((Nat.card (patternDivisors (IsLocalRing.ResidueField m.R) m.s P) : ℕ) : ℚ) =
        (tangentCount m.s P).eval (m.toMeasured.q : ℚ)) := by
  have hfin : Finite (IsLocalRing.ResidueField m.R) :=
    Finite.of_equiv _ m.S.residueEquiv.toEquiv
  refine ⟨fun P ↦ pattern_divisors_finite _ m.s P, fun _ P hP ↦ ?_⟩
  rw [(pattern_divisor_count _ m.s P hP).2]
  congr 2
  exact Nat.card_congr m.S.residueEquiv.toEquiv.symm

/-! ### Auxiliary algebra and measurability -/

/-- Every quotient of a finite product of fields `∏ᵢ Lᵢ` is the product of the factors over some
subset `S`, compatibly with the coordinate projections. -/
theorem pi_field_quotient_equiv (K : Type) [Field K] (ι : Type) [Finite ι] (L : ι → Type)
    [∀ i, Field (L i)] [∀ i, Algebra K (L i)] (I : Ideal (∀ i, L i)) :
    ∃ (S : Finset ι) (e : ((∀ i, L i) ⧸ I) ≃ₐ[K] (∀ i : S, L i.1)), ∀ (x : ∀ i, L i) (i : S),
    e (Ideal.Quotient.mk I x) i = x i.1 := by
  have := Fintype.ofFinite ι
  classical
  let S : Finset ι := Finset.univ.filter (fun i ↦ (Pi.single i (1 : L i) : ∀ j, L j) ∉ I)
  let π : (∀ i, L i) →ₐ[K] (∀ i : S, L i.1) :=
    AlgHom.pi (fun i : S ↦ Pi.evalAlgHom K L i.1)
  have hπ : ∀ x i, π x i = x i.1 := fun x i ↦ rfl
  have hsurj : Function.Surjective π := by
    intro y
    refine ⟨fun i ↦ if h : i ∈ S then y ⟨i, h⟩ else 0, ?_⟩
    funext i
    rw [hπ]
    simp [i.2]
  have hker : I = RingHom.ker π := by
    ext x
    rw [RingHom.mem_ker]
    constructor
    · intro hx
      funext i
      rw [hπ]
      by_contra hne
      have hi := i.2
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      apply hi
      have : (Pi.single i.1 (1 : L i.1) : ∀ j, L j) = Pi.single i.1 ((x i.1)⁻¹) * x := by
        funext j
        by_cases hj : j = i.1
        · subst hj; simp [inv_mul_cancel₀ hne]
        · simp [hj]
      rw [this]
      exact I.mul_mem_left _ hx
    · intro hx
      rw [← Finset.univ_sum_single x]
      refine I.sum_mem fun i _ ↦ ?_
      by_cases hi : i ∈ S
      · rw [show x i = 0 from congrFun hx ⟨i, hi⟩, Pi.single_zero]
        exact I.zero_mem
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      rw [← mul_one (x i), Pi.single_mul]
      exact I.mul_mem_left _ hi
  refine ⟨S, (Ideal.quotientEquivAlgOfEq K hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj), fun x i ↦ ?_⟩
  simp [Ideal.quotientEquivAlgOfEq_mk, hπ]

/-- The measurability and mass clauses for the set of `z` with `HasPolynomialTypeF` of the monic
polynomial of `π • z` transport along an equality of dimensions `n = r`. -/
theorem root_cell_clauses_reindex (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (pi : O) (σ : FactorType) (v : ℝ≥0∞) (n r : ℕ) (h : n = r)
    (hn : MeasurableSet {z : Fin n → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} ∧
        coefficientMeasure O n
          {z : Fin n → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} = v) :
    MeasurableSet {z : Fin r → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} ∧
    coefficientMeasure O r {z : Fin r → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} =
        v := by
  subst h; exact hn

/-- The scaled strict normalizer map is measurable for the adic cylinder σ-algebra: it factors as
a continuous linear part after a measurable adic perturbation. -/
theorem scaled_strict_map_measurable (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (H : (Fin n → O) →ₗ[O] R) (k : ℕ)
    (ha : k < a) (Q : (Fin n → O) →ₗ[O] (Fin n → O))
    (hQ : ∀ w, normalizationLinearPart E H (Q w) = (pi ^ k) • w)
    [IsAdicComplete (Ideal.span {pi}) (Fin n → O)] [TopologicalSpace (Fin n → O)]
    [MeasurableSpace (Fin n → O)] [BorelSpace (Fin n → O)]
    (hgen : ‹MeasurableSpace (Fin n → O)› = adicCylinderSpace (Ideal.span {pi}) (Fin n → O))
    (hcont : Continuous (fun z : Fin n → O ↦ (pi^a) • normalizationLinearPart E H z)) :
    Measurable (scaledStrictMap pi a b E H) := by
  have h1 : scaledStrictMap pi a b E H =
    (fun z : Fin n → O ↦ (pi^a) • normalizationLinearPart E H z) ∘
    adicPerturb (normalizationCorrection pi a k b E H Q) := by
    funext z
    exact strict_normalizer_factors_through_linear O R n pi a b E H k ha Q hQ z
  rw [h1]
  exact hcont.measurable.comp
    (adic_perturb_measurable O (Fin n → O) (Ideal.span {pi}) _
      (strict_correction_raises_order O R n pi a b E H k ha Q) hgen)

/-! ### The repeated-root chart -/

/-- The powers `1, x, …, x^(r-1)` form a residue basis of `R/(f)` as soon as some reduction
map `φ : R → k⟦X⟧` is surjective, sends `x` to `X`, `f` to `X^r`, scalars to their residues,
and has kernel `π R`. -/
private theorem residue_basis_of_reduction {O R : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [CommRing R] [Algebra O R] (pi : O) (hpi : Irreducible pi) (x f : R) (r : ℕ)
    (φ : R →+* PowerSeries (IsLocalRing.ResidueField O)) (hφs : Function.Surjective φ)
    (hφx : φ x = PowerSeries.X)
    (hφc : ∀ c : O, φ (algebraMap O R c) = PowerSeries.C (IsLocalRing.residue O c))
    (hφker : ∀ w : R, φ w = 0 → ∃ m' : R, w = pi • m') (hφf : φ f = PowerSeries.X ^ r) :
    ResidueBasisFamily pi (fun i : Fin r ↦ Ideal.Quotient.mk (Ideal.span {f}) (x ^ (i : ℕ))) := by
  have hφsmul (c : O) (y : R) : φ (c • y) = PowerSeries.C (IsLocalRing.residue O c) * φ y := by
    rw [show c • y = algebraMap O R c * y from Algebra.smul_def c y, map_mul, hφc]
  have hres0 (c : O) : IsLocalRing.residue O c = 0 ↔ pi ∣ c := by
    rw [IsLocalRing.residue_eq_zero_iff, hpi.maximalIdeal_eq, Ideal.mem_span_singleton]
  have hlin (c : O) (y : R) : c • Ideal.Quotient.mk (Ideal.span {f}) y =
      Ideal.Quotient.mk (Ideal.span {f}) (c • y) :=
    (map_smul (Ideal.Quotient.mkₐ O (Ideal.span {f})) c y).symm
  refine ⟨fun m ↦ ?_, fun z ⟨m', hm'⟩ i ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective m
    set g := φ w with hgdef
    choose z' hz' using fun n ↦ IsLocalRing.residue_surjective (PowerSeries.coeff n g)
    obtain ⟨h', hh'⟩ : ∃ h', φ h' = PowerSeries.mk fun i ↦ PowerSeries.coeff (i + r) g :=
      hφs _
    have htr : ((PowerSeries.trunc r g : Polynomial _) : PowerSeries _) =
        ∑ i : Fin r, PowerSeries.C (PowerSeries.coeff (i : ℕ) g) * PowerSeries.X ^ (i : ℕ) := by
      rw [PowerSeries.trunc_apply, ← Finset.range_eq_Ico, Fin.sum_univ_eq_sum_range
        (fun n ↦ PowerSeries.C (PowerSeries.coeff n g) * PowerSeries.X ^ n),
        ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial,
        PowerSeries.monomial_eq_C_mul_X_pow]
    have key : φ (w - ∑ i : Fin r, z' i • x ^ (i : ℕ) - f * h') = 0 := by
      rw [map_sub, map_sub, map_mul, hφf, hh', map_sum]
      simp_rw [hφsmul, hz', map_pow, hφx]
      rw [← hgdef]
      linear_combination PowerSeries.eq_X_pow_mul_shift_add_trunc r g + htr
    obtain ⟨m', hm'⟩ := hφker _ key
    refine ⟨fun i ↦ z' i, Ideal.Quotient.mk _ m', ?_⟩
    simp_rw [hlin, ← map_sum, ← map_add]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨h', by linear_combination -hm'⟩
  · obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective m'
    simp_rw [hlin, ← map_sum] at hm'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hm')
    have h2 := congrArg φ hc
    rw [map_mul, map_sub, hφsmul, map_sum, hφf, (hres0 pi).2 dvd_rfl, map_zero, zero_mul,
      sub_zero] at h2
    have h3 := congrArg (PowerSeries.coeff (i : ℕ)) h2
    rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega), map_sum] at h3
    simp_rw [hφsmul, map_pow, hφx, PowerSeries.coeff_C_mul_X_pow] at h3
    rw [Finset.sum_eq_single i (fun j _ hj ↦ if_neg (fun h ↦ hj (Fin.ext h).symm))
      (by simp), if_pos rfl] at h3
    exact (hres0 _).1 h3.symm

/-- For monic `F` of degree `r > 0` whose lower coefficients lie in the maximal ideal, the
quotient of the concrete surface `(1, 1, 0)` by `F(x)` is `O`-isomorphic to `AdjoinRoot F`,
compatibly with evaluation of polynomials at `x`. -/
theorem series_quotient_equiv_adjoinRoot (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (F : Polynomial O) (hF : F.Monic) (r : ℕ) (hr : 0 < r)
    (hdeg : F.natDegree = r) (hred : ∀ i : ℕ, i < r → F.coeff i ∈ IsLocalRing.maximalIdeal O) :
    ∃ e : (ConcreteSurface O pi 1 1 0 ⧸
        Ideal.span {Polynomial.aeval (surfaceX O pi 1 1 0) F}) ≃ₐ[O] AdjoinRoot F,
      ∀ P : Polynomial O, e (Ideal.Quotient.mk
        (Ideal.span {Polynomial.aeval (surfaceX O pi 1 1 0) F})
        (Polynomial.aeval (surfaceX O pi 1 1 0) P)) = AdjoinRoot.mk F P := by
  set R := ConcreteSurface O pi 1 1 0
  set x : R := surfaceX O pi 1 1 0
  set f : R := Polynomial.aeval x F with hfdef
  obtain ⟨hC, -, hX, -, -⟩ := residueKillT_apply_ker O pi hpi
  have hT : algebraMap O R pi = surfaceT O pi 1 1 0 := by
    rw [concrete_surface_vertical]; simp [surfaceUnit]
  -- `φ : R → k⟦X⟧` is reduction modulo `T = π`.
  obtain ⟨q, hq⟩ := concrete_surface_quotient_T_equiv O pi hpi 1 1 0 one_pos
  let φ : R →+* PowerSeries (IsLocalRing.ResidueField O) :=
    q.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {surfaceT O pi 1 1 0}))
  have hφx : φ x = PowerSeries.X := (hq _).trans hX
  have hφc (c : O) : φ (algebraMap O R c) = PowerSeries.C (IsLocalRing.residue O c) :=
    (hq (MvPowerSeries.C c)).trans (hC c)
  have hφker (w : R) (hw : φ w = 0) : ∃ m' : R, w = pi • m' := by
    obtain ⟨m', hm'⟩ := Ideal.mem_span_singleton'.1
      (Ideal.Quotient.eq_zero_iff_mem.1 (q.injective (hw.trans (map_zero q).symm)))
    exact ⟨m', by rw [← hm', ← hT, mul_comm]; exact (Algebra.smul_def _ _).symm⟩
  have hφf : φ f = PowerSeries.X ^ r := by
    have hFbar : F.map (IsLocalRing.residue O) = Polynomial.X ^ r := by
      ext i
      rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
      rcases lt_trichotomy i r with h | rfl | h
      · rw [if_neg h.ne, (IsLocalRing.residue_eq_zero_iff _).2 (hred i h)]
      · rw [if_pos rfl, ← hdeg, hF.coeff_natDegree, map_one]
      · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg ▸ h), map_zero]
    rw [hfdef, Polynomial.aeval_def, Polynomial.hom_eval₂, hφx,
      show φ.comp (algebraMap O R) = PowerSeries.C.comp (IsLocalRing.residue O) from
        RingHom.ext hφc, ← Polynomial.eval₂_map, hFbar]
    simp
  have hf : Function.Injective fun w : R ⧸ Ideal.span {algebraMap O R pi} ↦
      Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) f * w := by
    rw [hT]
    refine fun w w' h ↦ q.injective (mul_left_cancel₀ (a := q (Ideal.Quotient.mk _ f)) ?_
      (by simpa only [map_mul] using congrArg q h))
    change φ f ≠ 0
    rw [hφf]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  have hβ := residue_basis_of_reduction pi hpi x f r φ
    (q.surjective.comp Ideal.Quotient.mk_surjective) hφx hφc hφker hφf
  obtain ⟨B, hB⟩ := concrete_surface_curve_basis O pi hpi 1 1 0 one_pos f hf _ hβ
  subst hdeg
  let ψ : AdjoinRoot F →ₐ[O] R ⧸ Ideal.span {f} :=
    AdjoinRoot.liftAlgHom F (Algebra.ofId O _) (Ideal.Quotient.mk _ x)
      ((Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ O _) x F).trans
        (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)))
  have hψ (P : Polynomial O) :
      ψ (AdjoinRoot.mk F P) = Ideal.Quotient.mk (Ideal.span {f}) (Polynomial.aeval x P) :=
    (AdjoinRoot.liftAlgHom_mk ..).trans (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ O _) x P)
  let pb := AdjoinRoot.powerBasis' hF
  let L : AdjoinRoot F ≃ₗ[O] R ⧸ Ideal.span {f} := pb.basis.equiv B (Equiv.refl _)
  have hψL : ψ.toLinearMap = L.toLinearMap := pb.basis.ext fun i ↦ by
    rw [AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
      show L (pb.basis i) = B i from Module.Basis.equiv_apply _ _ _ _]
    refine Eq.trans ?_ (hB i).symm
    rw [pb.basis_eq_pow, AdjoinRoot.powerBasis'_gen, ← AdjoinRoot.mk_X, ← map_pow, hψ, map_pow,
      Polynomial.aeval_X]
  have hbij : Function.Bijective ψ := by
    rw [show ⇑ψ = ⇑L from congrArg DFunLike.coe hψL]; exact L.bijective
  refine ⟨(AlgEquiv.ofBijective ψ hbij).symm, fun P ↦ ?_⟩
  rw [AlgEquiv.symm_apply_eq, AlgEquiv.ofBijective_apply, hψ]

/-- In the repeated-root chart `x^r` with basis `(x^i)`, the coordinate ideal of `z` has algebra
type `σ` iff the monic polynomial with lower coefficients `π • z` has polynomial type `σ`. -/
theorem repeated_root_chart_type (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (r : ℕ) (hr : 0 < r) (z : Fin r → O) (σ : FactorType) :
    HasAlgebraType O (ConcreteSurface O pi 1 1 0 ⧸ coordinateIdeal pi (surfaceX O pi 1 1 0 ^ r)
        (fun i : Fin r ↦ surfaceX O pi 1 1 0 ^ i.val) z) σ ↔
    HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ := by
  obtain ⟨hm, hd, hc, -⟩ := monic_poly_reconstruct O r (pi • z)
  have hI : coordinateIdeal pi (surfaceX O pi 1 1 0 ^ r)
      (fun i : Fin r ↦ surfaceX O pi 1 1 0 ^ i.val) z
      = Ideal.span {Polynomial.aeval (surfaceX O pi 1 1 0) (monicPolyO (pi • z))} := by
    unfold coordinateIdeal normalizedIdeal normalizedGenerator coordinateLift
    congr 2
    simp [monicPolyO, Polynomial.aeval_add, Algebra.smul_def, mul_assoc]
  have hred : ∀ i : ℕ, i < r → (monicPolyO (pi • z)).coeff i ∈ IsLocalRing.maximalIdeal O := by
    intro i hi
    have := hc ⟨i, hi⟩
    simp only at this
    rw [this, (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).1 hpi]
    exact Ideal.mem_span_singleton.2 ⟨z ⟨i, hi⟩, by simp⟩
  obtain ⟨e, -⟩ := series_quotient_equiv_adjoinRoot O pi hpi _ hm r hr hd hred
  rw [hI, ← monicPolyO_map_fraction, polynomial_type_iff_algebra_type O _ hm]
  exact ⟨algebra_type_algEquiv O _ _ e σ, algebra_type_algEquiv O _ _ e.symm σ⟩

/-- The quotient of the concrete surface `(1, 1, 0)` by `x^n` (`n > 0`) has the `O`-basis
`1, x, …, x^(n-1)`. -/
private theorem surface_quotient_xpow_basis (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (n : ℕ) (hn : 0 < n) :
    ∃ B : Module.Basis (Fin n) O
        (ConcreteSurface O pi 1 1 0 ⧸ Ideal.span {surfaceX O pi 1 1 0 ^ n}),
      ∀ i, B i = Ideal.Quotient.mk (Ideal.span {surfaceX O pi 1 1 0 ^ n})
        (surfaceX O pi 1 1 0 ^ i.val) := by
  set x := surfaceX O pi 1 1 0
  obtain ⟨φ, hφ⟩ := series_quotient_equiv_adjoinRoot O pi hpi (Polynomial.X ^ n)
    (Polynomial.monic_X_pow n) n hn (Polynomial.natDegree_X_pow n)
    (fun i hi ↦ by simp [Polynomial.coeff_X_pow, hi.ne])
  generalize hg : Polynomial.aeval x (Polynomial.X ^ n : Polynomial O) = g at φ hφ
  simp only [map_pow, Polynomial.aeval_X] at hg
  subst hg
  let pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow (R := O) n)
  refine ⟨(pb.basis.reindex (finCongr (Polynomial.natDegree_X_pow n))).map
    φ.symm.toLinearEquiv, fun i ↦ ?_⟩
  apply φ.injective
  have := hφ (Polynomial.X ^ i.val)
  simp only [Polynomial.aeval_X_pow] at this
  rw [this, Module.Basis.map_apply, Module.Basis.reindex_apply, pb.basis_eq_pow]
  simp [pb, map_pow, AdjoinRoot.mk_X]
  rfl

/-- The state `single 1 r` on the concrete surface `(1, 1, 0)` admits a one-chart ideal atlas,
with chart `x^r` and basis `(x^i)`, whose state measure is `q⁻ʳ` times the pushforward of the
coefficient measure under the coordinate ideal map. -/
theorem repeated_root_one_chart_atlas (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (pi : O) (hpi : Irreducible pi)
    [IsDomain (ConcreteSurface O pi 1 1 0)] [IsRegularLocalRing (ConcreteSurface O pi 1 1 0)]
    (S : SurfaceData O (ConcreteSurface O pi 1 1 0)) (hSpi : S.pi = pi)
    (hSt : S.t = surfaceT O pi 1 1 0) (hSa : S.a = 1)
    (hSb : S.b = 0) (r : ℕ) (hr : 0 < r) :
    ∃ A : IdealAtlas O (ConcreteSurface O pi 1 1 0) S.pi (State.single 1 r).degree
      (surfaceStateSet O (ConcreteSurface O pi 1 1 0) S (State.single 1 r)),
    ∃ i₀ : A.ι, (∀ i, i = i₀) ∧
    (A.chart i₀).f = (surfaceX O pi 1 1 0) ^ (State.single 1 r).degree ∧
    (A.chart i₀).b = (fun i : Fin (State.single 1 r).degree ↦ (surfaceX O pi 1 1 0) ^ i.val) ∧
    (letI : MeasurableSpace (Ideal (ConcreteSurface O pi 1 1 0)) :=
      idealChartSigma O (ConcreteSurface O pi 1 1 0) S.pi
    stateMeasure O (ConcreteSurface O pi 1 1 0) S.pi (State.single 1 r).degree
      (Nat.card (IsLocalRing.ResidueField O)) A =
    ((Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (State.single 1 r).degree) •
      (coefficientMeasure O (State.single 1 r).degree).map
        (coordinateIdeal S.pi ((surfaceX O pi 1 1 0) ^ (State.single 1 r).degree)
          (fun i : Fin (State.single 1 r).degree ↦ (surfaceX O pi 1 1 0) ^ i.val))) := by
  set n := (State.single 1 r).degree with hn_def
  have hn : n = r := by simp [n, State.degree]
  set R := ConcreteSurface O pi 1 1 0
  set k := IsLocalRing.ResidueField O
  set x : R := surfaceX O pi 1 1 0
  obtain ⟨e, he⟩ := concrete_surface_special_fiber_equiv O pi hpi 1 1 0
  have hpar := concrete_surface_special_fiber_equiv_parameters O pi 1 1 0 e he
  -- the image of `x^n` in the special fibre
  have hex : e (Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) (x ^ n)) =
      Ideal.Quotient.mk (monomialIdeal k 1 0) (axisX k ^ n) := by
    rw [map_pow, map_pow, hpar.2.1, fiberX, map_pow]
  have hcont : contact (Ideal.Quotient.mk (monomialIdeal k 1 0) (axisX k ^ n))
      (fiberT k 1 0) = r := by
    rw [contact_fiberT_eq_axisQuotientLength _ 1 0 one_pos,
      axisQuotientLength_eq _ (by decide : (0 : Fin 2) ≠ 1) _ n, hn]
    · intro j hj
      rw [axisX, MvPowerSeries.coeff_X_pow, if_neg]
      intro h
      have := congrArg (fun m ↦ m 1) h
      simp at this; omega
    · rw [axisX, MvPowerSeries.coeff_X_pow, if_pos rfl]; exact one_ne_zero
  have hxne : x ^ n ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero, ← map_zero (Ideal.Quotient.mk (monomialIdeal k 1 0))] at hex
    rw [← hex, contact_fiberT_eq_axisQuotientLength _ 1 0 one_pos,
      axisQuotientLength_eq_top _ (by decide : (0 : Fin 2) ≠ 1) _ (fun j ↦ by simp)] at hcont
    exact ENat.top_ne_natCast r hcont
  have hreg : Function.Injective fun y : R ⧸ Ideal.span {algebraMap O R pi} ↦
      y * Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) (x ^ n) := by
    have h501 := concrete_surface_residue_regular_of_special_fiber O pi 1 1 0 _ e
      (special_fiber_single_contact_regular k 1 r one_pos _ (hex ▸ hcont))
    intro a b hab
    apply h501
    change _ * a = _ * b
    rw [mul_comm _ a, mul_comm _ b]; exact hab
  obtain ⟨B, hB⟩ := surface_quotient_xpow_basis O pi hpi n (hn ▸ hr)
  obtain ⟨E, hE⟩ := division_linear_equivalence O R n (x ^ n) B (fun i ↦ x ^ i.val)
    (fun i ↦ (hB i).symm) hxne
  let c₀ : IdealChart O R pi n := ⟨x ^ n, fun i ↦ x ^ i.val, E, hE, hreg⟩
  have hcover : surfaceStateSet O R S (State.single 1 r) =
      residueIdealCell (algebraMap O R pi) (x ^ n) := by
    have hcard := single_residue_ideal_count k 1 r one_pos
    rw [one_mul, Nat.sub_self, pow_zero, Nat.card_eq_one_iff_unique] at hcard
    obtain ⟨hsub, hne⟩ := hcard
    let I0 : singleResidueIdeals k 1 r :=
      ⟨Ideal.span {Ideal.Quotient.mk (monomialIdeal k 1 0) (axisX k ^ n)}, _, rfl, hcont⟩
    obtain ⟨h1, -⟩ := concrete_single_state_eq_union_cells O pi 1 1 one_pos S hSt hSa hSb e he r hr
      (fun _ ↦ x ^ n) (fun I ↦ by
        rw [hex]; exact congrArg Subtype.val (Subsingleton.elim I0 I))
    rw [h1]
    exact Set.iUnion_const _
  rw [hSpi]
  refine ⟨⟨Unit, fun _ ↦ c₀, ?_, ?_⟩, (), fun _ ↦ rfl, rfl, rfl, ?_⟩
  · rw [hcover]; exact (Set.iUnion_const _).symm
  · exact Subsingleton.pairwise
  · simp only [stateMeasure, Fintype.sum_unique]; rfl

/-! ### Child data at points of the exceptional line -/

/-- Transporting the strict transform at a point of a blowup chart along a ring isomorphism of
its completed local ring gives the strict transform ideal for the composite map. -/
private theorem strict_transform_map_along_point_equiv (O R : Type) [CommRing O] [CommRing R]
    [Algebra O R]
    (t x : R) (P : Ideal (BlowupChart R t x)) [P.IsPrime] (S' : Type) [CommRing S'] [Algebra O S']
    (Eq : CompletedLocalAt (BlowupChart R t x) P ≃+* S') (alpha : R →ₐ[O] S')
    (halpha : ∀ r : R, alpha r = Eq (completedPointMap (BlowupChart R t x) P (chartBase R t x r)))
    (d : ℕ) (J : Ideal R) :
    Ideal.map (Eq : CompletedLocalAt (BlowupChart R t x) P →+* S') (strictTransformAt R t x P d J) =
        strictTransformIdeal alpha
        (Eq (completedPointMap (BlowupChart R t x) P (chartBase R t x t))) d J := by
  unfold strictTransformAt strictTransformIdeal
  have h1 : J.map alpha.toRingHom =
    (J.map ((completedPointMap (BlowupChart R t x) P).comp
    (chartBase R t x))).map (Eq : CompletedLocalAt (BlowupChart R t x) P →+* S') := by
    rw [Ideal.map_map]
    congr 1
    ext r
    exact halpha r
  rw [h1, ← map_pow]
  generalize J.map ((completedPointMap (BlowupChart R t x) P).comp (chartBase R t x)) = I
  generalize (completedPointMap (BlowupChart R t x) P (chartBase R t x t)) ^ d = z
  ext y
  have key : ∀ (K : Ideal (CompletedLocalAt (BlowupChart R t x) P)) w, w ∈
    K.map (Eq : CompletedLocalAt (BlowupChart R t x) P →+* S') ↔ Eq.symm w ∈ K := by
    intro K w
    have := Ideal.comap_symm (I := K) Eq
    exact (Iff.of_eq (congrArg (w ∈ ·) this.symm))
  rw [key, Submodule.mem_colon_singleton, Submodule.mem_colon_singleton, key, smul_eq_mul,
    smul_eq_mul]
  simp

/-- The divisor strict transform at a support point, transported along a ring isomorphism of its
local ring, is the strict transform ideal for the composite map. -/
private theorem divisor_strict_transform_map_along_equiv (R : Type) [CommRing R] (t x : R)
    [IsLocalRing R]
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (IsLocalRing.ResidueField R))
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField R)) (hinf : (infinityPoint R t x).IsPrime)
    (Q : divisorSupport Dv) (O S' : Type) [CommRing O] [Algebra O R] [CommRing S'] [Algebra O S']
    (E : divisorLocalRing R t x e Dv hinf Q ≃+* S') (alpha : R →ₐ[O] S')
    (halpha : ∀ r : R, alpha r = E (divisorFromSurface R t x e Dv hinf Q r)) (d : ℕ) (J : Ideal R) :
    Ideal.map (E : divisorLocalRing R t x e Dv hinf Q →+* S')
        (divisorStrictTransform R t x e Dv hinf d J Q) =
        strictTransformIdeal alpha (E (divisorException R t x e Dv hinf Q)) d J := by
  rcases Q with ⟨_ | φ, h⟩
  · exact @strict_transform_map_along_point_equiv O R _ _ _ x t (infinityPoint R t x) hinf S' _ _
      E alpha halpha d J
  · exact @strict_transform_map_along_point_equiv O R _ _ _ t x (directionPoint R t x e φ)
      (directionPoint_isPrime R t x e φ) S' _ _ E alpha halpha d J

/-- The child map `D.Φ` of cell child data is the image of the divisor strict transform under
the identification `D.Eq j` of local rings. -/
theorem cell_child_Phi_eq_map (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c)
    (J : Ideal m.R) (j : m.toMeasured.childIdx c) :
    D.Φ J j = Ideal.map (D.Eq j : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) →+*
        (D.mc j).R) (divisorStrictTransform m.R m.S.t m.S.x D.e c.2.1 D.hinf
        (m.toMeasured.cellDegree c) J (D.point j)) := by
  rw [divisor_strict_transform_map_along_equiv m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) m.O
    (D.mc j).R (D.Eq j) (D.alpha j) (fun r ↦ rfl), D.hEq_e j]
  rfl

private theorem natDegree_eq_of_span_eq (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (O : Type) [CommRing O] (f : O →+* R)
    (P : Ideal (BlowupChart R t x)) [P.IsMaximal] (hP : chartBase R t x t ∈ P)
    (Φ : Polynomial O) (hΦ : Φ.Monic)
    (hspan : P = Ideal.span {chartBase R t x t,
      Polynomial.eval₂ ((chartBase R t x).comp f) (chartSlope R t x) Φ}) (δ : ℕ)
    (hdeg : Module.length R (BlowupChart R t x ⧸ P) = (δ : ℕ∞)) : Φ.natDegree = δ := by
  obtain ⟨e, he, heZ⟩ := exceptional_line_equiv_chart_exceptional R t x
  obtain ⟨φ, hmon, hirr, himg, -, hlen⟩ :=
    blowup_chart_exceptional_point_polynomial R t x e he heZ P hP
  rw [hdeg] at hlen
  have hδ : φ.natDegree = δ := by exact_mod_cast hlen.symm
  set g : O →+* (R ⧸ Ideal.span ({t,x} : Set R)) :=
    (Ideal.Quotient.mk _).comp f with hg
  have key : (P.map (Ideal.Quotient.mk (chartExceptional R t x))).map e = Ideal.span {Φ.map g} := by
    rw [hspan, Ideal.map_span, Ideal.map_span]
    have h0 : e (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x t)) = 0 := by
      have : Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x t) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
      rw [this, map_zero]
    have h1 : e (Ideal.Quotient.mk (chartExceptional R t x)
        (Polynomial.eval₂ ((chartBase R t x).comp f) (chartSlope R t x) Φ)) = Φ.map g := by
      have := Polynomial.hom_eval₂ Φ ((chartBase R t x).comp f)
        (e.toRingHom.comp (Ideal.Quotient.mk (chartExceptional R t x))) (chartSlope R t x)
      change (e.toRingHom.comp (Ideal.Quotient.mk (chartExceptional R t x))) _ = _
      rw [this]
      change Polynomial.eval₂ _
        (e (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x))) Φ =
        Polynomial.eval₂ (Polynomial.C.comp g) Polynomial.X Φ
      rw [heZ]
      congr 1
      ext r
      simp [he, hg]
    rw [Set.image_pair, Set.image_pair, h0, h1]
    simp
  rw [himg] at key
  have hassoc : Associated φ (Φ.map g) := by
    rwa [Ideal.span_singleton_eq_span_singleton] at key
  have := Polynomial.eq_of_monic_of_associated hmon (hΦ.map g) hassoc
  rw [← hδ, this, hΦ.natDegree_map]

/-- A closed point of degree `δ ≥ 2` on the exceptional line of the `t`-chart is cut out by an
unramified lift `Φ` of degree `δ`, and its completed local ring is a concrete surface over
`AdjoinRoot Φ` with explicit `t`-parameter and `O`-structure. -/
theorem t_chart_nonrational_point_child_data (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a)
    (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)))
    [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (surfaceT O pi u a b) ∈ P)
    (δ : ℕ)
    (hdeg : Module.length (ConcreteSurface O pi u a b)
        ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸
          P) = (δ : ℕ∞))
    (h2 : 2 ≤ δ) :
    ∃ Φ : Polynomial O, IsUnramifiedLift O Φ ∧ Φ.natDegree = δ ∧
    P = Ideal.span {(chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) (surfaceT O pi u a b),
        Polynomial.eval₂ ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)).comp (algebraMap O (ConcreteSurface O pi u a b)))
        (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) Φ} ∧
    ∃ (hθ : IsUnit (AdjoinRoot.root Φ))
        (Eq : CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) P ≃+*
        ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
        (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) *
        shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0),
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) P) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) (surfaceT O pi u a b))) =
        surfaceT (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
        (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) *
        shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0 ∧
    ∀ c : O,
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) P) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) (algebraMap O (ConcreteSurface O pi u a b) c))) =
        algebraMap (AdjoinRoot Φ) (ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
        (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) *
        shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0)
        (algebraMap O (AdjoinRoot Φ) c) := by
  obtain ⟨e459, -⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  have hmax : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} :
      Set (ConcreteSurface O pi u a b))).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (e459.toMulEquiv.isField (Field.toIsField _))
  have hspanform := concrete_chart_point_span_form O pi hpi u a b ha P hP
  have hdeg' := natDegree_eq_of_span_eq (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)
    O (algebraMap O (ConcreteSurface O pi u a b)) P hP
  rcases hspanform with h | ⟨α, -, h⟩ | ⟨Φ, hΦ, h2Φ, hPΦ⟩
  · exfalso
    have := hdeg' Polynomial.X (Polynomial.monic_X) (by simpa using h) δ hdeg
    simp at this; omega
  · exfalso
    have := hdeg' (Polynomial.X - Polynomial.C α) (Polynomial.monic_X_sub_C α)
      (by simpa [sub_eq_add_neg] using h) δ hdeg
    rw [Polynomial.natDegree_X_sub_C] at this; omega
  · have hnd : Φ.natDegree = δ := hdeg' Φ hΦ.1 hPΦ δ hdeg
    have hθ := unramified_root_isUnit_of_two_le_natDegree O Φ hΦ h2Φ
    obtain ⟨Eq, hs, -, hc, -⟩ :=
      t_chart_nonrational_point_completion_equiv O pi hpi u a b ha Φ hΦ hθ P hPΦ
    refine ⟨Φ, hΦ, hnd, hPΦ, hθ, Eq, ?_, hc⟩
    have := hs (axisT O)
    obtain ⟨-, h2, -⟩ := chartSubst_apply_generators (AdjoinRoot Φ) (AdjoinRoot.root Φ)
    have hm : MvPowerSeries.map (algebraMap O (AdjoinRoot Φ)) (axisT O) = axisT (AdjoinRoot Φ) := by
      simp [axisT, MvPowerSeries.map_X]
    rwa [hm, h2] at this

private theorem not_two_le_natDegree_of_length_one (O R : Type) [CommRing O] [CommRing R]
    (f : O →+* R) (t x : R)
    [(Ideal.span ({t, x} : Set R)).IsMaximal] (P : Ideal (BlowupChart R t x)) [P.IsMaximal]
    (Φ : Polynomial O) (hΦ : Φ.Monic) (h2 : 2 ≤ Φ.natDegree)
    (hPeq : P = Ideal.span {chartBase R t x t,
      Polynomial.eval₂ ((chartBase R t x).comp f) (chartSlope R t x) Φ})
    (hdeg : Module.length R (BlowupChart R t x ⧸ P) = (1 : ℕ∞)) : False := by
  obtain ⟨e1, he, heZ⟩ := exceptional_line_equiv_chart_exceptional R t x
  have hP : chartBase R t x t ∈ P := hPeq ▸ Ideal.subset_span (by simp)
  obtain ⟨φ, hmon, hirr, hmap, -, hlen⟩ :=
    blowup_chart_exceptional_point_polynomial R t x e1 he heZ P hP
  rw [hdeg] at hlen
  have hφ : φ.natDegree = 1 := by exact_mod_cast hlen.symm
  have hk : (Ideal.Quotient.mk (chartExceptional R t x)) (chartBase R t x t) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [hPeq, Ideal.map_span, Set.image_pair, hk, Ideal.map_span] at hmap
  simp only [Set.image_pair] at hmap
  have hev : e1 ((Ideal.Quotient.mk (chartExceptional R t x))
      (Polynomial.eval₂ ((chartBase R t x).comp f) (chartSlope R t x) Φ))
      = Φ.map ((Ideal.Quotient.mk (Ideal.span ({t, x} : Set R))).comp f) := by
    have := Polynomial.hom_eval₂ Φ ((chartBase R t x).comp f)
      (((e1 : _ ≃+* _).toRingHom).comp
        (Ideal.Quotient.mk (chartExceptional R t x))) (chartSlope R t x)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe] at this
    rw [this, heZ]
    simp only [Polynomial.map]
    congr 1
    ext c
    simp [he]
  simp only [hev, map_zero] at hmap
  have h0 : ∀ (K : Type) [CommRing K] (p : K), Ideal.span ({0, p} : Set K) = Ideal.span {p} := by
    intro K _ p
    rw [Ideal.span_insert, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq]
  rw [h0] at hmap
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hmap
  have hne : (Φ.map ((Ideal.Quotient.mk (Ideal.span ({t, x} : Set R))).comp f)) ≠ 0 :=
    (hΦ.map _).ne_zero
  have := congrArg Polynomial.natDegree hw
  rw [Polynomial.natDegree_mul hne w.ne_zero, Polynomial.natDegree_coe_units,
    hΦ.natDegree_map, hφ] at this
  omega

open scoped Classical in
/-- A degree-one point on the exceptional line of the `t`-chart has slope `α` with `α = 0` or a
unit, and its completed local ring is a concrete surface over `O` with explicit parameters. -/
theorem t_chart_rational_point_child_data (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a)
    (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)))
    [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (surfaceT O pi u a b) ∈ P)
    (hdeg : Module.length (ConcreteSurface O pi u a b)
        ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸
          P) = (1 : ℕ∞)) :
    ∃ α : O, (α = 0 ∨ IsUnit α) ∧
    P = Ideal.span {(chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) (surfaceT O pi u a b),
        (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) -
        (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (algebraMap O (ConcreteSurface O pi u a b) α)} ∧
    ∃ (u' : (TwoSeries O)ˣ) (Eq : CompletedLocalAt
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P ≃+*
        ConcreteSurface O pi u' (a + b) (if α = 0 then b else 0)),
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) P) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) (surfaceT O pi u a b))) =
        surfaceT O pi u' (a + b) (if α = 0 then b else 0) ∧
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) P) (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b))) = surfaceX O pi u' (a + b) (if α = 0 then b else 0) +
        algebraMap O (ConcreteSurface O pi u' (a + b) (if α = 0 then b else 0)) α ∧
    ∀ c : O,
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) P) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) (algebraMap O (ConcreteSurface O pi u a b) c))) =
        algebraMap O (ConcreteSurface O pi u' (a + b) (if α = 0 then b else 0)) c := by
  obtain ⟨e, -⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  have hmax : (Ideal.span ({surfaceT O pi u a b, surfaceX O pi u a b} :
      Set (ConcreteSurface O pi u a b))).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := chartSubst_apply_generators O 0
  rcases concrete_chart_point_span_form O pi hpi u a b ha P hP with h | ⟨α, hα, h⟩ | ⟨Φ, hΦ, h2', h⟩
  · have hb : (if (0 : O) = 0 then b else 0) = b := if_pos rfl
    obtain ⟨E, hE1, hE2, hE3⟩ := t_chart_origin_completion_equiv O pi hpi u a b ha P h
    refine ⟨0, Or.inl rfl, ?_, ?_⟩
    · simpa using h
    · rw [hb]
      refine ⟨substUnit O 0 u, E, ?_, ?_, hE3⟩
      · have := hE1 (axisT O)
        rwa [h2] at this
      · simpa using hE2
  · have hα0 : α ≠ 0 := hα.ne_zero
    have hb : (if α = 0 then b else 0) = 0 := if_neg hα0
    obtain ⟨E, hE1, hE2, hE3⟩ := t_chart_unit_point_completion_equiv O pi hpi u a b ha α hα P h
    refine ⟨α, Or.inr hα, h, ?_⟩
    rw [hb]
    refine ⟨_, E, ?_, hE2, hE3⟩
    have := hE1 (axisT O)
    rwa [(chartSubst_apply_generators O α).2.1] at this
  · exact (not_two_le_natDegree_of_length_one O _ (algebraMap O _) _ _ P Φ hΦ.1 h2' h hdeg).elim

end SurfaceBlowup
