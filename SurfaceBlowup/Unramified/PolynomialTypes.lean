/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Algebra.FactorInvariant

/-!
# Polynomial types, form products and residue cells

Polynomial types of polynomials over `Frac O` (invariance under isomorphism of quotient algebras,
additivity on coprime products, uniqueness); the Hensel-type analysis of the normalized product
map on binary-form factor cells (congruence reflection, digit lifting, bijectivity); congruence
criteria for products of monic factors; residue cells as cylinders and their masses; and the
residue extension of an unramified lift `Φ` (a finite field in which `Φ̄` splits into distinct
conjugate linear factors), with the block translation `X ↦ X + θ`.

## Main results

* `SurfaceBlowup.polynomial_type_algEquiv_iff`, `SurfaceBlowup.polynomial_type_unique`
* `SurfaceBlowup.form_product_bijection`, `SurfaceBlowup.factor_product_congruence_iff`
* `SurfaceBlowup.residue_cell_mass`, `SurfaceBlowup.factor_cell_product_measure`
* `SurfaceBlowup.residue_extension_field`, `SurfaceBlowup.conjugate_roots_distinct`,
  `SurfaceBlowup.block_translation`

Provenance: `Thm_SurfaceBlowupV2_{polynomial_type_eq_of_algEquiv, polynomial_type_algEquiv_iff,
polynomial_type_mul_coprime, polynomial_type_unique, primitive_iff_residue_ne_zero,
product_first_order_expansion, form_product_congruence_reflects, form_product_digit_lift,
form_product_bijection, hensel_family_unique_mod_pow, factor_product_congruence_iff,
projective_normalizer_eval, residue_cell_cylinder, residue_cell_mass, factor_cell_product_measure,
residue_extension_equiv, residue_extension_field, block_translation, conjugate_roots_distinct,
residue_vector_fiber_mass, scalar_class_card}`.
-/

namespace SurfaceBlowup

open scoped ENNReal

/-- Polynomials over `Frac O` with isomorphic quotient algebras have the same polynomial type. -/
private theorem polynomial_type_eq_of_algEquiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (F F' : Polynomial (BaseField O)) (σ τ : FactorType)
    (hF : HasPolynomialTypeF O F σ) (hF' : HasPolynomialTypeF O F' τ)
    (e : AdjoinRoot F ≃ₐ[BaseField O] AdjoinRoot F') :
    σ = τ := by
  obtain ⟨gs, hgs, hgd, rfl, rfl, hfin⟩ := hF
  obtain ⟨hs, hhs, hhd, rfl, rfl, -⟩ := hF'
  obtain ⟨e₁, -⟩ := polynomial_quotient_product_equiv (BaseField O) gs hgs hgd
  obtain ⟨e₂, -⟩ := polynomial_quotient_product_equiv (BaseField O) hs hhs hhd
  have : ∀ i : Fin gs.length, Fact (Irreducible (gs.get i)) :=
    fun i => ⟨(hgs _ (List.get_mem _ _)).2⟩
  have : ∀ j : Fin hs.length, Fact (Irreducible (hs.get j)) :=
    fun j => ⟨(hhs _ (List.get_mem _ _)).2⟩
  obtain ⟨π, hπ⟩ := pi_fields_algEquiv_index_bijection (BaseField O) (Fin gs.length)
    (Fin hs.length) (fun i => AdjoinRoot (gs.get i)) (fun j => AdjoinRoot (hs.get j))
    (e₁.symm.trans (e.trans e₂))
  have key : ∀ i, factorInvariant O (gs.get i) = factorInvariant O (hs.get (π i)) := by
    intro i
    obtain ⟨φ, -⟩ := (hπ i).2
    exact factor_invariant_algEquiv O _ _ (hgs _ (List.get_mem _ _)).1
      (hgs _ (List.get_mem _ _)).2 (hhs _ (List.get_mem _ _)).1 (hhs _ (List.get_mem _ _)).2 φ
      (hfin _ (List.get_mem _ _))
  have hL : ∀ l : List (Polynomial (BaseField O)),
      ((l.map (factorInvariant O) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) =
        Multiset.map (factorInvariant O ∘ l.get) (Finset.univ : Finset (Fin l.length)).val := by
    intro l
    conv_lhs => rw [← List.ofFn_get l]
    rw [← Multiset.map_coe, ← Multiset.map_map, Fin.univ_val_map]
  rw [hL gs, hL hs, ← Multiset.map_univ_val_equiv π, Multiset.map_map]
  exact Multiset.map_congr rfl (fun i _ => key i)

/-- One direction of `polynomial_type_algEquiv_iff`. -/
private theorem hasPolynomialTypeF_of_algEquiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (F F' : Polynomial (BaseField O)) (hF' : F'.Monic)
    (e : AdjoinRoot F ≃ₐ[BaseField O] AdjoinRoot F') (σ : FactorType) :
    HasPolynomialTypeF O F σ → HasPolynomialTypeF O F' σ := by
  intro h
  obtain ⟨gs, h1, h2, h3, h4, h5⟩ := h
  have hred : IsReduced (AdjoinRoot F) := by
    subst h3
    obtain ⟨p, _⟩ := SurfaceBlowup.polynomial_quotient_product_equiv (BaseField O) gs h1 h2
    have : ∀ i : Fin gs.length, Fact (Irreducible (gs.get i)) :=
        fun i => ⟨(h1 _ (List.get_mem _ _)).2⟩
    exact isReduced_of_injective (p.toRingEquiv.toRingHom) p.injective
  have hred' : IsReduced (AdjoinRoot F') :=
    isReduced_of_injective (e.symm.toRingEquiv.toRingHom) e.symm.injective
  obtain ⟨hs, k1, k2, k3⟩ := SurfaceBlowup.monic_squarefree_factors_of_reduced
      (BaseField O) F' hF' hred'
  -- closure finiteness of the factors of `F'`, by matching root fields with those of `F`
  have k4 : ∀ g ∈ hs, Module.Finite O (integralClosure O (AdjoinRoot g)) := by
    obtain ⟨e₁, -⟩ := SurfaceBlowup.polynomial_quotient_product_equiv (BaseField O) gs h1 h2
    obtain ⟨e₂, -⟩ := SurfaceBlowup.polynomial_quotient_product_equiv (BaseField O) hs k1 k2
    have : ∀ i : Fin gs.length, Fact (Irreducible (gs.get i)) :=
      fun i => ⟨(h1 _ (List.get_mem _ _)).2⟩
    have : ∀ j : Fin hs.length, Fact (Irreducible (hs.get j)) :=
      fun j => ⟨(k1 _ (List.get_mem _ _)).2⟩
    have e' : AdjoinRoot gs.prod ≃ₐ[BaseField O] AdjoinRoot hs.prod := by
      rw [← h3, ← k3]; exact e
    obtain ⟨π, hπ⟩ := SurfaceBlowup.pi_fields_algEquiv_index_bijection (BaseField O) (Fin gs.length)
      (Fin hs.length) (fun i => AdjoinRoot (gs.get i)) (fun j => AdjoinRoot (hs.get j))
      (e₁.symm.trans (e'.trans e₂))
    intro g hg
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hg
    obtain ⟨i, rfl⟩ := π.surjective j
    obtain ⟨φ, -⟩ := (hπ i).2
    obtain ⟨χ, -⟩ := SurfaceBlowup.integral_closure_algEquiv O _ _ (φ.restrictScalars O)
    have := h5 _ (List.get_mem gs i)
    exact Module.Finite.equiv χ.toLinearEquiv
  have hty : HasPolynomialTypeF O F' (hs.map (factorInvariant O) : Multiset (ℕ × ℕ)) :=
    ⟨hs, k1, k2, k3, rfl, k4⟩
  have := SurfaceBlowup.polynomial_type_eq_of_algEquiv O F F' σ _ ⟨gs, h1, h2, h3, h4, h5⟩ hty e
  rw [this]; exact hty


/-- For monic `F, F'` with `Frac O[X]/(F) ≅ Frac O[X]/(F')`, `F` has type `σ` iff `F'` does. -/
theorem polynomial_type_algEquiv_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (F F' : Polynomial (BaseField O)) (hF : F.Monic)
    (hF' : F'.Monic) (e : AdjoinRoot F ≃ₐ[BaseField O] AdjoinRoot F') (σ : FactorType) :
    HasPolynomialTypeF O F σ ↔ HasPolynomialTypeF O F' σ :=
  ⟨hasPolynomialTypeF_of_algEquiv O F F' hF' e σ, hasPolynomialTypeF_of_algEquiv O F' F hF e.symm σ⟩

/-- The polynomial type of a product of coprime polynomials is the sum of their types. -/
theorem polynomial_type_mul_coprime (O : Type) [CommRing O] [IsDomain O]
    (G H : Polynomial (BaseField O)) (σ τ : FactorType) (hG : HasPolynomialTypeF O G σ)
    (hH : HasPolynomialTypeF O H τ) (hc : IsCoprime G H) :
    HasPolynomialTypeF O (G * H) (σ + τ) := by
  obtain ⟨gs, hg1, hg2, hg3, hg4, hg5⟩ := hG
  obtain ⟨hs, hh1, hh2, hh3, hh4, hh5⟩ := hH
  refine ⟨gs ++ hs, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun g hg => (List.mem_append.1 hg).elim (hg1 g) (hh1 g)
  · rw [List.pairwise_append]
    refine ⟨hg2, hh2, ?_⟩
    intro g hg h hh e
    subst e
    have h1 : g ∣ G := hg3 ▸ List.dvd_prod hg
    have h2 : g ∣ H := hh3 ▸ List.dvd_prod hh
    exact (hg1 g hg).2.not_isUnit (hc.isUnit_of_dvd' h1 h2)
  · rw [List.prod_append, hg3, hh3]
  · rw [List.map_append, hg4, hh4]; rfl
  · exact fun g hg => (List.mem_append.1 hg).elim (hg5 g) (hh5 g)

/-- A polynomial has at most one polynomial type. -/
theorem polynomial_type_unique (O : Type) [CommRing O] [IsDomain O] (F : Polynomial (BaseField O))
    (σ τ : FactorType) (hσ : HasPolynomialTypeF O F σ) (hτ : HasPolynomialTypeF O F τ) :
    σ = τ := by
  obtain ⟨gs, hg, -, hF, rfl, -⟩ := hσ
  obtain ⟨hs, hh, -, hF', rfl, -⟩ := hτ
  have hrel : Multiset.Rel Associated (gs : Multiset (Polynomial (BaseField O)))
      (hs : Multiset _) := by
    apply UniqueFactorizationMonoid.factors_unique
    · intro x hx; exact (hg x (by simpa using hx)).2
    · intro x hx; exact (hh x (by simpa using hx)).2
    · rw [Multiset.prod_coe, Multiset.prod_coe, ← hF, ← hF']; exact Associated.refl _
  have : Multiset.Rel Eq (gs : Multiset (Polynomial (BaseField O))) (hs : Multiset _) := by
    refine hrel.mono fun a ha b hb hab => ?_
    exact Polynomial.eq_of_monic_of_associated (hg a (by simpa using ha)).1
      (hh b (by simpa using hb)).1 hab
  have h2 := Multiset.rel_eq.mp this
  rw [Multiset.coe_eq_coe] at h2 ⊢
  exact (List.Perm.map _ h2)

/-- A coefficient vector is primitive iff its reduction is nonzero. -/
theorem primitive_iff_residue_ne_zero (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (a : Fin (n + 1) → O) :
    primitive O a ↔ residueVector O a ≠ 0 := by
  rw [Function.ne_iff]
  unfold primitive residueVector
  refine exists_congr fun i => ?_
  simp only [Pi.zero_apply, ne_eq, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

open scoped Classical in
/-- First-order expansion of a product: `∏ (G i + E i) ≡ ∏ G i + ∑ E i ∏_{j ≠ i} G j`
modulo `J²` when all `E i ∈ J`. -/
private theorem product_first_order_expansion (A ι : Type) [CommRing A] (J : Ideal A) (G E : ι → A)
    (hE : ∀ i, E i ∈ J) (s : Finset ι) :
    ∏ i ∈ s, (G i + E i) - ∏ i ∈ s, G i - ∑ i ∈ s, E i * ∏ j ∈ s.erase i, G j ∈ J ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    set Q := ∏ i ∈ s, (G i + E i)
    set P := ∏ i ∈ s, G i
    set F := ∑ i ∈ s, E i * ∏ j ∈ s.erase i, G j
    have hF : F ∈ J := Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_right _ _ (hE i))
    have hsum : ∑ i ∈ s, E i * ∏ j ∈ (insert a s).erase i, G j = G a * F := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hne : i ≠ a := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne (Ne.symm hne), Finset.prod_insert
          (fun h => ha (Finset.mem_of_mem_erase h))]
      ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha,
      hsum]
    have hR : Q - P - F ∈ J ^ 2 := ih
    have hQP : Q - P ∈ J := by
      have : Q - P = (Q - P - F) + F := by ring
      rw [this]
      exact J.add_mem (Ideal.pow_le_self two_ne_zero hR) hF
    have key : (G a + E a) * Q - G a * P - (E a * P + G a * F)
        = G a * (Q - P - F) + E a * (Q - P) := by ring
    rw [key]
    refine (J ^ 2).add_mem (Ideal.mul_mem_left _ _ hR) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul (hE a) hQP

/-! ### Coefficient lemmas for binary forms -/

section FormPoly

variable {A : Type} [CommRing A] {n : ℕ}

private theorem formPoly_coeff_eq (x : Fin (n + 1) → A) (k : Fin (n + 1)) :
    (formPoly x).coeff (k : ℕ) = x k := by
  simp [formPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Fin.val_inj]

private theorem formPoly_smul_eq (c : A) (a : Fin (n + 1) → A) :
    formPoly (c • a) = Polynomial.C c * formPoly a := by
  simp [formPoly, Finset.mul_sum, mul_assoc]

private theorem formPoly_natDeg_le (a : Fin (n + 1) → A) : (formPoly a).natDegree ≤ n :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.2)

private theorem formPoly_map_eq {B : Type} [CommRing B] (f : A →+* B) (a : Fin (n + 1) → A) :
    formPoly (fun k => f (a k)) = (formPoly a).map f := by
  simp [formPoly, Polynomial.map_sum]

private theorem formPoly_map_residue (O : Type) [CommRing O] [IsLocalRing O]
    (x : Fin (n + 1) → O) :
    (formPoly x).map (IsLocalRing.residue O) = formPoly (residueVector O x) :=
  (formPoly_map_eq _ x).symm

private theorem formPoly_prod_natDeg_le {ι : Type} (d : ι → ℕ) (v : ∀ i, Fin (d i + 1) → A)
    (s : Finset ι) : (∏ i ∈ s, formPoly (v i)).natDegree ≤ ∑ i ∈ s, d i :=
  (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun _ _ => formPoly_natDeg_le _)

variable {ι : Type} [Fintype ι] {d : ι → ℕ}

open scoped Classical in
/-- The first-order term `∑ i, H i ∏_{j ≠ i} A j` has degree at most `∑ d i`. -/
private theorem natDegree_sum_formPoly_mul_le (A' H : ∀ i, Fin (d i + 1) → A) :
    (∑ i, formPoly (H i) * ∏ j ∈ Finset.univ.erase i, formPoly (A' j)).natDegree ≤ ∑ i, d i :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => Polynomial.natDegree_mul_le.trans <| by
    have := formPoly_prod_natDeg_le d A' (Finset.univ.erase i)
    have := formPoly_natDeg_le (H i)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    omega

open scoped Classical in
/-- First-order expansion of a perturbed form product, coefficientwise:
`∏ (A i + c H i) ≡ ∏ A i + c ∑ H i ∏_{j ≠ i} A j` modulo `c²`. -/
private theorem formProd_add_smul_dvd (c : A) (A' H : ∀ i, Fin (d i + 1) → A)
    (k : Fin ((∑ i, d i) + 1)) :
    c ^ 2 ∣ formProd d (fun i => A' i + c • H i) k - formProd d A' k -
      c * (∑ i, formPoly (H i) * ∏ j ∈ Finset.univ.erase i, formPoly (A' j)).coeff k := by
  have h := product_first_order_expansion (Polynomial A) ι (Ideal.span {Polynomial.C c})
    (fun i => formPoly (A' i)) (fun i => Polynomial.C c * formPoly (H i))
    (fun i => Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) Finset.univ
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow,
    Polynomial.C_dvd_iff_dvd_coeff] at h
  simpa only [formProd, formPoly_add, formPoly_smul_eq, mul_assoc, ← Finset.mul_sum,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul] using h k

end FormPoly

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

private theorem mem_maximalIdeal_pow_iff (hϖ : Irreducible ϖ) (n : ℕ) (x : O) :
    x ∈ IsLocalRing.maximalIdeal O ^ n ↔ ϖ ^ n ∣ x := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem residue_eq_zero_iff_dvd (hϖ : Irreducible ϖ) (x : O) :
    IsLocalRing.residue O x = 0 ↔ ϖ ∣ x := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]

end DVR

/-- On the product of the factor cells, the normalized product map is `P_{μ}⁻¹ P` with the
`μ`-coordinate dropped. -/
private theorem reducedFormProduct_of_mem (O : Type) [CommRing O] [IsLocalRing O] {ι : Type}
    [Fintype ι] (d : ι → ℕ) (ν : ∀ i, Fin (d i + 1))
    (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O) (μ : Fin ((∑ i, d i) + 1))
    {a : ∀ i, Fin (d i) → O} (ha : ∀ i, a i ∈ reducedFormCell O (d i) (ν i) (g i))
    (j : Fin (∑ i, d i)) :
    reducedFormProduct O d ν g μ a j =
      Ring.inverse (formProd d (fun i => insertOne (ν i) (a i)) μ) *
        formProd d (fun i => insertOne (ν i) (a i)) (μ.succAbove j) := by
  simp only [reducedFormProduct, if_pos ha, dropCoord, normalizeAt, Fin.removeNth_apply,
    Pi.smul_apply, smul_eq_mul]

/-- One step of congruence reflection: if two families `A, A'` of forms normalized at `ν`, with
residues `g`, agree modulo `ϖ ^ t` (`t ≥ 1`) and their products are proportional modulo
`ϖ ^ (t + 1)`, then the families agree modulo `ϖ ^ (t + 1)`. -/
private theorem form_congruence_step {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] (d : ι → ℕ)
    (ν : ∀ i, Fin (d i + 1)) (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (hgν : ∀ i, g i (ν i) = 1) (hc : FormsCoprime d g) (μ : Fin ((∑ i, d i) + 1))
    (hμ : formProd d g μ = 1) (A A' : ∀ i, Fin (d i + 1) → O) (hA1 : ∀ i, A i (ν i) = 1)
    (hA'1 : ∀ i, A' i (ν i) = 1) (hAres : ∀ i, residueVector O (A i) = g i)
    (hPres : ∀ k, IsLocalRing.residue O (formProd d A k) = formProd d g k) {t : ℕ} (ht : 1 ≤ t)
    (hM : ∀ k, ϖ ^ (t + 1) ∣
      formProd d A' μ * formProd d A k - formProd d A μ * formProd d A' k)
    (H : ∀ i, Fin (d i + 1) → O) (hH : ∀ i k, A' i k - A i k = ϖ ^ t * H i k) :
    ∀ i k, ϖ ^ (t + 1) ∣ A' i k - A i k := by
  classical
  have hres := residue_eq_zero_iff_dvd hϖ
  set P := formProd d A
  set P' := formProd d A'
  have hHν : ∀ i, H i (ν i) = 0 := fun i => by
    have h := hH i (ν i)
    rw [hA'1 i, hA1 i, sub_self, eq_comm, mul_eq_zero] at h
    exact h.resolve_left (pow_ne_zero _ hϖ.ne_zero)
  set S := ∑ i, formPoly (H i) * ∏ j ∈ Finset.univ.erase i, formPoly (A j)
  have hexp : ∀ k, (ϖ ^ t) ^ 2 ∣ P' k - P k - ϖ ^ t * S.coeff k := by
    have hA'H : A' = fun i => A i + ϖ ^ t • H i := funext fun i => funext fun k => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hH i k]; ring
    intro k
    have h := formProd_add_smul_dvd (ϖ ^ t) A H k
    rwa [← hA'H] at h
  have hX : ∀ k, ϖ ∣ S.coeff μ * P k - P μ * S.coeff k := by
    intro k
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    obtain ⟨e, he⟩ := hexp k
    obtain ⟨e', he'⟩ := hexp μ
    obtain ⟨f, hf⟩ := hM k
    refine (mul_dvd_mul_iff_left (pow_ne_zero (s + 1) hϖ.ne_zero)).mp
      ⟨f - ϖ ^ s * (e' * P k - P μ * e), ?_⟩
    linear_combination hf + P μ * he - P k * he'
  have hSmap : S.map (IsLocalRing.residue O) =
      Polynomial.C (IsLocalRing.residue O (S.coeff μ)) * ∏ i, formPoly (g i) := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
    by_cases hn : n ≤ ∑ i, d i
    · have h := (hres _).2 (hX ⟨n, by omega⟩)
      rw [map_sub, map_mul, map_mul, hPres, hPres, hμ, one_mul, sub_eq_zero] at h
      exact h.symm
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_sum_formPoly_mul_le A H).trans_lt (by omega)),
        Polynomial.coeff_eq_zero_of_natDegree_lt
        ((formPoly_prod_natDeg_le d g Finset.univ).trans_lt (by omega)), mul_zero, map_zero]
  have hinj := forms_linear_injective (IsLocalRing.ResidueField O) ι d g
    (fun i h0 => by simpa [h0] using hgν i) hc ν (fun i => by simp [hgν])
    (fun i m => IsLocalRing.residue O (H i m)) (fun i => by simp [hHν])
    (IsLocalRing.residue O (S.coeff μ)) (by
      rw [← hSmap, Polynomial.map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Polynomial.map_mul, Polynomial.map_prod, formPoly_map_residue, hAres]
      rfl)
  intro i k
  obtain ⟨y, hy⟩ := (hres _).1 (congrFun (hinj i) k)
  exact ⟨y, by rw [hH i k, hy]; ring⟩

/-- The normalized form-product map reflects congruences: if the products of two families in
the factor cells agree modulo `m^L`, so do the families. -/
theorem form_product_congruence_reflects (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : Type) [Fintype ι] (d : ι → ℕ) (ν : ∀ i, Fin (d i + 1))
    (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O) (hgν : ∀ i, g i (ν i) = 1)
    (hc : FormsCoprime d g) (μ : Fin ((∑ i, d i) + 1)) (hμ : formProd d g μ = 1)
    (a a' : ∀ i, Fin (d i) → O)
    (ha : a ∈ Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i)))
    (ha' : a' ∈ Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i))) (L : ℕ)
    (hL : ∀ j, reducedFormProduct O d ν g μ a j - reducedFormProduct O d ν g μ a' j ∈
      (IsLocalRing.maximalIdeal O) ^ L) :
    ∀ i j, a i j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hres := residue_eq_zero_iff_dvd hϖ
  have ha₁ : ∀ i, a i ∈ reducedFormCell O (d i) (ν i) (g i) := fun i => ha i (Set.mem_univ _)
  have ha₁' : ∀ i, a' i ∈ reducedFormCell O (d i) (ν i) (g i) := fun i => ha' i (Set.mem_univ _)
  obtain ⟨-, hPres, hu, -⟩ := form_product_maps_to_and_preserves O ι d ν g μ hμ a a ha ha
  obtain ⟨-, -, hu', -⟩ := form_product_maps_to_and_preserves O ι d ν g μ hμ a' a' ha' ha'
  set A : ∀ i, Fin (d i + 1) → O := fun i => insertOne (ν i) (a i) with hA
  set A' : ∀ i, Fin (d i + 1) → O := fun i => insertOne (ν i) (a' i) with hA'
  set P := formProd d A
  set P' := formProd d A'
  have hAres : ∀ i k, IsLocalRing.residue O (A i k) = g i k := fun i k => congrFun (ha₁ i).2 k
  have hA'res : ∀ i k, IsLocalRing.residue O (A' i k) = g i k := fun i k => congrFun (ha₁' i).2 k
  have hPres : ∀ k, IsLocalRing.residue O (P k) = formProd d g k := fun k => congrFun hPres k
  have e1 : Ring.inverse (P μ) * P μ = 1 := Ring.inverse_mul_cancel _ hu
  have e2 : Ring.inverse (P' μ) * P' μ = 1 := Ring.inverse_mul_cancel _ hu'
  -- `hL`, cross-multiplied, in all coordinates
  have hM : ∀ k, ϖ ^ L ∣ P' μ * P k - P μ * P' k := by
    intro k
    have hN : ϖ ^ L ∣ Ring.inverse (P μ) * P k - Ring.inverse (P' μ) * P' k := by
      rcases Fin.eq_self_or_eq_succAbove μ k with rfl | ⟨j, rfl⟩
      · rw [e1, e2, sub_self]; exact dvd_zero _
      · have h := (mem_maximalIdeal_pow_iff hϖ _ _).1 (hL j)
        rwa [reducedFormProduct_of_mem O d ν g μ ha₁, reducedFormProduct_of_mem O d ν g μ ha₁'] at h
    convert dvd_mul_of_dvd_right hN (P μ * P' μ) using 1
    linear_combination (-(P' μ * P k)) * e1 + (P μ * P' k) * e2
  -- induction on the precision
  have claim : ∀ t, 1 ≤ t → t ≤ L → ∀ i k, ϖ ^ t ∣ A' i k - A i k := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro _ i k; rw [pow_one, ← hres, map_sub, hAres, hA'res, sub_self]
    | succ t ht IH =>
      intro htL
      choose H hH using IH (by omega)
      exact form_congruence_step hϖ d ν g hgν hc μ hμ A A' (fun i => (ha₁ i).1)
        (fun i => (ha₁' i).1) (fun i => (ha₁ i).2) hPres ht
        (fun k => (pow_dvd_pow ϖ htL).trans (hM k)) H hH
  intro i j
  rcases Nat.eq_zero_or_pos L with rfl | hL0
  · simp
  · rw [mem_maximalIdeal_pow_iff hϖ, ← dvd_neg, neg_sub]
    simpa [hA, hA', insertOne] using claim L hL0 le_rfl i ((ν i).succAbove j)

/-- Digit lifting for the normalized form-product map: an approximate preimage modulo `m^t` can
be corrected by `m^t` to an approximate preimage modulo `m^(t+1)`. -/
private theorem form_product_digit_lift (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    (ι : Type) [Fintype ι] (d : ι → ℕ) (ν : ∀ i, Fin (d i + 1))
    (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O) (hgν : ∀ i, g i (ν i) = 1)
    (hc : FormsCoprime d g) (μ : Fin ((∑ i, d i) + 1)) (hμ : formProd d g μ = 1)
    (a : ∀ i, Fin (d i) → O)
    (ha : a ∈ Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i)))
    (c : Fin (∑ i, d i) → O) (hcD : c ∈ reducedFormCell O (∑ i, d i) μ (formProd d g)) (t : ℕ)
    (ht : 1 ≤ t)
    (hct : ∀ j, reducedFormProduct O d ν g μ a j - c j ∈ (IsLocalRing.maximalIdeal O) ^ t) :
    ∃ a' ∈ Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i)),
      (∀ i j, a' i j - a i j ∈ (IsLocalRing.maximalIdeal O) ^ t) ∧ ∀ j,
      reducedFormProduct O d ν g μ a' j - c j ∈ (IsLocalRing.maximalIdeal O) ^ (t+1) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hM := mem_maximalIdeal_pow_iff hπ
  have hres := residue_eq_zero_iff_dvd hπ
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have ha₁ : ∀ i, a i ∈ reducedFormCell O (d i) (ν i) (g i) := fun i => ha i (Set.mem_univ _)
  obtain ⟨-, hPres, hu, -⟩ := form_product_maps_to_and_preserves O ι d ν g μ hμ a a ha ha
  set A : ∀ i, Fin (d i + 1) → O := fun i => insertOne (ν i) (a i) with hAdef
  have hA1 : ∀ i, A i (ν i) = 1 := fun i => (ha₁ i).1
  have hAres : ∀ i, residueVector O (A i) = g i := fun i => (ha₁ i).2
  set P := formProd d A
  set v := Ring.inverse (P μ)
  have hvu : v * P μ = 1 := Ring.inverse_mul_cancel _ hu
  have hu1 : π ∣ P μ - 1 := by
    rw [← hres, map_sub, map_one, sub_eq_zero, ← hμ]
    exact congrFun hPres μ
  set ct := insertOne μ c
  have hct1 : ct μ = 1 := hcD.1
  -- the defect `ct - v P`, in units of `π^t`
  have hdiff : ∀ k, π ^ (s+1) ∣ ct k - v * P k := by
    intro k
    rcases Fin.eq_self_or_eq_succAbove μ k with rfl | ⟨j, rfl⟩
    · rw [hct1, hvu, sub_self]; exact dvd_zero _
    · have h := (hM _ _).1 (hct j)
      rw [reducedFormProduct_of_mem O d ν g μ ha₁, ← dvd_neg, neg_sub] at h
      rwa [show ct (μ.succAbove j) = c j by simp [ct, insertOne]]
  choose w hw using hdiff
  -- solve the linearized equation over the residue field and lift the solution
  obtain ⟨hb, c₀, hbν, hbeq⟩ := forms_linear_bijective (IsLocalRing.ResidueField O) ι d g
    (fun i h => by simpa [h] using hgν i) hc ν (fun i => by simp [hgν]) (residueVector O w)
  choose H₀ hH₀ using fun i k => IsLocalRing.residue_surjective (hb i k)
  set H : ∀ i, Fin (d i + 1) → O := fun i k => H₀ i k - H₀ i (ν i)
  have hHres : ∀ i, residueVector O (H i) = hb i := fun i => funext fun k => by
    simp [residueVector, H, hH₀, hbν]
  obtain ⟨c₀', hc₀'⟩ := IsLocalRing.residue_surjective c₀
  set A' : ∀ i, Fin (d i + 1) → O := fun i => A i + π ^ (s+1) • H i
  set a' : ∀ i, Fin (d i) → O := fun i => dropCoord (ν i) (A' i)
  have hA'1 : ∀ i, A' i (ν i) = 1 := fun i => by simp [A', H, hA1]
  have hins : ∀ i, insertOne (ν i) (a' i) = A' i := fun i => by
    simp only [a', insertOne, dropCoord]
    rw [← hA'1 i, Fin.insertNth_self_removeNth]
  have ha'cell : ∀ i, a' i ∈ reducedFormCell O (d i) (ν i) (g i) := fun i => by
    change insertOne (ν i) (a' i) ∈ normalizedFormCell O (d i) (ν i) (g i)
    rw [hins, ← hAres i]
    refine ⟨hA'1 i, funext fun k => ?_⟩
    simp [residueVector, A', (hres π).2 dvd_rfl]
  refine ⟨a', fun i _ => ha'cell i, fun i j => ?_, fun j => ?_⟩
  · rw [hM]
    simp [a', A', A, dropCoord, insertOne, Fin.removeNth_apply]
  -- main congruence: `P' ≡ λ ct` modulo `π^(t+1)`
  obtain ⟨-, -, hu', -⟩ := form_product_maps_to_and_preserves O ι d ν g μ hμ a' a'
    (fun i _ => ha'cell i) (fun i _ => ha'cell i)
  set S := ∑ i, formPoly (H i) * ∏ j ∈ Finset.univ.erase i, formPoly (A j)
  have hR : Polynomial.C π ∣ S + Polynomial.C c₀' * ∏ i, formPoly (A i) - formPoly w := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro m
    rw [← hres, ← Polynomial.coeff_map]
    convert Polynomial.coeff_zero m
    simp only [S, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_prod, formPoly_map_residue, hAres, hHres, Polynomial.map_C, hc₀']
    rw [sub_eq_zero, hbeq]
  set lam := P μ - π ^ (s+1) * c₀'
  have hkey : ∀ k, π ^ (s+2) ∣ formProd d A' k - lam * ct k := by
    intro k
    obtain ⟨f, hf⟩ := formProd_add_smul_dvd (π ^ (s+1)) A H k
    obtain ⟨r, hr⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 hR k
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      formPoly_coeff_eq, show (∏ i, formPoly (A i)).coeff k = P k from rfl] at hr
    obtain ⟨e, he⟩ := hu1
    refine ⟨π ^ s * f + r - e * w k - c₀' * P k * v * e + π ^ s * c₀' * w k, ?_⟩
    linear_combination hf + π ^ (s+1) * hr - lam * hw k -
      (π ^ (s+1) * w k + π ^ (s+1) * c₀' * P k * v) * he + (π ^ (s+1) * c₀' * P k - P k) * hvu
  have hv' := Ring.inverse_mul_cancel _ hu'
  rw [hM, reducedFormProduct_of_mem O d ν g μ ha'cell]
  have hf : (fun i => insertOne (ν i) (a' i)) = A' := funext hins
  rw [hf] at hv' ⊢
  obtain ⟨x, hx⟩ := hkey (μ.succAbove j)
  obtain ⟨y, hy⟩ : π ^ (s+2) ∣ formProd d A' μ - lam := by simpa [hct1] using hkey μ
  rw [show c j = ct (μ.succAbove j) by simp [ct, insertOne]]
  refine ⟨Ring.inverse (formProd d A' μ) * (x - y * ct (μ.succAbove j)), ?_⟩
  linear_combination ct (μ.succAbove j) * hv' + Ring.inverse (formProd d A' μ) * hx -
    Ring.inverse (formProd d A' μ) * ct (μ.succAbove j) * hy

/-- Membership in a reduced factor cell, coordinatewise. -/
private theorem reducedFormCell_iff (O : Type) [CommRing O] [IsLocalRing O] (d : ℕ)
    (ν : Fin (d + 1))
    (g : Fin (d + 1) → IsLocalRing.ResidueField O) (hgν : g ν = 1) (b : Fin d → O) :
    b ∈ reducedFormCell O d ν g ↔ ∀ j, IsLocalRing.residue O (b j) = g (ν.succAbove j) := by
  simp only [reducedFormCell, normalizedFormCell, Set.mem_ofPred_eq, insertOne,
    Fin.insertNth_apply_same, true_and, residueVector, funext_iff]
  rw [Fin.forall_iff_succAbove ν]
  simp [hgν]

private theorem sub_mem_maximalIdeal_iff (O : Type) [CommRing O] [IsLocalRing O] (x y : O) :
    x - y ∈ IsLocalRing.maximalIdeal O ↔ IsLocalRing.residue O x = IsLocalRing.residue O y :=
  (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal O)).symm

private theorem eq_zero_of_forall_mem_pow (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (x : O) (h : ∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal O) ^ n) : x = 0 :=
  IsHausdorff.haus (I := IsLocalRing.maximalIdeal O) IsAdicComplete.toIsHausdorff _ fun n => by
    simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using h n

/-- Over a complete DVR, the normalized form-product map is a bijection from the product of the
factor cells onto the product cell. -/
theorem form_product_bijection (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ι : Type) [Fintype ι] (d : ι → ℕ)
    (ν : ∀ i, Fin (d i + 1)) (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (hgν : ∀ i, g i (ν i) = 1) (hc : FormsCoprime d g) (μ : Fin ((∑ i, d i) + 1))
    (hμ : formProd d g μ = 1) :
    Set.BijOn (reducedFormProduct O d ν g μ)
      (Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i)))
      (reducedFormCell O (∑ i, d i) μ (formProd d g)) := by
  set m := IsLocalRing.maximalIdeal O
  set S := Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i))
  refine ⟨?_, ?_, ?_⟩
  · exact fun a ha => (form_product_maps_to_and_preserves O ι d ν g μ hμ a a ha ha).1
  · intro a ha a' ha' h
    funext i j
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_mem_pow O
    intro L
    refine form_product_congruence_reflects O ι d ν g hgν hc μ hμ a a' ha ha' L ?_ i j
    intro j; simp [h]
  · intro c hc'
    have hcell := fun i => reducedFormCell_iff O (d i) (ν i) (g i) (hgν i)
    have hGcell := reducedFormCell_iff O (∑ i, d i) μ (formProd d g) hμ
    -- base point
    have a₁ : ∃ a, a ∈ S := by
      refine ⟨fun i j => (IsLocalRing.residue_surjective (g i ((ν i).succAbove j))).choose, ?_⟩
      intro i _
      rw [hcell]
      intro j
      exact (IsLocalRing.residue_surjective _).choose_spec
    obtain ⟨a₁, ha₁⟩ := a₁
    let P : ℕ → (∀ i, Fin (d i) → O) → Prop := fun t a =>
      a ∈ S ∧ ∀ j, reducedFormProduct O d ν g μ a j - c j ∈ m ^ (t + 1)
    have hP0 : P 0 a₁ := by
      refine ⟨ha₁, fun j => ?_⟩
      rw [zero_add, pow_one, sub_mem_maximalIdeal_iff]
      have h1 := (hGcell _).1
        (form_product_maps_to_and_preserves O ι d ν g μ hμ a₁ a₁ ha₁ ha₁).1 j
      rw [h1, (hGcell c).1 hc' j]
    have step : ∀ t a, P t a → ∃ a', P (t+1) a' ∧ ∀ i j, a' i j - a i j ∈ m ^ (t + 1) := by
      intro t a ha
      obtain ⟨a', ha', h1, h2⟩ := form_product_digit_lift O ι d ν g hgν hc μ hμ a ha.1 c hc'
        (t+1) (by omega) ha.2
      exact ⟨a', ⟨ha', h2⟩, h1⟩
    let f : (t : ℕ) → {a // P t a} := fun t => Nat.rec (motive := fun t => {a // P t a})
      ⟨a₁, hP0⟩ (fun t x => ⟨(step t x.1 x.2).choose, (step t x.1 x.2).choose_spec.1⟩) t
    have hf : ∀ t i j, (f (t+1)).1 i j - (f t).1 i j ∈ m ^ (t + 1) := fun t =>
      (step t (f t).1 (f t).2).choose_spec.2
    have hcompat : ∀ s t, s ≤ t → ∀ i j, (f s).1 i j - (f t).1 i j ∈ m ^ (s + 1) := by
      intro s t hst i j
      induction t, hst using Nat.le_induction with
      | base => simp
      | succ t hst ih =>
        simpa only [sub_sub_sub_cancel_right] using
          sub_mem ih (Ideal.pow_le_pow_right (I := m) (by omega : s + 1 ≤ t + 1) (hf t i j))
    have hlim : ∀ i j, ∃ ℓ : O, ∀ n, (f n).1 i j - ℓ ∈ m ^ n := by
      intro i j
      obtain ⟨ℓ, hℓ⟩ := IsPrecomplete.prec (I := m) (IsAdicComplete.toIsPrecomplete)
        (f := fun n => (f n).1 i j) (by
          intro s t hst
          rw [SModEq.sub_mem]
          simpa [smul_eq_mul, Ideal.mul_top] using
            Ideal.pow_le_pow_right (I := m) (by omega : s ≤ s + 1) (hcompat s t hst i j))
      refine ⟨ℓ, fun n => ?_⟩
      have := hℓ n
      rw [SModEq.sub_mem] at this
      simpa [smul_eq_mul, Ideal.mul_top] using this
    choose ℓ hℓ using hlim
    have haS : ℓ ∈ S := by
      intro i _
      rw [hcell]
      intro j
      have h0' : (f 0).1 i j - ℓ i j ∈ m := by
        rw [← sub_add_sub_cancel _ ((f 1).1 i j)]
        exact add_mem (by simpa using hcompat 0 1 (by omega) i j) (by simpa using hℓ i j 1)
      rw [sub_mem_maximalIdeal_iff] at h0'
      rw [← h0']
      exact (hcell i _).1 ((f 0).2.1 i (Set.mem_univ _)) j
    refine ⟨ℓ, haS, ?_⟩
    funext j
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_mem_pow O
    intro t
    have h1 := (form_product_maps_to_and_preserves O ι d ν g μ hμ ℓ (f t).1 haS
      (f t).2.1).2.2.2 t (fun i j => by
        have := hℓ i j t
        rw [← neg_sub]; exact neg_mem this) j
    have h2 := Ideal.pow_le_pow_right (I := m) (by omega : t ≤ t + 1) ((f t).2.2 j)
    simpa only [sub_add_sub_cancel] using add_mem h1 h2

/-- Hensel uniqueness modulo `m^L`: monic factors with pairwise coprime reductions whose products
agree modulo `m^L` agree factorwise modulo `m^L`. -/
theorem hensel_family_unique_mod_pow (O ι : Type) [CommRing O] [IsLocalRing O] [Fintype ι] (pi : O)
    (hpi : IsLocalRing.maximalIdeal O = Ideal.span {pi}) (hreg : ∀ x : O, pi * x = 0 → x = 0)
    (G G' : ι → Polynomial O) (hG : ∀ i, (G i).Monic) (hG' : ∀ i, (G' i).Monic)
    (hred : ∀ i, (G i).map (IsLocalRing.residue O) = (G' i).map (IsLocalRing.residue O))
    (hc : ∀ i j, i ≠ j → IsCoprime ((G i).map (IsLocalRing.residue O))
      ((G j).map (IsLocalRing.residue O))) (L : ℕ)
    (hp : ∀ j, (∏ i, G i).coeff j - (∏ i, G' i).coeff j ∈ (IsLocalRing.maximalIdeal O) ^ L) :
    ∀ i j, (G i).coeff j - (G' i).coeff j ∈ (IsLocalRing.maximalIdeal O) ^ L := by
  classical
  have hmpow : ∀ t x, x ∈ (IsLocalRing.maximalIdeal O) ^ t ↔ pi ^ t ∣ x := by
    intro t x; rw [hpi, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hmem : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O ↔ pi ∣ x := by
    intro x; rw [hpi, Ideal.mem_span_singleton]
  have hdeg : ∀ i, (G' i).natDegree = (G i).natDegree := by
    intro i
    rw [← (hG i).natDegree_map (IsLocalRing.residue O),
      ← (hG' i).natDegree_map (IsLocalRing.residue O), hred i]
  -- induction on the precision
  have key : ∀ t, t ≤ L → ∀ i j, pi ^ t ∣ (G' i).coeff j - (G i).coeff j := by
    intro t
    induction t with
    | zero => intro _ i j; simp
    | succ t ih =>
      intro htL
      have ih := ih (by omega)
      rcases t with _ | s
      · intro i j
        rw [zero_add, pow_one, ← hmem, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
        simpa [Polynomial.coeff_map] using congrArg (Polynomial.coeff · j) (hred i).symm
      choose H hHeq hHdeg using fun i =>
        (monic_congruent_difference_factor O pi hreg (s + 1) _ (G i) (G' i) (hG i) (hG' i) rfl
          (hdeg i) (fun j => Ideal.mem_span_singleton.2 (ih i j))).1
      have hcancel := (monic_congruent_difference_factor O pi hreg (s + 1) 0 1 1
        Polynomial.monic_one Polynomial.monic_one Polynomial.natDegree_one
        Polynomial.natDegree_one (fun j => by simp)).2
      set S : Polynomial O := ∑ i, H i * ∏ j ∈ Finset.univ.erase i, G j with hS
      have hexp := product_first_order_expansion (Polynomial O) ι
        (Ideal.span {Polynomial.C (pi ^ (s + 1))}) G (fun i => Polynomial.C (pi ^ (s + 1)) * H i)
        (fun i => Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) Finset.univ
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hexp
      obtain ⟨R, hR⟩ := hexp
      have hprod : ∏ i, (G i + Polynomial.C (pi ^ (s + 1)) * H i) = ∏ i, G' i :=
        Finset.prod_congr rfl fun i _ => (sub_eq_iff_eq_add'.mp (hHeq i)).symm
      -- the first-order term vanishes modulo `pi`
      have hScoeff : ∀ j, pi ∣ S.coeff j := by
        intro j
        refine Ideal.mem_span_singleton.1 (hcancel _ (Ideal.mem_span_singleton.2 ?_))
        obtain ⟨r, hr⟩ := (pow_dvd_pow pi htL).trans ((hmpow _ _).1 (hp j))
        have hc := congrArg (Polynomial.coeff · j) hR
        simp only [hprod, mul_assoc, ← Finset.mul_sum, ← hS, Polynomial.coeff_sub,
          Polynomial.coeff_C_mul, ← map_pow] at hc
        exact ⟨-r - pi ^ s * R.coeff j, by linear_combination -hc - hr⟩
      have hzero := coprime_family_linear_injective (IsLocalRing.ResidueField O) ι
        (fun i => (G i).map (IsLocalRing.residue O)) (fun i => (hG i).map _) hc
        (fun i => (H i).map (IsLocalRing.residue O))
        (fun i => by rw [(hG i).natDegree_map]; exact Polynomial.degree_map_le.trans_lt (hHdeg i))
        (by
          have hSmap : S.map (IsLocalRing.residue O) = 0 := by
            ext j
            rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff, hmem]
            exact hScoeff j
          simpa only [hS, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_prod] using hSmap)
      intro i j
      obtain ⟨y, hy⟩ := (hmem ((H i).coeff j)).1 <| (IsLocalRing.residue_eq_zero_iff _).1 <| by
        rw [← Polynomial.coeff_map, hzero i, Polynomial.coeff_zero]
      exact ⟨y, by rw [← Polynomial.coeff_sub, hHeq i, Polynomial.coeff_C_mul, hy]; ring⟩
  intro i j
  rw [hmpow, ← neg_sub, dvd_neg]
  exact key L le_rfl i j

/-- Two monic polynomials of the same degree `n` agree in all coefficients of degree `≥ n`. -/
private theorem coeff_eq_of_monic_of_le {R : Type} [CommRing R] {n : ℕ} {P Q : Polynomial R}
    (hP : P.Monic) (hQ : Q.Monic) (hPn : P.natDegree = n) (hQn : Q.natDegree = n)
    {j : ℕ} (hj : n ≤ j) : P.coeff j = Q.coeff j := by
  rcases hj.eq_or_lt with rfl | hlt
  · have h1 := hP.coeff_natDegree
    have h2 := hQ.coeff_natDegree
    rw [hPn] at h1; rw [hQn] at h2; rw [h1, h2]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- For monic polynomials of the same degree `N`, coefficientwise congruence modulo `I` below
degree `N` is equivalent to congruence of all coefficients. -/
theorem monic_coeff_sub_mem_iff {O : Type} [CommRing O] (I : Ideal O) (N : ℕ)
    (P Q : Polynomial O) (hP : P.Monic) (hQ : Q.Monic) (hPd : P.natDegree = N)
    (hQd : Q.natDegree = N) :
    (∀ j : Fin N, P.coeff j - Q.coeff j ∈ I) ↔ ∀ j, P.coeff j - Q.coeff j ∈ I := by
  refine ⟨fun h j => if hj : j < N then h ⟨j, hj⟩ else ?_, fun h j => h j⟩
  rw [coeff_eq_of_monic_of_le hP hQ hPd hQd (not_lt.mp hj), sub_self]
  exact I.zero_mem

/-- For factor families in the residue cells of pairwise coprime monic `g i`, the factor products
are congruent modulo `m^L` iff the families are. -/
theorem factor_product_congruence_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : Type) [Fintype ι]
    (g : ι → Polynomial (IsLocalRing.ResidueField O))
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (L : ℕ) (a a' : ∀ i, Fin (g i).natDegree → O)
    (ha : a ∈ Set.pi Set.univ (fun i => residueCell O (g i).natDegree (g i)))
    (ha' : a' ∈ Set.pi Set.univ (fun i => residueCell O (g i).natDegree (g i))) :
    (∀ j, factorProduct (fun i => (g i).natDegree) a j - factorProduct
        (fun i => (g i).natDegree) a' j ∈ (IsLocalRing.maximalIdeal O) ^ L) ↔ ∀ i j,
      a i j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L := by
  set I := (IsLocalRing.maximalIdeal O) ^ L
  set G : ι → Polynomial O := fun i => monicPolyO (a i)
  set G' : ι → Polynomial O := fun i => monicPolyO (a' i)
  have R := fun i => monic_poly_reconstruct O (g i).natDegree (a i)
  have R' := fun i => monic_poly_reconstruct O (g i).natDegree (a' i)
  have hGm : ∀ i, (G i).Monic := fun i => (R i).1
  have hG'm : ∀ i, (G' i).Monic := fun i => (R' i).1
  have hPm : (∏ i, G i).Monic := Polynomial.monic_prod_of_monic _ _ (fun i _ => hGm i)
  have hP'm : (∏ i, G' i).Monic := Polynomial.monic_prod_of_monic _ _ (fun i _ => hG'm i)
  have hPd : (∏ i, G i).natDegree = ∑ i, (g i).natDegree := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => hGm i)]
    exact Finset.sum_congr rfl (fun i _ => (R i).2.1)
  have hP'd : (∏ i, G' i).natDegree = ∑ i, (g i).natDegree := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => hG'm i)]
    exact Finset.sum_congr rfl (fun i _ => (R' i).2.1)
  have hfac : (∀ j, factorProduct (fun i => (g i).natDegree) a j
      - factorProduct (fun i => (g i).natDegree) a' j ∈ I) ↔
      ∀ j, (∏ i, G i).coeff j - (∏ i, G' i).coeff j ∈ I :=
    monic_coeff_sub_mem_iff I _ _ _ hPm hP'm hPd hP'd
  have hcomp : ∀ i, (∀ j, a i j - a' i j ∈ I) ↔ ∀ j, (G i).coeff j - (G' i).coeff j ∈ I := by
    intro i
    rw [← monic_coeff_sub_mem_iff I _ _ _ (hGm i) (hG'm i) (R i).2.1 (R' i).2.1]
    refine forall_congr' fun j => ?_
    rw [(R i).2.2.1 j, (R' i).2.2.1 j]
  rw [hfac]
  constructor
  · intro hp i
    rw [hcomp i]
    obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hm : IsLocalRing.maximalIdeal O = Ideal.span {pi} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).1 hpi
    have hred : ∀ i, (G i).map (IsLocalRing.residue O) = (G' i).map (IsLocalRing.residue O) :=
      fun i => (ha i (Set.mem_univ _)).trans (ha' i (Set.mem_univ _)).symm
    have hcG : ∀ i j, i ≠ j → IsCoprime ((G i).map (IsLocalRing.residue O))
        ((G j).map (IsLocalRing.residue O)) := by
      intro i j hij
      have e1 : (G i).map (IsLocalRing.residue O) = g i := ha i (Set.mem_univ _)
      have e2 : (G j).map (IsLocalRing.residue O) = g j := ha j (Set.mem_univ _)
      rw [e1, e2]; exact hc i j hij
    exact hensel_family_unique_mod_pow O ι pi hm
      (fun x hx => (mul_eq_zero.1 hx).resolve_left hpi.ne_zero) G G' hGm hG'm hred hcG L hp i
  · intro h
    exact (polynomial_congruence_and_product O I).2 ι G G' (fun i => (hcomp i).1 (h i))

/-- The projective normalizer evaluates to `1 + q + ⋯ + q^n`, and
`(1 + ⋯ + q^n)(q − 1) = q^(n+1) − 1`. -/
theorem projective_normalizer_eval (q : ℚ) (n : ℕ) :
    (projectiveNormalizer n).eval q = ∑ i ∈ Finset.range (n+1), q ^ i ∧
      (∑ i ∈ Finset.range (n+1), q ^ i) * (q - 1) = q ^ (n+1) - 1 := by
  have hpow : ∀ (x : Expr) (m : ℕ), (x.pow m).eval q = (x.eval q) ^ m := by
    intro x m
    induction m with
    | zero => simp [Expr.pow, Expr.eval]
    | succ m ih => simp [Expr.pow, Expr.eval, ih, pow_succ]
  have hsum : ∀ xs : List Expr, (Expr.sum xs).eval q = (xs.map (Expr.eval q)).sum := by
    intro xs
    induction xs with
    | nil => simp [Expr.sum, Expr.eval]
    | cons x xs ih =>
      simp only [Expr.sum, List.foldr_cons, Expr.eval, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
  refine ⟨?_, geom_sum_mul q (n+1)⟩
  unfold projectiveNormalizer
  rw [hsum, List.map_map]
  have : (Expr.eval q ∘ fun i => Expr.pow Expr.var i) = fun i => q ^ i := by
    funext i; simp [hpow, Expr.eval]
  rw [this]
  simp [Finset.sum, Finset.range_val, Multiset.range]

/-- A residue cell is a congruence class modulo `m` around any of its points; it is nonempty iff
`G` is monic of degree `n`. -/
theorem residue_cell_cylinder (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (G : Polynomial (IsLocalRing.ResidueField O)) :
    (∀ a ∈ residueCell O n G, residueCell O n G =
        {b | ∀ i, b i - a i ∈ IsLocalRing.maximalIdeal O}) ∧
      (G.Monic → G.natDegree = n → (residueCell O n G).Nonempty) ∧
      ((residueCell O n G).Nonempty → G.Monic ∧ G.natDegree = n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    ext b
    have hcong := (polynomial_congruence_and_product O (IsLocalRing.maximalIdeal O)).1
      (monicPolyO b) (monicPolyO a)
    obtain ⟨hma, hna, hca, -⟩ := monic_poly_reconstruct O n a
    obtain ⟨hmb, hnb, hcb, -⟩ := monic_poly_reconstruct O n b
    simp only [residueCell, Set.mem_ofPred_eq] at ha ⊢
    rw [← ha]
    change _ ↔ _ at hcong
    refine hcong.trans ⟨fun h i => ?_, fun h j => ?_⟩
    · have := h i; rwa [hca, hcb] at this
    · by_cases hj : j < n
      · have := h ⟨j, hj⟩; rw [← hca ⟨j, hj⟩, ← hcb ⟨j, hj⟩] at this; exact this
      · rw [coeff_eq_of_monic_of_le hmb hma hnb hna (by omega), sub_self]
        exact Ideal.zero_mem _
  · intro hG hGn
    choose a ha using fun i : Fin n => IsLocalRing.residue_surjective (G.coeff i)
    refine ⟨a, ?_⟩
    obtain ⟨hma, hna, hca, -⟩ := monic_poly_reconstruct O n a
    change (monicPolyO a).map (IsLocalRing.residue O) = G
    ext j
    by_cases hj : j < n
    · rw [Polynomial.coeff_map]
      have := hca ⟨j, hj⟩
      simp only at this
      rw [this, ha]
    · exact coeff_eq_of_monic_of_le (hma.map _) hG ((hma.natDegree_map _).trans hna) hGn
        (by omega)
  · rintro ⟨a, ha⟩
    obtain ⟨hma, hna, -, -⟩ := monic_poly_reconstruct O n a
    simp only [residueCell, Set.mem_ofPred_eq] at ha
    subst ha
    exact ⟨hma.map _, (hma.natDegree_map _).trans hna⟩

/-- A nonempty residue cell is measurable of mass `q^(-n)`, and its normalized cell measure is a
probability measure. -/
theorem residue_cell_mass (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (G : Polynomial (IsLocalRing.ResidueField O)) (hG : G.Monic) (hGn : G.natDegree = n) :
    MeasurableSet (residueCell O n G) ∧ coefficientMeasure O n (residueCell O n G) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ n ∧ MeasureTheory.IsProbabilityMeasure
      (cellMeasure O n (residueCell O n G)) := by
  obtain ⟨hcyl, hne, -⟩ := SurfaceBlowup.residue_cell_cylinder O n G
  obtain ⟨a, ha⟩ := hne hG hGn
  have hS := hcyl a ha
  have hmeas : MeasurableSet (residueCell O n G) := by
    have e := SurfaceBlowup.finite_coordinate_borel_cylinders O (IsLocalRing.maximalIdeal O) htop n
    have h2 : @MeasurableSet _ (adicCylinderSpace (IsLocalRing.maximalIdeal O) (Fin n → O))
        (residueCell O n G) := by
      apply MeasurableSpace.measurableSet_generateFrom
      refine Or.inr ⟨1, a, ?_⟩
      rw [hS]
      ext b
      simp only [Set.mem_ofPred_eq]
      rw [SurfaceBlowup.finite_coordinate_adic_congruence]
      simp
    rwa [← e] at h2
  have hmass : coefficientMeasure O n (residueCell O n G)
      = (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ n := by
    rw [hS]
    have := SurfaceBlowup.coefficient_cylinder_mass O htop n 1 a
    simpa using this
  refine ⟨hmeas, hmass, ⟨?_⟩⟩
  have hq : (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞) ≠ 0 := by
    have : 0 < Nat.card (IsLocalRing.ResidueField O) := Nat.card_pos
    exact_mod_cast this.ne'
  have h0 : coefficientMeasure O n (residueCell O n G) ≠ 0 := by
    rw [hmass]; exact pow_ne_zero _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  have htop' : coefficientMeasure O n (residueCell O n G) ≠ ⊤ := by
    rw [hmass]; exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hq)
  unfold cellMeasure
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop']

/-- The product of the normalized factor-cell measures is a probability measure concentrated on the
product of the cells, giving mass `q^(-(∑ deg g i)(L-1))` to each congruence box modulo `m^L`. -/
theorem factor_cell_product_measure (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (ι : Type) [Fintype ι]
    (g : ι → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ i, (g i).Monic)
    [hσ : ∀ i, MeasureTheory.SigmaFinite
      (cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i)))] :
    MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.pi
        (fun i => cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i)))) ∧
      (MeasureTheory.Measure.pi
        (fun i => cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i))))
      (Set.pi Set.univ (fun i => residueCell O (g i).natDegree (g i)))ᶜ = 0 ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ a' ∈ Set.pi Set.univ (fun i => residueCell O (g i).natDegree (g i)),
      (MeasureTheory.Measure.pi
        (fun i => cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i))))
      (Set.pi Set.univ
        (fun i =>
          {b : Fin (g i).natDegree → O | ∀ j, b j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L})) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ ((∑ i, (g i).natDegree) * (L - 1)) := by
  have hM := fun i => residue_cell_mass O htop (g i).natDegree (g i) (hg i) rfl
  have : ∀ i, MeasureTheory.IsProbabilityMeasure
      (cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i))) := fun i => (hM i).2.2
  set q : ℝ≥0∞ := (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞) with hq
  have hq0 : q ≠ 0 := by
    rw [hq]; exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField O)).ne'
  have hqt : q ≠ ⊤ := by rw [hq]; exact ENNReal.natCast_ne_top _
  refine ⟨inferInstance, ?_, ?_⟩
  · have hmeas : MeasurableSet (Set.pi Set.univ (fun i => residueCell O (g i).natDegree (g i))) :=
      MeasurableSet.univ_pi (fun i => (hM i).1)
    rw [MeasureTheory.prob_compl_eq_zero_iff hmeas, MeasureTheory.Measure.pi_pi]
    refine Finset.prod_eq_one (fun i _ => ?_)
    have h1 := (hM i).1
    rw [← MeasureTheory.measure_univ
        (μ := cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i)))]
    unfold cellMeasure
    simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply' h1,
      Set.inter_self, Set.univ_inter]
  · intro L hL a' ha'
    rw [MeasureTheory.Measure.pi_pi]
    have key : ∀ i, cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i))
        {b : Fin (g i).natDegree → O | ∀ j, b j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L}
        = q⁻¹ ^ ((g i).natDegree * (L - 1)) := by
      intro i
      have h1 := (hM i).1
      have hsub :
          {b : Fin (g i).natDegree → O | ∀ j, b j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L}
          ⊆ residueCell O (g i).natDegree (g i) := by
        rw [(residue_cell_cylinder O (g i).natDegree (g i)).1 (a' i) (ha' i (Set.mem_univ _))]
        intro b hb j
        exact Ideal.pow_le_self (by omega) (hb j)
      unfold cellMeasure
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply' h1,
        Set.inter_eq_left.mpr hsub, (hM i).2.1, coefficient_cylinder_mass O htop, smul_eq_mul]
      have : (g i).natDegree * L = (g i).natDegree + (g i).natDegree * (L - 1) := by
        obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
        simp [Nat.mul_succ, Nat.add_comm]
      rw [this, pow_add, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
      · exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr hqt)
      · exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hq0)
    simp only [key]
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_mul]

/-- The residue extension `O_δ / m_O O_δ` is isomorphic to `k[X]/(Φ̄)`, compatibly with
reduction. -/
theorem residue_extension_equiv (O : Type) [CommRing O] [IsLocalRing O] (Φ : Polynomial O) :
    ∃ e : residueExtension O Φ ≃+* AdjoinRoot (residuePoly O Φ),
      (∀ p : Polynomial O, e (baseReduce O Φ (AdjoinRoot.mk Φ p)) = AdjoinRoot.mk (residuePoly O Φ)
        (p.map (IsLocalRing.residue O))) ∧
      (∀ c : O, e (baseReduce O Φ (algebraMap O (AdjoinRoot Φ) c)) = algebraMap
        (IsLocalRing.ResidueField O) (AdjoinRoot (residuePoly O Φ)) (IsLocalRing.residue O c)) := by
  have h1 : ∀ p : Polynomial O,
      (AdjoinRoot.quotEquivQuotMap Φ (IsLocalRing.maximalIdeal O)).toRingEquiv
      (baseReduce O Φ (AdjoinRoot.mk Φ p)) = AdjoinRoot.mk (residuePoly O Φ)
          (p.map (IsLocalRing.residue O)) :=
    fun p => AdjoinRoot.quotEquivQuotMap_apply_mk Φ p (IsLocalRing.maximalIdeal O)
  refine ⟨(AdjoinRoot.quotEquivQuotMap Φ (IsLocalRing.maximalIdeal O)).toRingEquiv, h1, fun c => ?_⟩
  have := h1 (Polynomial.C c)
  rwa [AdjoinRoot.mk_C, Polynomial.map_C, AdjoinRoot.mk_C] at this

/-- For an unramified lift `Φ`, the residue extension is a finite field with `q^(deg Φ)`
elements. -/
theorem residue_extension_field (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    IsField (residueExtension O Φ) ∧ Finite (residueExtension O Φ) ∧ Nat.card
      (residueExtension O Φ) = residueCard O ^ Φ.natDegree := by
  obtain ⟨e, -, -⟩ := SurfaceBlowup.residue_extension_equiv O Φ
  have : Fact (Irreducible (residuePoly O Φ)) := ⟨hΦ.2⟩
  have hm : (residuePoly O Φ).Monic := hΦ.1.map _
  have hdeg : (residuePoly O Φ).natDegree = Φ.natDegree := hΦ.1.natDegree_map _
  let pb := AdjoinRoot.powerBasis' hm
  let f : residueExtension O Φ ≃ (Fin (residuePoly O Φ).natDegree → IsLocalRing.ResidueField O) :=
    e.toEquiv.trans pb.basis.equivFun.toEquiv
  refine ⟨?_, Finite.of_equiv _ f.symm, ?_⟩
  · exact MulEquiv.isField (Field.toIsField _) e.toMulEquiv
  · rw [Nat.card_congr f, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin,
      hdeg]

open Polynomial in
/-- Translation `X ↦ X + θ` maps the block cell bijectively onto the `X^r` cell and preserves
congruences modulo powers of `m_O O_δ`. -/
theorem block_translation (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ) :
    Set.BijOn (translateBlock O Φ r) (blockCell O Φ r) (zeroCell O Φ r) ∧
      (∀ (L : ℕ) (b b' : Fin r → AdjoinRoot Φ), (∀ j, b j - b' j ∈ (baseIdeal O Φ) ^ L) ↔ ∀ j,
        translateBlock O Φ r b j - translateBlock O Φ r b' j ∈ (baseIdeal O Φ) ^ L) := by
  set A := AdjoinRoot Φ
  have : Nontrivial (residueExtension O Φ) := ⟨(residue_extension_field O Φ hΦ).1.exists_pair_ne⟩
  have : Nontrivial A := (baseReduce O Φ).domain_nontrivial
  set θ := AdjoinRoot.root Φ
  have R := fun (a : Fin r → A) => monic_poly_reconstruct A r a
  -- translated polynomial
  have hT : ∀ b : Fin r → A, monicPolyO (translateBlock O Φ r b) = taylor θ (monicPolyO b) := by
    intro b
    obtain ⟨h1, h2, -, -⟩ := R b
    exact (R b).2.2.2 _ (by rw [Monic, leadingCoeff_taylor]; exact h1)
        (by rw [natDegree_taylor, h2])
  -- coefficient congruence criterion
  have key : ∀ (J : Ideal A) (c c' : Fin r → A),
      (∀ j, c j - c' j ∈ J) ↔ monicPolyO c - monicPolyO c' ∈ J.map (C : A →+* A[X]) := by
    intro J c c'
    obtain ⟨m1, d1, e1, -⟩ := R c
    obtain ⟨m2, d2, e2, -⟩ := R c'
    rw [Ideal.mem_map_C_iff]
    constructor
    · intro h n
      rw [coeff_sub]
      by_cases hn : n < r
      · have := h ⟨n, hn⟩
        rwa [← e1 ⟨n, hn⟩, ← e2 ⟨n, hn⟩] at this
      · rw [coeff_eq_of_monic_of_le m1 m2 d1 d2 (not_lt.mp hn), sub_self]; exact J.zero_mem
    · intro h j
      have := h j
      rwa [coeff_sub, e1, e2] at this
  have tmem : ∀ (J : Ideal A) (s : A) (f : A[X]), f ∈ J.map (C : A →+* A[X]) →
      taylor s f ∈ J.map (C : A →+* A[X]) := by
    intro J s f hf
    have : ((taylorAlgHom s : A[X] →ₐ[A] A[X]) : A[X] →+* A[X]).comp C = C := by
      ext x
      · simp [taylor_C]
      · simp
    have h2 := Ideal.mem_map_of_mem ((taylorAlgHom s : A[X] →ₐ[A] A[X]) : A[X] →+* A[X]) hf
    rw [Ideal.map_map, this] at h2
    simpa using h2
  have hinv : ∀ f : A[X], taylor (-θ) (taylor θ f) = f := by
    intro f; rw [taylor_taylor, neg_add_cancel, taylor_zero]
  have hinv' : ∀ f : A[X], taylor θ (taylor (-θ) f) = f := by
    intro f; rw [taylor_taylor, add_neg_cancel, taylor_zero]
  have hcf : conjugateFactor O Φ 0 = X - C (baseReduce O Φ θ) := by
    simp [conjugateFactor, rootBar, θ]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro b hb
    change (monicPolyO _).map _ = _
    change (monicPolyO b).map _ = _ at hb
    rw [hT, map_taylor, hb, hcf, taylor_pow, sub_eq_add_neg, ← C_neg]
    simp [taylor_X, taylor_C]
  · intro b _ b' _ h
    have h1 : monicPolyO b = monicPolyO b' := by
      apply taylor_injective θ
      rw [← hT, ← hT, h]
    funext j
    rw [← (R b).2.2.1 j, ← (R b').2.2.1 j, h1]
  · intro c hc
    change (monicPolyO c).map _ = _ at hc
    set F := taylor (-θ) (monicPolyO c)
    obtain ⟨m1, d1, -, -⟩ := R c
    have hF := (R c).2.2.2 F (by rw [Monic, leadingCoeff_taylor]; exact m1)
      (by rw [natDegree_taylor, d1])
    have hF' : monicPolyO (coeffVec r F) = F := (R (coeffVec r F)).2.2.2 F
      (by rw [Monic, leadingCoeff_taylor]; exact m1) (by rw [natDegree_taylor, d1])
    refine ⟨coeffVec r F, ?_, ?_⟩
    · change (monicPolyO _).map _ = _
      rw [hF', map_taylor, hc, hcf, taylor_pow, sub_eq_add_neg, ← C_neg]
      simp [taylor_X]
    · have := hT (coeffVec r F)
      rw [hF', hinv'] at this
      funext j
      rw [← (R (translateBlock O Φ r (coeffVec r F))).2.2.1 j, this, (R c).2.2.1 j]
  · intro L b b'
    rw [key, key, hT, hT, ← map_sub]
    constructor
    · exact tmem _ θ _
    · intro h
      have := tmem _ (-θ) _ h
      rwa [hinv] at this

private theorem pow_natCard_eq_self (K : Type) [CommRing K] (hK : IsField K) [Finite K] (x : K) :
    x ^ Nat.card K = x := by
  let := hK.toField
  cases nonempty_fintype K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

private theorem natCard_le_of_pow_eq_self (K : Type) [CommRing K] (hK : IsField K) [Finite K]
    (n : ℕ) (hn : 1 < n)
    (hall : ∀ x : K, x ^ n = x) : Nat.card K ≤ n := by
  let := hK.toField
  cases nonempty_fintype K
  have hsub : (Finset.univ : Finset K).val ⊆
      (Polynomial.X ^ n - Polynomial.X : Polynomial K).roots := by
    intro x _
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hn)]
    simp [hall x]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hn, Finset.card_univ] at this
  rwa [Nat.card_eq_fintype_card]

private theorem monic_eq_prod_X_sub_C (K : Type) [CommRing K] (hK : IsField K) (p : Polynomial K)
    (hp : p.Monic) (d : ℕ)
    (hd : p.natDegree = d) (r : Fin d → K) (hr : Function.Injective r)
    (hroot : ∀ i, p.IsRoot (r i)) :
    p = ∏ i, (Polynomial.X - Polynomial.C (r i)) ∧ ∀ i j, i ≠ j → IsCoprime
      (Polynomial.X - Polynomial.C (r i)) (Polynomial.X - Polynomial.C (r j)) := by
  classical
  let := hK.toField
  refine ⟨?_, fun i j hij => Polynomial.pairwise_coprime_X_sub_C hr hij⟩
  set s := Finset.univ.image r
  have hs : s.card = d := by
    rw [Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_fin]
  have hle : s.val ≤ p.roots := by
    rw [Multiset.le_iff_subset s.nodup]
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_val.mp hx)
    exact (Polynomial.mem_roots hp.ne_zero).2 (hroot i)
  have heq : s.val = p.roots :=
    Multiset.eq_of_le_of_card_le hle
        (by rw [Finset.card_val, hs, ← hd]; exact Polynomial.card_roots' p)
  have hcard : Multiset.card p.roots = p.natDegree := by
    rw [← heq, Finset.card_val, hs, hd]
  rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hcard, ← heq]
  rw [← Finset.prod_eq_multiset_prod, Finset.prod_image (fun a _ b _ h => hr h)]


/-- The residue roots `θ̄^(q^i)`, `i < deg Φ`, are pairwise distinct roots of `Φ̄` in `k_δ`, so `Φ̄`
splits there as the product of the pairwise coprime conjugate factors. -/
theorem conjugate_roots_distinct (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    (∀ c : O, residueEmbed O Φ (IsLocalRing.residue O c) = baseReduce O Φ
        (algebraMap O (AdjoinRoot Φ) c)) ∧ Function.Injective (residueEmbed O Φ) ∧
      (∀ i : ℕ, ((residuePoly O Φ).map (residueEmbed O Φ)).IsRoot (rootBar O Φ ^ residueCard O ^ i))
      ∧ (∀ i j : ℕ, i < Φ.natDegree → j < Φ.natDegree → rootBar O Φ ^ residueCard O ^ i =
        rootBar O Φ ^ residueCard O ^ j → i = j) ∧ (residuePoly O Φ).map (residueEmbed O Φ) = ∏ i :
      Fin Φ.natDegree, conjugateFactor O Φ i ∧
      (∀ i j : Fin Φ.natDegree, i ≠ j → IsCoprime (conjugateFactor O Φ i) (conjugateFactor O Φ j))
      := by
  obtain ⟨hKf, hKfin, hKcard⟩ := residue_extension_field O Φ hΦ
  set K := residueExtension O Φ
  set q := residueCard O
  set δ := Φ.natDegree
  set ρ := residueEmbed O Φ
  set θ := rootBar O Φ
  -- compatibility
  have hcomp : ∀ c : O, ρ (IsLocalRing.residue O c) = baseReduce O Φ
      (algebraMap O (AdjoinRoot Φ) c) :=
    fun c => rfl
  have hcompR : ρ.comp (IsLocalRing.residue O) = (baseReduce O Φ).comp (AdjoinRoot.of Φ) :=
    RingHom.ext hcomp
  -- iterated Frobenius
  have hiter : ∀ (P : Polynomial (IsLocalRing.ResidueField O)) (y : K) (n : ℕ),
      P.eval₂ ρ (y ^ q ^ n) = (P.eval₂ ρ y) ^ q ^ n := by
    intro P y n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_mul, pow_mul, eval_at_pow_card, ih]
  -- every element is a polynomial expression in θ
  have hsurj : ∀ x : K, ∃ P : Polynomial (IsLocalRing.ResidueField O), x = P.eval₂ ρ θ := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction a using AdjoinRoot.induction_on with
    | ih p =>
      refine ⟨p.map (IsLocalRing.residue O), ?_⟩
      rw [Polynomial.eval₂_map, hcompR, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def,
        Polynomial.hom_eval₂]
      rfl
  have hq : 1 < q := Finite.one_lt_card
  have hroot : ∀ i : ℕ, ((residuePoly O Φ).map ρ).IsRoot (θ ^ q ^ i) := by
    intro i
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, hiter]
    have : (residuePoly O Φ).eval₂ ρ θ = 0 := by
      rw [Polynomial.eval₂_map, hcompR, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
    rw [this, zero_pow (pow_ne_zero _ (by omega))]
  have hθδ : θ ^ q ^ δ = θ := by rw [← hKcard]; exact pow_natCard_eq_self K hKf θ
  have hdist : ∀ i j : ℕ, i < δ → j < δ → θ ^ q ^ i = θ ^ q ^ j → i = j := by
    have key : ∀ i j : ℕ, i < j → j < δ → θ ^ q ^ i = θ ^ q ^ j → False := by
      intro i j hij hj h
      set m := i + (δ - j) with hm
      have h1 : θ ^ q ^ m = θ := by
        have := congrArg (· ^ q ^ (δ - j)) h
        simp only [← pow_mul, ← pow_add] at this
        rw [hm, this, show j + (δ - j) = δ by omega, hθδ]
      have hall : ∀ x : K, x ^ q ^ m = x := by
        intro x
        obtain ⟨P, rfl⟩ := hsurj x
        rw [← hiter, h1]
      have hm1 : 1 < q ^ m := Nat.one_lt_pow (by omega) hq
      have := natCard_le_of_pow_eq_self K hKf _ hm1 hall
      rw [hKcard] at this
      have := (Nat.pow_le_pow_iff_right hq).1 this
      omega
    intro i j hi hj h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hij | hij
    exacts [key i j hij hj h, key j i hij hi h.symm]
  have hnt : Nontrivial K := ⟨hKf.exists_pair_ne⟩
  have hmon : ((residuePoly O Φ).map ρ).Monic := (hΦ.1.map _).map _
  have hdeg : ((residuePoly O Φ).map ρ).natDegree = δ := by
    rw [(hΦ.1.map _).natDegree_map, hΦ.1.natDegree_map]
  have hinj : Function.Injective (fun i : Fin δ => θ ^ q ^ (i : ℕ)) :=
    fun i j h => Fin.ext (hdist i j i.2 j.2 h)
  obtain ⟨hfac, hcop⟩ := monic_eq_prod_X_sub_C K hKf _ hmon δ hdeg _ hinj (fun i => hroot i)
  exact ⟨hcomp, ρ.injective, hroot, hdist, hfac, hcop⟩

/-- Each fiber of the residue map on `O^(n+1)` is measurable of mass `q^(-(n+1))`. -/
theorem residue_vector_fiber_mass (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (w : Fin (n + 1) → IsLocalRing.ResidueField O) :
    MeasurableSet {a : Fin (n+1) → O | residueVector O a = w} ∧ coefficientMeasure O (n+1)
      {a : Fin (n+1) → O | residueVector O a = w} =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (n+1) := by
  choose a₀ ha₀ using fun i => IsLocalRing.residue_surjective (w i)
  have hset : {a : Fin (n+1) → O | residueVector O a = w}
      = {b | ∀ i, b i - a₀ i ∈ (IsLocalRing.maximalIdeal O) ^ 1} := by
    ext a
    simp only [Set.mem_ofPred_eq, pow_one, residueVector, funext_iff, ← ha₀]
    refine forall_congr' fun i => ?_
    exact Ideal.Quotient.eq
  refine ⟨?_, ?_⟩
  · have hm := finite_coordinate_borel_cylinders O (IsLocalRing.maximalIdeal O) htop (n+1)
    change @MeasurableSet _ (inferInstance : MeasurableSpace (Fin (n+1) → O)) _
    rw [hm, hset]
    apply MeasurableSpace.measurableSet_generateFrom
    right
    refine ⟨1, a₀, ?_⟩
    ext b
    exact (finite_coordinate_adic_congruence O (n+1) _ 1 b a₀).symm
  · rw [hset, coefficient_cylinder_mass O htop (n+1) 1 a₀, mul_one]

/-- The nonzero scalar multiples of a nonzero vector over a finite field `k` form a finite set of
`|k| − 1` nonzero vectors. -/
theorem scalar_class_card (k : Type) [Field k] [Finite k] (n : ℕ) (v : Fin (n + 1) → k)
    (hv : v ≠ 0) :
    Nat.card (scalarClass v) = Nat.card k - 1 ∧ (∀ w ∈ scalarClass v, w ≠ 0) ∧
      (scalarClass v).Finite := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  refine ⟨?_, ?_, Set.toFinite _⟩
  · let f : {c : k // c ≠ 0} → scalarClass v := fun c => ⟨c.1 • v, c.1, c.2, rfl⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b h
        have h2 := congrFun (congrArg Subtype.val h) i
        simp only [f, Pi.smul_apply, smul_eq_mul] at h2
        exact Subtype.ext (mul_right_cancel₀ hi h2)
      · rintro ⟨w, c, hc, rfl⟩
        exact ⟨⟨c, hc⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf)]
    have := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  · rintro w ⟨c, hc, rfl⟩ h
    exact hv ((smul_eq_zero.mp h).resolve_left hc)

end SurfaceBlowup
