/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Assembly.NullBridges
import SurfaceBlowup.Unramified.HomogeneousCells

/-!
# Type events and divisor counts

Type events of polynomials over a complete DVR `O` with finite residue field and the combinatorics
of exceptional divisors used to assemble the cell laws: unit scaling and the binary decomposition of
type events, type descent along unramified blocks, the array of a divisor and divisor counts, and
the law of a product of reduced forms.

## Main results

* `affine_type_event_unit_scaling`, `binary_type_event_decomposition`: elementary properties of
  type events.
* `descended_block_type_iff`: types of polynomials in a block cell.
* `divisor_array_exists_unique`, `divisor_count_of_point_set`,
  `divisor_count_eval_of_point_count`, `affine_divisor_count`: arrays and divisor counts.
* `monic_polynomial_divisor`: monic polynomials correspond to affine divisors.
* `form_product_type_event_law`: the law of a product of reduced forms.

Provenance: `Thm_SurfaceBlowupV2_{affine_type_event_unit_scaling, array_enumeration,
binary_type_event_decomposition, descended_block_type_iff, divisor_array_exists_unique,
divisor_count_of_point_set, affine_divisor_count, divisor_vector_properties, form_product_type_iff,
form_product_type_event_sets, form_product_type_event_law, monic_polynomial_divisor}`.
-/

namespace SurfaceBlowup

open scoped BigOperators ENNReal

private theorem directionDegree_mul_le_exceptionalDegree (k : Type) [Field k]
    (D : ExceptionalDivisor k) (Q : ClosedDirection k) :
    directionDegree k Q * D Q ≤ exceptionalDegree k D := by
  by_cases hQ : D Q = 0
  · simp [hQ]
  · exact Finset.single_le_sum (f := fun Q => directionDegree k Q * D Q) (by intros; positivity)
      (Finsupp.mem_support_iff.mpr hQ)

/-! ### Affine and binary type events -/

/-- Affine type events are invariant under scaling by units; in particular, normalising a point of
a projective residue cell at a coordinate `μ` with `G μ = 1` does not change its type. -/
theorem affine_type_event_unit_scaling (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (n : ℕ)
    (σ : FactorType) :
    (∀ (a : Fin (n+1) → O) (u : O), IsUnit u → (u • a ∈ affineTypeEvent O n σ ↔ a ∈ affineTypeEvent
      O n σ)) ∧ ∀ (G : Fin (n+1) → IsLocalRing.ResidueField O) (μ : Fin (n+1)), G μ = 1 → ∀ a ∈
      projectiveCell O n G, (insertOne μ (projectiveNormalize O n G μ a) ∈ affineTypeEvent O n σ ↔
      a ∈ affineTypeEvent O n σ) := by
  have key : ∀ (a : Fin (n+1) → O) (u : O), IsUnit u →
      (u • a ∈ affineTypeEvent O n σ ↔ a ∈ affineTypeEvent O n σ) := by
    intro a u hu
    have hu0 : u ≠ 0 := hu.ne_zero
    have hι : algebraMap O (BaseField O) u ≠ 0 := by
      intro h
      exact hu0 (IsFractionRing.injective O (BaseField O) (by simpa using h))
    have hP : affinePolynomial O (u • a) = Polynomial.C (algebraMap O (BaseField O) u) *
        affinePolynomial O a := by
      unfold affinePolynomial
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    have hlast : (u • a) (Fin.last n) ≠ 0 ↔ a (Fin.last n) ≠ 0 := by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Ne, Ne, mul_eq_zero]; simp [hu0]
    have hn : Polynomial.C (algebraMap O (BaseField O) ((u • a) (Fin.last n)))⁻¹ *
          affinePolynomial O (u • a) =
        Polynomial.C (algebraMap O (BaseField O) (a (Fin.last n)))⁻¹ * affinePolynomial O a := by
      rw [hP]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_inv]
      rw [← mul_assoc, mul_assoc (Polynomial.C (algebraMap O (BaseField O) u)⁻¹),
        mul_comm (Polynomial.C (algebraMap O (BaseField O) (a (Fin.last n)))⁻¹),
        ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hι]
      simp [mul_comm]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨hlast.1 h1, by rwa [hn] at h2⟩, fun ⟨h1, h2⟩ ↦ ⟨hlast.2 h1, by rwa [hn]⟩⟩
  refine ⟨key, fun G μ hG a ha ↦ ?_⟩
  have ⟨_, c, hc, hres⟩ := ha
  have hres' : IsLocalRing.residue O (a μ) = c := by simpa [residueVector, hG] using congrFun hres μ
  have hunit : IsUnit (a μ) := by
    by_contra hnu
    exact hc (hres'.symm.trans ((IsLocalRing.residue_eq_zero_iff _).2
      ((IsLocalRing.mem_maximalIdeal _).2 hnu)))
  have hpn : projectiveNormalize O n G μ a = dropCoord μ (normalizeAt μ a) := by
    unfold projectiveNormalize; rw [if_pos ha]
  have hins : insertOne μ (projectiveNormalize O n G μ a) = normalizeAt μ a := by
    rw [hpn]
    unfold insertOne dropCoord
    have h1 : normalizeAt μ a μ = 1 := by
      simp only [normalizeAt, Pi.smul_apply, smul_eq_mul]
      exact Ring.inverse_mul_cancel _ hunit
    rw [← h1]
    exact Fin.insertNth_self_removeNth μ _
  rw [hins]
  unfold normalizeAt
  apply key a
  obtain ⟨v, hv⟩ := hunit
  rw [← hv, Ring.inverse_unit]
  exact Units.isUnit _

/-- If the divisor `D` of degree `n` has array `m`, the non-root children of the pattern `m` are
enumerated by the support of `D`, the child at `Q` being `(deg Q, single 1 (D Q))`. -/
theorem array_enumeration (k : Type) [Field k] (n : ℕ) (D : ExceptionalDivisor k)
    (hD : exceptionalDegree k D = n) (m : Pattern n) (hm : HasArray k n D m) :
    ∃ e : Fin (otherChildren 1 m).length ≃ D.support, ∀ j, (otherChildren 1 m).get j =
      (directionDegree k (e j), State.single 1 (D (e j))) := by
  set Ls := otherChildren 1 m with hLs
  let ℓ₁ : Fin Ls.length → ℕ × State := fun j => Ls.get j
  let ℓ₂ : D.support → ℕ × State := fun Q => (directionDegree k Q, State.single 1 (D Q))
  have hdeg := directionDegree_pos k
  have hle : ∀ Q ∈ D.support, directionDegree k Q * D Q ≤ n := fun Q _ ↦ hD ▸
      directionDegree_mul_le_exceptionalDegree k D Q
  have hcard : ∀ x, Fintype.card {j // ℓ₁ j = x} = Fintype.card {Q // ℓ₂ Q = x} := by
    intro x
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have h1 : Nat.card {j // ℓ₁ j = x} = Ls.count x := by
      convert list_get_fiber_card _ Ls x using 2
      exact lawful_beq_subsingleton _ _
    rw [h1]
    by_cases hx : ∃ δ r, x = (δ, State.single 1 r)
    · obtain ⟨δ, r, rfl⟩ := hx
      rw [(other_children_count n m δ r).1]
      have hR : Nat.card {Q // ℓ₂ Q = (δ, State.single 1 r)} =
          Nat.card {Q : ClosedDirection k // directionDegree k Q = δ ∧ D Q = r ∧ 0 < r} := by
        apply Nat.card_congr
        exact
          { toFun := fun Q => ⟨Q.1.1, by
              have h := Q.2
              simp only [ℓ₂, Prod.mk.injEq, State.single.injEq, true_and] at h
              have hs := Finsupp.mem_support_iff.mp Q.1.2
              exact ⟨h.1, h.2, by omega⟩⟩
            invFun := fun Q => ⟨⟨Q.1, Finsupp.mem_support_iff.mpr (by omega)⟩, by
              simp only [ℓ₂, Prod.mk.injEq, State.single.injEq, true_and]
              exact ⟨Q.2.1, Q.2.2.1⟩⟩
            left_inv := fun Q => rfl
            right_inv := fun Q => rfl }
      rw [hR]
      split_ifs with h
      · rw [← hm (⟨δ - 1, by omega⟩, ⟨r - 1, by omega⟩)]
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro Q
        simp only
        omega
      · symm; rw [Nat.card_eq_zero]
        left
        refine ⟨fun ⟨Q, hQ1, hQ2, hQ3⟩ => h ?_⟩
        have h1 := hdeg Q
        have hQs : Q ∈ D.support := Finsupp.mem_support_iff.mpr (by omega)
        have h2 := hle Q hQs
        rw [hQ1] at h1; rw [hQ1, hQ2] at h2
        refine ⟨h1, ?_, hQ3, ?_⟩
        · nlinarith
        · nlinarith
    · have hL : Ls.count x = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        obtain ⟨ij, hij⟩ := (other_children_count n m 0 0).2.1 x hmem
        exact hx ⟨_, _, hij⟩
      rw [hL]
      symm
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun ⟨Q, hQ⟩ => hx ⟨_, _, hQ.symm⟩⟩
  refine ⟨(Equiv.sigmaFiberEquiv ℓ₁).symm.trans
    ((Equiv.sigmaCongrRight fun x => Fintype.equivOfCardEq (hcard x)).trans
      (Equiv.sigmaFiberEquiv ℓ₂)), fun j => ?_⟩
  have := ((Fintype.equivOfCardEq (hcard (ℓ₁ j))) ⟨j, rfl⟩).2
  exact this.symm

section

open Polynomial

private lemma affinePolynomial_coeff (O : Type) [CommRing O] [IsDomain O] {n : ℕ}
    (a : Fin (n + 1) → O) (k : ℕ) :
    (affinePolynomial O a).coeff k = if h : k < n+1 then algebraMap O (BaseField O)
      (a ⟨k,h⟩) else 0 := by
  unfold affinePolynomial
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k,h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; · simp
      intro e; apply hb; ext; simp [e]
    · simp
  · apply Finset.sum_eq_zero; intro i _; rw [if_neg]; · simp
    omega

private lemma affinePolynomial_natDegree_le (O : Type) [CommRing O] [IsDomain O] {n : ℕ}
    (a : Fin (n + 1) → O) : (affinePolynomial O a).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk; rw [affinePolynomial_coeff, dif_neg]; omega

private lemma affinePolynomial_natDegree_eq (O : Type) [CommRing O] [IsDomain O] {n : ℕ}
    (a : Fin (n + 1) → O) (h : a (Fin.last n) ≠ 0) :
    (affinePolynomial O a).natDegree = n ∧ (affinePolynomial O a).leadingCoeff = algebraMap O
      (BaseField O) (a (Fin.last n)) := by
  have hc : (affinePolynomial O a).coeff n = algebraMap O (BaseField O) (a (Fin.last n)) := by
    rw [affinePolynomial_coeff, dif_pos (by omega)]; rfl
  have hne : (affinePolynomial O a).coeff n ≠ 0 := by
    rw [hc]; exact (map_ne_zero_iff _ (IsFractionRing.injective O (BaseField O))).mpr h
  have hd := natDegree_eq_of_le_of_coeff_ne_zero (affinePolynomial_natDegree_le O a) hne
  exact ⟨hd, by rw [leadingCoeff, hd, hc]⟩

private lemma affinePolynomial_eq_init (O : Type) [CommRing O] [IsDomain O] {m : ℕ}
    (a : Fin (m + 2) → O) (h : a (Fin.last (m + 1)) = 0) :
    affinePolynomial O a = affinePolynomial O (Fin.init a) := by
  ext k; rw [affinePolynomial_coeff, affinePolynomial_coeff]
  by_cases hk : k < m + 1
  · rw [dif_pos (by omega), dif_pos hk]; rfl
  · rw [dif_neg hk]; split_ifs with h2
    · have : k = m+1 := by omega
      subst this
      have e : a ⟨m+1, h2⟩ = 0 := h
      rw [e, map_zero]
    · rfl

/-- Decomposition of the binary type event according to whether the top coefficient vanishes: if
it does not, it is the primitive affine type event; if it does, the type must contain a factor
`(1, 1)` at infinity and the remaining coefficients form an affine type event. -/
theorem binary_type_event_decomposition (O : Type) [CommRing O] [IsDomain O] (σ : FactorType) :
    (∀ n : ℕ, binaryTypeEvent O n σ ∩ {a | a (Fin.last n) ≠ 0} = affineTypeEvent O n σ ∩
      {a | primitive O a}) ∧ (binaryTypeEvent O 0 σ ∩ {a | a (Fin.last 0) = 0} = ∅) ∧ ∀ m : ℕ,
      binaryTypeEvent O (m+1) σ ∩ {a | a (Fin.last (m+1)) = 0} = {a | a (Fin.last (m+1)) = 0} ∩
      Fin.init ⁻¹' (if (1,1) ∈ σ then affineTypeEvent O m (σ.erase (1,1)) ∩ {b | primitive O b}
      else ∅) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n; ext a
    simp only [binaryTypeEvent, affineTypeEvent, HasBinaryTypeF, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hp, -, -, -, τ, hτ, hσ⟩, ha⟩
      obtain ⟨hd, hl⟩ := affinePolynomial_natDegree_eq O a ha
      rw [hd, Nat.sub_self, Multiset.replicate_zero, add_zero] at hσ
      subst hσ; rw [hl] at hτ; exact ⟨⟨ha, hτ⟩, hp⟩
    · rintro ⟨⟨ha, hτ⟩, hp⟩
      obtain ⟨hd, hl⟩ := affinePolynomial_natDegree_eq O a ha
      refine ⟨⟨hp, ?_, by omega, by omega, σ, by rwa [hl], by simp [hd]⟩, ha⟩
      intro h0; rw [h0, natDegree_zero] at hd; subst hd
      rw [h0] at hl; simp at hl
      exact ha ((map_eq_zero_iff _ (IsFractionRing.injective O (BaseField O))).mp hl.symm)
  · ext a
    simp only [binaryTypeEvent, primitive, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨⟨i, hi⟩, -⟩, h0⟩
    obtain rfl : i = Fin.last 0 := Subsingleton.elim (α := Fin 1) _ _
    rw [h0] at hi; exact not_isUnit_zero hi
  · intro m; ext a
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    have hprim : ∀ a : Fin (m+2) → O, a (Fin.last (m+1)) = 0 →
        (primitive O a ↔ primitive O (Fin.init a)) := by
      refine fun a h0 ↦ ⟨fun ⟨i, hi⟩ ↦ ?_, fun ⟨j, hj⟩ ↦ ⟨Fin.castSucc j, hj⟩⟩
      induction i using Fin.lastCases with
      | last => rw [h0] at hi; exact absurd hi not_isUnit_zero
      | cast j => exact ⟨j, hi⟩
    have hdeg : ∀ b : Fin (m+1) → O, affinePolynomial O b ≠ 0 →
        (affinePolynomial O b).natDegree = m → b (Fin.last m) ≠ 0 := fun b hne hd hb ↦ by
      refine hne (leadingCoeff_eq_zero.1 ?_)
      rw [leadingCoeff, hd, affinePolynomial_coeff, dif_pos (by omega)]
      exact (congrArg _ hb).trans (map_zero _)
    constructor
    · rintro ⟨⟨hp, hne, -, hle, τ, hτ, hσ⟩, h0⟩
      rw [affinePolynomial_eq_init O a h0] at hne hle hτ hσ
      have hd : (affinePolynomial O (Fin.init a)).natDegree = m := by
        have := affinePolynomial_natDegree_le O (Fin.init a); omega
      have hb := hdeg _ hne hd
      obtain ⟨-, hl⟩ := affinePolynomial_natDegree_eq O _ hb
      rw [hd, show m + 1 - m = 1 by omega, Multiset.replicate_one] at hσ
      have hmem : ((1:ℕ),(1:ℕ)) ∈ σ := by rw [hσ]; simp
      have her : σ.erase (1,1) = τ := by rw [hσ, add_comm, Multiset.singleton_add,
          Multiset.erase_cons_head]
      refine ⟨h0, ?_⟩
      rw [if_pos hmem]
      refine ⟨⟨hb, ?_⟩, (hprim a h0).mp hp⟩
      rw [her, ← hl]; exact hτ
    · rintro ⟨h0, hs⟩
      split_ifs at hs with hmem
      · obtain ⟨⟨hb, hτ⟩, hp⟩ := hs
        obtain ⟨hd, hl⟩ := affinePolynomial_natDegree_eq O _ hb
        refine ⟨⟨(hprim a h0).mpr hp, ?_⟩, h0⟩
        unfold HasBinaryTypeF
        rw [affinePolynomial_eq_init O a h0]; intro F; simp only [F]
        rw [hd, show m + 1 - m = 1 by omega, Multiset.replicate_one, hl]
        refine ⟨?_, by omega, le_refl _, σ.erase (1,1), hτ, ?_⟩
        · intro hz; rw [hz, leadingCoeff_zero] at hl
          exact hb ((map_eq_zero_iff _ (IsFractionRing.injective O (BaseField O))).mp hl.symm)
        · rw [add_comm, Multiset.singleton_add, Multiset.cons_erase hmem]
      · exact hs.elim

end

/-- For an unramified lift `Φ` and a monic polynomial in the residue cell of `(Φ mod π)^r`, its
`O`-type is `scaleType (deg Φ) τ` exactly when the translated block polynomial over `O[X]/(Φ)` has
type `τ`. -/
theorem descended_block_type_iff (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) [IsDomain (AdjoinRoot Φ)] (r : ℕ)
    (a : Fin (Φ.natDegree * r) → O) (ha : a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r))
    (σ : FactorType) :
    HasPolynomialTypeF O (monicPolynomial O a) σ ↔ ∃ τ : FactorType, HasPolynomialTypeF
      (AdjoinRoot Φ) (monicPolynomial (AdjoinRoot Φ) (pointChart O Φ r a)) τ ∧ σ =
      scaleType Φ.natDegree τ := by
  obtain ⟨_, _, hDVR, -, -, hComp, hFin, -⟩ := unramified_is_dvr O Φ hΦ
  have hδ : 0 < Φ.natDegree := by
    have h1 := Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_irreducible hΦ.2)
    rwa [Polynomial.Monic.natDegree_map hΦ.1] at h1
  obtain ⟨hbij, hdesc, -, hdiv⟩ := block_descent_bijection O Φ hΦ r
  set b := selectBlock O Φ r a with hb_def
  have hb : b ∈ blockCell O Φ r := hbij.mapsTo ha
  set B := monicPolyO b with hB_def
  have hBm : B.Monic := (hdiv a ha).1
  have hBdvd : B ∣ (monicPolyO a).map (AdjoinRoot.of Φ) := (hdiv a ha).2
  -- translation
  have hB' : monicPolyO (pointChart O Φ r a) = Polynomial.taylor (AdjoinRoot.root Φ) B := by
    have hrec := monic_poly_reconstruct (AdjoinRoot Φ) r b
    have hBn : B.natDegree = r := hrec.2.1
    have hTm : (Polynomial.taylor (AdjoinRoot.root Φ) B).Monic := by
      unfold Polynomial.Monic; rw [Polynomial.leadingCoeff_taylor]; exact hBm
    exact hrec.2.2.2 _ hTm ((Polynomial.natDegree_taylor B _).trans hBn)
  have htrans : ∀ τ, HasPolynomialTypeF (AdjoinRoot Φ)
      (B.map (algebraMap _ (BaseField (AdjoinRoot Φ)))) τ ↔
      HasPolynomialTypeF (AdjoinRoot Φ) (monicPolynomial (AdjoinRoot Φ) (pointChart O Φ r a)) τ :=
          by
    intro τ
    rw [← monicPolyO_map_fraction, hB']
    exact block_translation_type_iff (AdjoinRoot Φ) B hBm _ τ
  have hG : (monicPolyO a).map (algebraMap O (AdjoinRoot Φ)) = conjugateProduct O Φ B := by
    have := (descend_block_mem_cell O Φ hΦ r b hb).2
    rw [hdesc a ha] at this
    rw [AdjoinRoot.algebraMap_eq]; exact this
  have hback : ∀ τ, HasPolynomialTypeF (AdjoinRoot Φ)
      (B.map (algebraMap _ (BaseField (AdjoinRoot Φ)))) τ →
      HasPolynomialTypeF O (monicPolynomial O a) (scaleType Φ.natDegree τ) := by
    intro τ hτ
    rw [← monicPolyO_map_fraction]
    exact descended_polynomial_type O Φ hΦ B τ hτ (block_conjugates_coprime O Φ hΦ r b hb) _ hG
  constructor
  · intro hσ
    -- ascend the type to `Oδ` (closure-finiteness ascent), then pass to the divisor `B`
    obtain ⟨ι, hι, -⟩ := unramified_fraction_field_lift O Φ hΦ
    have hmap : (monicPolynomial O a).map ι =
        ((monicPolyO a).map (algebraMap O (AdjoinRoot Φ))).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))) := by
      rw [← monicPolyO_map_fraction, Polynomial.map_map, Polynomial.map_map]
      congr 1
      exact RingHom.ext hι
    have hdvd : B.map (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))) ∣
        ((monicPolyO a).map (algebraMap O (AdjoinRoot Φ))).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))) :=
      Polynomial.map_dvd _ (by rw [AdjoinRoot.algebraMap_eq]; exact hBdvd)
    obtain ⟨τ', hτ'⟩ := polynomial_type_map_unramified O Φ hΦ ι hι _ σ hσ
    rw [hmap] at hτ'
    obtain ⟨τ, hτ⟩ := polynomial_type_dvd (AdjoinRoot Φ) _ _ τ' hτ' (hBm.map _) hdvd
    refine ⟨τ, (htrans τ).1 hτ, ?_⟩
    exact polynomial_type_unique O _ σ _ hσ (hback τ hτ)
  · rintro ⟨τ, hτ, rfl⟩
    exact hback τ ((htrans τ).2 hτ)

/-! ### Divisors, arrays and counts -/

/-- Every exceptional divisor of degree `n` has a unique array, and that array is a residue
pattern. -/
theorem divisor_array_exists_unique (k : Type) [Field k] (n : ℕ) (D : ExceptionalDivisor k)
    (hD : exceptionalDegree k D = n) :
    (∃ m : Pattern n, HasArray k n D m ∧ m ∈ residuePatterns n) ∧ ∀ m m' : Pattern n,
      HasArray k n D m → HasArray k n D m' → m = m' := by
  have hdeg := directionDegree_pos k
  have hsum : exceptionalDegree k D = ∑ Q ∈ D.support, directionDegree k Q * D Q := rfl
  set S : Fin n × Fin n → Finset (ClosedDirection k) := fun ij =>
    D.support.filter (fun Q => directionDegree k Q = ij.1.val + 1 ∧ D Q = ij.2.val + 1) with hS
  have hcard : ∀ ij : Fin n × Fin n,
      Nat.card {Q : ClosedDirection k // directionDegree k Q = ij.1.val + 1 ∧ D Q = ij.2.val + 1}
        = (S ij).card := by
    intro ij
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro Q
    simp only [hS, Finset.mem_filter, Finsupp.mem_support_iff]
    constructor
    · intro h; exact ⟨by omega, h⟩
    · intro h; exact h.2
  have hconst : ∀ ij : Fin n × Fin n,
      ∑ Q ∈ S ij, directionDegree k Q * D Q = (S ij).card * ((ij.1.val + 1) * (ij.2.val + 1)) := by
    intro ij
    rw [Finset.sum_congr rfl (g := fun _ => (ij.1.val + 1) * (ij.2.val + 1))]
    · simp
    · intro Q hQ
      simp only [hS, Finset.mem_filter] at hQ
      rw [hQ.2.1, hQ.2.2]
  have hbound : ∀ ij : Fin n × Fin n, (S ij).card ≤ n := by
    intro ij
    have h1 : ∑ Q ∈ S ij, directionDegree k Q * D Q ≤ n := by
      rw [← hD, hsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
    rw [hconst] at h1
    have : 1 ≤ (ij.1.val + 1) * (ij.2.val + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  refine ⟨⟨fun ij => ⟨(S ij).card, Nat.lt_succ_of_le (hbound ij)⟩, fun ij => hcard ij, ?_⟩, ?_⟩
  · rw [residuePatterns, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold patternWeight
    have step1 : ∀ ij : Fin n × Fin n, (ij.1.val + 1) * (ij.2.val + 1) * (S ij).card
        = ∑ Q ∈ D.support, if (directionDegree k Q = ij.1.val + 1 ∧ D Q = ij.2.val + 1)
            then directionDegree k Q * D Q else 0 := by
      intro ij
      rw [← Finset.sum_filter, hconst, mul_comm]
    simp only [step1]
    rw [Finset.sum_comm, ← hD, hsum]
    apply Finset.sum_congr rfl
    intro Q hQ
    have hle : directionDegree k Q * D Q ≤ n := hD ▸ directionDegree_mul_le_exceptionalDegree k D Q
    have hD1 : 1 ≤ D Q := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hQ)
    have hd1 := hdeg Q
    have hA : directionDegree k Q ≤ n := by nlinarith
    have hB : D Q ≤ n := by nlinarith
    rw [Finset.sum_eq_single_of_mem (⟨directionDegree k Q - 1, by omega⟩, ⟨D Q - 1, by omega⟩)
      (Finset.mem_univ _)]
    · rw [if_pos]; simp only; constructor <;> omega
    · intro ij _ hne
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hne
      ext <;> simp <;> omega
  · intro m m' hm hm'
    funext ij
    exact Fin.ext ((hm ij).symm.trans (hm' ij))

private theorem finite_directions_of_degree (k : Type) [Field k] [Finite k]
    (p : ClosedDirection k → Prop) (n : ℕ) :
    Finite {Q : ClosedDirection k // p Q ∧ directionDegree k Q = n} := by
  let f : {Q : ClosedDirection k // p Q ∧ directionDegree k Q = n} → Option (Fin (n+1) → k) :=
    fun Q => Option.map (fun φ : AffineDirection k => fun i : Fin (n+1) => φ.val.coeff i) Q.1
  refine Finite.of_injective f ?_
  rintro ⟨Q, hQ⟩ ⟨Q', hQ'⟩ h
  apply Subtype.ext
  simp only [f] at h
  cases Q with
  | none =>
    cases Q' with
    | none => rfl
    | some _ => simp at h
  | some φ =>
    cases Q' with
    | none => simp at h
    | some ψ =>
      simp only [Option.map_some, Option.some.injEq] at h
      change some φ = some ψ
      congr 1
      apply Subtype.ext
      apply Polynomial.ext
      intro i
      by_cases hi : i < n + 1
      · exact congrFun h ⟨i, hi⟩
      · have h1 : φ.val.natDegree < i := by simp [directionDegree] at hQ; omega
        have h2 : ψ.val.natDegree < i := by simp [directionDegree] at hQ'; omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt h1,
          Polynomial.coeff_eq_zero_of_natDegree_lt h2]

private theorem coloring_count (T : Type) [Finite T] (r : ℕ) (m : Fin r → ℕ) :
    Finite {f : T → Option (Fin r) // ∀ j : Fin r, Nat.card {x // f x = some j} = m j} ∧
      ((Nat.card {f : T → Option (Fin r) // ∀ j : Fin r, Nat.card {x // f x = some j} = m j} : ℕ) :
      ℚ) = ((List.range (∑ i : Fin r, m i)).map fun j => (Nat.card T : ℚ) - j).prod / ∏ i : Fin r,
      (Nat.factorial (m i) : ℚ) := by
  refine ⟨inferInstance, ?_⟩
  obtain e := Finite.equivFin T
  have key : {f : T → Option (Fin r) // ∀ j : Fin r, Nat.card {x // f x = some j} = m j} ≃
      {f : Fin (Nat.card T) → Option (Fin r) //
        ∀ i : Fin r, Nat.card {x : Fin (Nat.card T) // f x = some i} = m i} := by
    refine Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl _)) ?_
    intro f
    refine forall_congr' fun j => ?_
    have : Nat.card {x // f x = some j} =
        Nat.card {x : Fin (Nat.card T) // (Equiv.arrowCongr e (Equiv.refl _) f) x = some j} := by
      apply Nat.card_congr
      refine e.subtypeEquiv ?_
      intro x
      simp [Equiv.arrowCongr_apply]
    rw [this]
  rw [Nat.card_congr key, colored_subset_count]

private theorem exceptionalDegree_eq_patternWeight (k : Type) [Field k] (n : ℕ)
    (D : ExceptionalDivisor k) (m : Pattern n)
    (hb : ∀ Q, D Q ≠ 0 → directionDegree k Q ≤ n ∧ D Q ≤ n) (hA : HasArray k n D m) :
    exceptionalDegree k D = patternWeight m := by
  have hsum : exceptionalDegree k D = ∑ Q ∈ D.support, directionDegree k Q * D Q := rfl
  set S : Fin n × Fin n → Finset (ClosedDirection k) := fun ij =>
    D.support.filter (fun Q => directionDegree k Q = ij.1.val + 1 ∧ D Q = ij.2.val + 1) with hS
  have hcard : ∀ ij : Fin n × Fin n, (m ij).val = (S ij).card := by
    intro ij
    rw [← hA ij, ← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro Q
    simp only [hS, Finset.mem_filter, Finsupp.mem_support_iff]
    constructor
    · intro h; exact ⟨by omega, h⟩
    · intro h; exact h.2
  have hconst : ∀ ij : Fin n × Fin n,
      ∑ Q ∈ S ij, directionDegree k Q * D Q = (S ij).card * ((ij.1.val + 1) * (ij.2.val + 1)) := by
    intro ij
    rw [Finset.sum_congr rfl (g := fun _ => (ij.1.val + 1) * (ij.2.val + 1))]
    · simp
    · intro Q hQ
      simp only [hS, Finset.mem_filter] at hQ
      rw [hQ.2.1, hQ.2.2]
  unfold patternWeight
  have step1 : ∀ ij : Fin n × Fin n, (ij.1.val + 1) * (ij.2.val + 1) * (m ij).val
      = ∑ Q ∈ D.support, if (directionDegree k Q = ij.1.val + 1 ∧ D Q = ij.2.val + 1)
          then directionDegree k Q * D Q else 0 := by
    intro ij
    rw [← Finset.sum_filter, hcard, hconst, mul_comm]
  simp only [step1]
  rw [Finset.sum_comm, hsum]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hD0 : D Q ≠ 0 := Finsupp.mem_support_iff.mp hQ
  have hd1 := directionDegree_pos k Q
  have hA' := (hb Q hD0).1
  have hB := (hb Q hD0).2
  rw [Finset.sum_eq_single_of_mem (⟨directionDegree k Q - 1, by omega⟩, ⟨D Q - 1, by omega⟩)
    (Finset.mem_univ _)]
  · rw [if_pos]; simp only; constructor <;> omega
  · intro ij _ hne
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hne
    ext <;> simp <;> omega

section
variable (k : Type) [Field k] (S : Set (ClosedDirection k)) (n : ℕ)

private abbrev DegPoints (i : Fin n) : Type := {Q : ClosedDirection k // Q ∈ S ∧ directionDegree k
    Q =
    i.val + 1}

private def degreeFiberEquiv (D : ExceptionalDivisor k) (hS : ∀ Q, D Q ≠ 0 → Q ∈ S) (i j : Fin n) :
    {Q : ClosedDirection k // directionDegree k Q = i.val + 1 ∧ D Q = j.val + 1} ≃
      {q : DegPoints k S n i // D q.1 = j.val + 1} where
  toFun Q := ⟨⟨Q.1, hS Q.1 (by omega), Q.2.1⟩, Q.2.2⟩
  invFun q := ⟨q.1.1, q.1.2.2, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
private noncomputable def divisorOfColoringFun (g : ∀ i : Fin n, DegPoints k S n i → Option (Fin n))
    (Q : ClosedDirection k) : ℕ :=
  if h : ∃ i : Fin n, Q ∈ S ∧ directionDegree k Q = i.val + 1 then
    (g h.choose ⟨Q, h.choose_spec⟩).elim 0 (fun j => j.val + 1) else 0

private theorem divisorOfColoringFun_support_finite [Finite k]
    (g : ∀ i : Fin n, DegPoints k S n i → Option (Fin n)) :
    (Function.support (divisorOfColoringFun k S n g)).Finite := by
  have : ∀ i, Finite (DegPoints k S n i) := fun i => finite_directions_of_degree k _ _
  refine Set.Finite.subset (Set.finite_iUnion fun i => Set.finite_range
      (Subtype.val : DegPoints k S n i → _)) ?_
  intro Q hQ
  simp only [Function.mem_support, divisorOfColoringFun] at hQ
  split_ifs at hQ with h
  · obtain ⟨i, hi⟩ := h
    exact Set.mem_iUnion.mpr ⟨i, ⟨Q, hi⟩, rfl⟩
  · exact absurd rfl hQ

private noncomputable def divisorOfColoring [Finite k]
    (g : ∀ i : Fin n, DegPoints k S n i → Option (Fin n)) : ExceptionalDivisor k :=
  Finsupp.ofSupportFinite (divisorOfColoringFun k S n g)
      (divisorOfColoringFun_support_finite k S n g)

private theorem divisorOfColoring_apply [Finite k]
    (g : ∀ i : Fin n, DegPoints k S n i → Option (Fin n)) (i : Fin n) (q : DegPoints k S n i) :
    divisorOfColoring k S n g q.1 = (g i q).elim 0 (fun j => j.val + 1) := by
  change divisorOfColoringFun k S n g q.1 = _
  have hex : ∃ i : Fin n, q.1 ∈ S ∧ directionDegree k q.1 = i.val + 1 := ⟨i, q.2⟩
  simp only [divisorOfColoringFun, dif_pos hex]
  have key : ∀ (i' : Fin n) (hi' : q.1 ∈ S ∧ directionDegree k q.1 = i'.val + 1), i' = i →
      (g i' ⟨q.1, hi'⟩).elim 0 (fun j => j.val + 1) = (g i q).elim 0 (fun j => j.val + 1) := by
    rintro _ _ rfl; rfl
  apply key
  apply Fin.ext
  have h1 := hex.choose_spec.2
  have h2 := q.2.2
  omega

private theorem divisorOfColoring_eq_zero [Finite k]
    (g : ∀ i : Fin n, DegPoints k S n i → Option (Fin n)) (Q : ClosedDirection k)
    (h : ¬ (∃ i : Fin n, Q ∈ S ∧ directionDegree k Q = i.val + 1)) :
    divisorOfColoring k S n g Q = 0 := by
  change divisorOfColoringFun k S n g Q = 0
  simp only [divisorOfColoringFun, dif_neg h]

private theorem divisorOfColoring_supp [Finite k]
    (g : ∀ i : Fin n, DegPoints k S n i → Option (Fin n)) :
    ∀ Q, divisorOfColoring k S n g Q ≠ 0 → Q ∈ S := by
  intro Q hQ
  by_contra hS
  exact hQ (divisorOfColoring_eq_zero k S n g Q (fun ⟨i, hi⟩ => hS hi.1))

private theorem divisorOfColoring_bound [Finite k]
    (g : ∀ i : Fin n, DegPoints k S n i → Option (Fin n)) :
    ∀ Q, divisorOfColoring k S n g Q ≠ 0 → directionDegree k Q ≤ n ∧
      divisorOfColoring k S n g Q ≤ n := by
  intro Q hQ
  by_cases h : ∃ i : Fin n, Q ∈ S ∧ directionDegree k Q = i.val + 1
  · obtain ⟨i, hi⟩ := h
    have := divisorOfColoring_apply k S n g i ⟨Q, hi⟩
    simp only at this
    rw [this]
    refine ⟨by omega, ?_⟩
    cases g i ⟨Q, hi⟩ with
    | none => simp
    | some j => have := j.2; simp; try omega
  · exact absurd (divisorOfColoring_eq_zero k S n g Q h) hQ

private theorem divisorOfColoring_hasArray [Finite k] (m : Pattern n)
    (g : ∀ i : Fin n, DegPoints k S n i → Option (Fin n))
    (hg : ∀ i j, Nat.card {q // g i q = some j} = (m (i, j)).val) :
    HasArray k n (divisorOfColoring k S n g) m := by
  intro ij
  obtain ⟨i, j⟩ := ij
  rw [Nat.card_congr (degreeFiberEquiv k S n _ (divisorOfColoring_supp k S n _) i j), ← hg i j]
  apply Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
  rw [divisorOfColoring_apply k S n g i q]
  cases g i q with
  | none => simp
  | some j' => simp [Fin.ext_iff]

private def coloringOfDivisor (D : ExceptionalDivisor k) (hb : ∀ Q, D Q ≤ n) (i : Fin n)
    (q : DegPoints k S n i) : Option (Fin n) :=
  if h : D q.1 = 0 then none else some ⟨D q.1 - 1, by have := hb q.1; omega⟩

private theorem coloringOfDivisor_eq_some (D : ExceptionalDivisor k) (hb : ∀ Q, D Q ≤ n)
    (i j : Fin n) (q : DegPoints k S n i) :
    coloringOfDivisor k S n D hb i q = some j ↔ D q.1 = j.val + 1 := by
  simp only [coloringOfDivisor]
  split_ifs with h
  · simp; omega
  · simp only [Option.some.injEq, Fin.ext_iff]; omega

private theorem le_of_exceptionalDegree_eq (D : ExceptionalDivisor k)
    (hD : exceptionalDegree k D = n) : ∀ Q, D Q ≤ n := by
  intro Q
  have := directionDegree_mul_le_exceptionalDegree k D Q
  have := directionDegree_pos k Q
  nlinarith

end

/-- Counting divisors of degree `n` with a given array `m` and support in a point set `S` that has
`c δ` points of degree `δ`: their number is the product of falling factorials over multinomial
factors. -/
theorem divisor_count_of_point_set (k : Type) [Field k] [Finite k] (S : Set (ClosedDirection k))
    (c : ℕ → ℕ)
    (hc : ∀ δ : ℕ, 0 < δ → Nat.card {Q : ClosedDirection k // Q ∈ S ∧ directionDegree k
      Q = δ} = c δ) (n : ℕ) (m : Pattern n) (hm : m ∈ residuePatterns n) :
    Finite {D : ExceptionalDivisor k // (∀ Q, D Q ≠ 0 → Q ∈ S) ∧ exceptionalDegree k D = n ∧
      HasArray k n D m} ∧
      ((Nat.card {D : ExceptionalDivisor k // (∀ Q, D Q ≠ 0 → Q ∈ S) ∧ exceptionalDegree k D = n ∧
      HasArray k n D m} : ℕ) : ℚ) = ∏ i : Fin n,
      (((List.range (∑ j : Fin n, (m (i, j)).val)).map fun t => ((c (i.val + 1) : ℕ) : ℚ) -
      (t : ℚ)).prod / ∏ j : Fin n, ((Nat.factorial (m (i, j)).val : ℕ) : ℚ)) := by
  have hw : patternWeight m = n := (Finset.mem_filter.mp hm).2
  have hPfin : ∀ i, Finite (DegPoints k S n i) := fun i => finite_directions_of_degree k _ _
  let X := {D : ExceptionalDivisor k // (∀ Q, D Q ≠ 0 → Q ∈ S) ∧ exceptionalDegree k D = n ∧
      HasArray k n D m}
  let Y := ∀ i : Fin n, {f : DegPoints k S n i → Option (Fin n) // ∀ j : Fin n, Nat.card
      {q // f q = some j} = (m (i, j)).val}
  have e : X ≃ Y :=
    { toFun := fun D i => ⟨coloringOfDivisor k S n D.1 (le_of_exceptionalDegree_eq k n D.1 D.2.2.1)
        i, fun j => by
        rw [← D.2.2.2 (i, j), Nat.card_congr (degreeFiberEquiv k S n D.1 D.2.1 i j)]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun q => coloringOfDivisor_eq_some k S n _ _
            i j q)⟩
      invFun := fun g => ⟨divisorOfColoring k S n (fun i => (g i).1), divisorOfColoring_supp k S n
          _, by
        have hA := divisorOfColoring_hasArray k S n m (fun i => (g i).1) (fun i j => (g i).2 j)
        exact ⟨(exceptionalDegree_eq_patternWeight k n _ m (divisorOfColoring_bound k S n _)
            hA).trans hw, hA⟩⟩
      left_inv := by
        rintro ⟨D, hS, hD, hA⟩
        apply Subtype.ext
        ext Q
        by_cases h : ∃ i : Fin n, Q ∈ S ∧ directionDegree k Q = i.val + 1
        · obtain ⟨i, hi⟩ := h
          have := divisorOfColoring_apply k S n (fun i => coloringOfDivisor k S n D
              (le_of_exceptionalDegree_eq k n D hD) i) i ⟨Q, hi⟩
          simp only at this ⊢
          rw [this]
          simp only [coloringOfDivisor]
          split_ifs with h0
          · simp [h0]
          · simp; omega
        · simp only
          rw [divisorOfColoring_eq_zero k S n _ Q h]
          by_contra h0
          have h1 := directionDegree_mul_le_exceptionalDegree k D Q
          have h2 := directionDegree_pos k Q
          have h3 : directionDegree k Q ≤ n := by
            have : 1 ≤ D Q := by omega
            nlinarith
          exact h ⟨⟨directionDegree k Q - 1, by omega⟩, hS Q (Ne.symm h0), by simp; omega⟩
      right_inv := by
        intro g
        funext i
        apply Subtype.ext
        funext q
        have hb := divisorOfColoring_apply k S n (fun i => (g i).1) i q
        simp only [coloringOfDivisor]
        split_ifs with h0
        · rw [hb] at h0
          cases h : (g i).1 q with
          | none => rfl
          | some j => simp [h] at h0
        · cases h : (g i).1 q with
          | none => rw [hb, h] at h0; exact absurd rfl h0
          | some j =>
            simp only [Option.some.injEq]
            apply Fin.ext
            simp only
            rw [hb, h]
            simp }
  have hYfin : ∀ i, Finite {f : DegPoints k S n i → Option (Fin n) //
      ∀ j : Fin n, Nat.card {q // f q = some j} = (m (i, j)).val} :=
    fun i => (coloring_count _ _ _).1
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_pi, Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(coloring_count (DegPoints k S n i) n (fun j => (m (i, j)).val)).2, hc _ (Nat.succ_pos _)]

/-- If the points of `S` of each degree `δ > 0` are counted by `availablePoints offset δ` at
`q = |k|`, then the divisors of degree `n` supported on `S` with array `m` are counted by
`divisorCount offset m` at `q`. -/
theorem divisor_count_eval_of_point_count (k : Type) [Field k] [Finite k]
    (S : Set (ClosedDirection k)) (offset : ℤ)
    (hS : ∀ δ : ℕ, 0 < δ → ((Nat.card {Q : ClosedDirection k // Q ∈ S ∧ directionDegree k Q = δ} :
      ℕ) : ℚ) = (availablePoints offset δ).eval (Nat.card k))
    (n : ℕ) (m : Pattern n) (hm : m ∈ residuePatterns n) :
    Finite {D : ExceptionalDivisor k // (∀ Q, D Q ≠ 0 → Q ∈ S) ∧ exceptionalDegree k D = n ∧
      HasArray k n D m} ∧
      ((Nat.card {D : ExceptionalDivisor k // (∀ Q, D Q ≠ 0 → Q ∈ S) ∧ exceptionalDegree k D = n ∧
      HasArray k n D m} : ℕ) : ℚ) = (divisorCount offset m).eval (Nat.card k) := by
  obtain ⟨hfin, h⟩ := divisor_count_of_point_set k S _ (fun _ _ ↦ rfl) n m hm
  refine ⟨hfin, ?_⟩
  rw [h]
  unfold divisorCount
  rw [expression_prod_eval, List.map_map, ← Finset.prod_map_toList]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Expr.eval, falling, expression_prod_eval, List.map_map,
      div_eq_mul_inv, one_mul]
  congr 1
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, Expr.sub, Expr.neg, Expr.eval]
  rw [hS (i.val + 1) (Nat.succ_pos _)]
  ring_nf

/-- The number of affine divisors of degree `n` with array `m` is `divisorCount 0 m` evaluated at
the residue field size. -/
theorem affine_divisor_count (k : Type) [Field k] [Finite k] (n : ℕ) (m : Pattern n)
    (hm : m ∈ residuePatterns n) :
    Finite {D : ExceptionalDivisor k // AffineDivisor k n D ∧ HasArray k n D m} ∧
      ((Nat.card {D : ExceptionalDivisor k // AffineDivisor k n D ∧ HasArray k n D m} : ℕ) : ℚ) =
      (divisorCount 0 m).eval (Nat.card k) := by
  have hc : ∀ δ : ℕ, 0 < δ → ((Nat.card {Q : ClosedDirection k // Q ∈
      {Q : ClosedDirection k | Q ≠ none} ∧ directionDegree k Q = δ} : ℕ) : ℚ) =
      (availablePoints 0 δ).eval (Nat.card k) := by
    intro δ hδ
    have h915 := nonboundary_direction_count k (State.single 1 1) δ hδ
    simp only at h915
    rw [← h915]
    congr 1
  have h := divisor_count_eval_of_point_count k {Q : ClosedDirection k | Q ≠ none} 0 hc n m hm
  have e : ∀ D : ExceptionalDivisor k, ((∀ Q, D Q ≠ 0 → Q ∈ {Q : ClosedDirection k | Q ≠ none}) ∧
      exceptionalDegree k D = n ∧ HasArray k n D m) ↔ (AffineDivisor k n D ∧ HasArray k n D m) := by
    intro D
    simp only [AffineDivisor, infinityDirection, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by by_contra hh; exact h1 _ hh rfl, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun Q hQ hQn => hQ (hQn ▸ h1), h2, h3⟩
  have eq := Equiv.subtypeEquivRight e
  have := h.1
  exact ⟨Finite.of_equiv _ eq, by rw [← Nat.card_congr eq, h.2]⟩

/-- Basic properties of the divisor vector of a divisor `D` of degree `n`: the affine polynomial of
`D` is monic of degree `n - D ∞`, it is the form polynomial of the divisor vector, whose entry at
`n - D ∞` is `1` and whose higher entries vanish. -/
theorem divisor_vector_properties (k : Type) [Field k] (n : ℕ) (D : ExceptionalDivisor k)
    (hD : exceptionalDegree k D = n) :
    (divisorAffinePolynomial k D).Monic ∧ (divisorAffinePolynomial k D).natDegree = n - D
      (infinityDirection k) ∧ D (infinityDirection k) ≤ n ∧ formPoly (divisorVector k n D) =
      divisorAffinePolynomial k D ∧ divisorVector k n D (⟨n - D (infinityDirection k),
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ :
      Fin (n+1)) = 1 ∧ (∀ i : Fin (n+1), n - D (infinityDirection k) < i.val → divisorVector k n D
      i = 0) ∧ divisorVector k n D ≠ 0 := by
  classical
  set g : ClosedDirection k → ℕ → Polynomial k :=
    fun P r => (match P with | none => 1 | some phi => phi.val ^ r) with hg
  have hmon : ∀ P r, (g P r).Monic := by
    intro P r
    cases P with
    | none => exact Polynomial.monic_one
    | some phi => exact phi.property.1.pow r
  have hM : (divisorAffinePolynomial k D).Monic := by
    unfold divisorAffinePolynomial
    exact Polynomial.monic_prod_of_monic _ _ (fun P _ => hmon P (D P))
  have hdeg : (divisorAffinePolynomial k D).natDegree = ∑ P ∈ D.support, (g P (D P)).natDegree := by
    unfold divisorAffinePolynomial
    exact Polynomial.natDegree_prod_of_monic _ _ (fun P _ => hmon P (D P))
  have hsum : exceptionalDegree k D = (divisorAffinePolynomial k D).natDegree + D none := by
    rw [hdeg]
    have : ∀ P ∈ D.support, directionDegree k P * D P = (g P (D P)).natDegree +
        (if none = P then D P else 0) := by
      intro P _
      cases P with
      | none => simp [directionDegree, hg]
      | some phi => simp [directionDegree, hg, Polynomial.natDegree_pow]; ring
    unfold exceptionalDegree Finsupp.sum
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    by_cases h : none ∈ D.support
    · rw [Finset.sum_eq_single none]
      · simp
      · intro b _ hb; exact if_neg (Ne.symm hb)
      · intro h'; exact absurd h h'
    · have : D none = 0 := by simpa using h
      simp [this]
  have hinf : infinityDirection k = none := rfl
  simp only [hinf]
  have h1 : (divisorAffinePolynomial k D).natDegree = n - D none := by omega
  have h2 : D none ≤ n := by omega
  have hle : (divisorAffinePolynomial k D).natDegree < n + 1 := by omega
  have hcoef : divisorVector k n D (⟨n - D none, by omega⟩ : Fin (n+1)) = 1 := by
    change (divisorAffinePolynomial k D).coeff (n - D none) = 1
    rw [← h1]; exact hM
  refine ⟨hM, h1, h2, ?_, hcoef, ?_, ?_⟩
  · unfold formPoly
    conv_rhs => rw [Polynomial.as_sum_range' _ (n+1) hle]
    rw [← Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i
        ((divisorAffinePolynomial k D).coeff i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.C_mul_X_pow_eq_monomial]; rfl
  · intro i hi
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · intro h0
    have := congrFun h0 ⟨n - D none, by omega⟩
    rw [hcoef] at this
    simp at this

section
open Polynomial

private lemma formPoly_coeff {A : Type} [CommRing A] {d : ℕ} (v : Fin (d + 1) → A)
    (i : Fin (d + 1)) :
    (formPoly v).coeff i = v i := by
  simp only [formPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h).symm), mul_zero]
  · simp

/-- The form polynomial of a vector of length `d + 1` has degree at most `d`. -/
theorem formPoly_natDegree_le {A : Type} [CommRing A] {d : ℕ} (v : Fin (d + 1) → A) :
    (formPoly v).natDegree ≤ d := by
  unfold formPoly
  refine natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.2)

private lemma formPoly_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {d : ℕ}
    (v : Fin (d + 1) → A) : (formPoly v).map f = formPoly (fun i => f (v i)) := by
  simp [formPoly, Polynomial.map_sum]

private lemma formPoly_insertOne_last {A : Type} [CommRing A] {d : ℕ} (b : Fin d → A) :
    formPoly (insertOne (Fin.last d) b) = monicPolyO b := by
  simp [formPoly, insertOne, monicPolyO, Fin.sum_univ_castSucc, Fin.insertNth_last', add_comm]

private lemma formPoly_single_zero {A : Type} [CommRing A] {d : ℕ} :
    formPoly (Pi.single (0 : Fin (d+1)) (1 : A)) = 1 := by
  unfold formPoly
  rw [Fintype.sum_eq_single 0]
  · simp
  · intro i hi; simp [hi]

private lemma coeff_prod_sum_of_natDegree_le {A ι : Type} [CommRing A] (s : Finset ι) (p : ι → A[X])
    (d : ι → ℕ) (h : ∀ i ∈ s, (p i).natDegree ≤ d i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (p i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
      coeff_mul_add_eq_of_natDegree_le (h a (by simp)), ih (fun i hi => h i (by simp [hi]))]
    exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i hi => h i (by simp [hi]))

end

/-! ### Type events on products of cells -/

section ProductCells

variable {ι Y : Type} [Fintype ι] {X : ι → Type}

/-- If `f` maps the product of the cells `C j` into `E₀`, and a point `a` of that product has
`f a ∈ P` exactly when `a j ∈ Ev j (τ j)` for some `τ` with `σ = ∑ j, τ j`, then the trace of
`f ⁻¹' (E₀ ∩ P)` on the product is a finite union of products of events. -/
theorem preimage_inter_pi_eq_biUnion (f : (∀ j, X j) → Y) (C : ∀ j, Set (X j))
    (E₀ P : Set Y) (hf : Set.MapsTo f (Set.pi Set.univ C) E₀) (Ev : ∀ j, FactorType → Set (X j))
    (W : ι → Finset FactorType) (hW : ∀ j τ, (C j ∩ Ev j τ).Nonempty → τ ∈ W j)
    (σ : FactorType) (hP : ∀ a ∈ Set.pi Set.univ C,
      f a ∈ P ↔ ∃ τ : ι → FactorType, (∀ j, a j ∈ Ev j (τ j)) ∧ σ = ∑ j, τ j)
    (T : Finset (ι → FactorType)) (hT : ∀ τ, τ ∈ T ↔ (∀ j, τ j ∈ W j) ∧ σ = ∑ j, τ j) :
    f ⁻¹' (E₀ ∩ P) ∩ Set.pi Set.univ C = ⋃ τ ∈ T, Set.pi Set.univ fun j ↦ C j ∩ Ev j (τ j) := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, hT, Set.mem_univ_pi,
    exists_prop, forall_and]
  constructor
  · rintro ⟨⟨-, haP⟩, haC⟩
    obtain ⟨τ, hτ, hσ⟩ := (hP a (Set.mem_univ_pi.2 haC)).1 haP
    exact ⟨τ, ⟨fun j ↦ hW j (τ j) ⟨a j, haC j, hτ j⟩, hσ⟩, haC, hτ⟩
  · rintro ⟨τ, ⟨-, hσ⟩, haC, hτ⟩
    have ha := Set.mem_univ_pi.2 haC
    exact ⟨⟨hf ha, (hP a ha).2 ⟨τ, hτ, hσ⟩⟩, haC⟩

omit [Fintype ι] in
/-- Products of events `Ev j (τ j)` are pairwise disjoint for distinct `τ` when each family
`Ev j` is pairwise disjoint. -/
theorem pairwiseDisjoint_pi_events (C : ∀ j, Set (X j)) (Ev : ∀ j, FactorType → Set (X j))
    (huniq : ∀ j τ τ' x, x ∈ Ev j τ → x ∈ Ev j τ' → τ = τ') (T : Set (ι → FactorType)) :
    T.PairwiseDisjoint fun τ ↦ Set.pi Set.univ fun j ↦ C j ∩ Ev j (τ j) :=
  fun _ _ _ _ hne ↦ Set.disjoint_left.2 fun _ ha ha' ↦ hne <| funext fun j ↦
    huniq j _ _ _ (ha j (Set.mem_univ _)).2 (ha' j (Set.mem_univ _)).2

/-- If `f` is continuous and bijective from a closed subset `C` of a compact space onto `E₀`, and
the trace on `C` of `f ⁻¹' (E₀ ∩ A)` is measurable, then `E₀ ∩ A` is measurable. -/
theorem measurableSet_inter_of_bijOn {Z : Type} [TopologicalSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [BorelSpace Y] {f : Z → Y} {C : Set Z} {E₀ A : Set Y} (hC : IsClosed C)
    (hf : ContinuousOn f C) (hbij : Set.BijOn f C E₀) (hA : MeasurableSet (f ⁻¹' (E₀ ∩ A) ∩ C)) :
    MeasurableSet (E₀ ∩ A) := by
  have := image_measurable_of_continuousOn_injOn_compact Z Y f C hC hf hbij.injOn _ hA
  rwa [Set.inter_assoc, Set.inter_self, Set.image_preimage_inter, hbij.image_eq,
    Set.inter_assoc, Set.inter_comm A, ← Set.inter_assoc, Set.inter_self] at this

open MeasureTheory in
/-- If `f` is measure preserving from `Measure.pi m` to `ν`, the product of the cells `C j` is
conull, and the trace on it of `f ⁻¹' E` is the finite union over `τ ∈ T` of products of the
measurable factor events `C j ∩ Ev j (τ j)` (each family `Ev j` being pairwise disjoint), then the
`ν`-mass of `E` is the sum over `T` of the products of the factor masses. -/
theorem measure_eq_sum_prod_of_preimage [∀ j, MeasurableSpace (X j)] [MeasurableSpace Y]
    (m : ∀ j, Measure (X j)) [∀ j, SigmaFinite (m j)] {ν : Measure Y} {f : (∀ j, X j) → Y}
    (hf : MeasurePreserving f (Measure.pi m) ν) (C : ∀ j, Set (X j))
    (hC : Measure.pi m (Set.pi Set.univ C)ᶜ = 0) (hm : ∀ j s, m j (C j ∩ s) = m j s)
    (Ev : ∀ j, FactorType → Set (X j)) (hEv : ∀ j τ, MeasurableSet (C j ∩ Ev j τ))
    (huniq : ∀ j τ τ' x, x ∈ Ev j τ → x ∈ Ev j τ' → τ = τ') {E : Set Y} (hE : MeasurableSet E)
    (T : Finset (ι → FactorType))
    (hpre : f ⁻¹' E ∩ Set.pi Set.univ C = ⋃ τ ∈ T, Set.pi Set.univ fun j ↦ C j ∩ Ev j (τ j)) :
    ν E = ∑ τ ∈ T, ∏ j, m j (Ev j (τ j)) := by
  rw [← hf.measure_preimage hE.nullMeasurableSet, ← measure_inter_conull hC, hpre,
    measure_biUnion_finset (pairwiseDisjoint_pi_events C Ev huniq _)
      fun τ _ ↦ .univ_pi fun j ↦ hEv j (τ j)]
  simp only [Measure.pi_pi, hm]

/-- The finite convolution of the factor densities over any finite sets of types `W j` containing
the supports of the laws `Dl j` is the density of the product law. -/
theorem sum_prod_densityValue_eq_lawProd {L : ℕ} (Dl : Fin L → Law) (q : ℕ)
    (hnn : ∀ j τ, 0 ≤ (lawCoeff (Dl j) τ).eval (q : ℚ)) (W : Fin L → Finset FactorType)
    (hW : ∀ j, ((Dl j).map Prod.fst).toFinset ⊆ W j) (σ : FactorType) :
    ∑ τ ∈ (Fintype.piFinset W).filter (fun τ ↦ σ = ∑ j, τ j),
      ∏ j, densityValue (lawCoeff (Dl j) (τ j)) q =
        densityValue (lawCoeff (lawProd (List.ofFn Dl)) σ) q := by
  have hy : ∀ j τ, (0 : ℝ) ≤ (((lawCoeff (Dl j) τ).eval (q : ℚ) : ℚ) : ℝ) := fun j τ ↦ by
    exact_mod_cast hnn j τ
  simp only [densityValue]
  rw [Finset.sum_congr rfl fun τ _ ↦ (ENNReal.ofReal_prod_of_nonneg fun j _ ↦ hy j (τ j)).symm,
    ← ENNReal.ofReal_sum_of_nonneg fun τ _ ↦ Finset.prod_nonneg fun j _ ↦ hy j (τ j)]
  obtain ⟨hform, hzero⟩ := law_coeff_prod_formula L Dl σ (q : ℚ)
  rw [hform, Finset.sum_filter]
  simp only [Rat.cast_sum, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_prod, Rat.cast_zero]
  refine congrArg _ (Finset.sum_subset (Fintype.piFinset_subset _ _ hW) fun τ _ hτ ↦ ?_).symm
  obtain ⟨j, hj⟩ := not_forall.1 (Fintype.mem_piFinset.not.1 hτ)
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hzero (Dl j) (τ j) hj]), ite_self]

end ProductCells

/-! ### Products of reduced forms -/

open Polynomial in
/-- A product of reduced forms has type `σ` iff all factor polynomials keep their top coefficient
and the product of the normalized factors has type `σ`. -/
private theorem form_product_mem_affineTypeEvent_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (L : ℕ)
    (d : Fin L → ℕ) (ν : ∀ j, Fin (d j + 1)) (g : ∀ j, Fin (d j + 1) → IsLocalRing.ResidueField O)
    (μ : Fin ((∑ j, d j) + 1)) (hμ : formProd d g μ = 1) (a : ∀ j, Fin (d j) → O)
    (ha : a ∈ Set.pi Set.univ (fun j => reducedFormCell O (d j) (ν j) (g j))) (σ : FactorType) :
    insertOne μ (reducedFormProduct O d ν g μ a) ∈ affineTypeEvent O (∑ j, d j) σ ↔
      (∀ j, (formPoly (insertOne (ν j) (a j))).coeff (d j) ≠ 0) ∧
        HasPolynomialTypeF O (∏ j, C (algebraMap O (BaseField O)
          ((formPoly (insertOne (ν j) (a j))).coeff (d j)))⁻¹ *
          (formPoly (insertOne (ν j) (a j))).map (algebraMap O (BaseField O))) σ := by
  have hcell : ∀ j, a j ∈ reducedFormCell O (d j) (ν j) (g j) := fun j ↦ ha j (Set.mem_univ _)
  obtain ⟨-, -, hu, -⟩ := form_product_maps_to_and_preserves O (Fin L) d ν g μ hμ a a ha ha
  set ι := algebraMap O (BaseField O)
  have hι : ∀ {x : O}, x ≠ 0 → ι x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O _)).2
  set p : Fin L → O[X] := fun j ↦ formPoly (insertOne (ν j) (a j))
  set c : Fin L → O := fun j ↦ (p j).coeff (d j)
  set F : Fin L → (BaseField O)[X] := fun j ↦ C (ι (c j))⁻¹ * (p j).map ι with hF
  set Q := ∏ j, p j
  change IsUnit (Q.coeff μ) at hu
  set u := Ring.inverse (Q.coeff μ)
  have hu0' : u ≠ 0 := left_ne_zero_of_mul_eq_one (Ring.inverse_mul_cancel _ hu)
  have hu0 : ι u ≠ 0 := hι hu0'
  have hQn : Q.coeff (∑ j, d j) = ∏ j, c j :=
    coeff_prod_sum_of_natDegree_le _ _ _ fun j _ ↦ formPoly_natDegree_le _
  have hred : insertOne μ (reducedFormProduct O d ν g μ a) =
      fun i : Fin ((∑ j, d j) + 1) ↦ u * Q.coeff i := by
    unfold reducedFormProduct
    rw [if_pos hcell]
    have := Fin.insertNth_self_removeNth μ
      (normalizeAt μ (formProd d fun j ↦ insertOne (ν j) (a j)))
    rw [normalizeAt, Pi.smul_apply, smul_eq_mul, Ring.inverse_mul_cancel
      (formProd d (fun j ↦ insertOne (ν j) (a j)) μ) hu] at this
    exact this
  have hAff : affinePolynomial O (fun i : Fin ((∑ j, d j) + 1) ↦ u * Q.coeff i) =
      C (ι u) * Q.map ι := by
    have hlt : (Q.map ι).natDegree < ∑ j, d j + 1 := Nat.lt_succ_of_le (natDegree_map_le.trans
      ((natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ ↦ formPoly_natDegree_le _)))
    conv_rhs => rw [as_sum_range' (Q.map ι) _ hlt]
    rw [affinePolynomial, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← C_mul_X_pow_eq_monomial, coeff_map, map_mul, C_mul, mul_assoc]
  have hprod : C (ι (u * Q.coeff (∑ j, d j)))⁻¹ * (C (ι u) * Q.map ι) = ∏ j, F j := by
    rw [hF, Finset.prod_mul_distrib, ← map_prod C, ← Polynomial.map_prod, hQn, map_mul, mul_inv,
      C_mul, mul_mul_mul_comm, ← C_mul, inv_mul_cancel₀ hu0, C_1, one_mul, map_prod,
      Finset.prod_inv_distrib]
  have hι' : algebraMap O (BaseField O) = ι := rfl
  simp only [affineTypeEvent, hred, Set.mem_ofPred_eq, hAff, Fin.val_last, hι', hprod]
  rw [hQn, mul_ne_zero_iff, Finset.prod_ne_zero_iff]
  simp [hu0', c, p]

open Polynomial in
/-- A product of reduced forms has type `σ` iff its factors have types `τ j` (block types at the
infinity factor) with `σ = ∑ j, τ j`. -/
private theorem form_product_type_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (L : ℕ)
    (d : Fin L → ℕ) (ν : ∀ j, Fin (d j + 1)) (g : ∀ j, Fin (d j + 1) → IsLocalRing.ResidueField O)
    (hc : FormsCoprime d g) (μ : Fin ((∑ j, d j) + 1))
    (hμ : formProd d g μ = 1) (inf : Fin L → Bool)
    (hclass : ∀ j, if inf j = true then (ν j = 0 ∧ g j = Pi.single 0 1) else ν j = Fin.last (d j))
    (hone : ∀ i j, inf i = true → inf j = true → i = j) (a : ∀ j, Fin (d j) → O)
    (ha : a ∈ Set.pi Set.univ (fun j => reducedFormCell O (d j) (ν j) (g j))) (σ : FactorType) :
    insertOne μ (reducedFormProduct O d ν g μ a) ∈ affineTypeEvent O (∑ j, d j) σ ↔
      ∃ τ : Fin L → FactorType, (∀ j, a j ∈
        if inf j = true then infinityBlockEvent O (d j) (τ j) else typeEvent O (d j) (τ j)) ∧
        σ = ∑ j, τ j := by
  -- strategy: reduce to the normalized factors `F j`, which are pairwise coprime
  rw [form_product_mem_affineTypeEvent_iff O L d ν g μ hμ a ha σ]
  have hcell : ∀ j, a j ∈ reducedFormCell O (d j) (ν j) (g j) := fun j ↦ ha j (Set.mem_univ _)
  set ι := algebraMap O (BaseField O)
  have hι : ∀ {x : O}, x ≠ 0 → ι x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O _)).2
  set p : Fin L → O[X] := fun j ↦ formPoly (insertOne (ν j) (a j))
  set c : Fin L → O := fun j ↦ (p j).coeff (d j)
  set F : Fin L → (BaseField O)[X] := fun j ↦ C (ι (c j))⁻¹ * (p j).map ι with hF
  have hpred : ∀ j, (p j).map (IsLocalRing.residue O) = formPoly (g j) := fun j ↦ by
    simp only [p, formPoly_map]; exact congrArg formPoly (hcell j).2
  have hpfin : ∀ j, inf j = false → p j = monicPolyO (a j) := fun j hj ↦ by
    have hcl := hclass j
    rw [if_neg (by simp [hj])] at hcl
    simp only [p, hcl, formPoly_insertOne_last]
  have hpinf : ∀ j, inf j = true → (p j).map (IsLocalRing.residue O) = 1 := fun j hj ↦ by
    have hcl := hclass j
    rw [if_pos hj] at hcl
    rw [hpred, hcl.2, formPoly_single_zero]
  have hmon : ∀ j, (monicPolyO (a j)).Monic := fun j ↦ (monic_poly_reconstruct O _ (a j)).1
  have hblock : ∀ j (t : FactorType),
      (a j ∈ if inf j = true then infinityBlockEvent O (d j) t else typeEvent O (d j) t) ↔
        c j ≠ 0 ∧ HasPolynomialTypeF O (F j) t := by
    intro j t
    by_cases hj : inf j = true
    · have hcl := hclass j
      rw [if_pos hj] at hcl ⊢
      simp only [infinityBlockEvent, Set.mem_ofPred_eq, F, c, p, hcl.1, ι]
    · rw [if_neg hj]
      obtain ⟨hm, hd, -⟩ := monic_poly_reconstruct O _ (a j)
      have hc1 : c j = 1 := by simp only [c, hpfin j (by simpa using hj), ← hd]; exact hm
      simp [typeEvent, hF, hc1, hpfin j (by simpa using hj), ι, monicPolyO_map_fraction]
  have hcop : (∀ j, c j ≠ 0) → ∀ i j, i ≠ j → IsCoprime (F i) (F j) := by
    intro hall i j hij
    have hU : ∀ k, IsUnit (C (ι (c k))⁻¹) := fun k ↦
      isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (hι (hall k))))
    rw [hF, isCoprime_mul_units_left (hU i) (hU j)]
    rcases hi : inf i with _ | _ <;> rcases hj : inf j with _ | _
    · rw [hpfin i hi, hpfin j hj]
      refine coprime_of_coprime_residue_dvr O (BaseField O) _ _ (hmon i) (hmon j) ?_
      rw [← hpfin i hi, ← hpfin j hj, hpred, hpred]
      exact hc.1 i j hij
    · rw [hpfin i hi]
      exact coprime_of_monic_reduction_one O (BaseField O) _ _ (hmon i) (hpinf j hj)
    · rw [hpfin j hj]
      exact (coprime_of_monic_reduction_one O (BaseField O) _ _ (hmon j) (hpinf i hi)).symm
    · exact absurd (hone i j hi hj) hij
  simp only [hblock]
  by_cases hall : ∀ j, c j ≠ 0
  · rw [coprime_family_type_iff O (Fin L) F (fun j ↦ ?_) (hcop hall) σ]
    · exact ⟨fun ⟨_, τ, h1, h2⟩ ↦ ⟨τ, fun j ↦ ⟨hall j, h1 j⟩, h2⟩,
        fun ⟨τ, h1, h2⟩ ↦ ⟨hall, τ, fun j ↦ (h1 j).2, h2⟩⟩
    have hdeg : ((p j).map ι).natDegree = d j := natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_map_le.trans (formPoly_natDegree_le _)) (by rw [coeff_map]; exact hι (hall j))
    rw [Monic, hF, leadingCoeff_mul, leadingCoeff_C, leadingCoeff, hdeg, coeff_map,
      inv_mul_cancel₀ (hι (hall j))]
  · exact ⟨fun ⟨h, _⟩ ↦ absurd h hall, fun ⟨τ, h1, _⟩ ↦ absurd (fun j ↦ (h1 j).1) hall⟩

/-- A factorization type occurring in a block event of a cell of degree `d` has degree at most
`d`, so it lies in a fixed finite set of types. -/
private theorem type_mem_of_event_nonempty (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (d : ℕ) (ν : Fin (d + 1))
    (g : Fin (d + 1) → IsLocalRing.ResidueField O) (b : Bool) (τ : FactorType)
    (h : (reducedFormCell O d ν g ∩
      (if b = true then infinityBlockEvent O d τ else typeEvent O d τ)).Nonempty) :
    τ ∈ (Finset.range (d + 1)).biUnion fun n ↦ (finite_types_of_degree n).toFinset := by
  obtain ⟨a, _, ha⟩ := h
  obtain ⟨F, hF, hdeg⟩ : ∃ F : Polynomial (BaseField O),
      HasPolynomialTypeF O F τ ∧ F.natDegree ≤ d := by
    split_ifs at ha
    · exact ⟨_, ha.2, (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_map_le.trans (formPoly_natDegree_le _))⟩
    · exact ⟨_, ha, (monic_polynomial_degree O d a).2.le⟩
  obtain ⟨hv, htd⟩ := polynomial_type_degree O F τ hF
  simp only [Finset.mem_biUnion, Finset.mem_range, Set.Finite.mem_toFinset]
  exact ⟨typeDegree τ, by omega, hv, rfl⟩

section

open MeasureTheory

/-- **Product law.** If the factor cells have laws `Dl j`, then the product cell has law
`lawProd (List.ofFn Dl)`. -/
theorem form_product_type_event_law (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (L : ℕ) (d : Fin L → ℕ) (ν : ∀ j, Fin (d j + 1))
    (g : ∀ j, Fin (d j + 1) → IsLocalRing.ResidueField O) (hgν : ∀ j, g j (ν j) = 1)
    (hc : FormsCoprime d g) (μ : Fin ((∑ j, d j) + 1)) (hμ : formProd d g μ = 1)
    (inf : Fin L → Bool)
    (hclass : ∀ j, if inf j = true then (ν j = 0 ∧ g j = Pi.single 0 1) else ν j = Fin.last (d j))
    (hone : ∀ i j, inf i = true → inf j = true → i = j) (Dl : Fin L → Law)
    (hnn : ∀ (j : Fin L) (τ : FactorType), 0 ≤ (lawCoeff (Dl j) τ).eval
      (Nat.card (IsLocalRing.ResidueField O)))
    (hlaw : ∀ (j : Fin L) (τ : FactorType), MeasurableSet
      (reducedFormCell O (d j) (ν j) (g j) ∩ (if inf j = true then infinityBlockEvent O (d j) τ
      else typeEvent O (d j) τ)) ∧ cellMeasure O (d j) (reducedFormCell O (d j) (ν j) (g j))
      (if inf j = true then infinityBlockEvent O (d j) τ else typeEvent O (d j) τ) = densityValue
      (lawCoeff (Dl j) τ) (Nat.card (IsLocalRing.ResidueField O))) (σ : FactorType) :
    MeasurableSet (reducedFormCell O (∑ j, d j) μ (formProd d g) ∩
      (insertOne μ ⁻¹' affineTypeEvent O (∑ j, d j) σ)) ∧ cellMeasure O (∑ j, d j)
      (reducedFormCell O (∑ j, d j) μ (formProd d g)) (insertOne μ ⁻¹' affineTypeEvent O (∑ j, d j)
      σ) = densityValue (lawCoeff (lawProd (List.ofFn Dl)) σ)
      (Nat.card (IsLocalRing.ResidueField O)) := by
  have hcellj := fun j => normalized_form_cell_cylinder_mass O htop (d j) (ν j) (g j) (hgν j)
  have hcellD := normalized_form_cell_cylinder_mass O htop (∑ j, d j) μ (formProd d g) hμ
  have : ∀ j, IsProbabilityMeasure (cellMeasure O (d j) (reducedFormCell O (d j) (ν j) (g j))) :=
    fun j => (hcellj j).2.2.2.2.2.1
  -- strategy: pull the event back along the form-product bijection to a finite disjoint union
  -- of products of factor events, whose product measures multiply the factor laws
  let W : Fin L → Finset FactorType := fun j => (Finset.range (d j + 1)).biUnion
    (fun n => (finite_types_of_degree n).toFinset) ∪ ((Dl j).map Prod.fst).toFinset
  have hW : ∀ j τ, (reducedFormCell O (d j) (ν j) (g j) ∩
      (if inf j = true then infinityBlockEvent O (d j) τ else typeEvent O (d j) τ)).Nonempty → τ ∈
      W j := fun j τ h ↦ Finset.mem_union_left _ (type_mem_of_event_nonempty O _ _ _ _ τ h)
  have hmeas := fun j τ ↦ (hlaw j τ).1
  set T := (Fintype.piFinset W).filter (fun τ : Fin L → FactorType => σ = ∑ j, τ j) with hT
  have hbij := form_product_bijection O (Fin L) d ν g hgν hc μ hμ
  have hpre := preimage_inter_pi_eq_biUnion _ _ _ (insertOne μ ⁻¹' affineTypeEvent O (∑ j, d j) σ)
    hbij.mapsTo (fun j τ ↦ if inf j = true then infinityBlockEvent O (d j) τ else
      typeEvent O (d j) τ) W hW σ (form_product_type_iff O L d ν g hc μ hμ inf hclass hone · · σ) T
    fun τ ↦ by rw [hT, Finset.mem_filter, Fintype.mem_piFinset]
  have hE : MeasurableSet (reducedFormCell O (∑ j, d j) μ (formProd d g) ∩
      (insertOne μ ⁻¹' affineTypeEvent O (∑ j, d j) σ)) := by
    choose c hcc using fun j ↦ (hcellj j).2.2.1
    refine measurableSet_inter_of_bijOn ?_ ?_ hbij
      (hpre ▸ Finset.measurableSet_biUnion _ fun τ _ ↦ .univ_pi fun j ↦ hmeas j (τ j))
    · convert (coordinate_cylinder_clopen O (IsLocalRing.maximalIdeal O) htop 1).2.2 (Fin L) d c
        using 3 with j
      rw [pow_one]; exact (hcellj j).2.1 (c j) (hcc j)
    · exact continuousOn_of_congruence_compatible O O (IsLocalRing.maximalIdeal O) htop
        (IsLocalRing.maximalIdeal O) htop (Fin L) d (∑ j, d j) _ _ fun L' a ha a' ha' h ↦
        (form_product_maps_to_and_preserves O (Fin L) d ν g μ hμ a a' ha ha').2.2.2 L' h
  refine ⟨hE, ?_⟩
  rw [← cellMeasure_cell_inter hcellD.2.2.2.1, measure_eq_sum_prod_of_preimage _
    (form_cells_measure_preserving O htop (Fin L) d ν g hgν hc μ hμ) _
    (form_cell_product_measure O htop (Fin L) d ν g hgν).2.1
    (fun j ↦ cellMeasure_cell_inter (hcellj j).2.2.2.1) _ hmeas (fun j τ τ' x h1 h2 ↦ by
      split_ifs at h1 h2
      exacts [polynomial_type_unique O _ _ _ h1.2 h2.2, polynomial_type_unique O _ _ _ h1 h2])
    hE T hpre, Finset.sum_congr rfl fun τ _ ↦ Finset.prod_congr rfl fun j _ ↦ (hlaw j (τ j)).2]
  exact sum_prod_densityValue_eq_lawProd Dl _ hnn W (fun _ ↦ Finset.subset_union_right) σ

end

section

variable {k : Type} [Field k]

private noncomputable def directionPoly : ClosedDirection k → Polynomial k
  | none => 1
  | some φ => φ.val

open scoped Classical in
private noncomputable def directionOfPoly (p : Polynomial k) : ClosedDirection k :=
  if hp : p.Monic ∧ Irreducible p then some ⟨p, hp⟩ else none

private lemma directionOfPoly_directionPoly (φ : AffineDirection k) :
    directionOfPoly (directionPoly (some φ)) = some φ := by
  simp [directionOfPoly, directionPoly, φ.2]

private lemma directionPoly_directionOfPoly (p : Polynomial k) (hp : p.Monic ∧ Irreducible p) :
    directionPoly (directionOfPoly p) = p := by
  simp [directionOfPoly, directionPoly, hp]

open scoped Classical in
private lemma toFinsupp_prod_directionPoly (S : Multiset (ClosedDirection k)) :
    (Multiset.toFinsupp S).prod (fun a r => directionPoly a ^ r) = (S.map directionPoly).prod := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a S ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
        Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
      ih]
    simp

open scoped Classical in
private lemma toFinsupp_sum_directionDegree (S : Multiset (ClosedDirection k)) :
    (Multiset.toFinsupp S).sum (fun a r => directionDegree k a * r) =
      (S.map (directionDegree k)).sum := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a S ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
        Finsupp.sum_add_index' (by simp) (by intros; rw [mul_add]),
      ih]
    simp

private lemma divisorAffinePolynomial_eq_prod (D : ExceptionalDivisor k) :
    divisorAffinePolynomial k D = D.prod (fun a r => directionPoly a ^ r) := by
  unfold divisorAffinePolynomial
  congr 1
  funext a r
  cases a <;> simp [directionPoly]

end

/-- Every monic polynomial of degree `n` over `k` is the affine polynomial of a unique affine
divisor of degree `n`. -/
theorem monic_polynomial_divisor (k : Type) [Field k] (n : ℕ) (G : Polynomial k) (hG : G.Monic)
    (hn : G.natDegree = n) :
    ∃! D : ExceptionalDivisor k, AffineDivisor k n D ∧ divisorAffinePolynomial k D = G := by
  classical
  set N := UniqueFactorizationMonoid.normalizedFactors G with hN
  have hG0 : G ≠ 0 := hG.ne_zero
  have hNmi : ∀ p ∈ N, p.Monic ∧ Irreducible p := fun p hp =>
    ⟨by rw [← UniqueFactorizationMonoid.normalize_normalized_factor p hp]; exact
        Polynomial.monic_normalize (UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hp),
     UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp⟩
  have hNprod : N.prod = G := by
    have := Polynomial.eq_of_monic_of_associated
      (Polynomial.monic_multiset_prod_of_monic N id (fun p hp => (hNmi p hp).1)) hG
    simp only [Multiset.map_id] at this
    apply this
    exact UniqueFactorizationMonoid.prod_normalizedFactors hG0
  have hNg : (N.map directionOfPoly).map directionPoly = N := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id N]
    exact Multiset.map_congr rfl (fun p hp => directionPoly_directionOfPoly p (hNmi p hp))
  refine ⟨Multiset.toFinsupp (N.map directionOfPoly), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · change Multiset.toFinsupp (N.map directionOfPoly) none = 0
    rw [Multiset.toFinsupp_apply, Multiset.count_eq_zero, Multiset.mem_map]
    rintro ⟨p, hp, hgp⟩
    simp [directionOfPoly, hNmi p hp] at hgp
  · unfold exceptionalDegree
    rw [toFinsupp_sum_directionDegree, Multiset.map_map, ← hn, ← hNprod,
      Polynomial.natDegree_multiset_prod_of_monic _ (fun p hp => (hNmi p hp).1)]
    congr 1
    exact Multiset.map_congr rfl (fun p hp => by simp [directionOfPoly, hNmi p hp, directionDegree])
  · rw [divisorAffinePolynomial_eq_prod, toFinsupp_prod_directionPoly, hNg, hNprod]
  · rintro D ⟨⟨hinf, hdeg⟩, hprod⟩
    set S := Finsupp.toMultiset D with hS
    have hDS : D = Multiset.toFinsupp S := (Multiset.toFinsupp_eq_iff.2 rfl).symm
    have hnone : none ∉ S := by
      rw [hS, Finsupp.mem_toMultiset]
      simpa [Finsupp.mem_support_iff, infinityDirection] using hinf
    have hSmi : ∀ p ∈ S.map directionPoly, p.Monic ∧ Irreducible p := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hp
      cases a with
      | none => exact absurd ha hnone
      | some φ => exact φ.2
    have hSprod : (S.map directionPoly).prod = G := by
      rw [← hprod, divisorAffinePolynomial_eq_prod, hDS, toFinsupp_prod_directionPoly]
    have hrel : Multiset.Rel Associated (S.map directionPoly) N := by
      apply UniqueFactorizationMonoid.factors_unique (fun p hp => (hSmi p hp).2)
        (fun p hp => UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp)
      rw [hSprod, hNprod]
      exact Associated.refl G
    have hEq : S.map directionPoly = N := by
      rw [← Multiset.rel_eq]
      refine hrel.mono ?_
      intro a ha b hb hab
      exact Polynomial.eq_of_monic_of_associated (hSmi a ha).1 (hNmi b hb).1 hab
    rw [hDS, ← hEq, Multiset.map_map]
    congr 1
    conv_lhs => rw [← Multiset.map_id S]
    refine Multiset.map_congr rfl (fun a ha => ?_)
    cases a with
    | none => exact absurd ha hnone
    | some φ => exact (directionOfPoly_directionPoly φ).symm

end SurfaceBlowup
