/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.CurveOrders
import SurfaceBlowup.Surfaces.TruncatedSeries

/-!
# Generator normalization and residue-ideal counts

We study the normal form `(1 + π u) (f + π Σ zᵢ bᵢ) = f + π h` of a perturbed generator, show that
it is unique, continuous for the `π`-adic topology and injective on coordinates, and count the
residue ideals of a crossing state `k⟦T, X⟧ ⧸ (T^a X^b)` with prescribed contacts. We also collect
length/cardinality relations for finite modules over local rings with finite residue field.

## Main results

* `unique_scaled_generator_normalization`
* `coordinate_ideal_injective`
* `crossing_residue_ideal_count`
* `crossing_state_volume`
* `finite_module_length_card`
* `pi_mul_cokernel_length`

Provenance: normalizer_inverse_equation, normalizer_generator_equation,
normalizer_preserves_adic_congruence, coordinate_transition_congruence,
unique_scaled_generator_normalization, coordinate_ideal_injective, crossing_residue_ideal_count,
crossing_state_volume, finite_module_length_card, length_scaling_of_residue_card,
pi_module_length_sum, pi_mul_cokernel_length.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-- The generator normal form of `h` is the preimage of `E h` under the adic perturbation by
  `coordinateRemainder pi b E`. -/
private theorem normalizer_inverse_equation (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ)
    (pi : O) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (h : R) :
    adicPerturb (coordinateRemainder pi b E) (generatorNormalForm pi b E h) = E h := by
  have hb := adic_perturb_bijective O ((Fin n → O) × R) (Ideal.span {pi})
    (coordinateRemainder pi b E)
    (coordinate_remainder_raises_order O R n pi b E)
  exact Function.rightInverse_invFun hb.2 (E h)

/-- The normal-form coordinates `(z, u)` of `h` satisfy `(1 + π u) (f + π Σ zᵢ bᵢ) = f + π h`. -/
theorem normalizer_generator_equation (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (pi : O) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (f : R)
    (hE : ∀ s, E.symm s = divisionMap f b s) (h : R) :
    (1 + pi • (generatorNormalForm pi b E h).2) *
      (f + pi • coordinateLift b (generatorNormalForm pi b E h).1) = f + pi • h := by
  rw [scaled_normalization_identity O R n pi f b E hE,
    normalizer_inverse_equation O R n pi b E h, LinearEquiv.symm_apply_apply]

/-- The generator normal form preserves congruence modulo `(π)^j`. -/
private theorem normalizer_preserves_adic_congruence (O R : Type) [CommRing O] [CommRing R]
    [Algebra O R]
    (n : ℕ) (pi : O) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (j : ℕ) (h k : R)
    (hhk : adicCongr (Ideal.span {pi}) j h k) :
    adicCongr (Ideal.span {pi}) j (generatorNormalForm pi b E h)
      (generatorNormalForm pi b E k) := by
  have hE := linear_map_preserves_adic_congruence O R ((Fin n → O) × R)
    (Ideal.span {pi}) E.toLinearMap j h k hhk
  simp only [LinearEquiv.coe_coe] at hE
  rw [← normalizer_inverse_equation O R n pi b E h,
    ← normalizer_inverse_equation O R n pi b E k] at hE
  exact (adic_perturb_congruence_iff O ((Fin n → O) × R) (Ideal.span {pi})
    (coordinateRemainder pi b E)
    (coordinate_remainder_raises_order O R n pi b E) j _ _).mp hE

/-- The transition between the coordinates of two normalizations preserves congruence modulo
  `(π)^j`. -/
theorem coordinate_transition_congruence (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) (pi : O) (b : Fin n → R)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (c : Fin n → R)
    (F : R ≃ₗ[O] ((Fin n → O) × R)) (h0 : R) (j : ℕ) (z w : Fin n → O)
    (hzw : adicCongr (Ideal.span {pi}) j z w) :
    adicCongr (Ideal.span {pi}) j (idealTransition pi b c F h0 z)
      (idealTransition pi b c F h0 w) := by
  let L : (Fin n → O) →ₗ[O] R :=
    { toFun := fun z => coordinateLift b z
      map_add' := by
        intro x y
        simp [coordinateLift, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        simp [coordinateLift, Finset.smul_sum, smul_smul] }
  have h1 := linear_map_preserves_adic_congruence O _ _ (Ideal.span {pi}) L j z w hzw
  have h2 : adicCongr (Ideal.span {pi}) j (h0 + coordinateLift b z) (h0 + coordinateLift b w) := by
    unfold adicCongr at h1 ⊢
    have : h0 + coordinateLift b z - (h0 + coordinateLift b w) = L z - L w := by
      simp only [add_sub_add_left_eq_sub]; rfl
    rw [this]; exact h1
  have h3 := normalizer_preserves_adic_congruence O R n pi c F j _ _ h2
  exact linear_map_preserves_adic_congruence O _ _ (Ideal.span {pi})
    (LinearMap.fst O (Fin n → O) R) j _ _ h3

/-- Every `f + π h` is uniquely of the form `(1 + π u) (f + π Σ zᵢ bᵢ)`. -/
theorem unique_scaled_generator_normalization (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) [IsDomain R] (pi : O) (hpi : algebraMap O R pi ≠ 0) (f : R) (b : Fin n → R)
    (E : R ≃ₗ[O] ((Fin n → O) × R)) (hE : ∀ s, E.symm s = divisionMap f b s)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (h : R) :
    ∃! s : (Fin n → O) × R, (1 + pi • s.2) * (f + pi • coordinateLift b s.1) = f + pi • h := by
  have hbij := adic_perturb_bijective O _ (Ideal.span {pi})
    (coordinateRemainder pi b E)
    (coordinate_remainder_raises_order O R n pi b E)
  have key : ∀ s : (Fin n → O) × R,
      (1 + pi • s.2) * (f + pi • coordinateLift b s.1) = f + pi • h ↔
        adicPerturb (coordinateRemainder pi b E) s = E h := by
    intro s
    rw [scaled_normalization_identity O R n pi f b E hE s]
    constructor
    · intro hs
      have h1 := add_left_cancel hs
      rw [Algebra.smul_def, Algebra.smul_def] at h1
      have h2 := mul_left_cancel₀ hpi h1
      rw [← h2]; simp
    · intro hs
      rw [hs]; simp
  obtain ⟨s, hs⟩ := hbij.2 (E h)
  refine ⟨s, (key s).2 hs, fun t ht => hbij.1 (((key t).1 ht).trans hs.symm)⟩

/-- Over a local domain in which `π` is a nonzero nonunit, the normalized ideal
  `coordinateIdeal pi f b z` determines the coordinates `z`. -/
theorem coordinate_ideal_injective (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (pi : O) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] [IsDomain R] [IsLocalRing R]
    (hp0 : algebraMap O R pi ≠ 0) (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (f : R)
    (hE : ∀ s, E.symm s = divisionMap f b s)
    (hf : Function.Injective (fun x : R ⧸ Ideal.span {algebraMap O R pi} =>
      x * Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) f))
    :
    Function.Injective (coordinateIdeal pi f b) := by
  set I := Ideal.span {algebraMap O R pi} with hI
  have hIne : I ≠ ⊤ := by
    intro h
    have : I ≤ IsLocalRing.maximalIdeal R := by
      rw [hI, Ideal.span_le]; simpa using hpm
    exact IsLocalRing.maximalIdeal.isMaximal R |>.ne_top (top_le_iff.mp (h ▸ this))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have hfbar : Ideal.Quotient.mk I f ≠ 0 := by
    intro h0
    have := @hf 0 1 (by simp [h0])
    exact zero_ne_one this
  have hmk : ∀ z : Fin n → O,
      Ideal.Quotient.mk I (f + pi • coordinateLift b z) = Ideal.Quotient.mk I f := by
    intro z
    rw [Ideal.Quotient.eq]
    simp only [add_sub_cancel_left, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  intro z1 z2 hz
  simp only [coordinateIdeal, normalizedIdeal, normalizedGenerator, coordinateLift_smul_eq_mul,
    ← Algebra.smul_def] at hz
  have hg1 : f + pi • coordinateLift b z1 ≠ 0 := by
    intro h0
    apply hfbar
    rw [← hmk z1, h0, map_zero]
  obtain ⟨u, hu⟩ := regular_principal_generators_associated R _ _
    (fun x y hxy => mul_right_cancel₀ hg1 hxy) hz
  have hubar : Ideal.Quotient.mk I (u : R) = 1 := by
    apply hf
    have := congrArg (Ideal.Quotient.mk I) hu
    rw [map_mul, hmk, hmk] at this
    simpa using this.symm
  have : (u : R) - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, hubar, map_one]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp this
  obtain ⟨s, _, huniq⟩ := unique_scaled_generator_normalization O R n pi hp0 f b E hE
    (coordinateLift b z2)
  have e1 := huniq (z1, v) (by
    simp only [Algebra.smul_def] at hu ⊢
    rw [hu]; congr 1; linear_combination hv)
  have e2 := huniq (z2, 0) (by simp)
  exact congrArg Prod.fst (e1.trans e2.symm)

/-- The number of crossing residue ideals of `k⟦T, X⟧ ⧸ (T^a X^b)` with contacts `c` with `T` and
  `h` with `X` is `(q - 1) q^(ac + bh - c - h)`, where `q = #k`. -/
theorem crossing_residue_ideal_count (k : Type) [Field k] [Finite k] (a b c h : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hh : 0 < h) :
    Nat.card (crossingResidueIdeals k a b c h) = (Nat.card k-1)*(Nat.card k)^(a*c+b*h-c-h) := by
  have hcN : c ≤ a * c := Nat.le_mul_of_pos_left c ha
  have hhN : h ≤ b * h := Nat.le_mul_of_pos_left h hb
  set N := a*c+b*h with hNdef
  let P : TwoSeries k → Prop := fun F => axisQuotientLength k 0 F = c ∧ axisQuotientLength k 1 F = h
  have hlen : ∀ F, P F →
      Module.length (TwoSeries k) (TwoSeries k ⧸ (monomialIdeal k a b ⊔ Ideal.span {F})) = N := by
    intro F hF
    have h5 := length_double_quotient_eq (TwoSeries k) (monomialIdeal k a b) (Ideal.span {F})
    rw [Ideal.map_span, Set.image_singleton] at h5
    rw [← h5, crossing_special_fiber_length k a b c h ha hb _
      (by rw [contact_fiberT_eq_axisQuotientLength k a b ha, hF.1])
      (by rw [contact_fiberX_eq_axisQuotientLength k a b hb, hF.2]), hNdef]
    push_cast; rfl
  have : Finite (IsLocalRing.ResidueField (TwoSeries k)) :=
    .of_equiv _ (twoSeriesResidueEquiv k).toEquiv.symm
  have hmemS : ∀ j < N+1, ((0:ℕ), j) ∈ truncIndex a b (N+1) := by
    intro j hj; simp [truncIndex]; omega
  have hmemS' : ∀ i < N+1, (i, (0:ℕ)) ∈ truncIndex a b (N+1) := by
    intro i hi; simp [truncIndex]; omega
  have hEj : ∀ j, truncExponent ((0:ℕ), j) = Finsupp.single 1 j := by simp [truncExponent]
  have hEi : ∀ i, truncExponent (i, (0:ℕ)) = Finsupp.single 0 i := by simp [truncExponent]
  let A1 : Finset (truncIndex a b (N+1)) := Finset.univ.filter (fun s => s.1.1 = 0 ∧ s.1.2 < c)
  let A2 : Finset (truncIndex a b (N+1)) := Finset.univ.filter (fun s => s.1.2 = 0 ∧ s.1.1 < h)
  let B : Finset (truncIndex a b (N+1)) :=
    {⟨(0,c), hmemS c (by omega)⟩, ⟨(h,0), hmemS' h (by omega)⟩}
  have hA1 : A1.card = c := card_truncIndex_axis_segment a b _ c Prod.fst Prod.snd ((0, ·))
    (fun _ => ⟨rfl, rfl⟩) (fun x h => Prod.ext h.symm rfl) fun j hj => hmemS j (by omega)
  have hA2 : A2.card = h := card_truncIndex_axis_segment a b _ h Prod.snd Prod.fst ((·, 0))
    (fun _ => ⟨rfl, rfl⟩) (fun x h => Prod.ext rfl h.symm) fun i hi => hmemS' i (by omega)
  have hA12 : (A1 ∩ A2).card = 1 := by
    rw [Finset.card_eq_one]; refine ⟨⟨(0,0), hmemS 0 (by omega)⟩, ?_⟩
    ext ⟨⟨i, j⟩, hij⟩
    simp only [A1, A2, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
    omega
  have hA := Finset.card_union_add_card_inter A1 A2
  have hB : B.card = 2 := by
    rw [Finset.card_pair]
    simp only [ne_eq, Subtype.mk.injEq, Prod.mk.injEq]
    omega
  have hAB : Disjoint (A1 ∪ A2) B := by
    rw [Finset.disjoint_left]
    rintro ⟨⟨i, j⟩, hij⟩ hs hs'
    simp only [A1, A2, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq] at hs hs'
    omega
  have hcrit : ∀ F, P F ↔ (∀ s ∈ A1 ∪ A2, truncCoeffs k a b (N+1) F s = 0) ∧
      (∀ s ∈ B, truncCoeffs k a b (N+1) F s ≠ 0) := by
    intro F
    change axisQuotientLength k 0 F = c ∧ axisQuotientLength k 1 F = h ↔ _
    rw [axisQuotientLength_eq_iff k (by decide : (0 : Fin 2) ≠ 1),
      axisQuotientLength_eq_iff k (by decide : (1 : Fin 2) ≠ 0)]
    simp only [B, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      truncCoeffs_apply, hEj, hEi]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h1', h2'⟩⟩
      refine ⟨fun ⟨⟨i, j⟩, hij⟩ hs => ?_, h2, h2'⟩
      simp only [A1, A2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rcases hs with ⟨rfl, hj⟩ | ⟨rfl, hi⟩
      · rw [hEj]; exact h1 j hj
      · rw [hEi]; exact h1' i hi
    · rintro ⟨h1, h2, h2'⟩
      refine ⟨⟨fun j hj => ?_, h2⟩, ⟨fun i hi => ?_, h2'⟩⟩
      · simpa [hEj] using h1 ⟨(0, j), hmemS j (by omega)⟩ (by simp [A1, hj])
      · simpa [hEi] using h1 ⟨(i, 0), hmemS' i (by omega)⟩ (by simp [A2, hi])
  have key := principal_residue_ideal_count k a b N ha P
    (fun f => contact f (fiberT k a b) = c ∧ contact f (fiberX k a b) = h)
    (fun F => by
      rw [contact_fiberT_eq_axisQuotientLength k a b ha,
        contact_fiberX_eq_axisQuotientLength k a b hb])
    (fun U F hU hF => by
      change axisQuotientLength k 0 _ = c ∧ axisQuotientLength k 1 _ = h
      rwa [axisQuotientLength, axisQuotientLength, Ideal.span_singleton_mul_left_unit hU])
    hlen (fun F hF => by
      rw [finite_length_module_card (TwoSeries k) _ _ (hlen F hF),
        Nat.card_congr (twoSeriesResidueEquiv k).toEquiv])
    (A1 ∪ A2) B hAB (Finset.insert_nonempty _ _) hcrit
  rw [show (A1 ∪ A2).card + B.card - 1 = c + h by omega, hB,
    show N = c + h + (N - c - h) by omega, pow_add _ (c + h)] at key
  have hp : 0 < Nat.card k - 1 := by have := Finite.one_lt_card (α := k); omega
  have hpos : 0 < (Nat.card k - 1) * Nat.card k ^ (c + h) :=
    Nat.mul_pos hp (pow_pos Nat.card_pos _)
  unfold crossingResidueIdeals
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [sq] at key
  linarith [key]

/-- The total state measure of a crossing state with contacts `c` and `h` is `(q - 1) q^(-(c + h))`,
  where `q` is the residue cardinality. -/
theorem crossing_state_volume (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) [CommRing R] [Algebra O R]
    [MeasurableSpace (Ideal R)] (pi : O) (X : Set (Ideal R))
    (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hh : 0 < h)
    (A : IdealAtlas O R pi (a * c + b * h) X)
    (hA : ∀ i, Measurable (coordinateIdeal pi (A.chart i).f (A.chart i).b))
    (hcount : Nonempty (A.ι ≃ crossingResidueIdeals (IsLocalRing.ResidueField O) a b c h)) :
    stateMeasure O R pi (a*c+b*h) (Nat.card (IsLocalRing.ResidueField O)) A Set.univ =
      ((Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞) - 1) *
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(c+h) := by
  rw [state_measure_total_mass O R htop pi (a*c+b*h) X A hA]
  obtain ⟨e⟩ := hcount
  have hcard : Fintype.card A.ι = (Nat.card (IsLocalRing.ResidueField O) - 1) *
      (Nat.card (IsLocalRing.ResidueField O)) ^ (a*c+b*h-c-h) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
    exact crossing_residue_ideal_count _ a b c h ha hb hc hh
  rw [hcard]
  set q := Nat.card (IsLocalRing.ResidueField O)
  have hq : 1 ≤ q := Nat.card_pos
  have hN : a*c+b*h = (a*c+b*h-c-h) + (c+h) := by
    have : c ≤ a*c := Nat.le_mul_of_pos_left c ha
    have : h ≤ b*h := Nat.le_mul_of_pos_left h hb
    omega
  have hq0 : (q:ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqt : (q:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  set m := a*c+b*h-c-h
  rw [hN, pow_add, Nat.cast_mul, ENNReal.natCast_sub, Nat.cast_pow, Nat.cast_one]
  have : (q:ℝ≥0∞)^m * (q:ℝ≥0∞)⁻¹^m = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel hq0 hqt, one_pow]
  calc ((q:ℝ≥0∞) - 1) * (q:ℝ≥0∞)^m * ((q:ℝ≥0∞)⁻¹^m * (q:ℝ≥0∞)⁻¹^(c+h))
      = ((q:ℝ≥0∞) - 1) * ((q:ℝ≥0∞)^m * (q:ℝ≥0∞)⁻¹^m) * (q:ℝ≥0∞)⁻¹^(c+h) := by ring
    _ = _ := by rw [this, mul_one]

/-- A finite module over a local ring with residue field of cardinality `q` has finite length `ℓ`
  and cardinality `q ^ ℓ`. -/
theorem finite_module_length_card (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (M : Type) [AddCommGroup M] [Module O M] [Finite M] :
    ∃ ℓ : ℕ, Module.length O M = ℓ ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ ℓ := by
  have hN : IsNoetherian O M := isNoetherian_of_finite O M
  have hA : IsArtinian O M := isArtinian_of_finite
  have hF : IsFiniteLength O M := isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨hN, hA⟩
  have hne : Module.length O M ≠ ⊤ := Module.length_ne_top_iff.mpr hF
  obtain ⟨ℓ, hℓ⟩ := ENat.ne_top_iff_exists.mp hne
  exact ⟨ℓ, hℓ.symm, finite_length_module_card O M ℓ hℓ.symm⟩

/-- If `#k(O') = #k(O) ^ δ`, then a module of `O'`-length `ℓ` has `O`-length `δ ℓ`. -/
theorem length_scaling_of_residue_card (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (O' : Type) [CommRing O'] [IsLocalRing O']
    [Finite (IsLocalRing.ResidueField O')] (δ : ℕ)
    (hδ : Nat.card (IsLocalRing.ResidueField O') = Nat.card (IsLocalRing.ResidueField O) ^ δ)
    (M : Type) [AddCommGroup M] [Module O M] [Module O' M] (ℓ : ℕ) (hℓ : Module.length O' M = ℓ) :
    Module.length O M = ((δ * ℓ : ℕ) : ℕ∞) := by
  have h1 := finite_length_module_card O' M ℓ hℓ
  have hq : 2 ≤ Nat.card (IsLocalRing.ResidueField O) := by
    have := Finite.one_lt_card (α := IsLocalRing.ResidueField O)
    omega
  have hne : Nat.card M ≠ 0 := by
    rw [h1, hδ, ← pow_mul]
    exact pow_ne_zero _ (by omega)
  have : Finite M := Nat.finite_of_card_ne_zero hne
  obtain ⟨l, hl, hc⟩ := finite_module_length_card O M
  rw [hl]
  congr 1
  rw [h1, hδ, ← pow_mul] at hc
  exact (Nat.pow_right_injective hq hc).symm

/-- The length of a finite product of finite-length modules is the sum of the lengths. -/
private theorem pi_module_length_sum (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (ι : Type) [Fintype ι] (M : ι → Type)
    [∀ j, AddCommGroup (M j)] [∀ j, Module O (M j)] (ℓ : ι → ℕ)
    (hℓ : ∀ j, Module.length O (M j) = ℓ j) :
    Module.length O (∀ j, M j) = ((∑ j, ℓ j : ℕ) : ℕ∞) := by
  have hc := fun j => finite_length_module_card O (M j) (ℓ j) (hℓ j)
  set q := Nat.card (IsLocalRing.ResidueField O) with hq
  have hq2 : 2 ≤ q := by
    have : Nontrivial (IsLocalRing.ResidueField O) := inferInstance
    have : Finite (IsLocalRing.ResidueField O) := inferInstance
    exact Nat.succ_le_of_lt (Finite.one_lt_card)
  have hfin : ∀ j, Finite (M j) := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hc j]; positivity)
  have : Finite (∀ j, M j) := inferInstance
  obtain ⟨l, hl, hcard⟩ := finite_module_length_card O (∀ j, M j)
  have h2 : Nat.card (∀ j, M j) = q ^ (∑ j, ℓ j) := by
    rw [Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl (fun j _ => hc j)
  rw [hl]
  have : l = ∑ j, ℓ j := Nat.pow_right_injective hq2 (hcard.symm.trans h2)
  rw [this]

/-- The cokernel of multiplication by `e` on `(Π C_j) ⧸ (g)` has length
  `Σ_j length (C_j ⧸ (g_j, e_j))`. -/
theorem pi_mul_cokernel_length (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (ι : Type) [Fintype ι] (C : ι → Type)
    [∀ j, CommRing (C j)] [∀ j, Algebra O (C j)] (g e : ∀ j, C j) (ℓ : ι → ℕ)
    (hℓ : ∀ j, Module.length O (C j ⧸ (Ideal.span {g j} ⊔ Ideal.span {e j})) = ℓ j) :
    Module.length O (((∀ j, C j) ⧸ Ideal.span {g}) ⧸
      LinearMap.range (LinearMap.mulLeft O (Ideal.Quotient.mk (Ideal.span {g}) e))) =
      ((∑ j, ℓ j : ℕ) : ℕ∞) := by
  obtain ⟨φ, -⟩ := quotient_mul_range_equiv O (∀ j, C j) (Ideal.span {g}) e
  obtain ⟨-, ψ', -⟩ := pi_quotient_span_linearEquiv O ι C g e
  rw [φ.length_eq, ψ'.length_eq]
  exact pi_module_length_sum O ι _ ℓ hℓ

end SurfaceBlowup
