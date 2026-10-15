/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Recursion.OrderDefect

/-!
# Haar measures on unramified extensions and strict-transform normalizations

For an unramified lift `Φ` over a complete DVR `O` with finite residue field, `O[x] ⧸ (Φ)` is again
such a DVR whose Haar measure is the product of coordinate Haar measures in the power basis. We also
compute strict transforms of principal ideals, show that the scaled strict normalizer pushes Haar
measure forward like its linear part, construct the linear part of a member center with its cokernel
length, and show that algebra types descend to factors of a product.

## Main results

* `strict_transform_ideal_of_generator`: if `α f = e^d g` with `e` regular, the strict transform
  of `(f)` is `(g)`.
* `unramified_extension_measure_package`, `unramified_coefficient_measure_pi`: `O[x] ⧸ (Φ)` is a
  complete DVR whose coefficient Haar measure is the product of power-coordinate measures.
* `strict_normalizer_pushforward_linear`: the scaled strict normalizer pushes Haar measure forward
  like its scaled linear part.
* `member_center_linear_part`: the linear part at a member center is injective, has a scaled
  inverse, and has cokernel length `s · deg - tri(cellDegree)`.
* `algebra_type_children_exists`: algebra types descend to the factors of a product.

Provenance: strict_transform_ideal_of_generator, power_coordinates_isAdic,
unramified_extension_measure_package, unramified_coefficient_measure_pi,
strict_normalizer_pushforward_linear, member_center_linear_part,
algebra_type_pi_factor, algebra_type_children_exists.
-/

open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-- If `α f = e^d g` with `e` a nonzerodivisor, then the strict transform of `(f)` is `(g)`. -/
theorem strict_transform_ideal_of_generator (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (alpha : R →ₐ[O] C) (e g : C) (d : ℕ) (f : R)
    (hf : alpha f = e ^ d * g) (he : Function.Injective (fun z : C => e * z)) :
    strictTransformIdeal alpha e d (Ideal.span {f}) = Ideal.span {g} := by
  have hinj : ∀ n : ℕ, ∀ a b : C, e ^ n * a = e ^ n * b → a = b := by
    intro n
    induction n with
    | zero => intro a b h; simpa using h
    | succ n ih =>
      intro a b h
      apply ih
      apply he
      simp only [pow_succ] at h
      simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hmap : (Ideal.span {f}).map alpha.toRingHom = Ideal.span {e ^ d * g} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp [hf]
  ext u
  unfold strictTransformIdeal
  rw [hmap, Submodule.mem_colon_singleton, Ideal.mem_span_singleton', Ideal.mem_span_singleton']
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, hinj d _ _ ?_⟩
    calc e ^ d * (v * g) = v * (e ^ d * g) := by ring
      _ = u • e ^ d := hv
      _ = e ^ d * u := by simp [mul_comm]
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    calc v * (e ^ d * g) = e ^ d * (v * g) := by ring
      _ = u • e ^ d := by rw [hv]; simp [mul_comm]

/-- On `O[x] ⧸ (Φ)` with the power-coordinate topology, the topology is adic for the base ideal
  `𝔪 O[x] ⧸ (Φ)`. -/
private theorem power_coordinates_isAdic (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (Φ : Polynomial O) (hm : Φ.Monic)
    [TopologicalSpace (AdjoinRoot Φ)]
    (hτ : ‹TopologicalSpace (AdjoinRoot Φ)› = unramifiedTopology O Φ hm) [IsDiscreteValuationRing O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) :
    IsAdic (baseIdeal O Φ) := by
  let _ : MeasurableSpace (AdjoinRoot Φ) := unramifiedMeasurableSpace O Φ hm
  obtain ⟨hTR, -, -, -, -, hcont, -⟩ :=
    power_coordinates_transport O Φ hm hτ rfl
  set e := powerCoordinates O Φ hm with he
  set m := IsLocalRing.maximalIdeal O
  have hB := finite_coordinate_cylinder_basis O m htop Φ.natDegree
  -- coordinates of I^L
  have hpre : ∀ L : ℕ, ((baseIdeal O Φ ^ L : Ideal _) : Set (AdjoinRoot Φ)) =
      e ⁻¹' {v | adicCongr m L v 0} := by
    intro L
    ext x
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_ofPred_eq,
      finite_coordinate_adic_congruence, Pi.zero_apply, sub_zero]
    rw [base_ideal_coordinates O Φ hm L x]
    exact Iff.rfl
  have hopenB : ∀ L : ℕ, IsOpen {v : Fin Φ.natDegree → O | adicCongr m L v 0} := fun L =>
    hB.isOpen (Or.inr ⟨L, 0, rfl⟩)
  rw [isAdic_iff]
  refine ⟨fun L => ?_, fun s hs => ?_⟩
  · rw [hpre L]; exact (hopenB L).preimage hcont
  · have hs' : s ∈ Filter.comap e (nhds (e 0)) := by
      subst hτ
      rw [← nhds_induced]; exact hs
    rw [map_zero] at hs'
    obtain ⟨V, hV, hVs⟩ := Filter.mem_comap.1 hs'
    obtain ⟨W, hW, h0W, hWV⟩ := hB.mem_nhds_iff.1 hV
    rcases hW with rfl | ⟨L, x, rfl⟩
    · exact absurd h0W (Set.notMem_empty _)
    refine ⟨L, ?_⟩
    rw [hpre L]
    intro y hy
    apply hVs
    apply hWV
    have R := adic_congruence_rules O (Fin Φ.natDegree → O) m
    exact R.2.2.1 L _ _ _ hy h0W

/-- For an unramified lift `Φ`, the ring `O[x] ⧸ (Φ)` is a complete DVR with residue field of
  cardinality `q^(deg Φ)`, carrying a compact second-countable Borel topology that is adic for its
  maximal ideal. -/
theorem unramified_extension_measure_package (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [TopologicalSpace (AdjoinRoot Φ)] [MeasurableSpace (AdjoinRoot Φ)]
    (hτ : ‹TopologicalSpace (AdjoinRoot Φ)› = unramifiedTopology O Φ hΦ.1)
    (hmeas : ‹MeasurableSpace (AdjoinRoot Φ)› = unramifiedMeasurableSpace O Φ hΦ.1) :
    ∃ (_ : IsDomain (AdjoinRoot Φ)) (_ : IsLocalRing (AdjoinRoot Φ)), True ∧
      IsDiscreteValuationRing (AdjoinRoot Φ) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (AdjoinRoot Φ)) (AdjoinRoot Φ) ∧
      Finite (IsLocalRing.ResidueField (AdjoinRoot Φ)) ∧
      Nat.card (IsLocalRing.ResidueField (AdjoinRoot Φ)) = residueCard O ^ Φ.natDegree ∧
      IsTopologicalRing (AdjoinRoot Φ) ∧ CompactSpace (AdjoinRoot Φ) ∧ T2Space (AdjoinRoot Φ) ∧
      SecondCountableTopology (AdjoinRoot Φ) ∧ BorelSpace (AdjoinRoot Φ) ∧
      IsAdic (IsLocalRing.maximalIdeal (AdjoinRoot Φ)) := by
  obtain ⟨d, l, hdvr, hmax, -, hcomp, hfin, hcard⟩ := unramified_is_dvr O Φ hΦ
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := power_coordinates_transport O Φ hΦ.1 hτ hmeas
  have hadic := power_coordinates_isAdic O Φ hΦ.1 hτ htop
  have hdeg : 0 < Φ.natDegree := by
    have := (unramified_free_module O Φ hΦ.1).2.2
    have hf : Module.finrank O (AdjoinRoot Φ) ≠ 0 := by
      have : Nontrivial (AdjoinRoot Φ) := d.toNontrivial
      have := (unramified_free_module O Φ hΦ.1).1
      have := (unramified_free_module O Φ hΦ.1).2.1
      exact Module.finrank_pos.ne'
    omega
  have hinj : Function.Injective (algebraMap O (AdjoinRoot Φ)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hm : ∀ L : ℕ, c ∈ (IsLocalRing.maximalIdeal O)^L := fun L =>
      (base_ideal_pure O Φ hΦ.1 hdeg L c).1 (by rw [hc]; exact Ideal.zero_mem _)
    have := Ideal.iInf_pow_eq_bot_of_isDomain (IsLocalRing.maximalIdeal O)
      ((IsLocalRing.maximalIdeal.isMaximal O).ne_top)
    rw [← Ideal.mem_bot, ← this]
    exact Ideal.mem_iInf.2 hm
  exact ⟨d, l, trivial, hdvr, hcomp, hfin, hcard, h1, h2, h3, h4, h5, by rw [hmax]; exact hadic⟩

/-- On `O[x] ⧸ (Φ)` the coefficient Haar measure is the product of the power-coordinate measures,
  and a ball of radius `L` in `r` coordinates has mass `q^(-deg Φ · r · L)`. -/
theorem unramified_coefficient_measure_pi (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [TopologicalSpace (AdjoinRoot Φ)] [MeasurableSpace (AdjoinRoot Φ)]
    (hτ : ‹TopologicalSpace (AdjoinRoot Φ)› = unramifiedTopology O Φ hΦ.1)
    (hmeas : ‹MeasurableSpace (AdjoinRoot Φ)› = unramifiedMeasurableSpace O Φ hΦ.1)
    [IsDomain (AdjoinRoot Φ)] [IsTopologicalRing (AdjoinRoot Φ)] [CompactSpace (AdjoinRoot Φ)]
    [T2Space (AdjoinRoot Φ)] [SecondCountableTopology (AdjoinRoot Φ)] [BorelSpace (AdjoinRoot Φ)]
    [MeasureTheory.SigmaFinite (unramifiedCoefficientMeasure O Φ hΦ.1)] (r : ℕ) :
    coefficientMeasure (AdjoinRoot Φ) r =
      MeasureTheory.Measure.pi (fun _ : Fin r => unramifiedCoefficientMeasure O Φ hΦ.1) ∧
      ∀ (L : ℕ) (a : Fin r → AdjoinRoot Φ),
      coefficientMeasure (AdjoinRoot Φ) r {b | ∀ j, b j - a j ∈ (baseIdeal O Φ) ^ L} =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (Φ.natDegree * r * L) := by
  obtain ⟨_, _, _, _, _, _, hcard, _, _, _, _, _, hadic⟩ :=
    unramified_extension_measure_package O htop Φ hΦ hτ hmeas
  obtain ⟨_, _, _, hmax, -⟩ := unramified_is_dvr O Φ hΦ
  obtain ⟨hH, hP, -⟩ :=
    unramified_coefficient_measure_haar O Φ hΦ.1 hτ hmeas htop
  have hprob := coefficient_measure_probability (AdjoinRoot Φ) hadic r
  have hμ : MeasureTheory.Measure.IsAddHaarMeasure (coefficientMeasure (AdjoinRoot Φ) r) := by
    unfold coefficientMeasure
    apply MeasureTheory.Measure.IsAddHaarMeasure.smul
    · exact ENNReal.inv_ne_zero.mpr (MeasureTheory.measure_ne_top _ _)
    · exact ENNReal.inv_ne_top.mpr
        (MeasureTheory.Measure.IsOpenPosMeasure.open_pos _ isOpen_univ Set.univ_nonempty)
  refine ⟨MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _, ?_⟩
  intro L a
  have h := coefficient_cylinder_mass (AdjoinRoot Φ) hadic r L a
  rw [hmax, hcard] at h
  rw [h, Nat.cast_pow, ← ENNReal.inv_pow, ← pow_mul, mul_assoc, ENNReal.inv_pow]

/-- The scaled strict normalizer pushes an invariant probability measure forward to the same measure
  as its scaled linear part. -/
theorem strict_normalizer_pushforward_linear (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (H : (Fin n → O) →ₗ[O] R) (k : ℕ)
    (ha : k < a) (Q : (Fin n → O) →ₗ[O] (Fin n → O))
    (hQ : ∀ w, normalizationLinearPart E H (Q w) = (pi ^ k) • w)
    [IsAdicComplete (Ideal.span {pi}) (Fin n → O)] [MeasurableSpace (Fin n → O)]
    [MeasurableAdd (Fin n → O)]
    (hgen : ‹MeasurableSpace (Fin n → O)› = adicCylinderSpace (Ideal.span {pi}) (Fin n → O))
    (mu : MeasureTheory.Measure (Fin n → O)) [MeasureTheory.IsProbabilityMeasure mu]
    [MeasureTheory.Measure.IsAddLeftInvariant mu]
    (hfinite : ∀ j, Finite (AdicQuotient (Ideal.span {pi}) (Fin n → O) j))
    (hL : Measurable (fun z : Fin n → O => (pi^a) • normalizationLinearPart E H z)) :
    mu.map (scaledStrictMap pi a b E H) =
      mu.map (fun z : Fin n → O => (pi^a) • normalizationLinearPart E H z) := by
  have hr := strict_correction_raises_order O R n pi a b E H k ha Q
  have hP := adic_perturb_measure_preserving O (Fin n → O) (Ideal.span {pi})
    _ hr mu hgen hfinite
  have hfun : scaledStrictMap pi a b E H =
      (fun z : Fin n → O => (pi^a) • normalizationLinearPart E H z) ∘
        adicPerturb (normalizationCorrection pi a k b E H Q) := by
    funext z
    exact strict_normalizer_factors_through_linear O R n pi a b E H k ha Q hQ z
  rw [hfun, ← MeasureTheory.Measure.map_map hL hP.measurable, hP.map_eq]

/-- If each `g j` generates a state ideal of the child `mc j`, then the parameters `e j = t_j`
  act injectively on `Π R_j ⧸ (g)`. -/
private theorem child_quotient_mul_parameter_injective (m : ConcreteMember)
    (c : m.toMeasured.cellIndex) (mc : m.toMeasured.childIdx c → ConcreteMember)
    (e g : ∀ j, (mc j).toMeasured.R) (he : ∀ j, e j = (mc j).toMeasured.S.t)
    (hgj : ∀ j, Ideal.span {g j} ∈ (mc j).toMeasured.stateSet) :
    Function.Injective (fun y : (∀ j, (mc j).toMeasured.R) ⧸ Ideal.span {g} =>
      Ideal.Quotient.mk (Ideal.span {g}) e * y) := by
  have hmem : ∀ x : ∀ j, (mc j).toMeasured.R, x ∈ Ideal.span {g} ↔ ∀ j, x j ∈ Ideal.span {g j} :=
    fun x ↦ by rw [← Ideal.pi_span, Ideal.mem_pi]
  intro x y hxy
  induction x using Quotient.inductionOn' with | h x => ?_
  induction y using Quotient.inductionOn' with | h y => ?_
  change Ideal.Quotient.mk _ e * Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ e *
    Ideal.Quotient.mk _ y at hxy
  change Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ y
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at hxy
  rw [Ideal.Quotient.eq, hmem]
  intro j
  have h0 : Ideal.Quotient.mk (Ideal.span {g j}) (mc j).toMeasured.S.t *
      Ideal.Quotient.mk _ ((x - y) j) = Ideal.Quotient.mk _ (mc j).toMeasured.S.t * 0 := by
    rw [mul_zero, ← map_mul, ← he j, Ideal.Quotient.eq_zero_iff_mem]
    simpa using (hmem _).1 hxy j
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (concrete_member_state_generator_transverse (mc j) (g j) (hgj j)).2 h0

/-- The linear part of the normalization at a member center is injective, admits a scaled inverse,
  and has cokernel of length `s · deg - tri(cellDegree)`. -/
theorem member_center_linear_part (m : ConcreteMember) (c : m.toMeasured.cellIndex)
    (mc : m.toMeasured.childIdx c → ConcreteMember)
    [∀ j, Algebra m.toMeasured.O (mc j).toMeasured.O]
    [∀ j, Algebra m.toMeasured.O (mc j).toMeasured.R]
    [∀ j, IsScalarTower m.toMeasured.O (mc j).toMeasured.O (mc j).toMeasured.R]
    (hcard : ∀ j, (mc j).toMeasured.q = m.toMeasured.q ^ m.toMeasured.childDelta c j)
    (alpha : ∀ j, m.toMeasured.R →ₐ[m.toMeasured.O] (mc j).toMeasured.R)
    (e : ∀ j, (mc j).toMeasured.R) (he : ∀ j, e j = (mc j).toMeasured.S.t)
    (hbij : Set.BijOn
      (fun (J : Ideal m.toMeasured.R) (j : m.toMeasured.childIdx c) => strictTransformIdeal
      (alpha j) (e j) (m.toMeasured.cellDegree c) J) (m.toMeasured.cell c)
      (Set.pi Set.univ fun j => (mc j).toMeasured.stateSet))
    (hindex : ∀ f : m.toMeasured.R, Ideal.span {f} ∈ m.toMeasured.cell c →
      ∀ g : (∀ j, (mc j).toMeasured.R), (∀ j, alpha j f = e j ^ m.toMeasured.cellDegree c * g j) →
      ∀ iota : (m.toMeasured.R ⧸ Ideal.span {f}) →ₗ[m.toMeasured.O]
      ((∀ j, (mc j).toMeasured.R) ⧸ Ideal.span {g}),
      (∀ h : m.toMeasured.R, iota (Ideal.Quotient.mk (Ideal.span {f}) h) =
      Ideal.Quotient.mk (Ideal.span {g}) (fun j => alpha j h)) → Function.Injective iota ∧
      Module.length m.toMeasured.O
      (((∀ j, (mc j).toMeasured.R) ⧸ Ideal.span {g}) ⧸ LinearMap.range iota) =
      (chooseTwo (m.toMeasured.cellDegree c) : ℕ∞))
    (hsum : ∑ j, m.toMeasured.childDelta c j * (mc j).toMeasured.s.firstContact =
      m.toMeasured.cellDegree c)
    (s : ℕ) (hs : tri (m.toMeasured.cellDegree c) ≤ s) (cc : (∀ j, (mc j).toMeasured.R))
    (hcc : (algebraMap m.toMeasured.O (∀ j, (mc j).toMeasured.R) m.toMeasured.S.pi) ^ s =
      e ^ m.toMeasured.cellDegree c * cc)
    (f : m.toMeasured.R) (b : Fin m.toMeasured.s.degree → m.toMeasured.R)
    (E₀ : m.toMeasured.R ≃ₗ[m.toMeasured.O]
      ((Fin m.toMeasured.s.degree → m.toMeasured.O) × m.toMeasured.R))
    (hE₀ : ∀ w, E₀.symm w = divisionMap f b w) (hf : Ideal.span {f} ∈ m.toMeasured.cell c)
    (g : (∀ j, (mc j).toMeasured.R)) (hg : ∀ j, alpha j f = e j ^ m.toMeasured.cellDegree c * g j)
    (bc : Fin m.toMeasured.s.degree → (∀ j, (mc j).toMeasured.R)) :
    (letI : Module m.toMeasured.O (∀ j, (mc j).toMeasured.R) := Algebra.toModule;
      ∀ (E : (∀ j, (mc j).toMeasured.R) ≃ₗ[m.toMeasured.O]
      ((Fin m.toMeasured.s.degree → m.toMeasured.O) × (∀ j, (mc j).toMeasured.R))),
      (∀ w, E.symm w = divisionMap g bc w) →
      ∃ Q : (Fin m.toMeasured.s.degree → m.toMeasured.O) →ₗ[m.toMeasured.O]
      (Fin m.toMeasured.s.degree → m.toMeasured.O),
      (∀ w, normalizationLinearPart E (pulledVariation (AlgHom.pi alpha) cc b) (Q w) =
      (m.toMeasured.S.pi ^ (s * m.toMeasured.s.degree - tri (m.toMeasured.cellDegree c))) • w) ∧
      Function.Injective (normalizationLinearPart E (pulledVariation (AlgHom.pi alpha) cc b)) ∧
      Module.length m.toMeasured.O
      ((Fin m.toMeasured.s.degree → m.toMeasured.O) ⧸ LinearMap.range
      (normalizationLinearPart E (pulledVariation (AlgHom.pi alpha) cc b))) =
      ((s * m.toMeasured.s.degree - tri (m.toMeasured.cellDegree c) : ℕ) : ℕ∞)) := by
  intro E hE
  -- compute the cokernel length through the strict quotient maps `R ⧸ (f) → Π R_j ⧸ (g)`, then
  -- invert the linear part up to `π^(s · deg - tri)` from the length bound
  have hpiO : Irreducible m.toMeasured.S.pi := m.toMeasured.S.pi_irreducible
  have hf' : AlgHom.pi alpha f = e ^ (m.toMeasured.cellDegree c) * g := by
    funext j; simp [AlgHom.pi_apply, hg j]
  have hgj : ∀ j, Ideal.span {g j} ∈ (mc j).toMeasured.stateSet := fun j => by
    simpa [strict_transform_ideal_of_generator _ _ _ (alpha j) (e j) (g j) _ f (hg j)
      (concrete_member_mul_t_injective (he j))] using hbij.mapsTo hf j (Set.mem_univ _)
  obtain ⟨phi, hphi⟩ := strict_quotient_map_exists m.toMeasured.O m.toMeasured.R _ _ f g e cc _ hf'
  obtain ⟨iota, hiota⟩ :=
    strict_quotient_inclusion_exists m.toMeasured.O m.toMeasured.R _ _ f g e _ hf'
  obtain ⟨hiota_inj, hindex'⟩ := hindex f hf g hg iota hiota
  have hereg := child_quotient_mul_parameter_injective m c mc e g he hgj
  have hechild : Module.length m.toMeasured.O
      (((∀ j, (mc j).toMeasured.R) ⧸ Ideal.span {g}) ⧸ LinearMap.range
      (LinearMap.mulLeft m.toMeasured.O (Ideal.Quotient.mk (Ideal.span {g}) e))) =
      ((m.toMeasured.cellDegree c) : ℕ∞) := by
    rw [pi_mul_cokernel_length m.toMeasured.O _ _ g e
      (fun j => m.toMeasured.childDelta c j * (mc j).toMeasured.s.firstContact) fun j => by
      apply length_scaling_of_residue_card m.toMeasured.O (mc j).toMeasured.O _ (hcard j)
      rw [he j]
      exact concrete_member_state_generator_contact_length (mc j) (g j) (hgj j), hsum]
  obtain ⟨EC, -⟩ := division_equiv_child_coordinates m.toMeasured.O _ _ g bc E hE
  obtain ⟨hpireg, hpiquot⟩ := coordinate_module_pi_quotient_length m.toMeasured.O _ hpiO _ _ EC
  have hlen := strict_quotient_cokernel_length m.toMeasured.O m.toMeasured.R _ _ f g e cc _ _ s hcc
    _ phi iota hphi hiota hindex' hereg hechild hpireg hpiquot
    (le_trans hs (Nat.le_mul_of_pos_right s (concrete_member_one_le_degree m)))
  have hphi_inj := strict_quotient_map_injective m.toMeasured.O m.toMeasured.R _ _ f g e cc _ _ s
    hcc phi iota hphi hiota hiota_inj hpireg
  obtain ⟨EB, hEB⟩ := division_quotient_basis_equiv m.toMeasured.O m.toMeasured.R _ f b E₀ hE₀
  obtain ⟨hL, hI⟩ := normalization_linear_part_cokernel_length_eq m.toMeasured.O m.toMeasured.R _ _
    f g e cc _ hf' _ _ s hcc b bc E hE phi hphi EB hEB
  have hDinj := hI hphi_inj
  have hkl := hL.trans hlen
  obtain ⟨Q, hQ, -⟩ := scaled_inverse_from_image_containment m.toMeasured.O _ _ _ _ _ hDinj
    (linear_image_bound_from_cokernel_length m.toMeasured.O _ _ _ hpiO.maximalIdeal_eq _ _ hkl)
  exact ⟨Q, hQ, hDinj, hkl⟩

/-- If `A` has an algebra type and `K ⊗ A ≃ K ⊗ Π B_j`, then every factor `B_j` has an algebra
  type. -/
private theorem algebra_type_pi_factor (O : Type) [CommRing O] [IsDomain O] (A : Type) [CommRing A]
    [Algebra O A] (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)]
    (e : TensorProduct O (BaseField O) A ≃ₐ[BaseField O] TensorProduct O (BaseField O) (∀ j, B j))
    (σ : FactorType) (hσ : HasAlgebraType O A σ) :
    ∀ j, ∃ τ : FactorType, HasAlgebraType O (B j) τ := by
  intro j
  obtain ⟨ι, hι, L, hF, hK, hO, hT, hD, e₀, -, hsepL⟩ := hσ
  let p := Algebra.TensorProduct.piRight O (BaseField O) (BaseField O) B
  let π := Pi.evalAlgHom (BaseField O) (fun j => TensorProduct O (BaseField O) (B j)) j
  have hπ : Function.Surjective π := fun y => ⟨Pi.single j y, by simp [π]⟩
  let q := Ideal.quotientKerAlgEquivOfSurjective hπ
  let g := p.symm.trans (e.symm.trans e₀)
  let I := (RingHom.ker π).map
      (g : ((i : Fin n) → TensorProduct O (BaseField O) (B i)) →+* ((i : ι) → L i))
  obtain ⟨S, e₁, -⟩ := pi_field_quotient_equiv (BaseField O) ι L I
  let E := q.symm.trans ((Ideal.quotientEquivAlg (RingHom.ker π) I g rfl).trans e₁)
  exact ⟨_, S, inferInstance, fun i => L i.1, fun i => hF i.1, fun i => hK i.1, fun i => hO i.1,
    fun i => hT i.1, fun i => hD i.1, E, rfl, fun i => hsepL i.1⟩

/-- If `A → Π B_j` is injective with finite-length cokernel and `A` has an algebra type, then every
  factor `B_j` has an algebra type. -/
theorem algebra_type_children_exists (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (A : Type) [CommRing A] [Algebra O A] (n : ℕ) (B : Fin n → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)] (ψ : A →ₐ[O] ∀ j, B j)
    (hinj : Function.Injective ψ) (ℓ : ℕ)
    (hℓ : Module.length O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = ℓ) (σ : FactorType)
    (hσ : HasAlgebraType O A σ) :
    ∀ j, ∃ τ : FactorType, HasAlgebraType O (B j) τ := by
  have hb := baseChange_bijective_of_finite_cokernel O A (∀ j, B j) ψ.toLinearMap hinj ℓ hℓ
  have hfun : ∀ x, (Algebra.TensorProduct.map (AlgHom.id (BaseField O) (BaseField O)) ψ) x
      = LinearMap.baseChange (BaseField O) ψ.toLinearMap x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k a => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hΨ : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id (BaseField O) (BaseField O)) ψ) := by
    have : ⇑(Algebra.TensorProduct.map (AlgHom.id (BaseField O) (BaseField O)) ψ)
        = ⇑(LinearMap.baseChange (BaseField O) ψ.toLinearMap) := funext hfun
    rw [this]; exact hb
  exact algebra_type_pi_factor O A n B (AlgEquiv.ofBijective _ hΨ) σ hσ

end SurfaceBlowup
