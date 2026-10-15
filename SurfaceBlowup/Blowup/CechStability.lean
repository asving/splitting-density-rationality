/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.TwoChartCurveData

/-!
# Stability of the finite Čech coefficients

For a regular parameter pair `(t, x)` of `R`, the finite Čech complexes of the two-chart cover
of the blow-up compute, level by level, the cokernel of the twisted Čech differential. This file
shows that the reduction maps between consecutive cokernels are bijective once the level exceeds
the twist `d`, computes the length of the level-`n` cokernel as `∑_{j < n} (d - j - 1)`, and hence
identifies it with `chooseTwo d` in the stable range. As an application, threads of the curve
order limit that are approximable at one stable level lie in the image of the surface.

## Main results

* `SurfaceBlowup.actual_twisted_coker_reduction_bijective`: for `d ≤ j + 1` the reduction map
  between the cokernels at levels `j + 1` and `j` is bijective.
* `SurfaceBlowup.actual_finite_cech_coefficient_length`: the length of the level-`n` cokernel.
* `SurfaceBlowup.actual_finite_cech_coefficient_triangular`: in the stable range `d - 1 ≤ n`
  this length is `chooseTwo d`.
* `SurfaceBlowup.curve_limit_range_of_stable_level`: a thread approximable by a surface function at
  a stable level is in the range of any section of the surface-to-curve map.

Provenance: `Thm_SurfaceBlowupV2_{actual_twisted_coker_reduction_bijective,
actual_finite_cech_coefficient_length, actual_finite_cech_coefficient_triangular,
curve_limit_range_of_stable_level}`.
-/

namespace SurfaceBlowup

/-! ### The cokernel tower -/

/-- In the stable range `d ≤ j + 1`, the map induced by reduction between the cokernels of the
twisted finite Čech differentials at levels `j + 1` and `j` is a bijection. -/
theorem actual_twisted_coker_reduction_bijective (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x) (d j : ℕ) (hd : d ≤ j + 1)
    (hnext : cechInputLattice R t x (j + 1) ≤
      (cechOutputLattice R t x (j + 1)).comap (fullCechDifferential R t x beta d))
    (hnow : cechInputLattice R t x j ≤
      (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d))
    (hcomm : (cechOutputReduction R t x j).comp
        (finiteCechDifferential R t x beta d (j + 1) hnext) =
      (finiteCechDifferential R t x beta d j hnow).comp (cechInputReduction R t x j)) :
    Function.Bijective (twoTermCokerMap (finiteCechDifferential R t x beta d (j+1) hnext)
      (finiteCechDifferential R t x beta d j hnow) (cechInputReduction R t x j)
      (cechOutputReduction R t x j) hcomm) := by
  refine ⟨?_, two_term_coker_map_surjective R _ _ _ _ _ _ _ _ hcomm
    (actual_cech_reductions_surjective R t x j).2⟩
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨wbar, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wbar
  obtain ⟨abar, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hq
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ abar
  replace ha := (Submodule.Quotient.eq _).1 ha
  have hbase : ∀ r : R, (beta.right : BlowupChart R x t →+* BlowupOverlap R t x) (chartBase R x t r)
      = (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x r) := fun r =>
    (beta.right.commutes r).trans (IsScalarTower.algebraMap_apply R _ _ r)
  obtain ⟨a', b', -, -, hc⟩ := two_chart_layer_correction R t x hreg
    (beta.right : BlowupChart R x t →+* BlowupOverlap R t x) hbase beta.slope j d hd
    (w - fullCechDifferential R t x beta d a) (by simpa [cechOutputLattice] using neg_mem ha)
  refine (Submodule.Quotient.mk_eq_zero _).2
    ⟨Submodule.Quotient.mk (a + (a', b')), (Submodule.Quotient.eq _).2 ?_⟩
  have : fullCechDifferential R t x beta d (a + (a', b')) - w =
      -(w - fullCechDifferential R t x beta d a - ((algebraMap (BlowupChart R t x)
        (BlowupOverlap R t x)) a' - (IsLocalization.Away.invSelf (chartSlope R t x))^d *
          beta.right b')) := by
    rw [map_add]
    change _ + ((IsScalarTower.toAlgHom R (BlowupChart R t x) (BlowupOverlap R t x)) a' - _ *
      beta.right b') - w = _
    simp only [IsScalarTower.coe_toAlgHom']
    ring
  rw [this]
  exact neg_mem hc

/-- The length of the cokernel of the twisted finite Čech differential at level `n` is
`∑_{j < n} (d - j - 1)`. -/
theorem actual_finite_cech_coefficient_length (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (t x : R) (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
    (hregSwap : RegularParameterPair R x t) [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (hres : Function.Surjective (algebraMap O (R ⧸ Ideal.span {t,x}))) (d n : ℕ)
    (hpres : ∀ j : ℕ, cechInputLattice R t x j ≤
      (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d)) :
    Module.length O
      (CechLevelOutput R t x n ⧸ LinearMap.range (finiteCechDifferential R t x beta d n (hpres n)))
      = ((∑ j ∈ Finset.range n, (d-j-1) : ℕ) : ℕ∞) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
    apply Module.length_eq_zero_iff.mpr
    have : Subsingleton (CechLevelOutput R t x 0) := by
      constructor
      intro a b
      induction a using Submodule.Quotient.induction_on
      induction b using Submodule.Quotient.induction_on
      rw [Submodule.Quotient.eq]
      simp [cechOutputLattice]
    infer_instance
  | succ j ih =>
    have hcomm := actual_cech_differentials_commute_with_reduction R t x beta d j (hpres (j+1))
      (hpres j)
    have hsurj := two_term_coker_map_surjective R _ _ _ _ _ _ _ _ hcomm
      (actual_cech_reductions_surjective R t x j).2
    rw [Finset.sum_range_succ, Nat.cast_add, ← ih]
    by_cases hj : j < d
    · obtain ⟨i, hi, hex⟩ := actual_negative_layer_coker_exact R t x hreg beta hregSwap d j hj
        (hpres (j+1)) (hpres j) hcomm
      rw [Module.length_eq_add_of_exact (i.restrictScalars O)
        ((twoTermCokerMap _ _ _ _ hcomm).restrictScalars O) hi hsurj hex, add_comm]
      congr 1
      rw [Module.length_eq_of_surjective hres]
      let _ := Ideal.Quotient.field (Ideal.span ({t,x} : Set R))
      exact (Module.length_eq_finrank _ _).trans (by simp)
    · have hbij := actual_twisted_coker_reduction_bijective R t x hreg beta d j (by omega)
        (hpres (j+1)) (hpres j) hcomm
      rw [(LinearEquiv.ofBijective ((twoTermCokerMap _ _ _ _ hcomm).restrictScalars O)
        hbij).length_eq]
      simp [show d - j - 1 = 0 by omega]

private theorem sum_range_sub_sub_one_eq_chooseTwo (d n : ℕ) (hn : d - 1 ≤ n) :
    (∑ j ∈ Finset.range n, (d-j-1) : ℕ) = chooseTwo d := by
  have h1 : ∀ m, (∑ j ∈ Finset.range (d-1+m), (d-j-1) : ℕ)
      = ∑ j ∈ Finset.range (d-1), (d-j-1) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← add_assoc, Finset.sum_range_succ, ih]
      omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [h1]
  have h2 : (∑ j ∈ Finset.range (d-1), (d-j-1) : ℕ) = ∑ j ∈ Finset.range d, (d-1-j) := by
    rcases d with _ | d
    · rfl
    · rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel]
      rw [show d - d = 0 by omega, add_zero]
      exact Finset.sum_congr rfl fun j _ => by omega
  rw [h2, Finset.sum_range_reflect (fun j => j) d, Finset.sum_range_id]
  rfl

/-- In the stable range `d - 1 ≤ n`, the cokernel of the twisted finite Čech differential at
level `n` has length `chooseTwo d`. -/
theorem actual_finite_cech_coefficient_triangular (O R : Type) [CommRing O] [CommRing R]
    [Algebra O R] (t x : R) (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
    (hregSwap : RegularParameterPair R x t) [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (hres : Function.Surjective (algebraMap O (R ⧸ Ideal.span {t,x}))) (d n : ℕ) (hn : d - 1 ≤ n)
    (hpres : ∀ j : ℕ, cechInputLattice R t x j ≤
      (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d)) :
    Module.length O
      (CechLevelOutput R t x n ⧸ LinearMap.range (finiteCechDifferential R t x beta d n (hpres n)))
      = (chooseTwo d : ℕ∞) := by
  rw [actual_finite_cech_coefficient_length O R t x hreg beta hregSwap hres d n hpres,
    sum_range_sub_sub_one_eq_chooseTwo d n hn]

/-! ### Threads of the curve order limit -/

section Threads

variable {R : Type} [CommRing R] {t x : R} {beta : BlowupRestriction R t x} {d : ℕ}
  (G : GluedGenerators R t x beta d)

private theorem curveIdealLattice_le_of_le {j k : ℕ} (hjk : j ≤ k) :
    curveIdealLattice R t x beta G k ≤ curveIdealLattice R t x beta G j := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact le_trans (curve_lattices_antitone R t x beta d G k).1 ih

private theorem thread_sub_succ_mem (p : curveThreads R t x beta G) (j : ℕ) :
    p.val j - p.val (j+1) ∈ curveIdealLattice R t x beta G j := by
  have h := (Submodule.mem_inf.mp p.2).2
  rw [Submodule.mem_comap, Submodule.mem_pi] at h
  exact h j (Set.mem_univ _)

private theorem thread_mem_curveSections (p : curveThreads R t x beta G) (j : ℕ) :
    p.val j ∈ curveSections R t x beta G j :=
  Submodule.mem_pi.mp (Submodule.mem_inf.mp p.2).1 j (Set.mem_univ _)

private theorem thread_sub_mem (p : curveThreads R t x beta G) {j k : ℕ} (hjk : j ≤ k) :
    p.val j - p.val k ∈ curveIdealLattice R t x beta G j := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    simpa only [sub_add_sub_cancel] using
      add_mem ih (curveIdealLattice_le_of_le G hk (thread_sub_succ_mem G p k))

end Threads

/-- A curve thread that is approximable by surface functions modulo the curve lattice at one
stable level `J ≥ d - 1` is approximable at every level: going up uses the bijectivity of the
cokernel reduction maps, going down the antitonicity of the curve lattices. -/
private theorem exists_surface_approx_of_stable_level {R : Type} [CommRing R] {t x : R}
    {beta : BlowupRestriction R t x} {d : ℕ} (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t)
    (hregF : ∀ j : ℕ, Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    {J : ℕ} (hJ : d - 1 ≤ J) (p : curveThreads R t x beta G)
    (hp : ∃ r : R, p.val J - surfaceToChartPair R t x r ∈ curveIdealLattice R t x beta G J)
    (j : ℕ) : ∃ r : R, p.val j - surfaceToChartPair R t x r ∈ curveIdealLattice R t x beta G j := by
  -- Step 1: `p` is approximable by surface functions at every level `≥ J`.
  have step1 : ∀ n : ℕ, ∃ r : R, p.val (J+n) - surfaceToChartPair R t x r ∈
      curveIdealLattice R t x beta G (J+n) := by
    intro n
    induction n with
    | zero => simpa using hp
    | succ n ih =>
      obtain ⟨r0, hr0⟩ := ih
      rw [← add_assoc]
      generalize hj : J + n = j at hr0 ⊢
      have hsec := thread_mem_curveSections G p (j+1)
      obtain ⟨_, hyy, zz, hzz, hyz⟩ := Submodule.mem_sup.mp hsec
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hyy
      have hc : fullCechDifferential R t x beta 0 (p.val (j+1)) -
          (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left (j+1)) * a ∈
          (Ideal.span {overlapException R t x})^(j+1) := by
        rw [← hyz, mul_comm a, add_sub_cancel_left]; exact hzz
      have hnow := actual_cech_preserves_exceptional_lattices R t x beta d j
      have hnext := actual_cech_preserves_exceptional_lattices R t x beta d (j+1)
      have hbij := actual_twisted_coker_reduction_bijective R t x hreg beta d j (by omega) hnext
        hnow (actual_cech_differentials_commute_with_reduction R t x beta d j hnext hnow)
      refine (curve_section_connecting_class_zero_iff R t x beta d G hreg hregSwap (j+1) hnext
        (hregF (j+1)) (p.val (j+1)) hsec a hc).mp (hbij.1 ?_)
      rw [map_zero]
      have hcj : fullCechDifferential R t x beta 0 (p.val (j+1)) -
          (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j) * a ∈
          (Ideal.span {overlapException R t x})^j := by
        have hm := Ideal.mem_map_of_mem (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))
          (G.left_compat j)
        rw [chartExceptional, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at hm
        convert add_mem (Ideal.pow_le_pow_right (Nat.le_succ j) hc) (Ideal.mul_mem_right a _ hm)
          using 1
        rw [map_sub]; ring
      refine (curve_section_connecting_class_zero_iff R t x beta d G hreg hregSwap j hnow
        (hregF j) (p.val (j+1)) ((curve_lattices_antitone R t x beta d G j).2 hsec) a hcj).mpr
        ⟨r0, ?_⟩
      convert sub_mem hr0 (thread_sub_succ_mem G p j) using 1; abel
  -- Step 2: hence at every level.
  obtain ⟨r, hr⟩ := step1 j
  refine ⟨r, ?_⟩
  simpa only [sub_add_sub_cancel] using add_mem (thread_sub_mem G p (k := J + j) (by omega))
    (curveIdealLattice_le_of_le G (j := j) (by omega) hr)

/-- Let `σ` be a section of the surface-to-curve-limit map that sends a surface function to its
constant thread. If a thread `p` of the curve order limit agrees with a surface function modulo the
curve lattice at a single stable level `J ≥ d - 1`, then its class lies in the range of `σ`. -/
theorem curve_limit_range_of_stable_level (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t)
    (hregF : ∀ j : ℕ, Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x})^j =>
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j)
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (G.left j)) * c))
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    [IsAdicComplete (Ideal.span {t,x}) R] (J : ℕ) (hJ : d - 1 ≤ J)
    (σ : R →ₗ[R] CurveOrderLimit R t x beta G)
    (hσ : ∀ r : R, ∃ p : curveThreads R t x beta G, σ r = curveLimitMk R t x beta G p ∧ ∀ j : ℕ,
      p.val j = surfaceToChartPair R t x r)
    (p : curveThreads R t x beta G)
    (hp : ∃ r : R, p.val J - surfaceToChartPair R t x r ∈ curveIdealLattice R t x beta G J) :
    curveLimitMk R t x beta G p ∈ LinearMap.range σ := by
  -- Approximate `p` at every level, correct the approximants into an adically Cauchy sequence
  -- of surface functions, and take its limit.
  choose r hr using exists_surface_approx_of_stable_level G hreg hregSwap hregF hJ p hp
  have hker : ∀ (j : ℕ) (a : R), surfaceToChartPair R t x a ∈ curveIdealLattice R t x beta G j ↔
      a ∈ Ideal.span {f} ⊔ (Ideal.span {t,x})^j := fun j a ↦
    surface_to_curve_quotient_kernel R t x beta d G hreg hregSwap j (hregF j) f hf a
  have hdiff : ∀ j, r (j+1) - r j ∈ Ideal.span {f} ⊔ (Ideal.span {t,x})^j := fun j ↦ by
    rw [← hker]
    convert sub_mem (sub_mem (hr j) (thread_sub_succ_mem G p j))
      ((curve_lattices_antitone R t x beta d G j).1 (hr (j+1))) using 1
    rw [map_sub]; abel
  choose y hy z hz hyz using fun j ↦ Submodule.mem_sup.mp (hdiff j)
  set r' : ℕ → R := fun j ↦ r j - ∑ i ∈ Finset.range j, y i with hr'
  have hcauchy : ∀ m n, m ≤ n → r' m - r' n ∈ (Ideal.span {t,x})^m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have h2 : r' n - r' (n+1) = -z n := by
        simp only [hr', Finset.sum_range_succ]; linear_combination hyz n
      simpa only [← h2, sub_add_sub_cancel] using
        add_mem ih (neg_mem (Ideal.pow_le_pow_right hn (hz n)))
  obtain ⟨Lim, hLim⟩ := IsPrecomplete.prec (I := Ideal.span {t,x}) (M := R) inferInstance
    (f := r') fun {m n} hmn ↦ by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact hcauchy m n hmn
  have hLim' : ∀ j, p.val j - surfaceToChartPair R t x Lim ∈ curveIdealLattice R t x beta G j :=
    fun j ↦ by
      have h := hLim j
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
      have h1 := (hker j (Lim - r j)).2 <| by
        convert sub_mem
          (Ideal.mem_sup_left (neg_mem (sum_mem fun i (_ : i ∈ Finset.range j) ↦ hy i)))
          (Ideal.mem_sup_right h) using 1
        simp only [hr']; abel
      convert sub_mem (hr j) h1 using 1
      rw [map_sub]; abel
  obtain ⟨q, hq1, hq2⟩ := hσ Lim
  refine ⟨Lim, hq1.trans ((Submodule.Quotient.eq _).2 (Submodule.mem_pi.2 fun j _ ↦ ?_))⟩
  change q.val j - p.val j ∈ curveIdealLattice R t x beta G j
  rw [hq2 j, ← neg_sub]
  exact neg_mem (hLim' j)

end SurfaceBlowup
