/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Surfaces.PowerSeries
import SurfaceBlowup.Unramified.FrobeniusDescent
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit

/-!
# Completeness of the concrete surface

We study the concrete surface `O[[T,X]] / (π - u T^a X^b)` over a discrete valuation ring `O`:
the quotient by `t` is the power series ring over the residue field, ring maps out of
`O[[T,X]]` are determined by their values on constants and on nilpotent images of `T`, `X`,
and the surface (as well as its curve quotients) is adically complete for the parameter
ideal, the maximal ideal and the ideal `(π)`.

## Main results

* `concrete_surface_quotient_T_equiv`: `R / (t) ≃+* k[[X]]`.
* `concrete_surface_span_T_isPrime`: `(t)` is a prime ideal of the surface.
* `transverse_of_reduction_ne_zero`: a criterion for `g, e` to form a transverse pair.
* `twoSeries_ringHom_ext_of_isNilpotent`, `twoSeries_eval_exists_of_isAdicComplete`:
  uniqueness and existence of evaluations of two-variable power series.
* `concrete_surface_isAdicComplete_maximalIdeal`, `concrete_surface_isAdicComplete_span_pi`,
  `division_coordinate_module_isAdicComplete`: adic completeness statements.

Provenance: `surfaceRelation_span_axisT_{eq,isPrime}`, `concrete_surface_{quotient_T_equiv,
span_T_isPrime, ringHom_ext_of_isNilpotent, curve_isAdicComplete}`,
`transverse_of_reduction_ne_zero`, `twoSeries_{mem_variableIdeal_pow_of_coeff_eq_zero,
ringHom_ext_of_isNilpotent, eval_exists_of_isAdicComplete, isAdicComplete_variableIdeal}`,
`unramified_{lift_map_parameter_quotient_irreducible, root_isUnit_of_two_le_natDegree}`,
`variableIdeal_{eq_span_range_X, ne_top}`, `concrete_surface_isAdicComplete_{parameterIdeal,
maximalIdeal, span_pi, span_pi_base}`, `division_coordinate_module_isAdicComplete`.
-/

namespace SurfaceBlowup

/-! ### The quotient by `t` -/

/-- For `0 < a`, the ideals `(π - u T^a X^b, T)` and `(π, T)` of `O[[T,X]]` coincide. -/
private theorem surfaceRelation_span_axisT_eq (O : Type) [CommRing O] (pi : O) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) :
    Ideal.span {surfaceRelation O pi u a b, axisT O} =
      Ideal.span {(MvPowerSeries.C pi : TwoSeries O), axisT O} := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [show surfaceRelation O pi u (a' + 1) b = MvPowerSeries.C pi +
      -((u : TwoSeries O) * axisT O ^ a' * axisX O ^ b) * axisT O by rw [surfaceRelation]; ring,
    Ideal.span_pair_add_mul_right]

/-- The quotient of the concrete surface by `t` is the power series ring `k[[X]]` over the
residue field, compatibly with `residueKillT`. -/
theorem concrete_surface_quotient_T_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    ∃ q : (ConcreteSurface O pi u a b ⧸ Ideal.span {surfaceT O pi u a b}) ≃+*
        PowerSeries (IsLocalRing.ResidueField O),
      ∀ s : TwoSeries O, q (Ideal.Quotient.mk (Ideal.span {surfaceT O pi u a b})
        (surfaceMk O pi u a b s)) = residueKillT O s := by
  obtain ⟨-, -, -, hsurj, hker⟩ := residueKillT_apply_ker O pi hpi
  set I := surfaceIdeal O pi u a b
  set J : Ideal (TwoSeries O) := Ideal.span {axisT O}
  have h1 : Ideal.span {surfaceT O pi u a b} = J.map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  have h2 : I ⊔ J = RingHom.ker (residueKillT O) := by
    rw [hker, ← surfaceRelation_span_axisT_eq O pi u a b ha, Ideal.span_insert]; rfl
  exact ⟨((Ideal.quotEquivOfEq h1).trans (DoubleQuot.quotQuotEquivQuotSup I J)).trans
    ((Ideal.quotEquivOfEq h2).trans (RingHom.quotientKerEquivOfSurjective hsurj)), fun _ ↦ rfl⟩

/-- The ideal `(π - u T^a X^b, T)` of `O[[T,X]]` is prime when `π` is a uniformizer. -/
private theorem surfaceRelation_span_axisT_isPrime (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    (Ideal.span {surfaceRelation O pi u a b, axisT O}).IsPrime := by
  rw [surfaceRelation_span_axisT_eq O pi u a b ha]
  simpa [axisT] using mvPowerSeries_fin_two_span_C_var_isPrime O pi
    (by rw [← hpi.maximalIdeal_eq]; infer_instance) 0

/-- The ideal `(t)` of the concrete surface is prime. -/
theorem concrete_surface_span_T_isPrime (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    (Ideal.span {surfaceT O pi u a b}).IsPrime := by
  have := surfaceRelation_span_axisT_isPrime O pi hpi u a b ha
  have hker : RingHom.ker (surfaceMk O pi u a b) ≤
      Ideal.span {surfaceRelation O pi u a b, axisT O} := by
    rw [surfaceMk, Ideal.mk_ker]
    exact Ideal.span_mono (by simp)
  have h0 : surfaceMk O pi u a b (surfaceRelation O pi u a b) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have himg : (Ideal.span {surfaceRelation O pi u a b, axisT O}).map (surfaceMk O pi u a b) =
      Ideal.span {surfaceT O pi u a b} := by
    rw [Ideal.map_span, Set.image_pair, h0, Ideal.span_insert_zero]; rfl
  exact himg ▸ Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker

/-- Let `e` be a non-zero-divisor of a noetherian local ring `S` with `S / (e) ≃ k[[X]]`, and
let `g` have nonzero image in `k[[X]]`. Then `e` is a non-zero-divisor modulo `g`, `g` is a
non-zero-divisor modulo `e`, and `(g, e)` contains a power of the maximal ideal. -/
theorem transverse_of_reduction_ne_zero (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (e g : S) (hereg : Function.Injective (fun y : S ↦ e * y)) (k : Type)
    [Field k] (q : (S ⧸ Ideal.span {e}) ≃+* PowerSeries k)
    (hg : q (Ideal.Quotient.mk (Ideal.span {e}) g) ≠ 0) :
    Function.Injective (fun a : S ⧸ Ideal.span {g} ↦ Ideal.Quotient.mk (Ideal.span {g}) e * a) ∧
      Function.Injective
        (fun a : S ⧸ Ideal.span {e} ↦ Ideal.Quotient.mk (Ideal.span {e}) g * a) ∧
      ∃ L : ℕ, (IsLocalRing.maximalIdeal S)^L ≤ Ideal.span {g, e} := by
  set π := Ideal.Quotient.mk (Ideal.span {e})
  have hker : ∀ x : S, q (π x) = 0 ↔ ∃ c, x = e * c := fun x ↦ by
    rw [map_eq_zero_iff q q.injective, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact Iff.rfl
  refine ⟨fun a a' h ↦ ?_, fun a a' h ↦ q.injective (mul_left_cancel₀ hg (by
    simpa only [map_mul] using congrArg q h)), ?_⟩
  · induction a using Quotient.inductionOn' with | h a => ?_
    induction a' using Quotient.inductionOn' with | h a' => ?_
    change Ideal.Quotient.mk _ e * Ideal.Quotient.mk _ a =
      Ideal.Quotient.mk _ e * Ideal.Quotient.mk _ a' at h
    change Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ a'
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
    obtain ⟨b, hb⟩ := h
    have h0 : q (π g) * q (π b) = 0 := by
      rw [← map_mul, ← map_mul, mul_comm, hb, ← mul_sub]
      exact (hker _).2 ⟨_, rfl⟩
    obtain ⟨c, rfl⟩ := (hker b).1 ((mul_eq_zero.1 h0).resolve_left hg)
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨c, hereg (by simp only; rw [mul_sub, ← hb]; ring)⟩
  · -- `(g, e)` contains `𝔪^L` with `L = ord_X (q ḡ)`: `𝔪^L` maps into `(X^L) = (q ḡ)` in `k[[X]]`.
    set p := q (π g)
    have hu : IsUnit p.divXPowOrder := by
      rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
      exact fun h ↦ hg (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.1 h)
    let f : S →+* PowerSeries k := (q : (S ⧸ Ideal.span {e}) →+* PowerSeries k).comp π
    have hfs : Function.Surjective f := q.surjective.comp Ideal.Quotient.mk_surjective
    refine ⟨p.order.toNat, fun x hx ↦ ?_⟩
    have hx' := Ideal.mem_map_of_mem f hx
    rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective f hfs,
      PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hx'
    obtain ⟨y, hy⟩ : f g ∣ f x := dvd_trans ⟨↑hu.unit⁻¹, by
      change _ = p * _
      rw [← mul_one (_ ^ _), ← hu.mul_val_inv, ← mul_assoc,
        PowerSeries.X_pow_order_mul_divXPowOrder]⟩ hx'
    obtain ⟨y, rfl⟩ := hfs y
    obtain ⟨c, hc⟩ := (hker _).1 (by
      change f (x - g * y) = 0
      rw [map_sub, map_mul, hy, sub_self])
    exact Ideal.mem_span_pair.2 ⟨y, c, by linear_combination -hc⟩

/-! ### Ring maps out of `O[[T,X]]` -/

/-- A two-variable power series all of whose coefficients of total degree `< N` vanish lies in
`(T, X)^N`. -/
private theorem twoSeries_mem_variableIdeal_pow_of_coeff_eq_zero (O : Type) [CommRing O] (N : ℕ)
    (g : TwoSeries O) (hg : ∀ m : Fin 2 →₀ ℕ, m 0 + m 1 < N → MvPowerSeries.coeff m g = 0) :
    g ∈ variableIdeal O ^ N :=
  (axis_ideal_pow_mem_iff O N g).2 hg

/-- Two ring maps out of `O[[T,X]]` that agree on constants, `T` and `X`, and send `T` and
`X` to nilpotent elements, are equal. -/
theorem twoSeries_ringHom_ext_of_isNilpotent (O S : Type) [CommRing O] [CommRing S]
    (φ ψ : TwoSeries O →+* S) (hC : ∀ c : O, φ (MvPowerSeries.C c) = ψ (MvPowerSeries.C c))
    (hT : φ (axisT O) = ψ (axisT O)) (hX : φ (axisX O) = ψ (axisX O))
    (hTn : IsNilpotent (φ (axisT O))) (hXn : IsNilpotent (φ (axisX O))) :
    φ = ψ := by
  obtain ⟨N, hN⟩ : IsNilpotent (Ideal.span {φ (axisT O), φ (axisX O)}) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.toFinite _)),
      Ideal.span_le]
    rintro x (rfl | rfl)
    exacts [hTn, hXn]
  -- both maps kill `(T, X)^N`, whose image is generated by powers of `φ T, φ X`
  have kill (χ : TwoSeries O →+* S) (hχT : χ (axisT O) = φ (axisT O))
      (hχX : χ (axisX O) = φ (axisX O)) (g) (hg : g ∈ variableIdeal O ^ N) : χ g = 0 := by
    have : χ g ∈ ((variableIdeal O) ^ N).map χ := Ideal.mem_map_of_mem _ hg
    rw [Ideal.map_pow, variableIdeal, Ideal.map_span, Set.image_pair, hχT, hχX, hN] at this
    simpa using this
  have hpoly : φ.comp (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 2) (R := O)) =
      ψ.comp (MvPolynomial.coeToMvPowerSeries.ringHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa using hC c
    · intro s
      fin_cases s
      · simpa [axisT] using hT
      · simpa [axisX] using hX
  ext f
  set p := MvPowerSeries.truncTotal N f
  have hg : f - (p : TwoSeries O) ∈ variableIdeal O ^ N := by
    apply twoSeries_mem_variableIdeal_pow_of_coeff_eq_zero
    intro m hm
    rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal, sub_self]
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hm
  have h1 := kill φ rfl rfl _ hg
  have h2 := kill ψ hT.symm hX.symm _ hg
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2]
  exact congrArg (fun F ↦ F p) hpoly

/-- Two ring maps out of the concrete surface that agree on constants, `t` and `x`, and send
`t` and `x` to nilpotent elements, are equal. -/
theorem concrete_surface_ringHom_ext_of_isNilpotent (O S : Type) [CommRing O] [CommRing S]
    (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) (φ ψ : ConcreteSurface O pi u a b →+* S)
    (hC : ∀ c : O, φ (algebraMap O (ConcreteSurface O pi u a b) c) =
      ψ (algebraMap O (ConcreteSurface O pi u a b) c))
    (hT : φ (surfaceT O pi u a b) = ψ (surfaceT O pi u a b))
    (hX : φ (surfaceX O pi u a b) = ψ (surfaceX O pi u a b))
    (hTn : IsNilpotent (φ (surfaceT O pi u a b))) (hXn : IsNilpotent (φ (surfaceX O pi u a b))) :
    φ = ψ :=
  Ideal.Quotient.ringHom_ext
    (twoSeries_ringHom_ext_of_isNilpotent O S _ _ (fun c ↦ hC c) hT hX hTn hXn)

/-- Over a ring `S` complete for an ideal `I`, any ring map `O' → S` extends to an evaluation
`O'[[T,X]] → S` sending `T ↦ e` and `X ↦ z` for given `e, z ∈ I`. -/
theorem twoSeries_eval_exists_of_isAdicComplete (S : Type) [CommRing S] (I : Ideal S)
    [IsAdicComplete I S] (O' : Type) [CommRing O'] (κ : O' →+* S) (e z : S) (he : e ∈ I)
    (hz : z ∈ I) :
    ∃ Θ : TwoSeries O' →+* S,
      (∀ c : O', Θ (MvPowerSeries.C c) = κ c) ∧ Θ (axisT O') = e ∧ Θ (axisX O') = z := by
  have nil : ∀ (n : ℕ) (a : S), a ∈ I → IsNilpotent (Ideal.Quotient.mk (I ^ n) a) :=
    fun n a ha ↦ ⟨n, by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow ha n⟩
  let f : (n : ℕ) → TwoSeries O' →+* S ⧸ I ^ n := fun n ↦
    nilpotentEval ((Ideal.Quotient.mk (I ^ n)).comp κ) (Ideal.Quotient.mk (I ^ n) e)
      (Ideal.Quotient.mk (I ^ n) z) (nil n e he) (nil n z hz)
  have hgen := fun n ↦ nilpotentEval_apply_generators O' (S ⧸ I ^ n)
      ((Ideal.Quotient.mk (I ^ n)).comp κ) (Ideal.Quotient.mk (I ^ n) e)
      (Ideal.Quotient.mk (I ^ n) z) (nil n e he) (nil n z hz)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    obtain ⟨hC, hT, hX⟩ := hgen n
    obtain ⟨hC', hT', hX'⟩ := hgen m
    apply twoSeries_ringHom_ext_of_isNilpotent
    · intro c; simp only [RingHom.comp_apply, f, hC, hC']; rfl
    · simp only [RingHom.comp_apply, f, hT, hT']; rfl
    · simp only [RingHom.comp_apply, f, hX, hX']; rfl
    · simp only [RingHom.comp_apply, f, hT]; exact (nil n e he).map _
    · simp only [RingHom.comp_apply, f, hX]; exact (nil n z hz).map _
  have hsep : ∀ a b : S, (∀ n : ℕ, Ideal.Quotient.mk (I ^ n) a = Ideal.Quotient.mk (I ^ n) b) →
      a = b := by
    intro a b h
    rw [IsHausdorff.eq_iff_smodEq (I := I)]
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
    exact h n
  refine ⟨IsAdicComplete.liftRingHom I f hf, fun c ↦ hsep _ _ fun n ↦ ?_,
    hsep _ _ fun n ↦ ?_, hsep _ _ fun n ↦ ?_⟩ <;> rw [IsAdicComplete.mk_liftRingHom]
  exacts [(hgen n).1 c, (hgen n).2.1, (hgen n).2.2]

/-! ### Unramified extensions -/

/-- The reduction of an unramified lift `Φ` to the quotient of the concrete surface by its
parameter ideal `(t, x)` is irreducible. -/
theorem unramified_lift_map_parameter_quotient_irreducible (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    Irreducible (Φ.map ((Ideal.Quotient.mk (Ideal.span ({surfaceT O pi u a b,
      surfaceX O pi u a b} : Set (ConcreteSurface O pi u a b)))).comp
        (algebraMap O (ConcreteSurface O pi u a b)))) := by
  have key : ∀ (R : Type) [CommRing R] (alg : O →+* R) (I : Ideal R)
      (e : R ⧸ I ≃+* IsLocalRing.ResidueField O),
      (∀ c, e (Ideal.Quotient.mk I (alg c)) = IsLocalRing.residue O c) →
      Irreducible (Φ.map ((Ideal.Quotient.mk I).comp alg)) := by
    intro R _ alg I e hc
    have hc' : e.toRingHom.comp ((Ideal.Quotient.mk I).comp alg) = IsLocalRing.residue O := by
      ext c; exact hc c
    have h := hΦ.2
    rw [residuePoly, ← hc', ← Polynomial.map_map] at h
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e).toMulEquiv).mp (by simpa using h)
  obtain ⟨e, he⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  exact key _ _ _ e fun c ↦ (he (.C c)).trans (congrArg _ (MvPowerSeries.constantCoeff_C ..))

/-- If `Φ` is an unramified lift of degree at least `2` over a complete local ring with finite
residue field, then the root of `Φ` in `O[X]/(Φ)` is a unit. -/
theorem unramified_root_isUnit_of_two_le_natDegree (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (h2 : 2 ≤ Φ.natDegree) :
    IsUnit (AdjoinRoot.root Φ) := by
  obtain ⟨_, hunit, _⟩ := base_ideal_maximal_local O Φ hΦ
  apply hunit
  obtain ⟨hfield, _, _⟩ := residue_extension_field O Φ hΦ
  obtain ⟨e, he, _⟩ := residue_extension_equiv O Φ
  have hne : baseReduce O Φ (AdjoinRoot.root Φ) ≠ 0 := by
    intro h0
    have h1 : e (baseReduce O Φ (AdjoinRoot.mk Φ Polynomial.X)) = 0 := by
      rw [AdjoinRoot.mk_X, h0]; simp
    rw [he, Polynomial.map_X, AdjoinRoot.mk_eq_zero] at h1
    exact Polynomial.X_ne_zero (Polynomial.eq_zero_of_dvd_of_natDegree_lt h1
      (by rw [Polynomial.natDegree_X, hΦ.1.natDegree_map]; omega))
  let := hfield.toField
  exact isUnit_iff_ne_zero.mpr hne

/-! ### Adic completeness -/

/-- The ideal `(T, X)` is the span of the two variables of `O[[T,X]]`. -/
private theorem variableIdeal_eq_span_range_X (O : Type) [CommRing O] :
    variableIdeal O = Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → TwoSeries O)) := by
  unfold variableIdeal
  congr 1
  ext x
  simp [axisT, axisX, Fin.exists_fin_two, eq_comm]

/-- `O[[T,X]]` is complete for the ideal `(T, X)`. -/
private theorem twoSeries_isAdicComplete_variableIdeal (O : Type) [CommRing O] :
    IsAdicComplete (variableIdeal O) (TwoSeries O) := by
  rw [variableIdeal_eq_span_range_X]
  infer_instance

/-- Over a nontrivial ring, `(T, X)` is a proper ideal of `O[[T,X]]`. -/
private theorem variableIdeal_ne_top (O : Type) [CommRing O] [Nontrivial O] :
    variableIdeal O ≠ ⊤ := by
  intro h
  have h1 : (1 : TwoSeries O) ∈ variableIdeal O := h ▸ Submodule.mem_top
  rw [variableIdeal, axisT, axisX, mvPowerSeries_fin_two_mem_variableIdeal_iff] at h1
  simp at h1

/-- The concrete surface is complete for its parameter ideal `(t, x)`. -/
theorem concrete_surface_isAdicComplete_parameterIdeal (O : Type) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    IsAdicComplete (surfaceParameterIdeal O pi u a b) (ConcreteSurface O pi u a b) := by
  have := twoSeries_isAdicComplete_variableIdeal O
  have e : surfaceParameterIdeal O pi u a b =
      (variableIdeal O).map (Ideal.Quotient.mk (surfaceIdeal O pi u a b)) := by
    unfold surfaceParameterIdeal variableIdeal
    rw [Ideal.map_span, Set.image_pair]
    rfl
  exact e ▸ isAdicComplete_quotient_of_iInf_sup_pow (TwoSeries O) (variableIdeal O)
    (surfaceIdeal O pi u a b)
    (iInf_sup_pow_eq_of_isLocalRing (TwoSeries O) _ _ (variableIdeal_ne_top O))

/-- The concrete surface is complete for its maximal ideal. -/
theorem concrete_surface_isAdicComplete_maximalIdeal (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [IsLocalRing (ConcreteSurface O pi u a b)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b))
      (ConcreteSurface O pi u a b) := by
  rw [concrete_surface_maximalIdeal_eq O pi hpi u a b ha]
  exact concrete_surface_isAdicComplete_parameterIdeal O pi u a b

/-- The concrete surface is complete for the ideal generated by the image of `π`. -/
theorem concrete_surface_isAdicComplete_span_pi (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    IsAdicComplete (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      (ConcreteSurface O pi u a b) := by
  have : IsLocalRing (ConcreteSurface O pi u a b) :=
    concrete_surface_isLocalRing O pi u a b hpi.not_isUnit ha
  have : IsNoetherianRing (ConcreteSurface O pi u a b) :=
    concrete_surface_isNoetherianRing O pi u a b
  have := concrete_surface_isAdicComplete_maximalIdeal O pi hpi u a b ha
  apply isAdicComplete_of_isAdicComplete_maximalIdeal
  have hle : Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi} ≤
      IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b) := by
    rw [Ideal.span_singleton_le_iff_mem, concrete_surface_maximalIdeal_eq O pi hpi u a b ha]
    have h2 : surfaceMk O pi u a b (surfaceRelation O pi u a b) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have h3 : surfaceMk O pi u a b (MvPowerSeries.C pi) =
        (surfaceUnit O pi u a b : ConcreteSurface O pi u a b) * surfaceT O pi u a b ^ a *
          surfaceX O pi u a b ^ b := by
      have := sub_eq_zero.mp (by simpa [surfaceRelation, map_sub, map_mul, map_pow] using h2)
      simpa [surfaceUnit, surfaceT, surfaceX, map_mul, map_pow] using this
    rw [show algebraMap O (ConcreteSurface O pi u a b) pi =
      surfaceMk O pi u a b (MvPowerSeries.C pi) from rfl, h3]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
      (Ideal.pow_mem_of_mem _ (Ideal.subset_span (by simp)) a ha))
  exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle

/-- Every principal quotient of the concrete surface is `π`-adically complete. -/
theorem concrete_surface_curve_isAdicComplete (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) (f : ConcreteSurface O pi u a b) :
    IsAdicComplete (Ideal.span {pi} : Ideal O) (ConcreteSurface O pi u a b ⧸ Ideal.span {f}) := by
  have : IsLocalRing (ConcreteSurface O pi u a b) :=
    concrete_surface_isLocalRing O pi u a b hpi.not_isUnit ha
  have : IsNoetherianRing (ConcreteSurface O pi u a b) :=
    concrete_surface_isNoetherianRing O pi u a b
  have hI := concrete_surface_isAdicComplete_span_pi O pi hpi u a b ha
  have hItop : Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi} ≠ ⊤ := fun h ↦ by
    have hH := hI.toIsHausdorff
    rw [h] at hH
    exact not_subsingleton _ hH.subsingleton
  have hc := isAdicComplete_quotient_of_iInf_sup_pow _ _ (Ideal.span {f})
    (iInf_sup_pow_eq_of_isLocalRing _ _ (Ideal.span {f}) hItop)
  rw [← IsAdicComplete.map_algebraMap_iff (S := ConcreteSurface O pi u a b ⧸ Ideal.span {f}),
    Ideal.map_span]
  rw [Ideal.map_span] at hc
  simp only [Set.image_singleton] at hc ⊢
  convert hc using 2
  rfl

/-- The concrete surface is `π`-adically complete as an `O`-module. -/
theorem concrete_surface_isAdicComplete_span_pi_base (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    IsAdicComplete (Ideal.span {pi} : Ideal O) (ConcreteSurface O pi u a b) :=
  (IsAdicComplete.map_algebraMap_iff (S := ConcreteSurface O pi u a b) _ _).1 <| by
    rw [Ideal.map_span, Set.image_singleton]
    exact concrete_surface_isAdicComplete_span_pi O pi hpi u a b ha

/-- Over a complete discrete valuation ring, `Oⁿ × R` is `π`-adically complete, where `R` is the
concrete surface. -/
theorem division_coordinate_module_isAdicComplete (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a) (n : ℕ) :
    IsAdicComplete (Ideal.span {pi} : Ideal O) ((Fin n → O) × ConcreteSurface O pi u a b) := by
  have : IsAdicComplete (Ideal.span {pi} : Ideal O) O :=
    dvr_isAdicComplete_span_uniformizer O pi hpi
  have : IsAdicComplete (Ideal.span {pi} : Ideal O) (Fin n → O) :=
    finite_free_adic_complete O (Fin n → O) _
  have := concrete_surface_isAdicComplete_span_pi_base O pi hpi u a b ha
  exact isAdicComplete_prod O _ _ _

end SurfaceBlowup
