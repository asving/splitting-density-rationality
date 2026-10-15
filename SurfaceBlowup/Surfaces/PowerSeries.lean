/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Formula.LawAlgebra
import SurfaceBlowup.Surfaces.Lengths

/-!
# Power series, residue bases and the local structure of concrete surfaces

Commutative algebra of the power series rings `A[[T,X]]` and `k[[X]]` used to analyse the
concrete surfaces `O[[T,X]]/(π - u T^a X^b)` over a discrete valuation ring `O` with residue
field `k`: the ideal `(T, X)` and regular elements of `A[[T,X]]`, kernels of the reduction maps,
lengths of quotients of `k[[X]]`, residue basis families (bases modulo `π` lifting to bases), and
the local structure of the concrete surface (maximal ideal `(t, x)`, residue field, special fiber).

## Main results

* `mvPowerSeries_fin_two_mem_variableIdeal_iff`,
  `mvPowerSeries_fin_two_quotient_var_regular_mod_var`: the ideal `(T, X)` and regular sequences
  in `A[[T,X]]`.
* `powerSeries_quotient_length_eq_order`: `ℓ(k[[X]]/(g)) = ord g`.
* `residue_basis_family_of_length`, `residue_basis_family_basis`: residue basis families.
* `concrete_surface_special_fiber_equiv`, `concrete_surface_maximalIdeal_eq`,
  `concrete_surface_isLocalRing`, `concrete_surface_base_injective`: structure of the concrete
  surface.

Provenance: the `Thm_SurfaceBlowupV2_*` nodes named after the theorems of this file.
-/

noncomputable section

namespace SurfaceBlowup

/-! ### Power series in two variables -/

private theorem mvPowerSeries_X_ne_zero {σ A : Type} [CommRing A] [Nontrivial A] (s : σ) :
    (MvPowerSeries.X s : MvPowerSeries σ A) ≠ 0 := fun h ↦ by
  simpa [h] using MvPowerSeries.coeff_index_single_self_X (R := A) s

/-- A series lies in `(T^a X^b)` iff its coefficients vanish outside the quadrant
`a ≤ m 0, b ≤ m 1`. -/
theorem monomialIdeal_mem_iff (k : Type) [CommRing k] (a b : ℕ) (φ : TwoSeries k) :
    φ ∈ monomialIdeal k a b ↔ ∀ m : Fin 2 →₀ ℕ, ¬(a ≤ m 0 ∧ b ≤ m 1) →
    MvPowerSeries.coeff m φ = 0 := by
  set n₀ : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b with hn₀
  have hgen : axisT k ^ a * axisX k ^ b = MvPowerSeries.monomial n₀ (1 : k) := by
    simp only [axisT, axisX, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul,
      hn₀]
  have hle : ∀ m : Fin 2 →₀ ℕ, n₀ ≤ m ↔ (a ≤ m 0 ∧ b ≤ m 1) := by
    intro m
    rw [Finsupp.le_def, Fin.forall_fin_two]
    simp [hn₀]
  unfold monomialIdeal
  rw [hgen, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨ψ, rfl⟩ m hm
    rw [MvPowerSeries.coeff_monomial_mul, if_neg (by rwa [hle])]
  · intro h
    obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPowerSeries (Fin 2) k,
        ∀ m, MvPowerSeries.coeff m ψ = MvPowerSeries.coeff (m + n₀) φ :=
      ⟨fun m ↦ MvPowerSeries.coeff (m + n₀) φ, fun m ↦ rfl⟩
    refine ⟨ψ, ?_⟩
    ext m
    rw [MvPowerSeries.coeff_monomial_mul, one_mul]
    split_ifs with hm
    · rw [hψ, tsub_add_cancel_of_le hm]
    · exact h m (by rwa [hle] at hm)

/-- A two-variable series lies in `(X 0, X 1)` iff its constant coefficient vanishes. -/
theorem mvPowerSeries_fin_two_mem_variableIdeal_iff (A : Type) [CommRing A]
    (g : MvPowerSeries (Fin 2) A) :
    g ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1} ↔
    MvPowerSeries.constantCoeff g = 0 := by
  refine (pow_one (Ideal.span {axisT A, axisX A}) ▸ axis_ideal_pow_mem_iff A 1 g).trans
    ⟨fun h ↦ h 0 (by simp), fun h m hm ↦ ?_⟩
  obtain rfl : m = 0 := by ext i; fin_cases i <;> simp <;> omega
  exact h

/-- A two-variable series with zero constant coefficient splits as `X t * h₁ + X s * q`. -/
private theorem mvPowerSeries_fin_two_split_of_constantCoeff_zero (A : Type) [CommRing A]
    (s t : Fin 2)
    (hst : s ≠ t) (h : MvPowerSeries (Fin 2) A) (h0 : MvPowerSeries.constantCoeff h = 0) :
    ∃ h₁ q : MvPowerSeries (Fin 2) A, h = MvPowerSeries.X t * h₁ + MvPowerSeries.X s * q := by
  obtain ⟨a, b, rfl⟩ :=
    Ideal.mem_span_pair.mp ((mvPowerSeries_fin_two_mem_variableIdeal_iff A h).2 h0)
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : s = 0 ∧ t = 1 ∨ s = 1 ∧ t = 0 := by omega
  exacts [⟨b, a, by ring⟩, ⟨a, b, by ring⟩]

/-- The kernel of `O[[T,X]] → O → k` (constant coefficient, then residue) is `(π, T, X)`. -/
private theorem constantCoeff_residue_ker (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    (pi : O) (hpi : Irreducible pi) :
    RingHom.ker ((IsLocalRing.residue O).comp (MvPowerSeries.constantCoeff : TwoSeries O →+* O)) =
    Ideal.span {(MvPowerSeries.C pi : TwoSeries O), axisT O, axisX O} := by
  have key : ∀ g : TwoSeries O,
      g ∈ RingHom.ker
          ((IsLocalRing.residue O).comp (MvPowerSeries.constantCoeff : TwoSeries O →+* O)) ↔
        pi ∣ MvPowerSeries.constantCoeff g := by
    intro g
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hpi.maximalIdeal_eq,
      Ideal.mem_span_singleton]
  ext g
  rw [key]
  constructor
  · rintro ⟨c, hc⟩
    have h2 : g - MvPowerSeries.C (pi * c) ∈
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O), MvPowerSeries.X 1} := by
      rw [mvPowerSeries_fin_two_mem_variableIdeal_iff]
      simp [hc]
    have h3 : g = MvPowerSeries.C pi * MvPowerSeries.C c + (g - MvPowerSeries.C (pi * c)) := by
      rw [map_mul]; ring
    rw [h3]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))) ?_
    refine Ideal.span_mono (fun y hy ↦ ?_) h2
    rcases hy with rfl | rfl <;> simp [axisT, axisX]
  · intro h
    have : Ideal.span {(MvPowerSeries.C pi : TwoSeries O), axisT O, axisX O} ≤
        RingHom.ker ((IsLocalRing.residue O).comp
          (MvPowerSeries.constantCoeff : TwoSeries O →+* O)) := by
      rw [Ideal.span_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [SetLike.mem_coe, key]
      rcases hy with rfl | rfl | rfl <;> simp [axisT, axisX]
    exact (key g).1 (this h)

/-- If the constant coefficient of `P` is a nonzerodivisor and `X s ∣ P * h`, then `X s ∣ h`. -/
private theorem mvPowerSeries_var_dvd_of_var_dvd_mul (σ A : Type) [CommRing A] (s : σ)
    (P h : MvPowerSeries σ A) (hP : MvPowerSeries.constantCoeff P ∈ nonZeroDivisors A)
    (hdvd : (MvPowerSeries.X s : MvPowerSeries σ A) ∣ P * h) :
    (MvPowerSeries.X s : MvPowerSeries σ A) ∣ h := by
  classical
  rw [MvPowerSeries.X_dvd_iff] at hdvd ⊢
  intro m
  induction m using WellFoundedLT.induction with
  | _ e he =>
  intro hes
  have key := hdvd e hes
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (0, e),
    MvPowerSeries.coeff_zero_eq_constantCoeff] at key
  · exact (mem_nonZeroDivisors_iff_left.mp hP) _ key
  · rintro ⟨u, v⟩ huv hne
    have hsum : u + v = e := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    have hu : u ≠ 0 := by
      rintro rfl
      simp_all
    have hlt : v < e := lt_of_le_of_ne (hsum ▸ le_add_self) fun hve ↦
      hu (add_eq_right.mp (hsum.trans hve.symm))
    have hvs : v s = 0 := by
      have := DFunLike.congr_fun hsum s
      simp only [Finsupp.add_apply] at this
      omega
    simp [he v hlt hvs]
  · simp

/-- If `P` has nonzero constant coefficient over a domain, then `X s` is a nonzerodivisor
modulo `P`. -/
theorem mvPowerSeries_quotient_var_regular (σ A : Type) [CommRing A] [IsDomain A] (s : σ)
    (P : MvPowerSeries σ A) (hP : MvPowerSeries.constantCoeff P ≠ 0) :
    Function.Injective
    (fun g : MvPowerSeries σ A ⧸ Ideal.span {P} ↦ Ideal.Quotient.mk (Ideal.span {P})
      (MvPowerSeries.X s) * g) := by
  intro a b hab
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [← map_mul] at hab
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← mul_sub] at hab
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  obtain ⟨h, hh⟩ := hab
  have hX : (MvPowerSeries.X s : MvPowerSeries σ A) ∣ P * h := ⟨g - g', hh.symm⟩
  obtain ⟨h1, rfl⟩ := mvPowerSeries_var_dvd_of_var_dvd_mul σ A s P h
    (mem_nonZeroDivisors_of_ne_zero hP) hX
  exact ⟨h1, mul_left_cancel₀ (mvPowerSeries_X_ne_zero s) (by rw [hh]; ring)⟩

/-- For distinct variables, `X t ∣ X s * w` implies `X t ∣ w`. -/
private theorem mvPowerSeries_var_dvd_of_var_dvd_other_var_mul (σ A : Type) [CommRing A] (s t : σ)
    (hst : s ≠ t) (w : MvPowerSeries σ A)
    (hdvd : (MvPowerSeries.X t : MvPowerSeries σ A) ∣ MvPowerSeries.X s * w) :
    (MvPowerSeries.X t : MvPowerSeries σ A) ∣ w := by
  rw [MvPowerSeries.X_dvd_iff] at hdvd ⊢
  intro m hm
  have h := hdvd (m + Finsupp.single s 1) (by simp [hm, Finsupp.single_eq_of_ne hst.symm])
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul] at h
  simpa using h

/-- If `P` has nonzero constant coefficient over a domain, then `X t` is a nonzerodivisor
modulo `(P, X s)` for `s ≠ t`. -/
theorem mvPowerSeries_fin_two_quotient_var_regular_mod_var (A : Type) [CommRing A] [IsDomain A]
    (s t : Fin 2) (hst : s ≠ t) (P : MvPowerSeries (Fin 2) A)
    (hP : MvPowerSeries.constantCoeff P ≠ 0) :
    Function.Injective
    (fun g : (MvPowerSeries (Fin 2) A ⧸ Ideal.span {P}) ⧸ Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (MvPowerSeries.X s)} => Ideal.Quotient.mk
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {P}) (MvPowerSeries.X s)})
      (Ideal.Quotient.mk (Ideal.span {P}) (MvPowerSeries.X t)) * g) := by
  set I := Ideal.span {P}
  set J := Ideal.span {Ideal.Quotient.mk I (MvPowerSeries.X s)}
  -- key: kernel is zero
  have key : ∀ g : MvPowerSeries (Fin 2) A,
      Ideal.Quotient.mk J (Ideal.Quotient.mk I (MvPowerSeries.X t * g)) = 0 →
      Ideal.Quotient.mk J (Ideal.Quotient.mk I g) = 0 := by
    intro g hg
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hg
    obtain ⟨r', hr'⟩ := hg
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r'
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hr'
    obtain ⟨h, hh⟩ := hr'
    -- h * P = r * X s - X t * g
    have h0 : MvPowerSeries.constantCoeff h = 0 := by
      simpa [MvPowerSeries.constantCoeff_X, hP] using congrArg MvPowerSeries.constantCoeff hh
    obtain ⟨h₁, q, rfl⟩ :=
      mvPowerSeries_fin_two_split_of_constantCoeff_zero A s t hst h h0
    have hdvd : (MvPowerSeries.X t : MvPowerSeries (Fin 2) A) ∣
        MvPowerSeries.X s * (P * q - r) :=
      ⟨-(g + P * h₁), by linear_combination hh⟩
    obtain ⟨w, hw⟩ :=
      mvPowerSeries_var_dvd_of_var_dvd_other_var_mul (Fin 2) A s t hst _ hdvd
    have hg : g = P * (-h₁) + MvPowerSeries.X s * (-w) := by
      apply mul_left_cancel₀ (mvPowerSeries_X_ne_zero t)
      linear_combination hh - MvPowerSeries.X s * hw
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨Ideal.Quotient.mk I (-w), ?_⟩
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨h₁, by rw [hg]; ring⟩
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  simp only at hab
  rw [← sub_eq_zero] at hab ⊢
  rw [← map_sub, ← map_sub]
  apply key
  rw [map_mul, map_mul, map_sub, map_sub]
  linear_combination hab

/-- Values of `nilpotentEval` on constants and on the two variables. -/
theorem nilpotentEval_apply_generators (O S : Type) [CommRing O] [CommRing S] (φ : O →+* S)
    (e z : S) (he : IsNilpotent e) (hz : IsNilpotent z) :
    (∀ c : O, nilpotentEval φ e z he hz (MvPowerSeries.C c) = φ c) ∧
    nilpotentEval φ e z he hz (axisT O) = e ∧ nilpotentEval φ e z he hz (axisX O) = z := by
  refine ⟨fun c ↦ ?_, ?_, ?_⟩
  · simp [nilpotentEval, MvPowerSeries.map_C]
  · simp only [nilpotentEval, AlgHom.toRingHom_eq_coe, axisT, RingHom.coe_comp, RingHom.coe_coe,
      MvPowerSeries.coe_substAlgHom, Function.comp_apply, MvPowerSeries.map_X]
    rw [MvPowerSeries.subst_X (nilpotentFamily_hasSubst e z he hz)]
    simp [nilpotentFamily]
  · simp only [nilpotentEval, AlgHom.toRingHom_eq_coe, axisX, RingHom.coe_comp, RingHom.coe_coe,
      MvPowerSeries.coe_substAlgHom, Function.comp_apply, MvPowerSeries.map_X]
    rw [MvPowerSeries.subst_X (nilpotentFamily_hasSubst e z he hz)]
    simp [nilpotentFamily]

/-- The kernel of coefficient reduction `O[[T,X]] → k[[T,X]]` is `(π)`. -/
private theorem residueSeries_ker (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (pi : O)
    (hpi : Irreducible pi) :
    RingHom.ker (residueSeries O) = Ideal.span {(MvPowerSeries.C pi : TwoSeries O)} := by
  have key : ∀ g : TwoSeries O, residueSeries O g = 0 ↔ ∀ m, pi ∣ MvPowerSeries.coeff m g := by
    intro g
    unfold residueSeries
    rw [MvPowerSeries.ext_iff]
    refine forall_congr' fun m ↦ ?_
    rw [MvPowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff,
      hpi.maximalIdeal_eq, Ideal.mem_span_singleton]
  ext g
  rw [RingHom.mem_ker, key, Ideal.mem_span_singleton]
  constructor
  · intro h
    choose q hq using h
    let Q : TwoSeries O := q
    refine ⟨Q, ?_⟩
    ext m
    rw [MvPowerSeries.coeff_C_mul, hq m]
    rfl
  · rintro ⟨q, rfl⟩ m
    rw [MvPowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _

/-- Coefficient reduction `O[[T,X]] → k[[T,X]]` is surjective. -/
private theorem residueSeries_surjective (O : Type) [CommRing O] [IsLocalRing O] :
    Function.Surjective (residueSeries O) := by
  intro ψ
  refine ⟨fun m ↦
    Classical.choose (IsLocalRing.residue_surjective (R := O) (MvPowerSeries.coeff m ψ)), ?_⟩
  ext m
  have := Classical.choose_spec (IsLocalRing.residue_surjective (R := O) (MvPowerSeries.coeff m ψ))
  exact (MvPowerSeries.coeff_map (IsLocalRing.residue O) m _).trans this

/-- The kernel of `O[[T,X]] → k[[T,X]]/(T^a X^b)` is `(π, T^a X^b)`. -/
private theorem residueSeries_comp_monomial_ker (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (a b : ℕ) :
    RingHom.ker
    ((Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a b)).comp (residueSeries O)) =
    Ideal.span {(MvPowerSeries.C pi : TwoSeries O), axisT O ^ a * axisX O ^ b} := by
  have hker := residueSeries_ker O pi hpi
  have hmono : residueSeries O (axisT O ^ a * axisX O ^ b) =
      axisT (IsLocalRing.ResidueField O) ^ a * axisX (IsLocalRing.ResidueField O) ^ b := by
    simp [residueSeries, axisT, axisX, MvPowerSeries.map_X]
  ext g
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, monomialIdeal,
    Ideal.mem_span_singleton', Ideal.mem_span_pair]
  constructor
  · rintro ⟨ψ, hψ⟩
    obtain ⟨q, hq⟩ := residueSeries_surjective O ψ
    have h0 : g - q * (axisT O ^ a * axisX O ^ b) ∈ RingHom.ker (residueSeries O) := by
      rw [RingHom.mem_ker, map_sub, map_mul, hq, hmono, ← hψ, mul_comm, sub_self]
    rw [hker, Ideal.mem_span_singleton'] at h0
    obtain ⟨c, hc⟩ := h0
    exact ⟨c, q, by rw [hc]; ring⟩
  · rintro ⟨c, q, hcq⟩
    refine ⟨residueSeries O q, ?_⟩
    have h1 : residueSeries O (MvPowerSeries.C pi) = 0 := by
      rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span rfl
    rw [← hcq, map_add, map_mul, map_mul, h1, hmono]; ring

private theorem coeff_killT (O : Type) [CommRing O] (g : TwoSeries O) (n : ℕ) :
    PowerSeries.coeff n (killT O g) = MvPowerSeries.coeff (Finsupp.single 1 n) g :=
  coeff_substAlgHom_kill O _ (killTFamily_hasSubst O) 0 1 (by decide) rfl rfl g n

private theorem coeff_residueKillT (O : Type) [CommRing O] [IsLocalRing O] (g : TwoSeries O)
    (n : ℕ) :
    PowerSeries.coeff n (residueKillT O g) =
      IsLocalRing.residue O (MvPowerSeries.coeff (Finsupp.single 1 n) g) := by
  rw [← coeff_killT]
  rfl

/-- Values of `residueKillT` on generators; it is surjective with kernel `(π, T)`. -/
theorem residueKillT_apply_ker (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (pi : O) (hpi : Irreducible pi) :
    (∀ c : O, residueKillT O (MvPowerSeries.C c) = PowerSeries.C (IsLocalRing.residue O c)) ∧
    residueKillT O (axisT O) = 0 ∧ residueKillT O (axisX O) = PowerSeries.X ∧
    Function.Surjective (residueKillT O) ∧
    RingHom.ker (residueKillT O) = Ideal.span {MvPowerSeries.C pi, axisT O} := by
  refine ⟨fun c ↦ ?_, ?_, ?_, ?_, ?_⟩
  · ext n
    rw [coeff_residueKillT]
    by_cases hn : n = 0
    · subst hn; simp [MvPowerSeries.coeff_C]
    · simp [MvPowerSeries.coeff_C, PowerSeries.coeff_C, hn]
  · ext n
    rw [coeff_residueKillT]
    simp [axisT, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff]
  · ext n
    rw [coeff_residueKillT]
    by_cases hn : n = 1
    · subst hn; simp [axisX, MvPowerSeries.coeff_X]
    · simp [axisX, MvPowerSeries.coeff_X, PowerSeries.coeff_X, hn, Finsupp.single_eq_single_iff]
  · intro h
    let g : TwoSeries O := fun m ↦
      if m 0 = 0 then (IsLocalRing.residue_surjective (PowerSeries.coeff (m 1) h)).choose else 0
    refine ⟨g, ?_⟩
    ext n
    rw [coeff_residueKillT]
    change IsLocalRing.residue O (if _ then _ else _) = _
    simp only [Finsupp.single_apply, one_ne_zero, ↓reduceIte]
    exact (IsLocalRing.residue_surjective (PowerSeries.coeff n h)).choose_spec
  · ext g
    rw [RingHom.mem_ker, axisT, mvPowerSeries_mem_span_C_var_iff]
    have hm : ∀ x : O, IsLocalRing.residue O x = 0 ↔ pi ∣ x := by
      intro x
      rw [IsLocalRing.residue_eq_zero_iff, hpi.maximalIdeal_eq, Ideal.mem_span_singleton]
    constructor
    · intro hg m hm0
      have := congrArg (PowerSeries.coeff (m 1)) hg
      rw [coeff_residueKillT, map_zero, hm] at this
      have hmeq : Finsupp.single 1 (m 1) = m := by
        ext i; fin_cases i <;> simp [hm0]
      rwa [hmeq] at this
    · intro hg
      ext n
      rw [coeff_residueKillT, map_zero, hm]
      exact hg _ (by simp)

/-! ### One-variable power series and polynomials -/

/-- The point-count expression evaluates to `(1/δ) ∑_{j ∣ δ} μ(j) q^(δ/j)`. -/
theorem pointCount_eval (δ : ℕ) (q : ℚ) :
    (pointCount δ).eval q = (1/(δ:ℚ)) * ∑ j ∈ δ.divisors, ((ArithmeticFunction.moebius j : ℤ) : ℚ) *
    q ^ (δ / j) := by
  unfold pointCount
  rw [Expr.eval, Expr.eval, expression_sum_eval, List.map_map]
  congr 1
  rw [← Finset.sum_map_toList]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [Expr.eval, expression_pow_eval]

/-- Hensel uniqueness: two roots of `f` congruent modulo the maximal ideal coincide when
`f'(x)` is a unit. -/
theorem polynomial_root_unique_of_derivative_isUnit (S : Type) [CommRing S] [IsLocalRing S]
    (f : Polynomial S) (x y : S) (hx : Polynomial.eval x f = 0) (hy : Polynomial.eval y f = 0)
    (hxy : y - x ∈ IsLocalRing.maximalIdeal S)
    (hd : IsUnit (Polynomial.eval x (Polynomial.derivative f))) :
    y = x := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion f x (y - x)
  have hy' : x + (y - x) = y := by ring
  rw [hy', hy, hx] at hk
  have h0 : (y - x) * (Polynomial.eval x (Polynomial.derivative f) + k * (y - x)) = 0 := by
    linear_combination -hk
  have hw : IsUnit (Polynomial.eval x (Polynomial.derivative f) + k * (y - x)) := by
    by_contra hn
    have h := (IsLocalRing.maximalIdeal S).sub_mem ((IsLocalRing.mem_maximalIdeal _).2 hn)
      (Ideal.mul_mem_left _ k hxy)
    exact (IsLocalRing.mem_maximalIdeal _).mp (by rwa [add_sub_cancel_right] at h) hd
  exact sub_eq_zero.mp (hw.mul_left_eq_zero.mp h0)

/-- `k[[X]]/(X^r)` has length `r`. -/
private theorem powerSeries_quotient_X_pow_length (k : Type) [Field k] (r : ℕ) :
    Module.length (PowerSeries k) (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ r})
    = r := by
  rw [← Ideal.span_singleton_pow, ← PowerSeries.maximalIdeal_eq_span_X]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal _ r

/-- `k[[X]]/(g)` has length equal to the order of `g`, and multiplication by `g` is injective
iff `g ≠ 0`. -/
theorem powerSeries_quotient_length_eq_order (k : Type) [Field k] (g : PowerSeries k) :
    Module.length (PowerSeries k) (PowerSeries k ⧸ Ideal.span {g}) = g.order ∧
    (Function.Injective (fun w : PowerSeries k ↦ g * w) ↔ g ≠ 0) := by
  refine ⟨?_, ?_⟩
  · by_cases hg : g = 0
    · subst hg
      rw [PowerSeries.order_zero]
      refine ENat.eq_top_iff_forall_ge.mpr (fun r ↦ ?_)
      have hle : Ideal.span {(0 : PowerSeries k)} ≤
          Ideal.span {(PowerSeries.X : PowerSeries k) ^ r} := by
        rw [Ideal.span_singleton_le_span_singleton]; exact dvd_zero _
      rw [← powerSeries_quotient_X_pow_length k r]
      exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    · have hu : IsUnit (PowerSeries.divXPowOrder g) := by
        rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
        exact PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hg
      have hspan : Ideal.span {g} =
          Ideal.span {(PowerSeries.X : PowerSeries k) ^ g.order.toNat} := by
        conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := g)]
        exact Ideal.span_singleton_mul_right_unit hu _
      rw [hspan, powerSeries_quotient_X_pow_length k,
        ENat.natCast_toNat (PowerSeries.order_eq_top.not.mpr hg)]
  · refine ⟨fun h hg ↦ ?_, mul_right_injective₀⟩
    subst hg
    exact one_ne_zero (h (show (0 : PowerSeries k) * 1 = 0 * 0 by simp))

/-! ### Residue basis families -/

/-- A residue basis family of a quotient `Q` of `M` (with kernel `π M`) lifts to `M`. -/
theorem residue_basis_family_lift_along_reduction (O M Q : Type) [CommRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module O Q] (pi : O) (q : M →ₗ[O] Q) (hq : Function.Surjective q)
    (hkq : ∀ m : M, q m = 0 ↔ ∃ w : M, m = pi • w) {N : ℕ} (γ : Fin N → Q)
    (hγ : ResidueBasisFamily pi γ) :
    ∃ β : Fin N → M, (∀ i, q (β i) = γ i) ∧ ResidueBasisFamily pi β := by
  choose β hβ using fun i ↦ hq (γ i)
  refine ⟨β, hβ, ?_, ?_⟩
  · intro m
    obtain ⟨z, m', h⟩ := hγ.1 (q m)
    obtain ⟨m₀, hm₀⟩ := hq m'
    have h0 : q (m - ((∑ i, z i • β i) + pi • m₀)) = 0 := by
      simp [map_sum, hβ, hm₀, ← h]
    obtain ⟨w, hw⟩ := (hkq _).1 h0
    refine ⟨z, m₀ + w, ?_⟩
    rw [smul_add, ← add_assoc, ← hw]
    abel
  · intro z ⟨w, hw⟩
    apply hγ.2 z
    refine ⟨q w, ?_⟩
    have := congrArg q hw
    simpa [map_sum, hβ] using this

/-- Over a `π`-adically separated ring, a residue basis family of a `π`-torsion-free module
is linearly independent. -/
private theorem residue_basis_family_linearIndependent (O M : Type) [CommRing O] [AddCommGroup M]
    [Module O M] (pi : O) [IsHausdorff (Ideal.span {pi}) O] (hreg : ∀ m : M, pi • m = 0 → m = 0)
    {N : ℕ} (β : Fin N → M) (hβ : ResidueBasisFamily pi β) :
    LinearIndependent O β := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hregk : ∀ k : ℕ, ∀ m : M, pi ^ k • m = 0 → m = 0 := by
    intro k
    induction k with
    | zero => intro m h; simpa using h
    | succ k ih =>
      intro m h
      rw [pow_succ, mul_smul] at h
      exact hreg m (ih _ h)
  have key : ∀ k : ℕ, ∀ i, pi ^ k ∣ g i := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      choose y hy using ih
      have hsum : ∑ i, y i • β i = 0 := by
        apply hregk k
        rw [Finset.smul_sum]
        simp_rw [smul_smul, ← hy]
        exact hg
      have hdiv := hβ.2 y ⟨0, by rw [hsum, smul_zero]⟩
      intro i
      obtain ⟨c, hc⟩ := hdiv i
      exact ⟨c, by rw [hy i, hc, pow_succ, mul_assoc]⟩
  intro i
  apply IsHausdorff.haus (I := Ideal.span {pi}) (M := O) inferInstance
  intro n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact key n i

/-- A residue basis family of `M₁` extends by one vector to `M` when `M/M₁` is simple. -/
private theorem residue_basis_family_of_simple_quotient (O B M : Type) [CommRing O] [CommRing B]
    [IsLocalRing B] [Algebra O B] [AddCommGroup M] [Module B M] [Module O M] [IsScalarTower O B M]
    (pi : O) (hsurj : ∀ b : B, ∃ c : O, b - algebraMap O B c ∈ IsLocalRing.maximalIdeal B)
    (hker : ∀ c : O, algebraMap O B c ∈ IsLocalRing.maximalIdeal B → pi ∣ c)
    (hpiM : ∀ m : M, pi • m = 0) (M₁ : Submodule B M) [IsSimpleModule B (M ⧸ M₁)] {N : ℕ}
    (β : Fin N → M) (hβM₁ : ∀ i, β i ∈ M₁)
    (hβ : ResidueBasisFamily pi (fun i ↦ (⟨β i, hβM₁ i⟩ : M₁))) :
    ∃ γ : Fin (N+1) → M, ResidueBasisFamily pi γ := by
  have : Nontrivial (M ⧸ M₁) := IsSimpleModule.nontrivial B _
  obtain ⟨x, hx⟩ := exists_ne (0 : M ⧸ M₁)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective M₁ x
  have hspan := IsSimpleModule.toSpanSingleton_surjective B hx
  -- the annihilator of `v̄ ∈ M/M₁` is the maximal ideal of `B`
  have hann (b : B) :
      b • (Submodule.Quotient.mk v : M ⧸ M₁) = 0 ↔ b ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsLocalRing.eq_maximalIdeal (IsSimpleModule.ker_toSpanSingleton_isMaximal B hx),
      LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  have hOsmul (c : O) (m : M) : c • m = algebraMap O B c • m := (algebraMap_smul B c m).symm
  refine ⟨Fin.snoc β v, ?_, ?_⟩
  · intro m
    obtain ⟨b, hb⟩ := hspan (Submodule.Quotient.mk m)
    rw [LinearMap.toSpanSingleton_apply] at hb
    obtain ⟨c, hc⟩ := hsurj b
    have hmem : m - c • v ∈ M₁ := by
      rw [← Submodule.Quotient.eq, ← hb, hOsmul, Submodule.Quotient.mk_smul, ← sub_eq_zero,
        ← sub_smul]
      exact (hann _).2 hc
    obtain ⟨z, m', hz⟩ := hβ.1 ⟨m - c • v, hmem⟩
    refine ⟨Fin.snoc z c, 0, ?_⟩
    have hz' := congrArg Subtype.val hz
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul_of_tower] at hz'
    rw [hpiM, add_zero] at hz'
    rw [Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last, hpiM, ← hz']
  · intro z ⟨m', hm'⟩
    rw [Fin.sum_univ_castSucc, hpiM] at hm'
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hm'
    have hSmem : (∑ i : Fin N, z (Fin.castSucc i) • β i) ∈ M₁ :=
      Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_of_tower_mem _ _ (hβM₁ i))
    have hlast : pi ∣ z (Fin.last N) := by
      refine hker _ ((hann _).1 ?_)
      have h := congrArg (Submodule.Quotient.mk (p := M₁)) hm'
      rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero M₁).mpr hSmem, zero_add,
        hOsmul, Submodule.Quotient.mk_smul] at h
      simpa using h
    obtain ⟨y, hy⟩ := hlast
    have hv0 : z (Fin.last N) • v = 0 := by
      rw [hy, mul_comm, mul_smul, hpiM, smul_zero]
    rw [hv0, add_zero] at hm'
    have hcast := hβ.2 (fun i ↦ z (Fin.castSucc i)) ⟨0, by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, smul_zero,
        Submodule.coe_zero]
      exact hm'⟩
    exact fun i ↦ Fin.lastCases ⟨y, hy⟩ hcast i

/-- A module of length `N` killed by `π` has a residue basis family of size `N`. -/
theorem residue_basis_family_of_length (O B M : Type) [CommRing O] [CommRing B] [IsLocalRing B]
    [Algebra O B] [AddCommGroup M] [Module B M] [Module O M] [IsScalarTower O B M] (pi : O)
    (hsurj : ∀ b : B, ∃ c : O, b - algebraMap O B c ∈ IsLocalRing.maximalIdeal B)
    (hker : ∀ c : O, algebraMap O B c ∈ IsLocalRing.maximalIdeal B → pi ∣ c)
    (hpiM : ∀ m : M, pi • m = 0) (N : ℕ) (hN : Module.length B M = N) :
    ∃ β : Fin N → M, ResidueBasisFamily pi β := by
  induction N generalizing M with
  | zero =>
    have hs : Subsingleton M := Module.length_eq_zero_iff.mp (by simpa using hN)
    refine ⟨Fin.elim0, fun m ↦ ⟨Fin.elim0, 0, Subsingleton.elim _ _⟩, fun z _ i ↦ i.elim0⟩
  | succ n ih =>
    have hfin : IsFiniteLength B M :=
      Module.length_ne_top_iff.mp (by rw [hN]; exact ENat.natCast_ne_top _)
    have hNoeth : IsNoetherian B M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
    have hnt : Nontrivial M := Module.length_pos_iff.mp (by rw [hN]; exact_mod_cast Nat.succ_pos n)
    obtain ⟨M₁, hco, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule B M)).resolve_left bot_ne_top
    have : IsSimpleModule B (M ⧸ M₁) := (isSimpleModule_iff_isCoatom).mpr hco
    have hadd := Module.length_eq_add_of_exact M₁.subtype M₁.mkQ M₁.injective_subtype
      M₁.mkQ_surjective (LinearMap.exact_subtype_mkQ M₁)
    rw [Module.length_eq_one B (M ⧸ M₁), hN] at hadd
    have hM₁ : Module.length B M₁ = n := by
      have : Module.length B M₁ ≠ ⊤ := by
        intro h; rw [h] at hadd; simp at hadd
      lift Module.length B M₁ to ℕ using this with k hk
      norm_cast at hadd ⊢
      omega
    obtain ⟨β, hβ⟩ := ih M₁ (fun m ↦ Subtype.ext (by simpa using hpiM m)) hM₁
    exact residue_basis_family_of_simple_quotient O B M pi hsurj hker hpiM M₁
      (fun i ↦ (β i : M)) (fun i ↦ (β i).2) (by simpa using hβ)

/-- Over a `π`-adically complete ring, a residue basis family of a separated module spans it. -/
private theorem residue_basis_family_spans (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]
    (pi : O)
    [IsAdicComplete (Ideal.span {pi}) O] [IsHausdorff (Ideal.span {pi}) M] {N : ℕ} (β : Fin N → M)
    (hβ : ResidueBasisFamily pi β) :
    Submodule.span O (Set.range β) = ⊤ := by
  set I : Ideal O := Ideal.span {pi} with hI
  have hpow : ∀ n : ℕ, pi ^ n ∈ I ^ n := fun n ↦
    Ideal.pow_mem_pow (Ideal.mem_span_singleton_self pi) n
  have memO : ∀ (n : ℕ) (y : O), pi ^ n * y ∈ (I ^ n • ⊤ : Submodule O O) := fun n y ↦
    Submodule.smul_mem_smul (hpow n) Submodule.mem_top
  choose zf mf hf using hβ.1
  refine eq_top_iff.mpr fun m _ ↦ ?_
  let seq : ℕ → M := fun n ↦ Nat.rec m (fun _ x ↦ mf x) n
  have seq_succ : ∀ n, seq (n + 1) = mf (seq n) := fun n ↦ rfl
  let z : ℕ → Fin N → O := fun n ↦ zf (seq n)
  let c : ℕ → Fin N → O := fun n i ↦ ∑ j ∈ Finset.range n, pi ^ j * z j i
  have inv : ∀ n, m = (∑ i, c n i • β i) + pi ^ n • seq n := by
    intro n
    induction n with
    | zero => simp [c, seq]
    | succ n ih =>
      rw [ih, hf (seq n), seq_succ]
      simp only [c, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, smul_add,
        Finset.smul_sum, smul_smul, pow_succ, add_assoc]
      rfl
  have cauchy : ∀ i, ∃ L : O, ∀ n, c n i ≡ L [SMOD (I ^ n • ⊤ : Submodule O O)] := by
    intro i
    refine IsPrecomplete.prec inferInstance ?_
    intro a b hab
    rw [SModEq.sub_mem, ← neg_mem_iff, neg_sub]
    change ∑ j ∈ Finset.range b, pi ^ j * z j i - ∑ j ∈ Finset.range a, pi ^ j * z j i ∈ _
    rw [← Finset.sum_Ico_eq_sub _ hab]
    refine Submodule.sum_mem _ fun j hj ↦ ?_
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Finset.mem_Ico.mp hj).1
    rw [pow_add, mul_assoc]
    exact memO a _
  choose L hL using cauchy
  have key : m = ∑ i, L i • β i := by
    rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := I) inferInstance _ fun n ↦ ?_
    rw [SModEq.zero]
    have : m - ∑ i, L i • β i = (∑ i, (c n i - L i) • β i) + pi ^ n • seq n := by
      conv_lhs => rw [inv n]
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    rw [this]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ ↦ ?_)
      (Submodule.smul_mem_smul (hpow n) Submodule.mem_top)
    have h1 := SModEq.sub_mem.mp (hL i n)
    rw [smul_eq_mul, Ideal.mul_top] at h1
    exact Submodule.smul_mem_smul h1 Submodule.mem_top
  rw [key]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- A residue basis family of a separated torsion-free module over a complete ring is a basis. -/
theorem residue_basis_family_basis (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (pi : O)
    [IsAdicComplete (Ideal.span {pi}) O] [IsHausdorff (Ideal.span {pi}) M]
    (hreg : ∀ m : M, pi • m = 0 → m = 0) {N : ℕ} (β : Fin N → M) (hβ : ResidueBasisFamily pi β) :
    ∃ B : Module.Basis (Fin N) O M, ∀ i, B i = β i := by
  have hs := residue_basis_family_spans O M pi β hβ
  exact ⟨.mk (residue_basis_family_linearIndependent O M pi hreg β hβ) (by rw [hs]), by simp⟩

/-! ### Concrete surfaces -/

/-- In the concrete surface, the image of `s` minus its constant coefficient lies in the
parameter ideal `(t, x)`. -/
theorem concrete_surface_sub_constantCoeff_mem_parameterIdeal (O : Type) [CommRing O] (pi : O)
    (u : (TwoSeries O)ˣ) (a b : ℕ) (s : TwoSeries O) :
    surfaceMk O pi u a b s -
    algebraMap O (ConcreteSurface O pi u a b) (MvPowerSeries.constantCoeff s) ∈
    surfaceParameterIdeal O pi u a b := by
  have h : s - MvPowerSeries.C (MvPowerSeries.constantCoeff s) ∈
      Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O), MvPowerSeries.X 1} := by
    rw [mvPowerSeries_fin_two_mem_variableIdeal_iff]
    simp
  have h2 : surfaceMk O pi u a b (s - MvPowerSeries.C (MvPowerSeries.constantCoeff s)) ∈
      surfaceParameterIdeal O pi u a b := by
    have : Ideal.map (surfaceMk O pi u a b)
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O), MvPowerSeries.X 1}) ≤
        surfaceParameterIdeal O pi u a b := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl
      · exact Ideal.subset_span (by simp [surfaceT, axisT])
      · exact Ideal.subset_span (by simp [surfaceX, axisX])
    exact this (Ideal.mem_map_of_mem _ h)
  convert h2 using 1
  rw [map_sub]
  congr 1

/-- The reduction of the surface relation is `-(ū T^a X^b)`. -/
private theorem residueSeries_surfaceRelation (O : Type) [CommRing O] [IsLocalRing O] (pi : O)
    (hpi : pi ∈ IsLocalRing.maximalIdeal O) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    residueSeries O (surfaceRelation O pi u a b) =
    -(residueSeries O (u : TwoSeries O) * axisT (IsLocalRing.ResidueField O) ^ a *
      axisX (IsLocalRing.ResidueField O) ^ b) := by
  have h0 : IsLocalRing.residue O pi = 0 := (IsLocalRing.residue_eq_zero_iff pi).2 hpi
  have hT : residueSeries O (axisT O) = axisT (IsLocalRing.ResidueField O) := by
    simp [residueSeries, axisT, MvPowerSeries.map_X]
  have hX : residueSeries O (axisX O) = axisX (IsLocalRing.ResidueField O) := by
    simp [residueSeries, axisX, MvPowerSeries.map_X]
  have hC : residueSeries O (MvPowerSeries.C pi) = 0 := by
    simp [residueSeries, MvPowerSeries.map_C, h0]
  unfold surfaceRelation
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, hT, hX, hC, zero_sub]

/-- The constant coefficient of the surface relation is `π` (when `a > 0`). -/
theorem surfaceRelation_constantCoeff (O : Type) [CommRing O] (pi : O) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) :
    MvPowerSeries.constantCoeff (surfaceRelation O pi u a b) = pi := by
  have hT : MvPowerSeries.constantCoeff (axisT O) = 0 := by
    simp [axisT, MvPowerSeries.constantCoeff_X]
  simp [surfaceRelation, hT, ha.ne']

/-- `π` is a nonzerodivisor in the concrete surface. -/
theorem concrete_surface_pi_regular (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    Function.Injective
    (fun r : ConcreteSurface O pi u a b ↦ algebraMap O (ConcreteSurface O pi u a b) pi * r) := by
  set P := surfaceRelation O pi u a b
  have hmem : pi ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hpi.not_isUnit
  have hker := residueSeries_ker O pi hpi
  have hrel := residueSeries_surfaceRelation O pi hmem u a b
  have key : ∀ d : TwoSeries O, MvPowerSeries.C pi * d ∈ surfaceIdeal O pi u a b →
      d ∈ surfaceIdeal O pi u a b := by
    intro d hd
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hd
    have h1 : residueSeries O (MvPowerSeries.C pi) = 0 := by
      rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span rfl
    have h2 : residueSeries O h * residueSeries O P = 0 := by
      rw [← map_mul, hh, map_mul, h1, zero_mul]
    have hX (i : Fin 2) : (MvPowerSeries.X i : TwoSeries (IsLocalRing.ResidueField O)) ≠ 0 :=
      mvPowerSeries_X_ne_zero i
    have hne : residueSeries O P ≠ 0 := by
      rw [hrel, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero _ (hX 0)))
        (pow_ne_zero _ (hX 1))
    have h3 : residueSeries O h = 0 := (mul_eq_zero.1 h2).resolve_right hne
    rw [← RingHom.mem_ker, hker] at h3
    obtain ⟨h₁, rfl⟩ := Ideal.mem_span_singleton'.1 h3
    have hC : (MvPowerSeries.C pi : TwoSeries O) ≠ 0 := by
      intro h0
      exact hpi.ne_zero (MvPowerSeries.C_injective (by simpa using h0))
    have : d = h₁ * P := by
      apply mul_left_cancel₀ hC
      rw [← hh]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  intro r s hrs
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective s
  simp only at hrs
  rw [Ideal.Quotient.eq]
  apply key
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, mul_sub, sub_eq_zero]
  exact hrs

/-- The structure map `O → O[[T,X]]/(π - u T^a X^b)` is injective. -/
theorem concrete_surface_base_injective (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    Function.Injective (algebraMap O (ConcreteSurface O pi u a b)) := by
  have step1 : ∀ c : O, algebraMap O (ConcreteSurface O pi u a b) c = 0 → pi ∣ c := by
    intro c hc
    change Ideal.Quotient.mk _ (MvPowerSeries.C c) = 0 at hc
    rw [Ideal.Quotient.eq_zero_iff_mem, surfaceIdeal, Ideal.mem_span_singleton'] at hc
    obtain ⟨h, hh⟩ := hc
    have := congrArg (MvPowerSeries.constantCoeff) hh
    simp only [surfaceRelation, axisT, axisX, map_mul, map_sub, MvPowerSeries.constantCoeff_C,
      map_pow, MvPowerSeries.constantCoeff_X, zero_pow ha.ne', mul_zero, zero_mul, sub_zero] at this
    exact ⟨_, by rw [← this]; ring⟩
  have step2 : ∀ k : ℕ, ∀ c : O, algebraMap O (ConcreteSurface O pi u a b) c = 0 → pi ^ k ∣ c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro c hc
      obtain ⟨c', rfl⟩ := step1 c hc
      have h0 : algebraMap O (ConcreteSurface O pi u a b) c' = 0 := by
        apply concrete_surface_pi_regular O pi hpi u a b
        simp only
        rw [← map_mul, hc, mul_zero]
      obtain ⟨d, rfl⟩ := ih c' h0
      exact ⟨d, by ring⟩
  rw [injective_iff_map_eq_zero]
  intro c hc
  have hI : Ideal.span {pi} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hpi.not_isUnit
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {pi}) hI
  have : c ∈ ⨅ k : ℕ, Ideal.span {pi} ^ k := by
    rw [Ideal.mem_iInf]
    intro k
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact step2 k c hc
  rw [hbot] at this
  exact (Ideal.mem_bot).1 this

/-- The special fiber of the concrete surface is `k[[T,X]]/(T^a X^b)`, compatibly with
reduction of coefficients. -/
theorem concrete_surface_special_fiber_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    ∃ e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
    ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b, ∀ s :
    TwoSeries O, e
    (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      (surfaceMk O pi u a b s)) =
    Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a b) (residueSeries O s) := by
  set k := IsLocalRing.ResidueField O
  set ψ : TwoSeries O →+* SpecialFiber k a b :=
    (Ideal.Quotient.mk (monomialIdeal k a b)).comp (residueSeries O) with hψdef
  have hψs : Function.Surjective ψ :=
    (Ideal.Quotient.mk_surjective).comp (residueSeries_surjective O)
  have hker : RingHom.ker ψ =
      Ideal.span {(MvPowerSeries.C pi : TwoSeries O), axisT O ^ a * axisX O ^ b} :=
    residueSeries_comp_monomial_ker O pi hpi a b
  have hmax : pi ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 hpi.not_isUnit
  have hle : surfaceIdeal O pi u a b ≤ RingHom.ker ψ := by
    rw [surfaceIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      hψdef, RingHom.comp_apply, residueSeries_surfaceRelation O pi hmax u a b,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.neg_mem_iff, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  set χ : ConcreteSurface O pi u a b →+* SpecialFiber k a b :=
    Ideal.Quotient.lift (surfaceIdeal O pi u a b) ψ fun _ hx ↦ hle hx
  have hχs : Function.Surjective χ := Ideal.Quotient.lift_surjective_of_surjective _ _ hψs
  -- in the surface, `π = u t^a x^b`, so `(π, t^a x^b) = (π)`
  have hrel : surfaceMk O pi u a b (MvPowerSeries.C pi) =
      surfaceMk O pi u a b (u : TwoSeries O) *
        surfaceMk O pi u a b (axisT O ^ a * axisX O ^ b) := by
    rw [← map_mul, surfaceMk, Ideal.Quotient.eq, ← mul_assoc]
    exact Ideal.subset_span rfl
  have hkerχ : RingHom.ker χ = Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi} := by
    rw [show RingHom.ker χ = _ from Ideal.ker_quotient_lift _ _, hker, Ideal.map_span,
      Set.image_pair, Set.pair_comm]
    refine Submodule.span_insert_eq_span ?_
    obtain ⟨v, hv⟩ := u.isUnit.map (surfaceMk O pi u a b)
    refine Ideal.mem_span_singleton'.2 ⟨↑v⁻¹, ?_⟩
    change _ * surfaceMk O pi u a b _ = surfaceMk O pi u a b _
    rw [hrel, ← hv, ← mul_assoc, Units.inv_mul, one_mul]
  exact ⟨(Ideal.quotEquivOfEq hkerχ).symm.trans (RingHom.quotientKerEquivOfSurjective hχs),
    fun _ ↦ rfl⟩

/-- Transport of `powerSeries_quotient_length_eq_order` along an identification of the
concrete surface modulo `t` with `k[[X]]`. -/
theorem concrete_surface_equiv_curve_length_and_regular (S : Type) [CommRing S] (O' : Type)
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O')
    (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (Eq : S ≃+* ConcreteSurface O' pi' u' a' b')
    (q : (ConcreteSurface O' pi' u' a' b' ⧸ Ideal.span {surfaceT O' pi' u' a' b'}) ≃+*
      PowerSeries (IsLocalRing.ResidueField O')) (g : S) :
    Module.length S (S ⧸ Ideal.span {g, Eq.symm (surfaceT O' pi' u' a' b')}) =
    (q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (Eq g))).order ∧
    (Function.Injective
      (fun w : S ⧸ Ideal.span {Eq.symm (surfaceT O' pi' u' a' b')} ↦ Ideal.Quotient.mk
        (Ideal.span {Eq.symm (surfaceT O' pi' u' a' b')}) g * w) ↔
      q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (Eq g)) ≠ 0) := by
  let f : S →+* PowerSeries (IsLocalRing.ResidueField O') :=
    (q.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}))).comp Eq.toRingHom
  have hfs : Function.Surjective f :=
    (q.surjective.comp Ideal.Quotient.mk_surjective).comp Eq.surjective
  have hfx : ∀ x, f x =
      q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'}) (Eq x)) := fun x ↦ rfl
  have hker : RingHom.ker f = Ideal.span {Eq.symm (surfaceT O' pi' u' a' b')} := by
    ext x
    rw [RingHom.mem_ker, hfx, map_eq_zero_iff _ q.injective, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩; exact ⟨Eq.symm c, by rw [← Eq.symm_apply_apply x, hc]; simp⟩
    · rintro ⟨c, hc⟩; exact ⟨Eq c, by rw [hc]; simp⟩
  have hfe : f (Eq.symm (surfaceT O' pi' u' a' b')) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
  obtain ⟨hlen, hinj⟩ := powerSeries_quotient_length_eq_order (IsLocalRing.ResidueField O') (f g)
  change _ = (f g).order ∧ (_ ↔ f g ≠ 0)
  constructor
  · let _ : Algebra S (PowerSeries (IsLocalRing.ResidueField O')) := f.toAlgebra
    have hJ : Ideal.map f (Ideal.span {g, Eq.symm (surfaceT O' pi' u' a' b')}) =
        Ideal.span {f g} := by
      rw [Ideal.map_span, Set.image_pair, hfe, Set.pair_comm, Ideal.span_insert_zero]
    let L : S →ₗ[S] (PowerSeries (IsLocalRing.ResidueField O') ⧸ Ideal.span {f g}) :=
      (Ideal.Quotient.mkₐ S (Ideal.span {f g})).toLinearMap ∘ₗ Algebra.linearMap S _
    have hL : Function.Surjective L := Ideal.Quotient.mk_surjective.comp hfs
    have hLk : LinearMap.ker L = Ideal.span {g, Eq.symm (surfaceT O' pi' u' a' b')} := by
      ext x
      have h1 : L x = Ideal.Quotient.mk _ (f x) := rfl
      rw [LinearMap.mem_ker, h1, Ideal.Quotient.eq_zero_iff_mem, ← hJ, ← Ideal.mem_comap,
        Ideal.comap_map_of_surjective _ hfs, ← RingHom.ker_eq_comap_bot, hker]
      rw [sup_eq_left.mpr (Ideal.span_mono (by simp))]
    rw [((Submodule.quotEquivOfEq _ _ hLk.symm).trans (L.quotKerEquivOfSurjective hL)).length_eq,
      Module.length_eq_of_surjective hfs, hlen]
  · let ψ : (S ⧸ Ideal.span {Eq.symm (surfaceT O' pi' u' a' b')}) ≃+*
        PowerSeries (IsLocalRing.ResidueField O') :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hfs)
    have hψ : ∀ x, ψ (Ideal.Quotient.mk _ x) = f x := fun x ↦ rfl
    have hfun : (fun w : S ⧸ Ideal.span {Eq.symm (surfaceT O' pi' u' a' b')} ↦
        Ideal.Quotient.mk (Ideal.span {Eq.symm (surfaceT O' pi' u' a' b')}) g * w) =
        ψ.symm ∘ (fun w ↦ f g * w) ∘ ψ := by
      funext w
      apply ψ.injective
      simp [map_mul, hψ]
    rw [hfun, ψ.symm.injective.of_comp_iff, Function.Injective.of_comp_iff' _ ψ.bijective, hinj]

/-- The concrete surface modulo `(t, x)` is the residue field of `O`. -/
theorem concrete_surface_quotient_parameters_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    ∃ e : (ConcreteSurface O pi u a b ⧸ surfaceParameterIdeal O pi u a b) ≃+*
    IsLocalRing.ResidueField O, ∀ s :
    TwoSeries O, e (Ideal.Quotient.mk (surfaceParameterIdeal O pi u a b) (surfaceMk O pi u a b s)) =
    IsLocalRing.residue O (MvPowerSeries.constantCoeff s) := by
  set φ : TwoSeries O →+* IsLocalRing.ResidueField O :=
    (IsLocalRing.residue O).comp (MvPowerSeries.constantCoeff : TwoSeries O →+* O) with hφdef
  have hpim : pi ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 hpi.not_isUnit
  have hφ : ∀ s : TwoSeries O, φ s = IsLocalRing.residue O (MvPowerSeries.constantCoeff s) :=
    fun s ↦ rfl
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨MvPowerSeries.C c, by simp [hφ]⟩
  have hkill : ∀ s ∈ surfaceIdeal O pi u a b, φ s = 0 := by
    intro s hs
    rw [surfaceIdeal, Ideal.mem_span_singleton] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [map_mul, hφ, surfaceRelation_constantCoeff O pi u a b ha,
      (IsLocalRing.residue_eq_zero_iff pi).2 hpim, zero_mul]
  set ψ := Ideal.Quotient.lift (surfaceIdeal O pi u a b) φ hkill with hψdef
  have hψsurj : Function.Surjective ψ :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hker : RingHom.ker ψ = surfaceParameterIdeal O pi u a b := by
    apply le_antisymm
    · have hk : RingHom.ker ψ = (RingHom.ker φ).map (Ideal.Quotient.mk _) :=
        Ideal.ker_quotient_lift φ hkill
      rw [hk, hφdef, constantCoeff_residue_ker O pi hpi,
        Ideal.map_span, Ideal.span_le]
      rintro _ ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · have : Ideal.Quotient.mk (surfaceIdeal O pi u a b) (MvPowerSeries.C pi) =
            surfaceMk O pi u a b ((u : TwoSeries O) * axisT O ^ a * axisX O ^ b) := by
          rw [surfaceMk, Ideal.Quotient.eq, surfaceIdeal]
          exact Ideal.subset_span rfl
        rw [SetLike.mem_coe, this, map_mul, map_mul, map_pow, map_pow]
        obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_lt ha
        apply Ideal.mul_mem_right
        apply Ideal.mul_mem_left
        apply Ideal.pow_mem_of_mem _ _ _ (by omega)
        exact Ideal.subset_span (by simp [surfaceT])
      · exact Ideal.subset_span (by simp [surfaceT, surfaceMk])
      · exact Ideal.subset_span (by simp [surfaceX, surfaceMk])
    · rw [surfaceParameterIdeal, Ideal.span_le]
      rintro _ (rfl | rfl)
      · simp [surfaceT, surfaceMk, hψdef, hφ, axisT]
      · simp [surfaceX, surfaceMk, hψdef, hφ, axisX]
  exact ⟨(Ideal.quotEquivOfEq hker).symm.trans (RingHom.quotientKerEquivOfSurjective hψsurj),
    fun _ ↦ rfl⟩

/-- The parameter ideal `(t, x)` of the concrete surface is maximal. -/
theorem concrete_surface_parameterIdeal_isMaximal (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    (surfaceParameterIdeal O pi u a b).IsMaximal := by
  obtain ⟨e, -⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  exact Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))

/-- The maximal ideal of the (local) concrete surface is `(t, x)`. -/
theorem concrete_surface_maximalIdeal_eq (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [IsLocalRing (ConcreteSurface O pi u a b)] :
    IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b) = surfaceParameterIdeal O pi u a b :=
  (IsLocalRing.eq_maximalIdeal (concrete_surface_parameterIdeal_isMaximal O pi hpi u a b ha)).symm

/-- The residue field of the concrete surface is that of `O`, compatibly with `O → R`. -/
theorem concrete_surface_residueField_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [IsLocalRing (ConcreteSurface O pi u a b)] :
    ∃ e : IsLocalRing.ResidueField O ≃+*
    IsLocalRing.ResidueField (ConcreteSurface O pi u a b), ∀ c : O, e (IsLocalRing.residue O c) =
    IsLocalRing.residue (ConcreteSurface O pi u a b)
    (algebraMap O (ConcreteSurface O pi u a b) c) := by
  obtain ⟨f, hf⟩ := concrete_surface_quotient_parameters_equiv O pi hpi u a b ha
  have hm := concrete_surface_maximalIdeal_eq O pi hpi u a b ha
  let g : IsLocalRing.ResidueField (ConcreteSurface O pi u a b) ≃+* IsLocalRing.ResidueField O :=
    (Ideal.quotEquivOfEq hm).trans f
  exact ⟨g.symm, fun c ↦ g.symm_apply_eq.2
    ((hf (.C c)).trans (congrArg _ (MvPowerSeries.constantCoeff_C ..))).symm⟩

/-- The maximal ideal of the concrete surface is generated by two elements. -/
theorem concrete_surface_spanFinrank_le_two (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) [IsLocalRing (ConcreteSurface O pi u a b)] :
    (IsLocalRing.maximalIdeal (ConcreteSurface O pi u a b)).spanFinrank ≤ 2 := by
  rw [concrete_surface_maximalIdeal_eq O pi hpi u a b ha]
  unfold surfaceParameterIdeal
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
  calc _ ≤ Set.ncard {surfaceX O pi u a b} + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

/-- The surface ideal is proper when `π` is not a unit and `a > 0`. -/
theorem surfaceIdeal_ne_top (O : Type) [CommRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (hpi : ¬ IsUnit pi) (ha : 0 < a) :
    surfaceIdeal O pi u a b ≠ ⊤ := by
  intro h
  rw [surfaceIdeal, Ideal.span_singleton_eq_top] at h
  exact hpi (surfaceRelation_constantCoeff O pi u a b ha ▸ MvPowerSeries.isUnit_constantCoeff _ h)

/-- The concrete surface over a local ring is local when `π` is not a unit and `a > 0`. -/
theorem concrete_surface_isLocalRing (O : Type) [CommRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    [IsLocalRing O] (hpi : ¬ IsUnit pi) (ha : 0 < a) :
    IsLocalRing (ConcreteSurface O pi u a b) := by
  have : Nontrivial (ConcreteSurface O pi u a b) :=
    Ideal.Quotient.nontrivial_iff.mpr (surfaceIdeal_ne_top O pi u a b hpi ha)
  exact IsLocalRing.of_surjective' (surfaceMk O pi u a b) Ideal.Quotient.mk_surjective

end SurfaceBlowup

end
