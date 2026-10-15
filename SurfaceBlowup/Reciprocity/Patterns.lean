/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Reciprocity.Plethysm

/-!
# Pattern sums, crossing factorization and unitarity

Coefficient-level identities connecting the recursion laws of single-boundary states `S(a;n)` and
crossing states `T(a,b;c,h)` to the series calculus of the reciprocity proof: pattern sums and
their independence of the ambient dimension, reciprocal and Adams substitution in laws, closed
forms of the weight rational functions, the Euler transform as a pattern sum, the crossing
factorization of the contact series `U_{a,b}`, and its unitarity `U U† ≡ 1` by induction.

## Main results

* `coeff_eulerSer`: `[xⁿ] eulerSer ε a = patternSum ε a n n`.
* `coeff_recipCoef_lawCoef`, `lawCoef_globalLaw_false`, `lawCoef_globalLaw_true`: coefficients of
  the laws in `Coef`.
* `crossingQ_eq_qmul_qplus_qdiag_qminus`: `U_{a,b} = U_{a+b,b}⁺ J(P_{a+b}) U_{a,a+b}⁻`.
* `qcongr_crossingQ_mul_qdagger`: unitarity of `U_{a,b}` through degree `2M + 1`.
* `coeff_qact_crossingQ_gaussPhi_eulerSer`, `lawCoef_single_self_term`: the two sides of the
  single-boundary operator equation.

## Implementation notes

The recursion is unfolded with `exitLaw` and `state_law_unfold` from
`SurfaceBlowup.Formula.StateCombinatorics`, so that the reciprocity proof only depends on the
combinatorics of the formula.

Provenance: `Thm_SurfaceBlowupV2_recip_{pattern_extend, pattern_pad, stateLaw_globalLaw_wf,
monic_projective_coef, subst_inv_var, lawCoef_recip_subst, subst_pow_var, lawCoef_descend,
otherChildren_coef, crossing_term_coef, crossing_exit_regroup, globalLaw_coef, single_term_coef,
weights_rational, closing_scalar, countSum_eq, crossing_exchange, crossingQ_basic,
euler_product_trunc, euler_coeff_product, euler_coeff_pattern, crossing_factorization_coeff,
crossing_factorization, contact_induction, eulerSer_coeff_one, cluster_base,
single_operator_coeff, single_self_term_value}`.
-/

namespace SurfaceBlowup

/-! ### Pattern sums -/

@[to_additive]
private theorem prod_castLE_extend {M : Type*} [CommMonoid M] (N N' : ℕ) (hNN' : N ≤ N')
    (f : Fin N' → M) (g : Fin N → M) (h1 : ∀ i : Fin N, f (Fin.castLE hNN' i) = g i)
    (h2 : ∀ i : Fin N', N ≤ i.val → f i = 1) : ∏ i, f i = ∏ i, g i := by
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hNN')))]
  · rw [Finset.prod_map]
    exact Finset.prod_congr rfl (fun i _ ↦ h1 i)
  · intro i _ hi
    apply h2
    by_contra hc
    exact hi (Finset.mem_map.2 ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

section Extend

variable {N N' : ℕ} (hNN' : N ≤ N') {m : Pattern N} {m' : Pattern N'}
  (h : ∀ i j : Fin N', (m' (i, j)).val =
    if hij : i.val < N ∧ j.val < N then (m (⟨i.val, hij.1⟩, ⟨j.val, hij.2⟩)).val else 0)
include h

@[to_additive]
private theorem prod_row_castLE {M : Type*} [CommMonoid M] (g : ℕ → ℕ → M)
    (hg : ∀ j, g j 0 = 1) (i : Fin N) :
    ∏ j : Fin N', g j (m' (Fin.castLE hNN' i, j)).val = ∏ j : Fin N, g j (m (i, j)).val :=
  prod_castLE_extend N N' hNN' _ _ (fun j ↦ by simp [h]) fun j hj ↦ by simp [h, not_lt.2 hj, hg]

@[to_additive]
private theorem prod_row_eq_one {M : Type*} [CommMonoid M] (g : ℕ → ℕ → M)
    (hg : ∀ j, g j 0 = 1) (i : Fin N') (hi : N ≤ i.val) :
    ∏ j : Fin N', g j (m' (i, j)).val = 1 :=
  Finset.prod_eq_one fun j _ ↦ by simp [h, not_lt.2 hi, hg]

include hNN' in
@[to_additive]
private theorem prod_pattern_extend {M : Type*} [CommMonoid M] (g : ℕ → ℕ → ℕ → M)
    (hg : ∀ i j, g i j 0 = 1) :
    ∏ ij : Fin N' × Fin N', g ij.1 ij.2 (m' ij).val =
      ∏ ij : Fin N × Fin N, g ij.1 ij.2 (m ij).val := by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
  exact prod_castLE_extend N N' hNN' _ _ (fun i ↦ prod_row_castLE hNN' h (g i) (hg i) i)
    fun i hi ↦ prod_row_eq_one h (g i) (hg i) i hi

include hNN' in
private theorem patternWeight_extend : patternWeight m' = patternWeight m :=
  sum_pattern_extend hNN' h (fun i j k ↦ (i + 1) * (j + 1) * k) fun _ _ ↦ mul_zero _

include hNN' in
private theorem rational_divisorCount_extend (ε : ℤ) :
    (divisorCount ε m').rational = (divisorCount ε m).rational := by
  rw [rational_divisorCount, rational_divisorCount]
  refine prod_castLE_extend N N' hNN' _ _ (fun i ↦ ?_) fun i hi ↦ ?_
  · rw [sum_row_castLE hNN' h (fun _ k ↦ k) (fun _ ↦ rfl),
      prod_row_castLE hNN' h (fun _ k ↦ ((k.factorial : ℕ) : ℚ)) (fun _ ↦ by simp)]
    simp
  · rw [sum_row_eq_zero h (fun _ k ↦ k) (fun _ ↦ rfl) i hi,
      prod_row_eq_one h (fun _ k ↦ ((k.factorial : ℕ) : ℚ)) (fun _ ↦ by simp) i hi]
    simp

end Extend

/-- The pattern sum of weight `w ≤ N` does not change when the ambient dimension grows from `N`
to `N' ≥ N` (patterns of weight `w` live in the first `w` rows and columns). -/
private theorem patternSum_extend (ε : ℤ) (a N N' w : ℕ) (hNN' : N ≤ N') (hw : w ≤ N) :
    patternSum ε a N w = patternSum ε a N' w := by
  let ext : Pattern N → Pattern N' := fun m ij ↦
    if hij : ij.1.val < N ∧ ij.2.val < N then
      Fin.castLE (by omega) (m (⟨ij.1.val, hij.1⟩, ⟨ij.2.val, hij.2⟩)) else 0
  let res : Pattern N' → Pattern N := fun m' ij ↦
    ⟨min (m' (Fin.castLE hNN' ij.1, Fin.castLE hNN' ij.2)).val N, by omega⟩
  have hext (m : Pattern N) (i j : Fin N') : ((ext m) (i, j)).val =
      if hij : i.val < N ∧ j.val < N then (m (⟨i.val, hij.1⟩, ⟨j.val, hij.2⟩)).val else 0 := by
    simp only [ext]
    split_ifs <;> simp
  have hres (m' : Pattern N') (hm : patternWeight m' = w) (i j : Fin N') : (m' (i, j)).val =
      if hij : i.val < N ∧ j.val < N then ((res m') (⟨i.val, hij.1⟩, ⟨j.val, hij.2⟩)).val
      else 0 := by
    split_ifs with hij
    · simpa [res, Fin.castLE] using
        (pattern_entry_le_patternWeight N' m' (i, j)).trans (hm.trans_le hw)
    · refine pattern_entry_eq_zero_of_lt N' m' (i, j) ?_
      rw [hm]
      rcases not_and_or.mp hij with h | h <;> dsimp only <;> nlinarith
  refine Finset.sum_nbij' ext res (fun m hm ↦ ?_) (fun m' hm' ↦ ?_) (fun m _ ↦ ?_)
    (fun m' hm' ↦ ?_) fun m _ ↦ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    rw [patternWeight_extend hNN' (hext m), hm]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
    rw [← patternWeight_extend hNN' (hres m' hm'), hm']
  · funext ij
    have := (m ij).isLt
    simp only [res, Fin.ext_iff, hext, Fin.val_castLE, ij.1.isLt, ij.2.isLt, and_self, dite_true,
      Fin.eta, Prod.mk.eta]
    omega
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm'
    funext ⟨i, j⟩
    exact Fin.ext ((hext _ i j).trans (hres m' hm' i j).symm)
  · rw [rational_divisorCount_extend hNN' (hext m),
      prod_pattern_extend hNN' (hext m) (fun i j k ↦
        adamsCoef (i + 1) (lawCoef (stateLaw (State.single a (j + 1)))) ^ k) fun _ _ ↦ pow_zero _]

/-- The pattern sum of weight `w` is independent of the ambient dimension, as long as it is at
least `w`. -/
theorem patternSum_eq_of_le (ε : ℤ) (a N N' w : ℕ) (hN : w ≤ N) (hN' : w ≤ N') :
    patternSum ε a N w = patternSum ε a N' w := by
  rw [patternSum_extend ε a N (max N N') w (le_max_left _ _) hN,
    patternSum_extend ε a N' (max N N') w (le_max_right _ _) hN']

/-- The laws of valid states consist of well-formed expressions. -/
theorem lawWf_stateLaw (s : State) (hs : s.Valid) : LawWf (stateLaw s) :=
  (local_law_safe s hs).lawWf

/-- The global laws consist of well-formed expressions. -/
theorem lawWf_globalLaw (ε : Bool) (n : ℕ) : LawWf (globalLaw ε n) :=
  (global_law_safe n ε).lawWf

/-- The `σ`-coefficient of the global monic law, read in `Coef`, is the rational function of
`monicExpr n σ`. -/
theorem coeff_lawCoef_globalLaw_false (n : ℕ) (σ : FactorType) :
    (lawCoef (globalLaw false n)).coeff σ = (monicExpr n σ).rational :=
  coeff_lawCoef _ (lawWf_globalLaw false n) σ

/-- The `σ`-coefficient of the global projective law, read in `Coef`, is the rational function
of `projectiveExpr n σ`. -/
theorem coeff_lawCoef_globalLaw_true (n : ℕ) (σ : FactorType) :
    (lawCoef (globalLaw true n)).coeff σ = (projectiveExpr n σ).rational :=
  coeff_lawCoef _ (lawWf_globalLaw true n) σ

/-- Substituting a well-formed expression `e` for the variable, where `e.rational = φ(q)` for a
ring endomorphism `φ` of `ℚ(q)`, preserves well-formedness and acts on rational functions as
`φ` (the two facts are proved by a joint induction). -/
private theorem wf_subst_and_rational_subst (e : Expr) (he : e.wf) (φ : RatFunc ℚ →+* RatFunc ℚ)
    (hX : e.rational = φ RatFunc.X) (x : Expr) (hx : x.wf) :
    (x.subst e).wf ∧ (x.subst e).rational = φ x.rational := by
  induction x with
  | const r =>
    refine ⟨trivial, ?_⟩
    simp only [Expr.subst, Expr.rational_const]
    rw [eq_ratCast RatFunc.C r, map_ratCast]
  | var => exact ⟨he, by simp only [Expr.subst, Expr.rational_var, hX]⟩
  | add a b iha ihb =>
    obtain ⟨wa, ea⟩ := iha hx.1
    obtain ⟨wb, eb⟩ := ihb hx.2
    refine ⟨⟨wa, wb⟩, ?_⟩
    simp only [Expr.subst]
    rw [Expr.rational_add wa wb, Expr.rational_add hx.1 hx.2, map_add, ea, eb]
  | mul a b iha ihb =>
    obtain ⟨wa, ea⟩ := iha hx.1
    obtain ⟨wb, eb⟩ := ihb hx.2
    refine ⟨⟨wa, wb⟩, ?_⟩
    simp only [Expr.subst]
    rw [Expr.rational_mul, Expr.rational_mul a b, map_mul, ea, eb]
  | inv a iha =>
    obtain ⟨ha, hn⟩ := hx
    obtain ⟨wa, ea⟩ := iha ha
    have hr : a.rational ≠ 0 :=
      div_ne_zero (RatFunc.algebraMap_ne_zero hn)
        (RatFunc.algebraMap_ne_zero (Expr.fraction_snd_ne_zero ha))
    refine ⟨⟨wa, fun h ↦ ?_⟩, ?_⟩
    · refine hr (φ.injective ?_)
      rw [← ea, map_zero, Expr.rational, h, map_zero, zero_div]
    · simp only [Expr.subst]
      rw [Expr.rational_inv, Expr.rational_inv a, map_inv₀, ea]

/-- Substituting a well-formed expression `e` with `e.rational = φ(q)` for the variable of a
well-formed expression acts on rational functions as `φ`. -/
private theorem rational_subst_of_wf (e : Expr) (he : e.wf) (φ : RatFunc ℚ →+* RatFunc ℚ)
    (hX : e.rational = φ RatFunc.X) {x : Expr} (hx : x.wf) :
    (x.subst e).rational = φ x.rational :=
  (wf_subst_and_rational_subst e he φ hX x hx).2

/-- Substituting `q ↦ 1/q` into a well-formed expression acts on its rational function as
`recipRat`. -/
private theorem rational_subst_inv_var (x : Expr) (hx : x.wf) :
    (x.subst (.inv .var)).rational = recipRat x.rational :=
  rational_subst_of_wf (.inv .var) ⟨trivial, by simp [Expr.fraction, Polynomial.X_ne_zero]⟩ recipRat
    (by rw [Expr.rational_inv, Expr.rational_var, recipRat_X]) hx

/-- For a well-formed law, the `σ`-coefficient of `lawCoef L` with `q ↦ 1/q` applied is the
rational function of the coefficient expression with `q ↦ 1/q` substituted. -/
theorem coeff_recipCoef_lawCoef (L : Law) (hL : LawWf L) (σ : FactorType) :
    (recipCoef (lawCoef L)).coeff σ = ((lawCoeff L σ).subst (.inv .var)).rational := by
  rw [recipCoef_coeff, coeff_lawCoef L hL σ, rational_subst_inv_var _ (hL.wf_lawCoeff σ)]

/-- Descending a well-formed law along a degree-`δ` extension acts on `lawCoef` as the Adams
operation `ψ_δ`. -/
private theorem lawCoef_lawDescend (δ : ℕ) (hδ : 0 < δ) (L : Law) (hL : LawWf L) :
    lawCoef (lawDescend δ L) = adamsCoef δ (lawCoef L) := by
  unfold lawCoef lawDescend
  rw [map_list_sum, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun z hz ↦ ?_
  simp only [Function.comp]
  rw [rational_subst_of_wf _ (Expr.wf_pow (x := Expr.var) trivial δ) (adamsRat δ)
    (by rw [Expr.rational_pow, Expr.rational_var, adamsRat_X δ hδ]) (hL z hz), adamsCoef_single]

/-- The product of the descended laws of the off-boundary children of a pattern `m` is
`Π_{(i,j)} ψ_{i+1}(F_{S(a;j+1)})^{m(i,j)}`. -/
private theorem lawCoef_otherChildren (a N : ℕ) (ha : 0 < a) (m : Pattern N) :
    lawCoef (lawProd ((otherChildren a m).map fun z ↦ lawDescend z.1 (stateLaw z.2))) =
        ∏ ij : Fin N × Fin N, (adamsCoef (ij.1.val + 1) (lawCoef
        (stateLaw (State.single a (ij.2.val + 1))))) ^ (m ij).val := by
  have hf : ∀ ij : Fin N × Fin N, lawCoef (lawDescend (ij.1.val + 1)
      (stateLaw (State.single a (ij.2.val + 1)))) = adamsCoef (ij.1.val + 1)
      (lawCoef (stateLaw (State.single a (ij.2.val + 1)))) := by
    intro ij
    refine lawCoef_lawDescend _ (Nat.succ_pos _) _ ?_
    exact (lawWf_stateLaw _ (by simp [State.Valid]; omega))
  rw [(lawCoef_lawProd _)]
  unfold otherChildren
  simp only [List.map_flatMap, List.map_replicate, hf]
  rw [List.flatMap_def, List.prod_flatten, List.map_map, Finset.prod_eq_multiset_prod,
      ← Multiset.prod_map_toList]
  simp [List.prod_replicate, Finset.toList, Function.comp_def]

private theorem prod_lawCoef_optional_child (p : Prop) [Decidable p] (s' : State)
    (hv : ¬p → s'.Valid) :
    ((if p then [] else [((1 : ℕ), s')]).map
        (lawCoef ∘ fun z : ℕ × State ↦ lawDescend z.1 (stateLaw z.2))).prod
      = if p then 1 else lawCoef (stateLaw s') := by
  split_ifs with h
  · simp
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Function.comp]
    rw [lawCoef_lawDescend 1 one_pos _ (lawWf_stateLaw _ (hv h)), adamsCoef_one]

/-- The contribution of an allowed tangent pattern `P` of the crossing state `T(a,b;c,h)` to its
recursion, as an element of `Coef`: the weights times the laws of the crossing children and the
off-boundary product. -/
private theorem lawCoef_crossing_term (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h)
    (P : TangentPattern (State.crossing a b c h).degree) (hP : Allowed (State.crossing a b c h) P) :
    lawCoef (lawScale (.mul (tangentCount (State.crossing a b c h) P)
        (divisorProbability (State.crossing a b c h) P.d.val))
        (lawProd ((children (State.crossing a b c h) P).map fun z ↦
        lawDescend z.1 (stateLaw z.2)))) = scalar ((divisorCount (-1) P.other).rational *
        (divisorProbability (State.crossing a b c h) P.d.val).rational) *
        ((if P.rt.val = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) a P.rt.val
        (c - P.d.val)))) * (if P.rx.val = 0 then 1 else lawCoef
        (stateLaw (State.crossing (a + b) b P.rx.val (h - P.d.val)))) *
        ∏ ij : Fin (State.crossing a b c h).degree × Fin (State.crossing a b c h).degree,
        (adamsCoef (ij.1.val + 1) (lawCoef (stateLaw (State.single (a + b) (ij.2.val + 1))))) ^
        (P.other ij).val) := by
  have hv : ∀ z ∈ children (State.crossing a b c h) P, z.2.Valid :=
    children_valid (State.crossing a b c h) ⟨ha, hb, hc, hh⟩ P hP
  rw [lawCoef_lawScale, Expr.rational_mul]
  congr 1
  have hch : children (State.crossing a b c h) P =
      (if P.rt.val=0 then [] else [(1,State.crossing (a+b) a P.rt.val (c-P.d.val))]) ++
      (if P.rx.val=0 then [] else [(1,State.crossing (a+b) b P.rx.val (h-P.d.val))]) ++
      otherChildren (a+b) P.other := rfl
  have hoth := lawCoef_otherChildren (a+b) _ (by omega) P.other
  rw [lawCoef_lawProd, List.map_map] at hoth
  rw [lawCoef_lawProd, List.map_map, hch, List.map_append, List.map_append, List.prod_append,
    List.prod_append, ← hoth, prod_lawCoef_optional_child _ _ ?_,
    prod_lawCoef_optional_child _ _ ?_]
  all_goals first | rfl | exact fun h1 ↦ hv (1, _) (by rw [hch]; simp [h1])

/-- Summing the pattern terms `scalar (divisorCount ε m · Y) · B · Π ψ_{i+1}(F_{S(a;j+1)})^{m(i,j)}`
over the patterns `m` of weight `w` gives `scalar Y · B · patternSum ε a N w`. -/
theorem sum_patterns_scalar_mul_eq_patternSum (ε : ℤ) (a N w : ℕ) (Y : RatFunc ℚ) (B : Coef) :
    ∑ m ∈ (Finset.univ : Finset (Pattern N)).filter (fun m ↦ patternWeight m = w),
      scalar ((divisorCount ε m).rational * Y) * (B * ∏ ij : Fin N × Fin N,
        (adamsCoef (ij.1.val + 1) (lawCoef (stateLaw (State.single a (ij.2.val + 1))))) ^
          (m ij).val) = scalar Y * (B * patternSum ε a N w) := by
  unfold patternSum
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [scalar_mul, Algebra.smul_def, ← scalar_eq_algebraMap]
  ring

/-- The exit law of `T(a,b;c,h)` regrouped by divisor degree `d` and tangent depths `rt`, `rx`
into crossing-child laws and pattern sums `patternSum (-1) (a+b) (ac+bh) (d-rt-rx)`. -/
private theorem lawCoef_exitLaw_crossing (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h) :
    lawCoef (exitLaw (State.crossing a b c h)) = ∑ d ∈ Finset.Icc 1 (min c h),
        ∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1),
        (if ((0 < rt ↔ d < c) ∧ (0 < rx ↔ d < h) ∧ rt + rx ≤ d) then scalar
        (divisorProbability (State.crossing a b c h) d).rational *
        ((if rt = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) a rt (c - d)))) *
        (if rx = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) b rx (h - d)))) *
        patternSum (-1) (a + b) (a * c + b * h) (d - rt - rx)) else 0) := by
  classical
  unfold exitLaw
  rw [lawCoef_flatMap, Finset.sum_map_toList]
  have hns : ∀ P, ¬ SelfPattern (State.crossing a b c h) P := by
    rintro P ⟨a', c', h1, -⟩
    exact State.noConfusion h1
  simp only [hns, if_false]
  refine (Finset.sum_congr rfl (fun P hP ↦ lawCoef_crossing_term a b c h ha hb hc hh P
    (by unfold allowedPatterns at hP; exact (Finset.mem_filter.mp hP).2))).trans ?_
  rw [sum_allowedPatterns_crossing a b c h ha hb hh (fun d rt rx m ↦
    scalar ((divisorCount (-1) m).rational * (divisorProbability (State.crossing a b c h)
        d).rational) *
      ((if rt = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) a rt (c - d)))) *
        (if rx = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) b rx (h - d)))) *
        ∏ ij : Fin (State.crossing a b c h).degree × Fin (State.crossing a b c h).degree,
          (adamsCoef (ij.1.val + 1) (lawCoef (stateLaw (State.single (a + b) (ij.2.val + 1))))) ^
              (m ij).val))]
  refine Finset.sum_congr rfl (fun d _ ↦ Finset.sum_congr rfl
      (fun rt _ ↦ Finset.sum_congr rfl (fun rx _ ↦ ?_)))
  by_cases hcond : ((0 < rt ↔ d < c) ∧ (0 < rx ↔ d < h) ∧ rt + rx ≤ d)
  · rw [if_pos hcond, if_pos hcond]; exact sum_patterns_scalar_mul_eq_patternSum _ _ _ _ _ _
  · rw [if_neg hcond, if_neg hcond]

private theorem lawCoef_residue_flatMap (n : ℕ) (b : Bool) :
    lawCoef ((residuePatterns n).toList.flatMap fun m ↦
      lawScale (divisorCount (if b then 1 else 0) m)
        (lawProd ((otherChildren 1 m).map fun z ↦ lawDescend z.1 (stateLaw z.2))))
      = patternSum (if b then 1 else 0) 1 n n := by
  rw [lawCoef_flatMap]
  unfold patternSum residuePatterns
  rw [Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [lawCoef_lawScale, lawCoef_otherChildren 1 n Nat.one_pos m, Algebra.smul_def]
  rfl

/-- The global monic law is `q^{-n}` times the pattern sum `patternSum 0 1 n n`. -/
theorem lawCoef_globalLaw_false (n : ℕ) :
    lawCoef (globalLaw false n) = qpow (-(n : ℤ)) * patternSum 0 1 n n := by
  have k0 := lawCoef_residue_flatMap n false
  simp only [Bool.false_eq_true, if_false] at k0
  unfold globalLaw
  simp only [Bool.false_eq_true, if_false]
  rw [lawCoef_lawScale, k0, Expr.rational_inv, Expr.rational_pow, Expr.rational_var, qpow,
    zpow_neg, zpow_natCast]

/-- The global projective law is the pattern sum `patternSum 1 1 n n` divided by
`1 + q + ⋯ + qⁿ`. -/
theorem lawCoef_globalLaw_true (n : ℕ) :
    lawCoef (globalLaw true n) =
      scalar (((projectiveNormalizer n).rational)⁻¹) * patternSum 1 1 n n := by
  have k1 := lawCoef_residue_flatMap n true
  simp only [if_true] at k1
  unfold globalLaw
  simp only [if_true]
  rw [lawCoef_lawScale, k1, Expr.rational_inv]

/-- The contribution of an allowed tangent pattern `P` of `S(a;n)` to its recursion, as an element
of `Coef`. -/
theorem lawCoef_single_term (a n : ℕ) (ha : 0 < a) (hn : 0 < n)
    (P : TangentPattern (State.single a n).degree) (hP : Allowed (State.single a n) P) :
    lawCoef (lawScale (.mul (tangentCount (State.single a n) P)
        (divisorProbability (State.single a n) P.d.val))
        (lawProd ((children (State.single a n) P).map fun z ↦ lawDescend z.1 (stateLaw z.2)))) =
        scalar ((divisorCount 0 P.other).rational * (divisorProbability (State.single a n)
        P.d.val).rational) * ((if P.rt.val = 0 then 1 else lawCoef
        (stateLaw (State.crossing a a P.rt.val (n - P.d.val)))) *
        ∏ ij : Fin (State.single a n).degree × Fin (State.single a n).degree,
        (adamsCoef (ij.1.val + 1) (lawCoef (stateLaw (State.single a (ij.2.val + 1))))) ^
        (P.other ij).val) := by
  have hv : ∀ z ∈ children (State.single a n) P, z.2.Valid :=
    children_valid (State.single a n) ⟨ha, hn⟩ P hP
  rw [lawCoef_lawScale, Expr.rational_mul]
  congr 1
  have hch : children (State.single a n) P =
      (if P.rt.val=0 then [] else [(1,State.crossing a a P.rt.val (n-P.d.val))]) ++
      otherChildren a P.other := rfl
  have hoth := lawCoef_otherChildren a _ ha P.other
  rw [lawCoef_lawProd, List.map_map] at hoth
  rw [lawCoef_lawProd, List.map_map, hch, List.map_append, List.prod_append, ← hoth,
    prod_lawCoef_optional_child _ _ ?_]
  all_goals first | rfl | exact fun h1 ↦ hv (1, _) (by rw [hch]; simp [h1])

/-! ### Closed forms of the weights -/

/-- The divisor probability of `S(a;c)` at degree `d` is `q^{-tri d} (q-1)^{[d < c]}`. -/
theorem rational_divisorProbability_single (a c d : ℕ) :
    (divisorProbability (State.single a c) d).rational =
      ((RatFunc.X : RatFunc ℚ) ^ tri d)⁻¹ *
        ((RatFunc.X : RatFunc ℚ) - 1) ^ (if d < c then 1 else 0) := by
  simp only [divisorProbability, Expr.rational_mul, Expr.rational_inv, Expr.rational_pow,
    Expr.rational_var, rational_eminusOne]

/-- The divisor probability of `T(a,b;c,h)` at degree `d` is `q^{-C(d,2)}` times the crossing weight
`w_j` (`w_0 = (q-1)⁻¹`, `w_j = (q-1)^{j-1}`) with `j = [d < c] + [d < h]`. -/
private theorem rational_divisorProbability_crossing (a b c h d : ℕ) :
    (divisorProbability (State.crossing a b c h) d).rational =
      ((RatFunc.X : RatFunc ℚ) ^ chooseTwo d)⁻¹ * (if (if d < c then 1 else 0) +
        (if d < h then 1 else 0) = 0 then ((RatFunc.X : RatFunc ℚ) - 1)⁻¹ else
        ((RatFunc.X : RatFunc ℚ) - 1) ^
          ((if d < c then 1 else 0) + (if d < h then 1 else 0) - 1)) := by
  simp only [divisorProbability]
  rw [Expr.rational_mul, Expr.rational_inv, Expr.rational_pow, Expr.rational_var]
  split_ifs <;> simp [Expr.rational_inv, Expr.rational_pow, rational_eminusOne]

/-- The return weight is `q · q^{-tri c}`. -/
theorem rational_returnWeight (c : ℕ) :
    (returnWeight c).rational = (RatFunc.X : RatFunc ℚ) * ((RatFunc.X : RatFunc ℚ) ^ tri c)⁻¹ := by
  simp only [returnWeight, Expr.rational_mul, Expr.rational_inv, Expr.rational_pow,
    Expr.rational_var]

/-- The point count `(1/δ) Σ_{j ∣ δ} μ(j) q^{δ/j}` of degree-`δ` points. -/
private theorem rational_pointCount (δ : ℕ) : (pointCount δ).rational = RatFunc.C (1 / (δ : ℚ)) *
    ∑ j ∈ δ.divisors, RatFunc.C (((ArithmeticFunction.moebius j : ℤ) : ℚ)) *
    (RatFunc.X : RatFunc ℚ) ^ (δ / j) := by
  unfold pointCount
  rw [Expr.rational_mul, Expr.rational_const, Expr.rational_sum]
  · rw [List.map_map, ← Finset.sum_map_toList]
    congr 2
    refine List.map_congr_left fun j _ ↦ ?_
    simp [Expr.rational_mul, Expr.rational_const, Expr.rational_pow, Expr.rational_var]
  · intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hz
    exact ⟨trivial, Expr.wf_pow (x := Expr.var) trivial _⟩

/-- The available points: `q + ε` in degree `1`, and the point count in higher degree. -/
private theorem rational_availablePoints (ε : ℤ) (δ : ℕ) :
    (availablePoints ε δ).rational =
      if δ = 1 then (RatFunc.X : RatFunc ℚ) + (ε : RatFunc ℚ) else (pointCount δ).rational := by
  unfold availablePoints
  split_ifs
  · rw [Expr.rational_add (x := Expr.var) (y := Expr.const (ε : ℚ)) trivial trivial,
      Expr.rational_var, Expr.rational_const, map_intCast]
  · rfl

/-- `q (q⁻¹ - q^{-tri n}) = 1 - returnWeight n`. -/
private theorem X_mul_X_inv_sub_X_zpow_neg_tri (n : ℕ) :
    (RatFunc.X : RatFunc ℚ) * ((RatFunc.X : RatFunc ℚ)⁻¹ - (RatFunc.X : RatFunc ℚ) ^
      (-(tri n : ℤ))) = 1 - (returnWeight n).rational := by
  rw [rational_returnWeight n, zpow_neg, zpow_natCast, mul_sub, mul_inv_cancel₀ RatFunc.X_ne_zero]

/-- For `n ≥ 2`, the return weight is not `1`: `1 - returnWeight n ≠ 0`. -/
theorem one_sub_rational_returnWeight_ne_zero (n : ℕ) (hn : 2 ≤ n) :
    1 - (returnWeight n).rational ≠ 0 := by
  have h3 : 3 ≤ tri n := by
    unfold tri
    have : 6 ≤ n * (n + 1) := by nlinarith
    omega
  intro h0
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h1 : (returnWeight n).rational = 1 := by linear_combination -h0
  rw [rational_returnWeight] at h1
  have hk : (RatFunc.X : RatFunc ℚ) = (RatFunc.X : RatFunc ℚ) ^ tri n := by
    have := congrArg (· * (RatFunc.X : RatFunc ℚ) ^ tri n) h1
    simpa [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hX)] using this
  have hp : (Polynomial.X : Polynomial ℚ) = Polynomial.X ^ tri n := by
    apply RatFunc.algebraMap_injective ℚ
    simpa [RatFunc.algebraMap_X] using hk
  have := congrArg Polynomial.natDegree hp
  simp at this
  omega

/-- For `n ≥ 2`, the scalar `q⁻¹ - q^{-tri n}` is nonzero. -/
theorem X_inv_sub_X_zpow_neg_tri_ne_zero (n : ℕ) (hn : 2 ≤ n) :
    (RatFunc.X : RatFunc ℚ)⁻¹ - (RatFunc.X : RatFunc ℚ) ^ (-(tri n : ℤ)) ≠ 0 := fun h ↦ by
  have := X_mul_X_inv_sub_X_zpow_neg_tri n
  rw [h, mul_zero] at this
  exact one_sub_rational_returnWeight_ne_zero n hn this.symm

private theorem adamsRat_X_add_int (k : ℕ) (hk : 0 < k) (ε : ℤ) :
    adamsRat k (RatFunc.X + (ε : RatFunc ℚ)) = RatFunc.X ^ k + (ε : RatFunc ℚ) := by
  rw [map_add, map_intCast, (adamsRat_X k hk)]

private theorem availablePoints_rational_eq_sum (ε : ℤ) (m : ℕ) (hm : 0 < m) :
    ∑ k ∈ m.divisors, (RatFunc.C ((k : ℚ)⁻¹ * (((ArithmeticFunction.moebius (m / k) : ℤ) : ℚ) /
        ((m / k : ℕ) : ℚ))))
      * ((RatFunc.X : RatFunc ℚ) ^ k + (ε : RatFunc ℚ)) = (availablePoints ε m).rational := by
  rw [rational_availablePoints]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have ht : ∀ k ∈ m.divisors,
      RatFunc.C ((k : ℚ)⁻¹ * (((ArithmeticFunction.moebius (m / k) : ℤ) : ℚ) / ((m / k : ℕ) : ℚ)))
        * ((RatFunc.X : RatFunc ℚ) ^ k + (ε : RatFunc ℚ))
      = (fun j : ℕ ↦ RatFunc.C (((ArithmeticFunction.moebius j : ℤ) : ℚ) / m)
          * ((RatFunc.X : RatFunc ℚ) ^ (m / j) + (ε : RatFunc ℚ))) (m / k) := by
    intro k hk
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
    simp only [Nat.div_div_self (Nat.dvd_of_mem_divisors hk) hm.ne']
    congr 2
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hk) hk0]
    field_simp
  rw [Finset.sum_congr rfl ht, Nat.sum_div_divisors m (fun j : ℕ ↦
      RatFunc.C (((ArithmeticFunction.moebius j : ℤ) : ℚ) / m)
          * ((RatFunc.X : RatFunc ℚ) ^ (m / j) + (ε : RatFunc ℚ)))]
  split_ifs with h1
  · subst h1; simp
  · rw [rational_pointCount]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have h0 : ∑ j ∈ m.divisors, RatFunc.C (((ArithmeticFunction.moebius j : ℤ) : ℚ) / m) *
        (ε : RatFunc ℚ) = 0 := by
      rw [← Finset.sum_mul, ← map_sum, ← Finset.sum_div, sum_divisors_moebius, if_neg h1]; simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← mul_assoc, ← map_mul]
    congr 2
    field_simp

/-- `Σ_k ψ_k((q+ε) · Σ_j μ(j) ψ_j(L)/j)/k` equals `Σ_m C_m ψ_m(L)` with
`C_m = availablePoints ε m`. -/
private theorem plethSum_C_mul_moebiusSum (ε : ℤ) (L : Ser) :
    plethSum (PowerSeries.C (scalar (RatFunc.X + (ε : RatFunc ℚ))) * moebiusSum L) =
        countSum ε L := by
  ext n : 1
  simp only [plethSum, moebiusSum, countSum, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    Finset.mul_sum, map_sum, Finset.smul_sum]
  have h1 : ∀ k ∈ n.divisors, ∀ j ∈ (n / k).divisors,
      (k : ℚ)⁻¹ • adamsCoef k (scalar (RatFunc.X + (ε : RatFunc ℚ)) *
        ((((ArithmeticFunction.moebius j : ℤ) : ℚ)) / (j : ℚ)) •
            adamsCoef j (PowerSeries.coeff (n / k / j) L))
        = (fun (k j : ℕ) ↦ scalar (RatFunc.C ((k : ℚ)⁻¹ *
            (((ArithmeticFunction.moebius j : ℤ) : ℚ) / (j : ℚ))) *
            ((RatFunc.X : RatFunc ℚ) ^ k + (ε : RatFunc ℚ))) *
            adamsCoef (k * j) (PowerSeries.coeff (n / (k * j)) L)) k j := by
    intro k hk j hj
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
    have hj0 : 0 < j := Nat.pos_of_mem_divisors hj
    rw [mul_smul_comm, map_rat_smul, map_mul, adamsCoef_adamsCoef k j hk0 hj0,
        Nat.div_div_eq_div_mul,
      adamsCoef_scalar k, adamsRat_X_add_int k hk0, smul_smul, rat_smul_eq_scalar_mul, ← mul_assoc,
      ← scalar_mul]
  rw [Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr rfl (h1 k hk),
    sum_divisors_sum_divisors_div]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm0 : 0 < m := Nat.pos_of_mem_divisors hm
  have h2 : ∀ k ∈ m.divisors, k * (m / k) = m := fun k hk ↦
      Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hk)
  rw [Finset.sum_congr rfl fun k hk ↦ by
      rw [h2 k hk], ← Finset.sum_mul, ← availablePoints_rational_eq_sum ε m hm0]
  simp only [scalar_eq_algebraMap, ← map_sum, Algebra.smul_def]

/-- The law of a crossing state is symmetric under exchanging the two branches:
`F_{T(a,b;c,h)} = F_{T(b,a;h,c)}`. -/
private theorem lawCoef_stateLaw_crossing_comm (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h) :
    lawCoef (stateLaw (State.crossing a b c h)) = lawCoef (stateLaw (State.crossing b a h c)) := by
  have h1 := (state_law_unfold (.crossing a b c h) ⟨ha, hb, hc, hh⟩ rfl).2 a b c h rfl
  have h2 := (state_law_unfold (.crossing b a h c) ⟨hb, ha, hh, hc⟩ rfl).2 b a h c rfl
  rw [h1, h2, lawCoef_exitLaw_crossing a b c h ha hb hc hh,
    lawCoef_exitLaw_crossing b a h c hb ha hh hc, Nat.min_comm h c]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun rt _ ↦ Finset.sum_congr rfl fun rx _ ↦ ?_
  have hp : (divisorProbability (State.crossing b a h c) d).rational
      = (divisorProbability (State.crossing a b c h) d).rational := by
    rw [rational_divisorProbability_crossing b a h c d,
      rational_divisorProbability_crossing a b c h d,
      Nat.add_comm (if d < h then 1 else 0)]
  rw [hp, Nat.add_comm b a, Nat.add_comm (b * h) (a * c), Nat.sub_right_comm d rx rt]
  by_cases hc1 : ((0 < rt ↔ d < c) ∧ (0 < rx ↔ d < h) ∧ rt + rx ≤ d)
  · have hc2 : ((0 < rx ↔ d < h) ∧ (0 < rt ↔ d < c) ∧ rx + rt ≤ d) := by
      obtain ⟨x, y, z⟩ := hc1; exact ⟨y, x, by omega⟩
    rw [if_pos hc1, if_pos hc2, mul_comm (if rx = 0 then _ else _)]
  · have hc2 : ¬ ((0 < rx ↔ d < h) ∧ (0 < rt ↔ d < c) ∧ rx + rt ≤ d) := by
      rintro ⟨y, x, z⟩; exact hc1 ⟨x, y, by omega⟩
    rw [if_neg hc1, if_neg hc2]

/-- The contact series `U_{a,b}` has constant term `1`. -/
theorem crossingQ_zero_zero (a b : ℕ) : crossingQ a b 0 0 = 1 := by simp [crossingQ]

/-- The contact series `U_{a,b}` vanishes on the axes away from `(0,0)`. -/
private theorem qPositive_crossingQ (a b : ℕ) : QPositive (crossingQ a b) := by
  intro c h h1 h2
  have : ¬ (0 < c ∧ 0 < h) := by omega
  simp [crossingQ, h2, this]

/-- The off-axis coefficients of `U_{a,b}` are `(q-1) F_{T(a,b;c,h)}`. -/
private theorem crossingQ_of_pos (a b c h : ℕ) (hc : 0 < c) (hh : 0 < h) :
    crossingQ a b c h = scalar (RatFunc.X - 1) * lawCoef (stateLaw (State.crossing a b c h)) := by
  have : ¬ (c = 0 ∧ h = 0) := by omega
  simp [crossingQ, this, hc, hh]

/-- The symmetry `U_{a,b}(c,h) = U_{b,a}(h,c)`. -/
theorem crossingQ_symm (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b) :
    crossingQ a b c h = crossingQ b a h c := by
  by_cases h1 : c = 0 ∧ h = 0
  · obtain ⟨rfl, rfl⟩ := h1
    simp [crossingQ]
  · by_cases h2 : 0 < c ∧ 0 < h
    · rw [crossingQ_of_pos a b c h h2.1 h2.2, crossingQ_of_pos b a h c h2.2 h2.1,
        lawCoef_stateLaw_crossing_comm a b c h ha hb h2.1 h2.2]
    · rw [qPositive_crossingQ a b c h (by omega) h1,
        qPositive_crossingQ b a h c (by omega) (by tauto)]

private theorem expSer_sum (s : Finset ℕ) (F : ℕ → Ser)
    (hF : ∀ m ∈ s, PowerSeries.constantCoeff (F m) = 0) :
    expSer (∑ m ∈ s, F m) = ∏ m ∈ s, expSer (F m) := by
  induction s using Finset.induction_on with
  | empty => simpa using expSer_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      expSer_add _ _ (hF a (Finset.mem_insert_self _ _)),
          ih (fun m hm ↦ hF m (Finset.mem_insert_of_mem hm))]
    rw [map_sum]
    exact Finset.sum_eq_zero (fun m hm ↦ hF m (Finset.mem_insert_of_mem hm))

/-- Through degree `N`, the plethystic power `P_{q+ε}(B)` is the Euler product
`Π_{m=1}^N ψ_m(B)^{C_m}`. -/
private theorem pPow_scongr_prod_formalPow_adamsSer (ε : ℤ) (B : Ser)
    (hB : PowerSeries.constantCoeff B = 1) (N : ℕ) :
    SCongr N (pPow (RatFunc.X + (ε : RatFunc ℚ)) B) (∏ m ∈ Finset.Icc 1 N,
        formalPow (availablePoints ε m).rational (adamsSer m B)) := by
  set L := logSer B with hLdef
  have hL : PowerSeries.constantCoeff L = 0 := (constantCoeff_logSer B hB)
  have hp : pPow (RatFunc.X + (ε : RatFunc ℚ)) B = expSer (countSum ε L) := by
    rw [pPow, pExp, pLog, plethSum_C_mul_moebiusSum]
  set S : Ser := ∑ m ∈ Finset.Icc 1 N,
    PowerSeries.C (scalar (availablePoints ε m).rational) * adamsSer m L with hS
  have hterm : ∀ m ∈ Finset.Icc 1 N, PowerSeries.constantCoeff
      (PowerSeries.C (scalar (availablePoints ε m).rational) * adamsSer m L) = 0 := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.1 hm).1; omega
    rw [map_mul, (constantCoeff_adamsSer m hm0 L), hL, map_zero, mul_zero]
  have hS0 : PowerSeries.constantCoeff S = 0 := by
    rw [hS, map_sum]; exact Finset.sum_eq_zero hterm
  have hc0 : PowerSeries.constantCoeff (countSum ε L) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [countSum]
  have h1 : SCongr N (countSum ε L) S := by
    intro n hn
    rw [hS, map_sum]
    have hrw : ∀ m ∈ Finset.Icc 1 N, PowerSeries.coeff n
        (PowerSeries.C (scalar (availablePoints ε m).rational) * adamsSer m L) =
        if m ∣ n then (availablePoints ε m).rational • adamsCoef m (PowerSeries.coeff (n / m) L)
            else 0 := by
      intro m hm
      have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.1 hm).1; omega
      rw [PowerSeries.coeff_C_mul, (coeff_adamsSer m hm0 L n), scalar_mul_eq_smul]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_filter]
    simp only [countSum, PowerSeries.coeff_mk]
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp only [Nat.divisors_zero, Finset.sum_empty, Nat.zero_div]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hL
      simp [hL]
    · apply Finset.sum_congr _ (fun _ _ ↦ rfl)
      ext m
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hd, hn0⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd hnpos, (Nat.le_of_dvd hnpos hd).trans hn⟩, hd⟩
      · rintro ⟨_, hd⟩
        exact ⟨hd, by omega⟩
  have h2 := (SCongr.expSer hc0 hS0 h1)
  have h3 : expSer S = ∏ m ∈ Finset.Icc 1 N, formalPow (availablePoints ε m).rational
      (adamsSer m B) := by
    rw [hS, expSer_sum _ _ hterm]
    apply Finset.prod_congr rfl
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.1 hm).1; omega
    rw [formalPow, ← (adamsSer_logSer m hm0 B hB)]
  rw [hp, ← h3]; exact h2

/-- The `n`-th coefficient of the Euler transform `eulerSer ε a` is that of the finite Euler
product `Π_{m=1}^n ψ_m(B_a)^{C_m}`. -/
private theorem coeff_eulerSer_eq_coeff_prod (ε : ℤ) (a n : ℕ) :
    PowerSeries.coeff n (eulerSer ε a) = PowerSeries.coeff n
        (∏ m ∈ Finset.Icc 1 n, formalPow (availablePoints ε m).rational
        (adamsSer m (clusterSer a))) := by
  have hB : PowerSeries.constantCoeff (clusterSer a) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [clusterSer]
  exact pPow_scongr_prod_formalPow_adamsSer ε (clusterSer a) hB n n le_rfl

/-- The `n`-th coefficient of the Euler transform `eulerSer ε a` is the pattern sum
`patternSum ε a n n`. -/
theorem coeff_eulerSer (ε : ℤ) (a n : ℕ) :
    PowerSeries.coeff n (eulerSer ε a) = patternSum ε a n n := by
  rw [coeff_eulerSer_eq_coeff_prod,
    prod_formalPow_adamsSer_clusterSer_scongr ε a n n le_rfl,
    coeff_euler_families_eq_patternSum]

private theorem crossing_factorization_term (a b c h d rt rx : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hdc : d ≤ min c h) :
    (if (rt + rx ≤ d ∧ d ≤ min c h) then
      qpow (-(chooseTwo (rx + (d - rt - rx) + rt) : ℤ)) *
        (crossingQ (a + b) b rx (h - (rx + (d - rt - rx) + rt)) *
          (PowerSeries.coeff (d - rt - rx) (eulerSer (-1) (a + b)) *
            crossingQ a (a + b) (c - (rx + (d - rt - rx) + rt)) rt)) else 0)
    = scalar (RatFunc.X - 1) * (if ((0 < rt ↔ d < c) ∧ (0 < rx ↔ d < h) ∧ rt + rx ≤ d) then scalar
        (divisorProbability (State.crossing a b c h) d).rational *
        ((if rt = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) a rt (c - d)))) *
        (if rx = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) b rx (h - d)))) *
        patternSum (-1) (a + b) (a * c + b * h) (d - rt - rx)) else 0) := by
  by_cases hsum : rt + rx ≤ d
  swap
  · simp [hsum]
  rw [show rx + (d - rt - rx) + rt = d by omega]
  simp only [hsum, hdc, and_self, if_true, and_true]
  rw [coeff_eulerSer,
    patternSum_eq_of_le (-1) (a + b) (d - rt - rx) (a * c + b * h) (d - rt - rx) le_rfl (by
      have : c ≤ a * c := Nat.le_mul_of_pos_left c ha
      have := min_le_left c h
      omega)]
  set P := patternSum (-1) (a + b) (a * c + b * h) (d - rt - rx)
  by_cases hT : (0 < rt ↔ d < c)
  swap
  · have : crossingQ a (a + b) (c - d) rt = 0 := by
      unfold crossingQ; rw [if_neg (by omega), if_neg (by omega)]
    simp [this, hT]
  by_cases hX : (0 < rx ↔ d < h)
  swap
  · have : crossingQ (a + b) b rx (h - d) = 0 := by
      unfold crossingQ; rw [if_neg (by omega), if_neg (by omega)]
    simp [this, hX]
  simp only [hT, hX, and_self, if_true]
  set Bt := (if rt = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) a rt (c - d))))
  set Bx := (if rx = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) b rx (h - d))))
  set i := (if d < c then 1 else 0)
  set k := (if d < h then 1 else 0)
  have eT : crossingQ a (a + b) (c - d) rt = scalar ((RatFunc.X - 1) ^ i) * Bt := by
    by_cases h1 : d < c
    · have hrt : 0 < rt := hT.2 h1
      simp only [i, Bt, crossingQ, if_pos h1, pow_one, if_neg
          (show ¬ (c - d = 0 ∧ rt = 0) by omega),
        if_pos (show 0 < c - d ∧ 0 < rt by omega), if_neg (show ¬ rt = 0 by omega)]
      rw [lawCoef_stateLaw_crossing_comm a (a + b) (c - d) rt ha (by omega) (by omega) hrt]
    · have hrt : rt = 0 := by omega
      simp only [i, Bt, crossingQ, if_neg h1, pow_zero, scalar_one, if_pos hrt, mul_one,
        if_pos (show c - d = 0 ∧ rt = 0 by omega)]
  have eX : crossingQ (a + b) b rx (h - d) = scalar ((RatFunc.X - 1) ^ k) * Bx := by
    by_cases h1 : d < h
    · have hrx : 0 < rx := hX.2 h1
      simp only [k, Bx, crossingQ, if_pos h1, pow_one, if_neg
          (show ¬ (rx = 0 ∧ h - d = 0) by omega),
        if_pos (show 0 < rx ∧ 0 < h - d by omega), if_neg (show ¬ rx = 0 by omega)]
    · have hrx : rx = 0 := by omega
      simp only [k, Bx, crossingQ, if_neg h1, pow_zero, scalar_one, if_pos hrx, mul_one,
        if_pos (show rx = 0 ∧ h - d = 0 by omega)]
  rw [eT, eX, rational_divisorProbability_crossing a b c h d,
    show qpow (-(chooseTwo d : ℤ)) = scalar (((RatFunc.X : RatFunc ℚ) ^ chooseTwo d)⁻¹) by
      rw [qpow, zpow_neg, zpow_natCast]]
  calc scalar ((RatFunc.X ^ chooseTwo d)⁻¹) * (scalar ((RatFunc.X - 1) ^ k) * Bx *
      (P * (scalar ((RatFunc.X - 1) ^ i) * Bt)))
      = scalar ((RatFunc.X ^ chooseTwo d)⁻¹ * ((RatFunc.X - 1) ^ (i + k))) * (Bt * Bx * P) := by
        rw [pow_add, scalar_mul, scalar_mul]; ring
    _ = _ := by
        rw [← X_sub_one_mul_crossingWeight (i + k), ← mul_assoc (scalar (RatFunc.X - 1)),
          ← scalar_mul]
        simp only [mul_assoc]
        congr 2
        ring

/-- The `(c,h)` coefficient of `U_{a+b,b}⁺ · J(P_{a+b}) · U_{a,a+b}⁻` (`c > 0`) is `(q-1)` times
the regrouped exit sum of `T(a,b;c,h)`. -/
private theorem qmul_qplus_qdiag_qminus_crossingQ_apply (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) :
    qmul (qmul (qplus (crossingQ (a + b) b)) (qdiag (eulerSer (-1) (a + b))))
        (qminus (crossingQ a (a + b))) c h = scalar (RatFunc.X - 1) *
        (∑ d ∈ Finset.Icc 1 (min c h), ∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1),
        (if ((0 < rt ↔ d < c) ∧ (0 < rx ↔ d < h) ∧ rt + rx ≤ d) then scalar
        (divisorProbability (State.crossing a b c h) d).rational *
        ((if rt = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) a rt (c - d)))) *
        (if rx = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) b rx (h - d)))) *
        patternSum (-1) (a + b) (a * c + b * h) (d - rt - rx)) else 0)) := by
  rw [qmul_qplus_qdiag_qminus_apply]
  set G : ℕ → ℕ → ℕ → Coef := fun rx m rt ↦
    qpow (-(chooseTwo (rx + m + rt) : ℤ)) *
        (crossingQ (a + b) b rx (h - (rx + m + rt)) *
          (PowerSeries.coeff m (eulerSer (-1) (a + b)) *
            crossingQ a (a + b) (c - (rx + m + rt)) rt)) with hG
  have step1 : ∀ rx m rt : ℕ, (if (rx + m + rt ≤ c ∧ rx + m + rt ≤ h) then qpow
      (-(chooseTwo rx : ℤ) - (chooseTwo m : ℤ) - (chooseTwo rt : ℤ) - (rx : ℤ) *
      (m : ℤ) - ((rx : ℤ) + (m : ℤ)) * (rt : ℤ)) * (crossingQ (a + b) b rx (h - (rx + m + rt)) *
      (PowerSeries.coeff m (eulerSer (-1) (a + b)) * crossingQ a (a + b) (c - (rx + m + rt)) rt))
      else 0)
      = if rx + m + rt ≤ min c h then G rx m rt else 0 := by
    intro rx m rt
    have e : (chooseTwo rx : ℤ) + chooseTwo m + chooseTwo rt + rx * m + rx * rt + m * rt =
        ((chooseTwo (rx + m + rt) : ℕ) : ℤ) := by
      rw [chooseTwo_add, chooseTwo_add]; push_cast; ring
    rw [hG]
    simp only [le_min_iff]
    split_ifs
    · congr 2
      rw [← e]; ring
    · rfl
  simp only [step1]
  rw [sum_triple_reindex c (min c h) (min_le_left _ _) G, Finset.mul_sum]
  symm
  have hsub : Finset.Icc 1 (min c h) ⊆ Finset.range (c + 1) := fun d hd ↦ by
    simp only [Finset.mem_Icc, Finset.mem_range] at hd ⊢; omega
  have hzero : ∀ d ∈ Finset.range (c + 1), d ∉ Finset.Icc 1 (min c h) →
      (∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1), if rt + rx ≤ d ∧ d ≤
          min c h then G rx (d - rt - rx) rt else 0) = 0 := by
    intro d hd hnot
    simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
    refine Finset.sum_eq_zero fun rt hrt ↦ Finset.sum_eq_zero fun rx hrx ↦ ?_
    rcases hnot with h0 | h1
    · obtain rfl : d = 0 := by omega
      simp only [Finset.mem_range] at hrt hrx
      obtain ⟨rfl, rfl⟩ : rt = 0 ∧ rx = 0 := by omega
      have hz : crossingQ a (a + b) c 0 = 0 := qPositive_crossingQ _ _ c 0 (Or.inr rfl) (by omega)
      simp [hG, hz]
    · exact if_neg (by omega)
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun rt _ ↦ Finset.sum_congr rfl fun rx _ ↦
    (crossing_factorization_term a b c h d rt rx ha hb (Finset.mem_Icc.1 hd).2).symm

/-- **Crossing factorization.** `U_{a,b} = U_{a+b,b}⁺ · J(P_{a+b}) · U_{a,a+b}⁻`, where `J` is the
diagonal substitution and `P_{a+b} = eulerSer (-1) (a+b)`. -/
theorem crossingQ_eq_qmul_qplus_qdiag_qminus (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b) :
    crossingQ a b c h = qmul (qmul (qplus (crossingQ (a + b) b)) (qdiag (eulerSer (-1) (a + b))))
        (qminus (crossingQ a (a + b))) c h := by
  have Q2 : QPositive (qmul (qplus (crossingQ (a + b) b)) (qdiag (eulerSer (-1) (a + b)))) :=
    (qPositive_crossingQ _ _).qplus.qmul (qPositive_qdiag _)
  by_cases h00 : c = 0 ∧ h = 0
  · obtain ⟨rfl, rfl⟩ := h00
    rw [qmul_zero_zero, qmul_zero_zero, crossingQ_zero_zero]
    simp [qplus, qminus, qdiag, chooseTwo, crossingQ_zero_zero, qpow_zero, coeff_zero_eulerSer]
  · by_cases hp : 0 < c ∧ 0 < h
    · rw [qmul_qplus_qdiag_qminus_crossingQ_apply a b c h ha hb hp.1,
        ← lawCoef_exitLaw_crossing a b c h ha hb hp.1 hp.2,
        ← (state_law_unfold (.crossing a b c h) ⟨ha, hb, hp.1, hp.2⟩ rfl).2 a b c h rfl,
        crossingQ_of_pos a b c h hp.1 hp.2]
    · have z : c = 0 ∨ h = 0 := by omega
      rw [Q2.qmul (qPositive_crossingQ _ _).qminus c h z h00, qPositive_crossingQ a b c h z h00]

/-- If `G_b ≡ S(B_bᵛ)` through degree `M` for all `b > 0`, then `U_{a,b}` is unitary,
`U_{a,b} U_{a,b}† ≡ 1`, through total contact degree `2M + 1`. -/
theorem qcongr_crossingQ_mul_qdagger (M : ℕ) (hS : ∀ a : ℕ, 0 < a →
    SCongr M (eulerSer 0 a) (dilate (recipSer (clusterSer a)))) (j : ℕ) (hj : j ≤ 2 * M + 1)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    QCongr j (qmul (crossingQ a b) (qdagger (crossingQ a b))) qone := by
  have refl : ∀ (k : ℕ) (U : QSer), QCongr k U U := fun k U c h _ ↦ rfl
  have posUU : ∀ x y : ℕ, QPositive (qmul (crossingQ x y) (qdagger (crossingQ x y))) :=
    fun x y ↦ (qPositive_crossingQ x y).qmul (qPositive_crossingQ x y).qdagger
  induction j generalizing a b with
  | zero =>
    intro c h hc
    obtain ⟨rfl, rfl⟩ : c = 0 ∧ h = 0 := by omega
    rw [qmul_zero_zero]
    simp [qdagger, qone, crossingQ_zero_zero, qpow_zero]
  | succ j ih =>
    have hj' : j ≤ 2 * M + 1 := by omega
    set s := a + b with hs
    have hs0 : 0 < s := by omega
    set A := crossingQ s b
    set D := qdiag (eulerSer (-1) s)
    set Cq := crossingQ a s
    have hfac : crossingQ a b = qmul (qmul (qplus A) D) (qminus Cq) := by
      funext c h; exact crossingQ_eq_qmul_qplus_qdiag_qminus a b c h ha hb
    have hdag : qdagger (crossingQ a b) =
        qmul (qminus (qdagger Cq)) (qmul (qdagger D) (qplus (qdagger A))) := by
      rw [hfac, qdagger_qmul, qdagger_qmul, qdagger_qplus, qdagger_qminus]
    rw [hdag, hfac]
    -- rearrange
    have e1 : qmul (qmul (qmul (qplus A) D) (qminus Cq))
        (qmul (qminus (qdagger Cq)) (qmul (qdagger D) (qplus (qdagger A)))) =
        qmul (qmul (qplus A) D) (qmul (qminus (qmul Cq (qdagger Cq)))
          (qmul (qdagger D) (qplus (qdagger A)))) := by
      rw [qminus_qmul, qmul_assoc, ← qmul_assoc (qminus Cq)]
    rw [e1]
    have hC : QCongr (j + 1) (qminus (qmul Cq (qdagger Cq))) qone :=
      qcongr_qminus_qone (j + 1) _ (posUU a s) (by simpa using ih hj' a s ha hs0)
    have hA : QCongr (j + 1) (qplus (qmul A (qdagger A))) qone :=
      qcongr_qplus_qone (j + 1) _ (posUU s b) (by simpa using ih hj' s b hs0 hb)
    have hD : QCongr (j + 1) (qmul D (qdagger D)) qone :=
      (qcongr_qdiag_mul_qdagger M s
        (dilate_recipSer_eulerSer_mul_scongr_one M s hs0 hS)).mono (by omega)
    refine ((refl _ _).qmul (hC.qmul (refl _ _))).trans ?_
    rw [qone_qmul, qmul_assoc, ← qmul_assoc D]
    refine ((refl _ _).qmul (hD.qmul (refl _ _))).trans ?_
    rw [qone_qmul, ← qplus_qmul]
    exact hA

/-- The degree-one coefficient of `G_a = eulerSer 0 a` is `q Z_{a,1}`. -/
theorem coeff_one_eulerSer_zero (a : ℕ) :
    PowerSeries.coeff 1 (eulerSer 0 a) = qpow 1 * AddMonoidAlgebra.single ({(a, 1)} : FactorType)
        1 := by
  rw [coeff_eulerSer]
  let m1 : Pattern 1 := fun _ ↦ 1
  have hf : (Finset.univ : Finset (Pattern 1)).filter (fun m ↦ patternWeight m = 1) = {m1} := by
    ext m
    have key : patternWeight m = (m (0,0)).val := by
      simp [patternWeight, Fintype.sum_prod_type]
    rw [Finset.mem_filter, Finset.mem_singleton, key]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      funext ij
      have : ij = (0,0) := Subsingleton.elim _ _
      subst this
      apply Fin.ext
      simpa [m1] using h
    · intro h; subst h; rfl
  unfold patternSum
  rw [hf, Finset.sum_singleton]
  have hc : lawCoef (stateLaw (State.single a 1)) =
      AddMonoidAlgebra.single ({(a, 1)} : FactorType) 1 :=
    (coeff_succ_clusterSer a 0).symm.trans (coeff_one_clusterSer a)
  have hP : (∏ ij : Fin 1 × Fin 1,
      (adamsCoef (ij.1.val + 1) (lawCoef (stateLaw (State.single a (ij.2.val + 1))))) ^ (m1 ij).val)
      = AddMonoidAlgebra.single ({(a, 1)} : FactorType) 1 := by
    simp [m1, hc, adamsCoef_one]
  have hD : (divisorCount 0 m1).rational = RatFunc.X := by
    rw [rational_divisorCount]
    simp [m1, rational_availablePoints]
  rw [hP, hD, Algebra.smul_def, qpow_one, scalar_eq_algebraMap]

/-- Base case of cluster reciprocity: `G_a ≡ S(B_aᵛ)` through degree `1`. -/
theorem cluster_reciprocity_one (a : ℕ) :
    SCongr 1 (eulerSer 0 a) (dilate (recipSer (clusterSer a))) := by
  intro m hm
  interval_cases m
  · rw [coeff_zero_eulerSer, coeff_zero_dilate_recipSer_clusterSer]
  · rw [coeff_one_eulerSer_zero a, coeff_one_dilate_recipSer_clusterSer]

/-- The `n`-th coefficient of `ρ(U_{a,a}) Φ(G_a)`, expanded by divisor degree `d` and crossing
depth `r` into crossing laws and pattern sums (plus `1` in degree `0`). -/
theorem coeff_qact_crossingQ_gaussPhi_eulerSer (a n : ℕ) (ha : 0 < a) :
    PowerSeries.coeff n (qact (crossingQ a a) (gaussPhi (eulerSer 0 a))) =
        (∑ d ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (d + 1),
        (if ((0 < r ↔ d < n) ∧ r ≤ d) then scalar (divisorProbability (State.single a n)
        d).rational * ((if r = 0 then 1 else lawCoef (stateLaw (State.crossing a a r (n - d)))) *
        patternSum 0 a (a * n) (d - r)) else 0)) + (if n = 0 then 1 else 0) := by
  have hG : ∀ d r, d ≤ n → PowerSeries.coeff (d - r) (eulerSer 0 a) =
      patternSum 0 a (a * n) (d - r) := by
    intro d r hd
    rw [coeff_eulerSer]
    apply patternSum_eq_of_le
    · exact le_rfl
    · have := Nat.le_mul_of_pos_left n ha; omega
  rw [coeff_qact_gaussPhi, Finset.sum_range_succ']
  congr 1
  · have hI : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rw [add_comm 1 d]
    refine Finset.sum_congr rfl fun r hr ↦ ?_
    rw [Finset.mem_range] at hr
    rw [hG _ _ (by omega), rational_divisorProbability_single a n (d+1)]
    simp only [crossingQ, qpow]
    have hX : (RatFunc.X : RatFunc ℚ) ^ (-((tri (d+1) : ℕ) : ℤ)) =
        ((RatFunc.X : RatFunc ℚ) ^ tri (d+1))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [hX]
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      by_cases hdn : d + 1 < n
      · have : ¬ (n - (d+1) = 0) := by omega
        simp [hdn, this]
      · have : n - (d+1) = 0 := by omega
        simp [hdn, this]
    · by_cases hdn : d + 1 < n
      · have : 0 < n - (d+1) := by omega
        have hr' : r ≤ d + 1 := by omega
        simp only [h0.ne', false_and, if_false, h0, this, hdn, iff_self, hr', and_self, if_true,
            pow_one, scalar_mul]
        ring
      · have : ¬ (0 < n - (d+1)) := by omega
        simp [h0.ne', hdn, this]
  · have ht : tri 0 = 0 := rfl
    simp only [zero_add, Finset.sum_range_one, Nat.sub_self, ht, Nat.cast_zero, neg_zero, qpow_zero,
      one_mul, coeff_zero_eulerSer, mul_one, crossingQ]
    by_cases hn : n = 0 <;> simp [hn]

/-- The self-pattern term of the recursion of `S(a;n)` (`n ≥ 2`) is
`q^{-tri n} · q · F_{S(a;n)}`. -/
theorem lawCoef_single_self_term (a n : ℕ) (ha : 0 < a) (hn : 2 ≤ n)
    (P : TangentPattern (State.single a n).degree) (hP : Allowed (State.single a n) P)
    (hself : SelfPattern (State.single a n) P) :
    lawCoef (lawScale (.mul (tangentCount (State.single a n) P)
        (divisorProbability (State.single a n) P.d.val))
        (lawProd ((children (State.single a n) P).map fun z ↦ lawDescend z.1 (stateLaw z.2)))) =
        qpow (-(tri n : ℤ)) * (qpow 1 * lawCoef (stateLaw (State.single a n))) := by
  rw [lawCoef_single_term a n ha (by omega) P hP]
  obtain ⟨hd, hrt, -, hother⟩ := (selfPattern_single_iff a n ha hn P hP).1 hself
  have hdeg : (State.single a n).degree = a * n := rfl
  have hpos : 0 < (State.single a n).degree := by rw [hdeg]; exact Nat.mul_pos ha (by omega)
  have hn1 : n - 1 < (State.single a n).degree := by
    rw [hdeg]; have := Nat.le_mul_of_pos_left n ha; omega
  have hprob : (divisorProbability (State.single a n) P.d.val).rational
      = ((RatFunc.X : RatFunc ℚ) ^ tri n)⁻¹ := by
    rw [hd, rational_divisorProbability_single a n n]; simp
  have hf : ∀ b, (∏ j : Fin (State.single a n).degree,
      ((Nat.factorial (P.other (b, j)).val : ℕ) : ℚ)) = 1 := fun b ↦
    Finset.prod_eq_one fun j _ ↦ by rw [hother]; split_ifs <;> simp
  have hcount : (divisorCount 0 P.other).rational = (RatFunc.X : RatFunc ℚ) := by
    rw [rational_divisorCount, Finset.prod_eq_single (⟨0, hpos⟩ : Fin (State.single a n).degree)]
    · rw [Finset.sum_eq_single (⟨n - 1, hn1⟩ : Fin (State.single a n).degree), hf]
      · simp [hother, rational_availablePoints]
      · intro b _ hb
        simp [hother, show b.val ≠ n - 1 from fun h ↦ hb (Fin.ext h)]
      · simp
    · intro b _ hb
      rw [Finset.sum_eq_zero fun j _ ↦ by
        simp [hother, show b.val ≠ 0 from fun h ↦ hb (Fin.ext h)], hf]
      simp
    · simp
  have hprod : (∏ ij : Fin (State.single a n).degree × Fin (State.single a n).degree,
      (adamsCoef (ij.1.val + 1) (lawCoef (stateLaw (State.single a (ij.2.val + 1))))) ^
          (P.other ij).val)
      = lawCoef (stateLaw (State.single a n)) := by
    rw [Finset.prod_eq_single ((⟨0, hpos⟩, ⟨n - 1, hn1⟩) : Fin (State.single a n).degree × Fin
        (State.single a n).degree)]
    · rw [hother]
      simp only [and_self, if_true, pow_one]
      rw [show n - 1 + 1 = n by omega, adamsCoef_one]
    · intro b _ hb
      rw [hother, if_neg, pow_zero]
      rintro ⟨h1, h2⟩
      exact hb (Prod.ext (Fin.ext h1) (Fin.ext h2))
    · simp
  rw [hprod, hprob, hcount, if_pos hrt, one_mul, scalar_mul, ← qpow_one,
    show qpow (-(tri n : ℤ)) = scalar (((RatFunc.X : RatFunc ℚ) ^ tri n)⁻¹) by
      rw [qpow, zpow_neg, zpow_natCast]]
  ring

end SurfaceBlowup
