/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log

/-!
# Reciprocity: definitions and basic lemmas

The algebraic setting of the reciprocity argument. Over the coefficient ring
`Coef = ℚ(q)[Z_{e,f}]` we define the substitutions `q ↦ q⁻¹` (`recipRat`, `recipCoef`) and the
Adams operations `ψ_δ` (`adamsRat`, `adamsCoef`, `adamsSer`), power series in the cluster variable
`x` (`Ser`) with their exponential, logarithm, plethystic exponential/logarithm, dilations and
congruences, and the quantum-torus side: contact series `QSer` with the twisted product `qmul`,
the embeddings `ι₊`, `ι₋`, the diagonal substitution `qdiag`, and the representation `qact`.
We then prove the first algebraic properties of these objects.

## Main results

* `adamsRat_recipRat`, `adamsRat_adamsRat`, `coeff_adamsSer`: the Adams substitutions.
* `derivative_expSer`, `mul_derivative_logSer`, `coeff_expSer_sub_of_scongr`: `exp` and `log`.
* `qact_qmul`, `qplus_qmul`, `qminus_qmul`, `qone_qmul`: the twisted product and its
  representation.
* `qmul_qplus_qdiag_qminus_apply`: the triple-sum expansion of `ι₊(A) qdiag(D) ι₋(C)`.
* `qcongr_qplus_qone`, `qcongr_qminus_qone`: `ι₊`, `ι₋` of positive series close to `1`.

Provenance: `Def_SurfaceBlowupV2_{RecipRational,RecipCoef,RecipSeries,RecipQuantum}`,
`Thm_SurfaceBlowupV2_recip_{adamsRat_apply, adamsSer_hom, adamsSer_cluster_trunc,
binomial_series_ode, crossing_pattern_reindex, crossing_weight_identity, expSer_basic,
gauss_exponents, logSer_basic, pattern_entry_bound, power_coeff_multinomial, qact_congr,
qact_gaussPhi_coeff, qact_leading, qact_mul, qact_one_linear, qcongr_basic, qdiag_degree,
qminus_mul, qmul_one, qmul_plus_diag_minus_expand, qplus_degree, scongr_exp_log_lead}`.
-/

noncomputable section

namespace SurfaceBlowup

/-! ### Definitions -/

namespace Expr
/-- Rational well-formedness: every inverted subexpression has a nonzero numerator polynomial, so
that `Expr.rational` is a ring homomorphism on the expression (its unreduced denominators never
vanish). -/
def wf : Expr → Prop
  | .const _ => True
  | .var => True
  | .add x y => wf x ∧ wf y
  | .mul x y => wf x ∧ wf y
  | .inv x => wf x ∧ x.fraction.1 ≠ 0
end Expr
/-- Polynomials evaluated at X⁻¹ in ℚ(X). -/
def recipPoly : Polynomial ℚ →+* RatFunc ℚ :=
  Polynomial.eval₂RingHom (RatFunc.C : ℚ →+* RatFunc ℚ) (RatFunc.X)⁻¹
/-- Polynomials evaluated at X^δ in ℚ(X). -/
private def adamsPoly (δ : ℕ) : Polynomial ℚ →+* RatFunc ℚ :=
  Polynomial.eval₂RingHom (RatFunc.C : ℚ →+* RatFunc ℚ) (RatFunc.X ^ δ)
/-- Evaluating a polynomial at `X` in `ℚ(X)` is the canonical embedding. -/
theorem eval₂_C_X_eq_algebraMap (g : Polynomial ℚ) :
    Polynomial.eval₂ (RatFunc.C : ℚ →+* RatFunc ℚ) (RatFunc.X : RatFunc ℚ) g =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [RatFunc.algebraMap_monomial]
/-- A nonzero polynomial stays nonzero after the substitution `X ↦ X⁻¹`. -/
private theorem recipPoly_ne_zero (p : Polynomial ℚ) (hp : p ≠ 0) : recipPoly p ≠ 0 := by
  let _ : Invertible (RatFunc.X : RatFunc ℚ) := invertibleOfNonzero RatFunc.X_ne_zero
  have key := Polynomial.eval₂_reflect_eq_zero_iff (RatFunc.C : ℚ →+* RatFunc ℚ)
    (RatFunc.X : RatFunc ℚ) p.natDegree (p.reflect p.natDegree)
    (by simpa using Polynomial.natDegree_reflect_le (N := p.natDegree) (p := p))
  rw [Polynomial.reflect_reflect, invOf_eq_inv] at key
  intro h
  have h3 := key.mp h
  rw [eval₂_C_X_eq_algebraMap] at h3
  exact hp (Polynomial.reflect_eq_zero_iff.mp
    (not_not.1 fun hne ↦ RatFunc.algebraMap_ne_zero hne h3))
/-- `recipPoly` is injective. -/
private theorem recipPoly_injective : Function.Injective recipPoly :=
  (injective_iff_map_eq_zero _).2 fun p hp ↦ not_not.1 fun hne ↦ recipPoly_ne_zero p hne hp
/-- A nonzero polynomial stays nonzero after the substitution `X ↦ X^δ`, `δ > 0`. -/
private theorem adamsPoly_ne_zero (δ : ℕ) (hδ : 0 < δ) (p : Polynomial ℚ) (hp : p ≠ 0) :
    adamsPoly δ p ≠ 0 := by
  intro h
  have h2 : Polynomial.eval₂ (RatFunc.C : ℚ →+* RatFunc ℚ) (RatFunc.X : RatFunc ℚ)
      ((Polynomial.X : Polynomial ℚ) ^ δ) = (RatFunc.X : RatFunc ℚ) ^ δ := by simp
  change Polynomial.eval₂ _ ((RatFunc.X : RatFunc ℚ) ^ δ) p = 0 at h
  rw [← h2, ← Polynomial.eval₂_comp, eval₂_C_X_eq_algebraMap] at h
  rcases Polynomial.comp_eq_zero_iff.mp
      (not_not.1 fun hne ↦ RatFunc.algebraMap_ne_zero hne h) with h4 | ⟨_, h5⟩
  · exact hp h4
  · have h6 := congrArg Polynomial.natDegree h5
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at h6
    omega
/-- `adamsPoly δ` is injective for `δ > 0`. -/
private theorem adamsPoly_injective (δ : ℕ) (hδ : 0 < δ) : Function.Injective (adamsPoly δ) :=
  (injective_iff_map_eq_zero _).2 fun p hp ↦ not_not.1 fun hne ↦ adamsPoly_ne_zero δ hδ p hne hp
/-- The automorphism q ↦ q⁻¹ of ℚ(X) (reciprocal substitution, the proof's `v`). -/
def recipRat : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom recipPoly
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective recipPoly recipPoly_injective)
/-- The Adams substitution q ↦ q^δ on ℚ(X) (δ > 0; the identity for δ = 0, never used). -/
def adamsRat (δ : ℕ) : RatFunc ℚ →+* RatFunc ℚ :=
  if hδ : 0 < δ then
    RatFunc.liftRingHom (adamsPoly δ)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (adamsPoly δ)
        (adamsPoly_injective δ hδ))
  else RingHom.id (RatFunc ℚ)

/-- The coefficient algebra ℚ(q)[Z_{e,f}]: finitely supported functions on types, multiplied by
adding the multisets (the product of Z-monomials). A law becomes an element of this commutative
ring. -/
abbrev Coef := AddMonoidAlgebra (RatFunc ℚ) FactorType
/-- The scalar embedding ℚ(q) → Coef (the empty type is the monomial 1). -/
def scalar (f : RatFunc ℚ) : Coef := AddMonoidAlgebra.single 0 f
/-- q^k for an integer k, as a scalar of Coef. -/
def qpow (k : ℤ) : Coef := scalar (RatFunc.X ^ k)
/-- A law as an element of Coef: the sum over its entries of (rational value) · Z^{type}. -/
def lawCoef (L : Law) : Coef := (L.map fun z ↦ AddMonoidAlgebra.single z.1 z.2.rational).sum
/-- scaleType δ as an additive monoid homomorphism of types (multisets add). -/
def scaleTypeHom (δ : ℕ) : FactorType →+ FactorType where
  toFun := scaleType δ
  map_zero' := by simp [scaleType]
  map_add' := fun σ τ ↦ by simp [scaleType, Multiset.map_add]
/-- The Adams operation ψ_δ on Coef: q ↦ q^δ on every coefficient and Z_{e,f} ↦ Z_{e,δf} on
types. -/
def adamsCoef (δ : ℕ) : Coef →+* Coef :=
  (AddMonoidAlgebra.mapDomainRingHom (RatFunc ℚ) (scaleTypeHom δ)).comp
    (AddMonoidAlgebra.mapRingHom FactorType (adamsRat δ))
/-- Reciprocal substitution v on Coef: q ↦ q⁻¹ on every coefficient, types unchanged. -/
def recipCoef : Coef →+* Coef := AddMonoidAlgebra.mapRingHom FactorType recipRat
/-- Every entry of the law is a well-formed expression. -/
def LawWf (L : Law) : Prop := ∀ z ∈ L, z.2.wf

/-- Series in the cluster-degree variable x with coefficients in Coef. -/
abbrev Ser := PowerSeries Coef
/-- Agreement of two series in every degree ≤ n (congruence modulo x^{n+1}). -/
def SCongr (n : ℕ) (f g : Ser) : Prop :=
  ∀ m : ℕ, m ≤ n → PowerSeries.coeff m f = PowerSeries.coeff m g
/-- The Adams operation ψ_k on series: ψ_k on every coefficient and x ↦ x^k (zero for k = 0,
never used). -/
def adamsSer (k : ℕ) (f : Ser) : Ser :=
  if hk : k = 0 then 0 else PowerSeries.expand k hk (PowerSeries.map (adamsCoef k) f)
/-- Σ_{k ≥ 1} ψ_k(f)/k, coefficientwise finite: the coefficient of xⁿ is
Σ_{k ∣ n} (1/k) ψ_k(f_{n/k}). -/
def plethSum (f : Ser) : Ser :=
  PowerSeries.mk fun n ↦ ∑ k ∈ n.divisors, ((k : ℚ)⁻¹) • adamsCoef k (PowerSeries.coeff (n / k) f)
/-- Σ_{k ≥ 1} μ(k) ψ_k(g)/k, coefficientwise finite. -/
def moebiusSum (g : Ser) : Ser :=
  PowerSeries.mk fun n ↦ ∑ k ∈ n.divisors,
    ((((ArithmeticFunction.moebius k : ℤ) : ℚ)) / (k : ℚ)) •
      adamsCoef k (PowerSeries.coeff (n / k) g)
/-- Σ_{m ≥ 1} C_m ψ_m(L) with C_m = availablePoints ε m: the coefficient of xⁿ is
Σ_{m ∣ n} C_m ψ_m(L_{n/m}). -/
def countSum (ε : ℤ) (L : Ser) : Ser :=
  PowerSeries.mk fun n ↦ ∑ m ∈ n.divisors,
    (availablePoints ε m).rational • adamsCoef m (PowerSeries.coeff (n / m) L)
/-- Ordinary exponential of a series with zero constant term (composition with Σ xⁿ/n!). -/
def expSer (f : Ser) : Ser := (PowerSeries.exp Coef).subst f
/-- Ordinary logarithm of a series with constant term one. -/
def logSer (g : Ser) : Ser := PowerSeries.logOf g
/-- The formal power g^c = exp(c · log g) for a scalar exponent c ∈ ℚ(q). -/
def formalPow (c : RatFunc ℚ) (g : Ser) : Ser := expSer (PowerSeries.C (scalar c) * logSer g)
/-- Plethystic exponential Exp f = exp(Σ_k ψ_k(f)/k). -/
def pExp (f : Ser) : Ser := expSer (plethSum f)
/-- Plethystic logarithm Log g = Σ_k μ(k) ψ_k(log g)/k. -/
def pLog (g : Ser) : Ser := moebiusSum (logSer g)
/-- The plethystic power P_w(g) = Exp(w · Log g) for a scalar w ∈ ℚ(q). -/
def pPow (w : RatFunc ℚ) (g : Ser) : Ser := pExp (PowerSeries.C (scalar w) * pLog g)
/-- Reciprocal substitution on every coefficient of a series (the proof's f ↦ f^v). -/
def recipSer (f : Ser) : Ser := PowerSeries.map recipCoef f
/-- Dilation S: x ↦ qx. -/
def dilate (f : Ser) : Ser := PowerSeries.rescale (scalar RatFunc.X) f
/-- Inverse dilation S⁻¹: x ↦ x/q. -/
def codilate (f : Ser) : Ser := PowerSeries.rescale (scalar RatFunc.X⁻¹) f
/-- The cluster series B_a = 1 + Σ_{n ≥ 1} F_{S(a;n)} xⁿ of vertical multiplicity a. -/
def clusterSer (a : ℕ) : Ser :=
  PowerSeries.mk fun n ↦ if n = 0 then 1 else lawCoef (stateLaw (State.single a n))
/-- The Euler transform P_{q+ε}(B_a) with q + ε rational points: G_a (ε = 0), P_a (ε = −1),
Q_a (ε = 1). -/
def eulerSer (ε : ℤ) (a : ℕ) : Ser := pPow (RatFunc.X + (ε : RatFunc ℚ)) (clusterSer a)
/-- The off-boundary pattern sum of weight w in ambient dimension N for vertical multiplicity a and
offset ε:
Σ over patterns m of weight w of divisorCount ε m · Π_{(i,j)} ψ_{i+1}(F_{S(a;j+1)})^{m(i,j)}. -/
def patternSum (ε : ℤ) (a N w : ℕ) : Coef :=
  ∑ m ∈ (Finset.univ : Finset (Pattern N)).filter (fun m ↦ patternWeight m = w),
    (divisorCount ε m).rational • ∏ ij : Fin N × Fin N,
      (adamsCoef (ij.1.val + 1) (lawCoef (stateLaw (State.single a (ij.2.val + 1))))) ^ (m ij).val

/-- Contact series: coefficient functions on contact pairs (c,h), i.e. Σ U(c,h) E_{c,h} in the
normal basis. -/
abbrev QSer := ℕ → ℕ → Coef
/-- The twisted product E_{c,h} E_{d,k} = q^{-ck} E_{c+d,h+k}, as a finite convolution. -/
def qmul (U V : QSer) : QSer := fun c h ↦
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal c, ∑ r ∈ Finset.HasAntidiagonal.antidiagonal h,
    qpow (-((p.1 : ℤ) * (r.2 : ℤ))) * (U p.1 r.1 * V p.2 r.2)
/-- The unit E_{0,0}. -/
def qone : QSer := fun c h ↦ if c = 0 ∧ h = 0 then 1 else 0
/-- Reciprocal substitution on every coefficient (the proof's V^v). -/
def qrecip (U : QSer) : QSer := fun c h ↦ recipCoef (U c h)
/-- The anti-involution †: (f E_{c,h})† = v(f) q^{c+h−ch} E_{c,h}. -/
def qdagger (U : QSer) : QSer := fun c h ↦
  qpow ((c : ℤ) + (h : ℤ) - (c : ℤ) * (h : ℤ)) * recipCoef (U c h)
/-- ι₊: E_{c,h} ↦ q^{-C(c,2)} E_{c,c+h}. -/
def qplus (U : QSer) : QSer := fun c k ↦
  if c ≤ k then qpow (-(chooseTwo c : ℤ)) * U c (k - c) else 0
/-- ι₋: E_{c,h} ↦ q^{-C(h,2)} E_{c+h,h}. -/
def qminus (U : QSer) : QSer := fun k h ↦
  if h ≤ k then qpow (-(chooseTwo h : ℤ)) * U (k - h) h else 0
/-- Diagonal substitution x ↦ J = E_{1,1}: Σ aₘ xᵐ ↦ Σ aₘ Jᵐ with Jᵐ = q^{-C(m,2)} E_{m,m}. -/
def qdiag (f : Ser) : QSer := fun c h ↦
  if c = h then qpow (-(chooseTwo c : ℤ)) * PowerSeries.coeff c f else 0
/-- U_{a,b} = 1 + (q−1) Σ_{c,h ≥ 1} F_{T(a,b;c,h)} E_{c,h}; zero on the two axes. -/
def crossingQ (a b : ℕ) : QSer := fun c h ↦
  if c = 0 ∧ h = 0 then 1
  else if 0 < c ∧ 0 < h then scalar (RatFunc.X - 1) * lawCoef (stateLaw (State.crossing a b c h))
  else 0
/-- Agreement through total contact degree j. -/
def QCongr (j : ℕ) (U V : QSer) : Prop := ∀ c h : ℕ, c + h ≤ j → U c h = V c h
/-- Vanishing on the two axes away from the constant term (support in the positive quadrant plus
`(0,0)`). -/
def QPositive (U : QSer) : Prop := ∀ c h : ℕ, (c = 0 ∨ h = 0) → ¬ (c = 0 ∧ h = 0) → U c h = 0
/-- The representation ρ: ρ(E_{c,h}) f = q^{-tri c} x^{c+h} f(x/q^c); coefficient n sums over
(c+h) + m = n. -/
def qact (U : QSer) (f : Ser) : Ser := PowerSeries.mk fun n ↦
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ r ∈ Finset.HasAntidiagonal.antidiagonal p.1,
    qpow (-(tri r.1 : ℤ) - (r.1 : ℤ) * (p.2 : ℤ)) * (U r.1 r.2 * PowerSeries.coeff p.2 f)
/-- The same representation with q replaced by q⁻¹ (all Gaussian exponents negated). -/
def qactRecip (U : QSer) (f : Ser) : Ser := PowerSeries.mk fun n ↦
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ r ∈ Finset.HasAntidiagonal.antidiagonal p.1,
    qpow ((tri r.1 : ℤ) + (r.1 : ℤ) * (p.2 : ℤ)) * (U r.1 r.2 * PowerSeries.coeff p.2 f)
/-- Φ: xᵐ ↦ q^{-tri m} xᵐ. -/
def gaussPhi (f : Ser) : Ser := PowerSeries.mk fun n ↦ qpow (-(tri n : ℤ)) * PowerSeries.coeff n f
/-- Φ⁻¹: xᵐ ↦ q^{tri m} xᵐ. -/
def gaussPhiInv (f : Ser) : Ser := PowerSeries.mk fun n ↦ qpow (tri n : ℤ) * PowerSeries.coeff n f

/-! ### Gaussian exponents and `qpow` -/

/-- `2 · tri n = n(n+1)`, as integers. -/
theorem two_mul_tri (n : ℕ) : 2 * (tri n : ℤ) = n * (n + 1) := by
  have : 2 * tri n = n * (n + 1) := by
    unfold tri; exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  exact_mod_cast this

/-- `2 · C(n,2) = n(n-1)`, as integers. -/
theorem two_mul_chooseTwo (n : ℕ) : 2 * (chooseTwo n : ℤ) = n * (n - 1) := by
  have h : 2 * chooseTwo n = n * (n - 1) := by
    unfold chooseTwo; exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  rcases n with _ | n
  · simp [chooseTwo]
  · have h' : (2 * chooseTwo (n + 1) : ℤ) = (n + 1) * n := by exact_mod_cast h
    rw [h']; push_cast; ring

/-- Additivity defect of the triangular numbers: `tri (r + m) = tri r + r m + tri m`. -/
private theorem tri_add (r m : ℕ) : (tri (r + m) : ℤ) = tri r + r * m + tri m := by
  have := two_mul_tri (r + m); have := two_mul_tri r; have := two_mul_tri m
  push_cast at *; linarith

/-- Additivity defect of `C(·,2)`: `C(r + s, 2) = C(r,2) + C(s,2) + r s`. -/
theorem chooseTwo_add (r s : ℕ) :
    (chooseTwo (r + s) : ℤ) = chooseTwo r + chooseTwo s + r * s := by
  have := two_mul_chooseTwo (r + s); have := two_mul_chooseTwo r; have := two_mul_chooseTwo s
  push_cast at *; linarith

/-- `q^{j+k} = q^j q^k` in `Coef`. -/
theorem qpow_add (j k : ℤ) : qpow (j + k) = qpow j * qpow k := by
  simp [qpow, scalar, AddMonoidAlgebra.single_mul_single, zpow_add₀ (RatFunc.X_ne_zero (K := ℚ))]

/-- `q^0 = 1` in `Coef`. -/
theorem qpow_zero : qpow 0 = 1 := by simp [qpow, scalar, AddMonoidAlgebra.one_def]

/-! ### The substitutions `q ↦ q^δ` and `q ↦ q⁻¹` on `ℚ(q)` -/

/-- `adamsRat δ` (`δ > 0`) extends `adamsPoly δ`. -/
private theorem adamsRat_algebraMap (δ : ℕ) (hδ : 0 < δ) (g : Polynomial ℚ) :
    adamsRat δ (algebraMap (Polynomial ℚ) (RatFunc ℚ) g) = adamsPoly δ g := by
  unfold adamsRat; rw [dif_pos hδ]; simp

/-- `recipRat` extends `recipPoly`. -/
theorem recipRat_algebraMap (g : Polynomial ℚ) :
    recipRat (algebraMap (Polynomial ℚ) (RatFunc ℚ) g) = recipPoly g := by
  simp [recipRat]

/-- `recipRat` fixes the constants. -/
theorem recipRat_C (r : ℚ) : recipRat (RatFunc.C r) = RatFunc.C r := by
  rw [← RatFunc.algebraMap_C, recipRat_algebraMap]; simp [recipPoly]

/-- `adamsRat δ q = q^δ` for `δ > 0`. -/
theorem adamsRat_X (δ : ℕ) (hδ : 0 < δ) : adamsRat δ RatFunc.X = RatFunc.X ^ δ := by
  rw [← RatFunc.algebraMap_X, adamsRat_algebraMap δ hδ]; simp [adamsPoly]

/-- `recipRat q = q⁻¹`. -/
theorem recipRat_X : recipRat RatFunc.X = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X, recipRat_algebraMap]; simp [recipPoly]

private theorem ratFunc_ringHom_ext (φ ψ : RatFunc ℚ →+* RatFunc ℚ)
    (h : ∀ g : Polynomial ℚ, φ (algebraMap (Polynomial ℚ) (RatFunc ℚ) g)
      = ψ (algebraMap (Polynomial ℚ) (RatFunc ℚ) g)) : φ = ψ := by
  ext f
  rw [← RatFunc.num_div_denom f, map_div₀, map_div₀, h, h]

private theorem ringHom_eval₂ (φ : RatFunc ℚ →+* RatFunc ℚ) (g : Polynomial ℚ) (a : RatFunc ℚ) :
    φ (g.eval₂ RatFunc.C a) = g.eval₂ RatFunc.C (φ a) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  ext r; simp

/-- The Adams substitution commutes with `q ↦ q⁻¹`. -/
theorem adamsRat_recipRat (δ : ℕ) (hδ : 0 < δ) (f : RatFunc ℚ) :
    adamsRat δ (recipRat f) = recipRat (adamsRat δ f) := by
  refine DFunLike.congr_fun (ratFunc_ringHom_ext ((adamsRat δ).comp recipRat)
    (recipRat.comp (adamsRat δ)) fun g ↦ ?_) f
  simp only [RingHom.comp_apply]
  rw [recipRat_algebraMap, adamsRat_algebraMap δ hδ]
  change adamsRat δ (g.eval₂ RatFunc.C (RatFunc.X)⁻¹) = recipRat (g.eval₂ RatFunc.C (RatFunc.X ^ δ))
  rw [ringHom_eval₂, ringHom_eval₂, map_inv₀, map_pow, adamsRat_X δ hδ, recipRat_X, inv_pow]

/-- `ψ_δ ∘ ψ_k = ψ_{δk}` on `ℚ(q)`. -/
theorem adamsRat_adamsRat (δ k : ℕ) (hδ : 0 < δ) (hk : 0 < k) (f : RatFunc ℚ) :
    adamsRat δ (adamsRat k f) = adamsRat (δ * k) f := by
  refine DFunLike.congr_fun (ratFunc_ringHom_ext ((adamsRat δ).comp (adamsRat k))
    (adamsRat (δ * k)) fun g ↦ ?_) f
  simp only [RingHom.comp_apply]
  rw [adamsRat_algebraMap k hk, adamsRat_algebraMap (δ * k) (Nat.mul_pos hδ hk)]
  change adamsRat δ (g.eval₂ RatFunc.C (RatFunc.X ^ k)) = g.eval₂ RatFunc.C (RatFunc.X ^ (δ * k))
  rw [ringHom_eval₂, map_pow, adamsRat_X δ hδ, pow_mul]

/-- `ψ_1` is the identity of `ℚ(q)`. -/
theorem adamsRat_one (f : RatFunc ℚ) : adamsRat 1 f = f := by
  refine DFunLike.congr_fun (ratFunc_ringHom_ext (adamsRat 1) (RingHom.id _) fun g ↦ ?_) f
  rw [adamsRat_algebraMap 1 one_pos]
  change g.eval₂ RatFunc.C (RatFunc.X ^ 1) = _
  rw [pow_one, eval₂_C_X_eq_algebraMap]; rfl

/-- `ψ_δ (q^j) = q^{δj}` for integer `j`. -/
theorem adamsRat_zpow_X (δ : ℕ) (hδ : 0 < δ) (j : ℤ) :
    adamsRat δ ((RatFunc.X : RatFunc ℚ) ^ j) = (RatFunc.X : RatFunc ℚ) ^ ((δ : ℤ) * j) := by
  rw [map_zpow₀, adamsRat_X δ hδ, ← zpow_natCast, ← zpow_mul]

/-! ### Adams operations on series -/

/-- `[xⁿ] ψ_k f = ψ_k([x^{n/k}] f)` if `k ∣ n`, and `0` otherwise (`k ≠ 0`). -/
theorem coeff_adamsSer (k : ℕ) (hk : k ≠ 0) (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (adamsSer k f) =
      if k ∣ n then adamsCoef k (PowerSeries.coeff (n / k) f) else 0 := by
  simp only [adamsSer, dif_neg hk, PowerSeries.coeff_expand, PowerSeries.coeff_map]

/-- The constant term of `ψ_k f` is `ψ_k` of the constant term of `f` (`k ≠ 0`). -/
theorem constantCoeff_adamsSer (k : ℕ) (hk : k ≠ 0) (f : Ser) :
    PowerSeries.constantCoeff (adamsSer k f) = adamsCoef k (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_adamsSer k hk]; simp

/-- `ψ_k 1 = 1` (`k ≠ 0`). -/
theorem adamsSer_one (k : ℕ) (hk : k ≠ 0) : adamsSer k (1 : Ser) = 1 := by
  simp [adamsSer, dif_neg hk]

/-- `ψ_k` on series is additive on differences (`k ≠ 0`). -/
theorem adamsSer_sub (k : ℕ) (hk : k ≠ 0) (f g : Ser) :
    adamsSer k (f - g) = adamsSer k f - adamsSer k g := by
  simp [adamsSer, dif_neg hk]

/-- Through degree `n`, `ψ_m(B_a) - 1` is the finite sum
`Σ_{r < n} ψ_m(F_{S(a;r+1)}) x^{m(r+1)}`. -/
theorem adamsSer_clusterSer_sub_one_scongr (a m n : ℕ) (hm : 0 < m) :
    SCongr n (adamsSer m (clusterSer a) - 1)
      (∑ r : Fin n, PowerSeries.C (adamsCoef m (lawCoef (stateLaw (State.single a (r.val + 1))))) *
        (PowerSeries.X : Ser) ^ (m * (r.val + 1))) := by
  intro i hi
  rw [map_sub, coeff_adamsSer m hm.ne', map_sum]
  simp only [PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_one]
  by_cases h0 : i = 0
  · subst h0
    have : ∀ r : Fin n, ¬ (0 = m * (r.val + 1)) := fun r ↦ (Nat.mul_pos hm r.val.succ_pos).ne
    simp [this, clusterSer]
  by_cases hd : m ∣ i
  · obtain ⟨s, rfl⟩ := hd
    have hs : 0 < s := Nat.pos_of_ne_zero (fun e ↦ h0 (by simp [e]))
    have hsn : s ≤ n := by nlinarith
    rw [Finset.sum_eq_single (⟨s - 1, by omega⟩ : Fin n)]
    · have e : s - 1 + 1 = s := by omega
      simp [h0, clusterSer, Nat.mul_div_cancel_left _ hm, hs.ne', e]
    · intro r _ hr
      rw [if_neg]
      intro hh
      exact hr (Fin.ext (by have := Nat.eq_of_mul_eq_mul_left hm hh; simp; omega))
    · simp
  · rw [if_neg hd, Finset.sum_eq_zero fun r _ ↦ if_neg fun h ↦ hd ⟨_, h⟩]
    simp [h0]

/-! ### Exponential, logarithm and binomial series -/

/-- The binomial series `Σ C(c,n) xⁿ` solves `(1 + x) y' = c y`. -/
theorem binomial_series_ode (c : RatFunc ℚ) :
    (1 + PowerSeries.X) * PowerSeries.derivative Coef (PowerSeries.mk fun n ↦
      ((n.factorial : ℚ)⁻¹) • ∏ j ∈ Finset.range n, (scalar c - (j : ℚ) • (1 : Coef))) =
    PowerSeries.C (scalar c) * PowerSeries.mk (fun n ↦
      ((n.factorial : ℚ)⁻¹) • ∏ j ∈ Finset.range n, (scalar c - (j : ℚ) • (1 : Coef))) := by
  set b : ℕ → Coef := fun n ↦
    ((n.factorial : ℚ)⁻¹) • ∏ j ∈ Finset.range n, (scalar c - (j : ℚ) • (1 : Coef)) with hb
  have key : ∀ n : ℕ, ((n + 1 : ℕ) : ℚ) • b (n + 1) = (scalar c - (n : ℚ) • (1 : Coef)) * b n := by
    intro n
    simp only [hb, Finset.prod_range_succ, smul_smul, Nat.factorial_succ, Nat.cast_mul]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, mul_comm _ (scalar c - _),
      mul_smul_comm]
  have hd : ∀ m : ℕ, PowerSeries.coeff m (PowerSeries.derivative Coef (PowerSeries.mk b))
      = ((m + 1 : ℕ) : ℚ) • b (m + 1) := by
    intro m
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, mul_comm, Nat.cast_smul_eq_nsmul,
      nsmul_eq_mul]
    push_cast; rfl
  refine PowerSeries.ext fun n ↦ ?_
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, add_mul, one_mul, map_add]
  rcases n with _ | n
  · rw [PowerSeries.coeff_zero_X_mul, add_zero, hd, key]
    simp [hb]
  · rw [PowerSeries.coeff_succ_X_mul, hd, hd, key, sub_mul, smul_mul_assoc, one_mul, sub_add_cancel]

/-- `exp f` has constant term `1` when `f(0) = 0`. -/
theorem constantCoeff_expSer (f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.constantCoeff (expSer f) = 1 := by
  change MvPowerSeries.constantCoeff _ = 1
  rw [expSer, PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hf),
    finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
    rfl
  · intro d hd
    have h0 : MvPowerSeries.constantCoeff f = 0 := hf
    simp [h0, zero_pow hd]

/-- The chain rule `(exp f)' = f' · exp f` (for `f(0) = 0`). -/
theorem derivative_expSer (f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.derivative Coef (expSer f) = PowerSeries.derivative Coef f * expSer f := by
  rw [expSer, PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hf),
    PowerSeries.derivative_exp, mul_comm]

/-- `exp 0 = 1`. -/
theorem expSer_zero : expSer (0 : Ser) = 1 := by
  rw [expSer, PowerSeries.subst_zero_eq_C_constantCoeff]
  ext n
  simp

/-- `log g` has constant term `0` when `g(0) = 1`. -/
theorem constantCoeff_logSer (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.constantCoeff (logSer g) = 0 :=
  PowerSeries.constantCoeff_logOf hg

/-- The logarithmic derivative `g · (log g)' = g'` (for `g(0) = 1`). -/
theorem mul_derivative_logSer (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    g * PowerSeries.derivative Coef (logSer g) = PowerSeries.derivative Coef g := by
  have hs : PowerSeries.HasSubst (g - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hg])
  set G : Ser := PowerSeries.mk fun n ↦ algebraMap ℚ Coef ((-1 : ℚ) ^ n) with hG
  have hgeom : (1 + PowerSeries.X) * G = 1 := by
    refine PowerSeries.ext fun n ↦ ?_
    rw [add_mul, one_mul, map_add]
    rcases n with _ | n
    · simp [hG]; rfl
    · rw [PowerSeries.coeff_succ_X_mul]
      simp only [hG, PowerSeries.coeff_mk, PowerSeries.coeff_one]
      rw [← map_add, if_neg (Nat.succ_ne_zero n), pow_succ]
      simp
  have hsub : g * G.subst (g - 1) = 1 := by
    have := congrArg (fun f : Ser ↦ f.subst (g - 1)) hgeom
    rw [PowerSeries.subst_mul hs, PowerSeries.subst_add hs, PowerSeries.subst_X hs] at this
    have h1 : (1 : Ser).subst (g - 1) = (1 : Ser) := by
      rw [← map_one (PowerSeries.C (R := Coef)), PowerSeries.subst_C]; rfl
    rwa [h1, add_sub_cancel] at this
  rw [logSer, PowerSeries.logOf_eq, PowerSeries.derivative_subst hs, PowerSeries.deriv_log, ← hG,
    map_sub, PowerSeries.derivative_one, sub_zero, ← mul_assoc, hsub, one_mul]

private theorem coeff_pow_eq_of_scongr (n : ℕ) (hn : 0 < n) (f g : Ser)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0)
    (h : SCongr (n - 1) f g) (d : ℕ) (hd : d ≠ 1) :
    PowerSeries.coeff n (f ^ d) = PowerSeries.coeff n (g ^ d) := by
  rcases d with _ | _ | k
  · simp [PowerSeries.coeff_one, hn.ne']
  · exact absurd rfl hd
  have htr : PowerSeries.trunc n f = PowerSeries.trunc n g := by
    refine Polynomial.ext fun m ↦ ?_
    simp only [PowerSeries.coeff_trunc]
    split_ifs with hm
    · exact h m (by omega)
    · rfl
  have hk : ∀ i, i ≤ n - 1 →
      PowerSeries.coeff i (f ^ (k + 1)) = PowerSeries.coeff i (g ^ (k + 1)) := by
    intro i hi
    have e : PowerSeries.trunc n (f ^ (k + 1)) = PowerSeries.trunc n (g ^ (k + 1)) := by
      rw [← PowerSeries.trunc_trunc_pow, htr, PowerSeries.trunc_trunc_pow]
    simpa only [PowerSeries.coeff_trunc, if_pos (show i < n by omega)] using
      congrArg (fun p ↦ Polynomial.coeff p i) e
  rw [pow_succ f, pow_succ g, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases hj : p.2 = 0
  · simp [hj, hf, hg]
  by_cases hi : p.1 = 0
  · simp [hi, hf, hg]
  rw [hk p.1 (by omega), h p.2 (by omega)]

/-- The `n`-th coefficient of `P ∘ f` (for `f(0) = 0`) only involves the powers `f^d`, `d ≤ n`. -/
theorem coeff_subst_eq_sum (n : ℕ) (P f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (P.subst f) =
      ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d P • PowerSeries.coeff n (f ^ d) := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hf)]
  refine finsum_eq_sum_of_support_subset _ fun d hd ↦ ?_
  simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hd ⊢
  by_contra hc
  refine hd ?_
  rw [PowerSeries.X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hf) d) n
    (by omega), smul_zero]

private theorem coeff_subst_sub (n : ℕ) (hn : 0 < n) (P f g : Ser)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0)
    (h : SCongr (n - 1) f g) :
    PowerSeries.coeff n (P.subst f) - PowerSeries.coeff n (P.subst g) =
      PowerSeries.coeff 1 P • (PowerSeries.coeff n f - PowerSeries.coeff n g) := by
  rw [coeff_subst_eq_sum n P f hf, coeff_subst_eq_sum n P g hg, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single 1]
  · rw [pow_one, pow_one, smul_sub]
  · intro d _ hd
    rw [coeff_pow_eq_of_scongr n hn f g hf hg h d hd, sub_self]
  · intro h1; simp at h1; omega

/-- If `f ≡ g` through degree `n - 1`, then the degree-`n` discrepancy of `exp f` and `exp g`
equals that of `f` and `g`. -/
theorem coeff_expSer_sub_of_scongr (n : ℕ) (hn : 0 < n) (f g : Ser)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0)
    (h : SCongr (n - 1) f g) :
    PowerSeries.coeff n (expSer f) - PowerSeries.coeff n (expSer g) =
      PowerSeries.coeff n f - PowerSeries.coeff n g := by
  rw [expSer, expSer, coeff_subst_sub n hn _ f g hf hg h, PowerSeries.coeff_exp]
  simp only [Nat.factorial_one, Nat.cast_one, div_one, map_one, one_smul]

/-- If `u ≡ v` through degree `n - 1`, then the degree-`n` discrepancy of `log u` and `log v`
equals that of `u` and `v`. -/
theorem coeff_logSer_sub_of_scongr (n : ℕ) (hn : 0 < n) (u v : Ser)
    (hu : PowerSeries.constantCoeff u = 1) (hv : PowerSeries.constantCoeff v = 1)
    (huv : SCongr (n - 1) u v) :
    PowerSeries.coeff n (logSer u) - PowerSeries.coeff n (logSer v) =
      PowerSeries.coeff n u - PowerSeries.coeff n v := by
  rw [logSer, logSer, PowerSeries.logOf_eq, PowerSeries.logOf_eq,
    coeff_subst_sub n hn _ _ _ (by simp [hu]) (by simp [hv]) (fun m hm ↦ by simp [huv m hm]),
    PowerSeries.coeff_one_log, one_smul]
  simp [PowerSeries.coeff_one, hn.ne']

/-! ### Patterns and multinomials -/

/-- A sum over the allowed tangent patterns of a state `s` whose summand depends only on the data
`(d, rt, rx)` and the off-boundary pattern, reindexed by `d ∈ [1, D]`, `rt, rx ≤ d` and the
off-boundary patterns of weight `d - rt - rx`. Here `D` bounds the divisor degree and `Q` is the
boundary condition on `(d, rt, rx)` in the description `hmem` of the allowed patterns. -/
theorem sum_allowedPatterns_reindex (s : State) (D : ℕ) (hD : D ≤ s.degree)
    (Q : ℕ → ℕ → ℕ → Prop) [∀ d rt rx, Decidable (Q d rt rx)]
    (hmem : ∀ P, P ∈ allowedPatterns s ↔ 0 < P.d.val ∧
      P.rt.val + P.rx.val + patternWeight P.other = P.d.val ∧ P.d.val ≤ D ∧
      Q P.d.val P.rt.val P.rx.val)
    (F : ℕ → ℕ → ℕ → Pattern s.degree → Coef) :
    ∑ P ∈ allowedPatterns s, F P.d.val P.rt.val P.rx.val P.other =
    ∑ d ∈ Finset.Icc 1 D, ∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1),
      (if Q d rt rx ∧ rt + rx ≤ d then
        ∑ m ∈ (Finset.univ : Finset (Pattern s.degree)).filter
          (fun m ↦ patternWeight m = d - rt - rx), F d rt rx m
      else 0) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun P ↦ P.d.val) (t := Finset.Icc 1 D)
    fun P hP ↦ by
      obtain ⟨h1, -, h3, -⟩ := (hmem P).1 hP
      simp only [Finset.mem_Icc]; omega]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [← Finset.sum_product', ← Finset.sum_fiberwise_of_maps_to (g := fun P ↦ (P.rt.val, P.rx.val))
    (t := Finset.range (d + 1) ×ˢ Finset.range (d + 1)) fun P hP ↦ by
      obtain ⟨hP', rfl⟩ := Finset.mem_filter.1 hP
      obtain ⟨-, h2, -⟩ := (hmem P).1 hP'
      simp only [Finset.mem_product, Finset.mem_range]; omega]
  refine Finset.sum_congr rfl fun ⟨rt, rx⟩ hr ↦ ?_
  simp only [Finset.mem_Icc, Finset.mem_product, Finset.mem_range] at hd hr
  simp only [Finset.filter_filter, Prod.mk.injEq]
  split_ifs with hcond
  · refine Finset.sum_bij' (fun P _ ↦ P.other)
      (fun m _ ↦ ⟨⟨d, by omega⟩, ⟨rt, by omega⟩, ⟨rx, by omega⟩, m⟩) ?_ ?_ ?_ ?_ ?_
    · intro P hP
      obtain ⟨hP', rfl, rfl, rfl⟩ := Finset.mem_filter.1 hP
      obtain ⟨-, h2, -⟩ := (hmem P).1 hP'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      exact Finset.mem_filter.2 ⟨(hmem _).2 ⟨by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega, hcond.1⟩, rfl, rfl, rfl⟩
    · rintro ⟨d', rt', rx', o⟩ hP
      obtain ⟨-, rfl, rfl, rfl⟩ := Finset.mem_filter.1 hP
      rfl
    · exact fun _ _ ↦ rfl
    · intro P hP
      obtain ⟨-, rfl, rfl, rfl⟩ := Finset.mem_filter.1 hP
      rfl
  · refine Finset.sum_eq_zero fun P hP ↦ (hcond ?_).elim
    obtain ⟨hP', rfl, rfl, rfl⟩ := Finset.mem_filter.1 hP
    obtain ⟨-, h2, -, h4⟩ := (hmem P).1 hP'
    exact ⟨h4, by omega⟩

/-- Reindexing the allowed patterns of the crossing state `T(a,b;c,h)` by their data
`(d, rt, rx)` and the off-boundary pattern of weight `d - rt - rx`. -/
theorem sum_allowedPatterns_crossing (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (F : ℕ → ℕ → ℕ → Pattern (State.crossing a b c h).degree → Coef) :
    ∑ P ∈ allowedPatterns (State.crossing a b c h), F P.d.val P.rt.val P.rx.val P.other =
    ∑ d ∈ Finset.Icc 1 (min c h), ∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1),
      (if ((0 < rt ↔ d < c) ∧ (0 < rx ↔ d < h) ∧ rt + rx ≤ d) then
        ∑ m ∈ (Finset.univ : Finset (Pattern (State.crossing a b c h).degree)).filter
          (fun m ↦ patternWeight m = d - rt - rx), F d rt rx m
      else 0) := by
  have hD : min c h ≤ (State.crossing a b c h).degree := by
    change min c h ≤ a * c + b * h
    have := min_le_left c h
    nlinarith
  rw [sum_allowedPatterns_reindex _ _ hD (fun d rt rx ↦ (0 < rt ↔ d < c) ∧ (0 < rx ↔ d < h))
    (fun P ↦ by simp [allowedPatterns, Allowed, and_assoc])]
  simp only [and_assoc]

/-- `q - 1 ≠ 0` in `ℚ(q)`. -/
private theorem X_sub_one_ne_zero : (RatFunc.X - 1 : RatFunc ℚ) ≠ 0 := by
  simpa using RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero (1 : ℚ))

/-- `(q-1) · w_j = (q-1)^j` for the crossing weight `w_0 = (q-1)⁻¹`, `w_j = (q-1)^{j-1}`. -/
theorem X_sub_one_mul_crossingWeight (j : ℕ) :
    (RatFunc.X - 1) * (if j = 0 then (RatFunc.X - 1 : RatFunc ℚ)⁻¹ else (RatFunc.X - 1) ^ (j - 1))
      = (RatFunc.X - 1) ^ j := by
  rcases j with _ | k
  · simp [X_sub_one_ne_zero]
  · simp [pow_succ, mul_comm]

private theorem pattern_entry_mul_le (N : ℕ) (m : Pattern N) (ij : Fin N × Fin N) :
    (ij.1.val + 1) * (ij.2.val + 1) * (m ij).val ≤ patternWeight m :=
  Finset.single_le_sum (f := fun ij : Fin N × Fin N ↦ (ij.1.val+1)*(ij.2.val+1)*(m ij).val)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ ij)

/-- Each entry of a pattern is bounded by its weight. -/
theorem pattern_entry_le_patternWeight (N : ℕ) (m : Pattern N) (ij : Fin N × Fin N) :
    (m ij).val ≤ patternWeight m :=
  le_trans (Nat.le_mul_of_pos_left _ (by positivity)) (pattern_entry_mul_le N m ij)

/-- An entry `m(i,j)` of a pattern of weight `< (i+1)(j+1)` vanishes. -/
theorem pattern_entry_eq_zero_of_lt (N : ℕ) (m : Pattern N) (ij : Fin N × Fin N)
    (h : patternWeight m < (ij.1.val + 1) * (ij.2.val + 1)) : (m ij).val = 0 := by
  have h1 := pattern_entry_mul_le N m ij
  by_contra hne
  have := Nat.le_mul_of_pos_right ((ij.1.val + 1) * (ij.2.val + 1)) (Nat.pos_of_ne_zero hne)
  omega

/-- Multinomial expansion of `(Σ_{r<n} b_{r+1} x^{m(r+1)})^k`. -/
theorem sum_C_mul_X_pow_pow (m n k : ℕ) (b : ℕ → Coef) :
    (∑ r : Fin n, PowerSeries.C (b (r.val + 1)) * (PowerSeries.X : Ser) ^ (m * (r.val + 1))) ^ k =
    ∑ κ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k,
      PowerSeries.C ((Nat.multinomial Finset.univ κ : Coef) * ∏ r : Fin n, b (r.val + 1) ^ κ r) *
        (PowerSeries.X : Ser) ^ (m * ∑ r : Fin n, (r.val + 1) * κ r) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  rw [Finset.prod_congr rfl (fun r _ ↦ mul_pow _ _ _), Finset.prod_mul_distrib]
  have h2 : ∏ r : Fin n, ((PowerSeries.X : Ser) ^ (m * (r.val + 1))) ^ κ r
      = (PowerSeries.X : Ser) ^ (m * ∑ r : Fin n, (r.val + 1) * κ r) := by
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun r _ ↦ by rw [← pow_mul, mul_assoc]
  rw [h2]
  simp only [map_mul, map_natCast, map_prod, map_pow]
  ring

/-! ### The representation `qact` and the Gauss twist -/

/-- If `U ≡ V` through total degree `n`, then `ρ(U) f ≡ ρ(V) f` through degree `n`. -/
theorem QCongr.qact_scongr {n : ℕ} {U V : QSer} (hUV : QCongr n U V) (f : Ser) :
    SCongr n (qact U f) (qact V f) := fun m hm ↦ by
  simp only [qact, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun r hr ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hr
  rw [hUV r.1 r.2 (by omega)]

/-- Coefficients of `ρ(U)(Φ f)` as a double sum over the total degree `d` and the first contact
index `r`. -/
theorem coeff_qact_gaussPhi (U : QSer) (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (qact U (gaussPhi f)) = ∑ d ∈ Finset.range (n + 1),
      ∑ r ∈ Finset.range (d + 1),
        qpow (-(tri d : ℤ)) * (U r (n - d) * PowerSeries.coeff (d - r) f) := by
  simp only [qact, gaussPhi, PowerSeries.coeff_mk, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have key : ∀ i r : ℕ, qpow (-(tri r : ℤ) - (r : ℤ) * ((n - i : ℕ) : ℤ)) *
      (U r (i - r) * (qpow (-(tri (n - i) : ℤ)) * PowerSeries.coeff (n - i) f)) =
      qpow (-(tri (r + (n - i)) : ℤ)) * (U r (i - r) * PowerSeries.coeff (n - i) f) := by
    intro i r
    rw [tri_add, mul_left_comm (U r (i - r)), ← mul_assoc, ← qpow_add]
    congr 2; ring
  simp only [key]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ ↦ ⟨x.2 + (n - x.1), x.2⟩) (fun x _ ↦ ⟨n - (x.1 - x.2), x.2⟩)
    ?_ ?_ ?_ ?_ ?_
  all_goals rintro ⟨i, r⟩ h; simp only [Finset.mem_sigma, Finset.mem_range] at h
  · simp only [Finset.mem_sigma, Finset.mem_range]; omega
  · simp only [Finset.mem_sigma, Finset.mem_range]; omega
  · simp only [Sigma.mk.injEq, heq_eq_eq, and_true]; omega
  · simp only [Sigma.mk.injEq, heq_eq_eq, and_true]; omega
  · dsimp only
    rw [show n - (r + (n - i)) = i - r by omega, show r + (n - i) - r = n - i by omega]

/-- Leading term: if `f` vanishes below degree `n` and `U₀₀ = 1`, then
`[xⁿ] ρ(U)(Φ f) = q^{-tri n} [xⁿ] f`. -/
theorem coeff_qact_gaussPhi_of_lt (U : QSer) (hU0 : U 0 0 = 1) (f : Ser) (n : ℕ)
    (hf : ∀ m : ℕ, m < n → PowerSeries.coeff m f = 0) :
    PowerSeries.coeff n (qact U (gaussPhi f)) = qpow (-(tri n : ℤ)) * PowerSeries.coeff n f := by
  rw [qact, gaussPhi, PowerSeries.coeff_mk, Finset.sum_eq_single (0, n)]
  · simp [PowerSeries.coeff_mk, show tri 0 = 0 from rfl, hU0, qpow_zero]
  · rintro ⟨a, b⟩ hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have : b < n := by
      by_contra h
      exact hne (Prod.ext (by simp; omega) (by simp; omega))
    exact Finset.sum_eq_zero fun r _ ↦ by simp [PowerSeries.coeff_mk, hf _ this]
  · simp

/-- `ρ` is multiplicative: `ρ(U V) = ρ(U) ∘ ρ(V)`. -/
theorem qact_qmul (U V : QSer) (f : Ser) : qact (qmul U V) f = qact U (qact V f) := by
  refine PowerSeries.ext fun n ↦ ?_
  simp only [qact, qmul, PowerSeries.coeff_mk, Finset.mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x ↦ ⟨(x.2.2.1.1 + x.2.2.2.1, x.2.2.1.2 + x.2.2.2.2 + x.1.2), (x.2.2.1.1, x.2.2.2.1),
      (x.2.2.1.2 + x.2.2.2.2, x.1.2), (x.2.2.1.2, x.2.2.2.2)⟩)
    (fun y ↦ ⟨(y.2.1.1 + y.2.1.2 + y.2.2.2.1 + y.2.2.2.2, y.2.2.1.2),
      (y.2.1.1 + y.2.2.2.1, y.2.1.2 + y.2.2.2.2), (y.2.1.1, y.2.2.2.1), (y.2.1.2, y.2.2.2.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  all_goals rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, g⟩, ⟨h, k⟩⟩ hx
  all_goals simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal,
    Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, and_true, true_and] at hx ⊢
  · omega
  · omega
  · omega
  · omega
  · obtain ⟨h1, rfl, rfl, rfl⟩ := hx
    have key : qpow (-((tri (e + g) : ℕ) : ℤ) - ((e + g : ℕ) : ℤ) * (b : ℤ)) *
        qpow (-((e : ℤ) * (k : ℤ))) = qpow (-(tri e : ℤ) - (e : ℤ) * ((g + k + b : ℕ) : ℤ)) *
          qpow (-(tri g : ℤ) - (g : ℤ) * (b : ℤ)) := by
      rw [← qpow_add, ← qpow_add, tri_add]
      congr 1
      push_cast
      ring
    linear_combination (U e h * V g k * PowerSeries.coeff b f) * key

/-- `ρ(1) = id`. -/
theorem qact_qone (f : Ser) : qact qone f = f := by
  ext n
  simp only [qact, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single (0, n)]
  · simp [qone, tri, qpow_zero]
  · rintro ⟨a, b⟩ hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have ha : a ≠ 0 := fun h ↦ hne (Prod.ext h (by simp at hp ⊢; omega))
    refine Finset.sum_eq_zero fun r hr ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hr
    have : ¬ (r.1 = 0 ∧ r.2 = 0) := by omega
    simp [qone, this]
  · simp

/-- `ρ(U)` is additive on differences. -/
theorem qact_sub (U : QSer) (f g : Ser) : qact U (f - g) = qact U f - qact U g := by
  ext n
  simp [qact, mul_sub, Finset.sum_sub_distrib]

/-! ### The twisted product -/

/-- Congruence of contact series through degree `j` implies congruence through any `i ≤ j`. -/
theorem QCongr.mono {i j : ℕ} {U V : QSer} (h : QCongr j U V) (hij : i ≤ j) : QCongr i U V :=
  fun c k hck ↦ h c k (hck.trans hij)

/-- Congruence of contact series is transitive. -/
theorem QCongr.trans {j : ℕ} {U V W : QSer} (h : QCongr j U V) (h' : QCongr j V W) :
    QCongr j U W :=
  fun c k hck ↦ (h c k hck).trans (h' c k hck)

/-- Congruence of contact series is compatible with the twisted product. -/
theorem QCongr.qmul {j : ℕ} {U U' V V' : QSer} (hU : QCongr j U U') (hV : QCongr j V V') :
    QCongr j (qmul U V) (qmul U' V') := fun c h hch ↦ by
  refine Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun r hr ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hr
  rw [hU p.1 r.1 (by omega), hV p.2 r.2 (by omega)]

/-- Diagonal substitution doubles the congruence degree: `f ≡ g` through `M` gives
`qdiag f ≡ qdiag g` through `2M + 1`. -/
theorem SCongr.qdiag {M : ℕ} {f g : Ser} (h : SCongr M f g) :
    QCongr (2 * M + 1) (qdiag f) (qdiag g) := by
  intro c k hck
  unfold SurfaceBlowup.qdiag
  split_ifs with e
  · subst e; rw [h c (by omega)]
  · rfl

private theorem antidiagonal_shift_sum {c k : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ Finset.HasAntidiagonal.antidiagonal c) (G : ℕ × ℕ → Coef) (hck : c ≤ k) :
    ∑ r ∈ Finset.HasAntidiagonal.antidiagonal k,
      (if p.1 ≤ r.1 ∧ p.2 ≤ r.2 then G (r.1 - p.1, r.2 - p.2) else 0) =
        ∑ r ∈ Finset.HasAntidiagonal.antidiagonal (k - c), G r := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun r ↦ (r.1 - p.1, r.2 - p.2)) (fun s ↦ (s.1 + p.1, s.2 + p.2))
  all_goals intro r hr
  all_goals simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hr ⊢
  · omega
  · omega
  · ext <;> simp <;> omega
  · ext <;> simp

private theorem antidiagonal_shift_sum_eq_zero {c k : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ Finset.HasAntidiagonal.antidiagonal c) (G : ℕ × ℕ → Coef) (hkc : k < c) :
    ∑ r ∈ Finset.HasAntidiagonal.antidiagonal k,
      (if p.1 ≤ r.1 ∧ p.2 ≤ r.2 then G (r.1 - p.1, r.2 - p.2) else 0) = 0 := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  refine Finset.sum_eq_zero fun r hr ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hr
  rw [if_neg]
  omega

/-- `ι₊` is multiplicative for the twisted product. -/
theorem qplus_qmul (U V : QSer) : qplus (qmul U V) = qmul (qplus U) (qplus V) := by
  funext c k
  simp only [qplus, qmul]
  set G : ℕ × ℕ → ℕ × ℕ → Coef := fun p s ↦ qpow (-((p.1 : ℤ) * ((s.2 + p.2 : ℕ) : ℤ))) *
    ((qpow (-(chooseTwo p.1 : ℤ)) * U p.1 s.1) * (qpow (-(chooseTwo p.2 : ℤ)) * V p.2 s.2)) with hG
  have key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal c,
      (∑ r ∈ Finset.HasAntidiagonal.antidiagonal k, qpow (-((p.1 : ℤ) * (r.2 : ℤ))) *
        ((if p.1 ≤ r.1 then qpow (-(chooseTwo p.1 : ℤ)) * U p.1 (r.1 - p.1) else 0) *
         (if p.2 ≤ r.2 then qpow (-(chooseTwo p.2 : ℤ)) * V p.2 (r.2 - p.2) else 0))) =
      ∑ r ∈ Finset.HasAntidiagonal.antidiagonal k,
        (if p.1 ≤ r.1 ∧ p.2 ≤ r.2 then G p (r.1 - p.1, r.2 - p.2) else 0) := by
    intro p _
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    by_cases h1 : p.1 ≤ r.1 <;> by_cases h2 : p.2 ≤ r.2 <;> simp [hG, h1, h2]
  rw [Finset.sum_congr rfl key]
  split_ifs with hck
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [antidiagonal_shift_sum hp (G p) hck, Finset.mul_sum]
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    subst hp
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have e2 : qpow (-(((chooseTwo (p.1 + p.2) : ℕ) : ℤ))) * qpow (-((p.1 : ℤ) * (s.2 : ℤ))) =
        qpow (-((p.1 : ℤ) * ((s.2 + p.2 : ℕ) : ℤ))) *
          (qpow (-(chooseTwo p.1 : ℤ)) * qpow (-(chooseTwo p.2 : ℤ))) := by
      rw [← qpow_add, ← qpow_add, ← qpow_add, chooseTwo_add]
      push_cast; ring_nf
    calc _ = (qpow (-(((chooseTwo (p.1 + p.2) : ℕ) : ℤ))) * qpow (-((p.1 : ℤ) * (s.2 : ℤ)))) *
          (U p.1 s.1 * V p.2 s.2) := by ring
      _ = _ := by rw [e2, hG]; ring
  · exact (Finset.sum_eq_zero fun p hp ↦ antidiagonal_shift_sum_eq_zero hp (G p) (by omega)).symm

/-- Transpose of a contact series. -/
private def qtranspose (U : QSer) : QSer := fun c h ↦ U h c

private theorem qminus_eq_transpose (U : QSer) :
    qminus U = qtranspose (qplus (qtranspose U)) := rfl

private theorem qtranspose_qmul (U V : QSer) :
    qtranspose (qmul U V) = qmul (qtranspose V) (qtranspose U) := by
  funext c h
  simp only [qtranspose, qmul]
  rw [Finset.sum_comm, ← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [mul_comm (U _ _), mul_comm (r.1 : ℤ)]

/-- `ι₋` is multiplicative for the twisted product. -/
theorem qminus_qmul (U V : QSer) : qminus (qmul U V) = qmul (qminus U) (qminus V) := by
  simp only [qminus_eq_transpose, qtranspose_qmul, qplus_qmul]

/-- `E_{0,0}` is a left unit for the twisted product. -/
theorem qone_qmul (U : QSer) : qmul qone U = U := by
  funext c h
  simp only [qmul, qone]
  rw [Finset.sum_eq_single (0, c), Finset.sum_eq_single (0, h)]
  · simp [qpow_zero]
  · intro r hr hne
    have : r.1 ≠ 0 := fun h2 ↦ hne (Prod.ext h2
      (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hr; simp_all))
    simp [this]
  · simp
  · intro p hp hne
    have : p.1 ≠ 0 := fun h2 ↦ hne (Prod.ext h2
      (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; simp_all))
    exact Finset.sum_eq_zero fun r _ ↦ by simp [this]
  · simp

private theorem qmul_eq_sum_range (U V : QSer) (c h : ℕ) :
    qmul U V c h = ∑ a ∈ Finset.range (c + 1), ∑ b ∈ Finset.range (h + 1),
      qpow (-((a : ℤ) * ((h - b : ℕ) : ℤ))) * (U a b * V (c - a) (h - b)) := by
  simp only [qmul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem sum_range_eq_sum_range_ite {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a N : ℕ)
    (haN : a ≤ N) :
    ∑ x ∈ Finset.range (a + 1), f x = ∑ x ∈ Finset.range (N + 1), if x ≤ a then f x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- The summand of the quadruple sum computing `(ι₊(A) · qdiag(D) · ι₋(C))_{c,h}`: the outer
product is split at `(a, b)` and the inner one at `(a', b')`. -/
private def qtripleTerm (A Cq : QSer) (D : Ser) (c h a b a' b' : ℕ) : Coef :=
  if a' ≤ a ∧ b' ≤ b then
    qpow (-((a : ℤ) * ((h - b : ℕ) : ℤ))) *
      ((qpow (-((a' : ℤ) * ((b - b' : ℕ) : ℤ))) * (qplus A a' b' * qdiag D (a - a') (b - b'))) *
        qminus Cq (c - a) (h - b))
  else 0

/-- The coefficient `(ι₊(A) · qdiag(D) · ι₋(C))_{c,h}` as an unrestricted quadruple sum over
the box `[0, c] × [0, h] × [0, c] × [0, h]`. -/
private theorem qmul_qplus_qdiag_qminus_eq_sum (A Cq : QSer) (D : Ser) (c h : ℕ) :
    qmul (qmul (qplus A) (qdiag D)) (qminus Cq) c h =
      ∑ x ∈ (Finset.range (c + 1) ×ˢ Finset.range (h + 1)) ×ˢ
        (Finset.range (c + 1) ×ˢ Finset.range (h + 1)),
        qtripleTerm A Cq D c h x.1.1 x.1.2 x.2.1 x.2.2 := by
  rw [qmul_eq_sum_range, Finset.sum_product, Finset.sum_product]
  refine Finset.sum_congr rfl fun a ha ↦ Finset.sum_congr rfl fun b hb ↦ ?_
  simp only [Finset.mem_range] at ha hb
  rw [Finset.sum_product, qmul_eq_sum_range, sum_range_eq_sum_range_ite _ a c (by omega),
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ ↦ ?_
  split_ifs with h1
  · rw [sum_range_eq_sum_range_ite _ b h (by omega), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ ↦ ?_
    simp only [qtripleTerm]
    split_ifs with h2 h3 <;> first | (exfalso; omega) | simp
  · simp [qtripleTerm, h1]

/-- The quadruple-sum summand at the splitting determined by `(rx, m, rt)`, in closed form. -/
private theorem qtripleTerm_eq (A Cq : QSer) (D : Ser) {c h rx m rt : ℕ}
    (hc1 : rx + m + rt ≤ c) (hc2 : rx + m + rt ≤ h) :
    qtripleTerm A Cq D c h (rx + m) (h - rt) rx (h - rt - m) =
      qpow (-(chooseTwo rx : ℤ) - (chooseTwo m : ℤ) - (chooseTwo rt : ℤ) - (rx : ℤ) * (m : ℤ) -
          ((rx : ℤ) + (m : ℤ)) * (rt : ℤ)) *
        (A rx (h - (rx + m + rt)) * (PowerSeries.coeff m D * Cq (c - (rx + m + rt)) rt)) := by
  simp only [qtripleTerm, qplus, qdiag, qminus]
  rw [if_pos (by omega : rx ≤ rx + m ∧ h - rt - m ≤ h - rt),
    show rx + m - rx = m by omega, show h - rt - (h - rt - m) = m by omega,
    show h - (h - rt) = rt by omega, if_pos (show rx ≤ h - rt - m by omega), if_pos rfl,
    if_pos (show rt ≤ c - (rx + m) by omega), show h - rt - m - rx = h - (rx + m + rt) by omega,
    show c - (rx + m) - rt = c - (rx + m + rt) by omega]
  have hq : qpow (-(chooseTwo rx : ℤ) - (chooseTwo m : ℤ) - (chooseTwo rt : ℤ) -
      (rx : ℤ) * (m : ℤ) - ((rx : ℤ) + (m : ℤ)) * (rt : ℤ)) =
      qpow (-(((rx + m : ℕ) : ℤ) * (rt : ℤ))) * qpow (-((rx : ℤ) * (m : ℤ))) *
        qpow (-(chooseTwo rx : ℤ)) * qpow (-(chooseTwo m : ℤ)) * qpow (-(chooseTwo rt : ℤ)) := by
    rw [← qpow_add, ← qpow_add, ← qpow_add, ← qpow_add]
    congr 1
    push_cast
    ring
  rw [hq]; ring

/-- Expansion of the coefficient `(ι₊(A) · qdiag(D) · ι₋(C))_{c,h}` as a triple sum. -/
theorem qmul_qplus_qdiag_qminus_apply (A Cq : QSer) (D : Ser) (c h : ℕ) :
    qmul (qmul (qplus A) (qdiag D)) (qminus Cq) c h =
      ∑ rx ∈ Finset.range (c + 1), ∑ m ∈ Finset.range (c + 1), ∑ rt ∈ Finset.range (c + 1),
        (if (rx + m + rt ≤ c ∧ rx + m + rt ≤ h) then
          qpow (-(chooseTwo rx : ℤ) - (chooseTwo m : ℤ) - (chooseTwo rt : ℤ) - (rx : ℤ) * (m : ℤ) -
            ((rx : ℤ) + (m : ℤ)) * (rt : ℤ)) *
            (A rx (h - (rx + m + rt)) * (PowerSeries.coeff m D * Cq (c - (rx + m + rt)) rt))
        else 0) := by
  -- Reindex the quadruple sum of `qmul_qplus_qdiag_qminus_eq_sum` by its nonzero terms,
  -- which are exactly the splittings `(rx + m, h - rt, rx, h - rt - m)`.
  set G := qtripleTerm A Cq D c h with hG
  set T : ℕ → ℕ → ℕ → Coef := fun rx m rt ↦
    (if (rx + m + rt ≤ c ∧ rx + m + rt ≤ h) then
      qpow (-(chooseTwo rx : ℤ) - (chooseTwo m : ℤ) - (chooseTwo rt : ℤ) - (rx : ℤ) * (m : ℤ) -
        ((rx : ℤ) + (m : ℤ)) * (rt : ℤ)) *
        (A rx (h - (rx + m + rt)) * (PowerSeries.coeff m D * Cq (c - (rx + m + rt)) rt))
    else 0) with hT
  have hval : ∀ rx m rt : ℕ, rx + m + rt ≤ c → rx + m + rt ≤ h →
      T rx m rt = G (rx + m) (h - rt) rx (h - rt - m) := fun rx m rt hc1 hc2 ↦ by
    rw [hT, hG, qtripleTerm_eq A Cq D hc1 hc2]; exact if_pos ⟨hc1, hc2⟩
  have hT0 : ∀ x : ℕ × ℕ × ℕ, T x.1 x.2.1 x.2.2 ≠ 0 →
      x.1 + x.2.1 + x.2.2 ≤ c ∧ x.1 + x.2.1 + x.2.2 ≤ h := fun x hne ↦ by
    by_contra hc; exact hne (by simp only [hT]; rw [if_neg hc])
  have hR : ∑ rx ∈ Finset.range (c + 1), ∑ m ∈ Finset.range (c + 1), ∑ rt ∈ Finset.range (c + 1),
      T rx m rt = ∑ x ∈ Finset.range (c + 1) ×ˢ (Finset.range (c + 1) ×ˢ Finset.range (c + 1)),
        T x.1 x.2.1 x.2.2 := by
    simp only [Finset.sum_product]
  rw [qmul_qplus_qdiag_qminus_eq_sum, ← hG, hR]
  symm
  refine Finset.sum_bij_ne_zero
    (fun x _ _ ↦ ((x.1 + x.2.1, h - x.2.2), (x.1, h - x.2.2 - x.2.1))) ?_ ?_ ?_ ?_
  · intro x hx hne
    have := hT0 x hne
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  · rintro ⟨x1, x2, x3⟩ _ hx ⟨y1, y2, y3⟩ _ hy hxy
    have := hT0 _ hx
    have := hT0 _ hy
    simp only [Prod.mk.injEq] at *
    omega
  · rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ hmem hne
    simp only [Finset.mem_product, Finset.mem_range] at hmem
    have key : a' ≤ a ∧ b' ≤ b ∧ a' ≤ b' ∧ a - a' = b - b' ∧ h - b ≤ c - a := by
      by_contra hc
      apply hne
      simp only [hG, qtripleTerm, qplus, qdiag, qminus]
      split_ifs <;> first | (exfalso; omega) | simp
    refine ⟨(a', a - a', h - b), ?_, ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      omega
    · dsimp only
      rw [hval _ _ _ (by omega) (by omega), show a' + (a - a') = a by omega,
        show h - (h - b) = b by omega, show b - (a - a') = b' by omega]
      exact hne
    · dsimp only
      rw [show a' + (a - a') = a by omega, show h - (h - b) = b by omega,
        show b - (a - a') = b' by omega]
  · intro x _ hx
    exact hval _ _ _ (hT0 x hx).1 (hT0 x hx).2

/-- If `U` is positive and agrees with `1` through degree `j - 1`, then `ι₊ U` agrees with `1`
through degree `j`. -/
theorem qcongr_qplus_qone (j : ℕ) (U : QSer) (hU : QPositive U) (h : QCongr (j - 1) U qone) :
    QCongr j (qplus U) qone := by
  intro c k hck
  simp only [qplus, qone]
  split_ifs with hc h1 h1
  · obtain ⟨rfl, rfl⟩ := h1
    simpa [chooseTwo, qpow_zero, qone] using h 0 0 (by omega)
  · rcases Nat.eq_zero_or_pos c with rfl | c0
    · rw [Nat.sub_zero, hU 0 k (Or.inl rfl) (by omega), mul_zero]
    · rw [h c (k - c) (by omega), qone, if_neg (by omega), mul_zero]
  · omega
  · rfl

private theorem qtranspose_qcongr_qone {j : ℕ} {U : QSer} (h : QCongr j U qone) :
    QCongr j (qtranspose U) qone := fun c k hck ↦ by
  simpa [qtranspose, qone, and_comm] using h k c (by omega)

/-- If `U` is positive and agrees with `1` through degree `j - 1`, then `ι₋ U` agrees with `1`
through degree `j`. -/
theorem qcongr_qminus_qone (j : ℕ) (U : QSer) (hU : QPositive U) (h : QCongr (j - 1) U qone) :
    QCongr j (qminus U) qone := by
  rw [qminus_eq_transpose]
  exact qtranspose_qcongr_qone (qcongr_qplus_qone j _
    (fun c k h1 h2 ↦ hU k c h1.symm (by tauto)) (qtranspose_qcongr_qone h))

end SurfaceBlowup
