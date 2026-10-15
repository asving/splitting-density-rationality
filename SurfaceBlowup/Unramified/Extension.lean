/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Measure.HenselProducts

/-!
# Binary forms, factor cells and unramified extensions

Basic definitions for the factorization-type analysis: binary forms and their products, the
residue, projective and normalized factor cells, the unramified extension `O_δ = O[X]/(Φ)` with
its Frobenius, and the Frobenius descent maps. Alongside, the algebraic toolkit used throughout:
adic completeness under change of ideal and for finite free modules, lifting idempotents,
locality criteria, coordinates of `m_O O_δ`, coprimality via residues, Hensel uniqueness for
families of factors, partial fractions for coprime binary forms, and descent of Frobenius orbits
of irreducible factors.

## Main results

* `SurfaceBlowup.base_ideal_coordinates`, `SurfaceBlowup.base_ideal_pure`
* `SurfaceBlowup.finite_free_adic_complete`, `SurfaceBlowup.complete_domain_finite_quotient_local`
* `SurfaceBlowup.coprime_of_coprime_residue_dvr`, `SurfaceBlowup.hensel_family_unique`
* `SurfaceBlowup.form_product_maps_to_and_preserves`, `SurfaceBlowup.forms_linear_bijective`
* `SurfaceBlowup.invariant_orbit_factors`

Provenance: `Def_SurfaceBlowupV2_{BinaryForms, FactorCells, ProjectiveCells, HomogeneousCells,
UnramifiedExtension, FrobeniusDescent}`; `Thm_SurfaceBlowupV2_{adic_complete_iff_of_pow_le,
adic_idempotent_lift, base_ideal_coordinates, base_ideal_pure,
conjugate_irreducible_factors_distinct, coprime_family_linear_injective,
coprime_of_coprime_residue_dvr, distinct_monic_irreducible_coprime,
dvr_extension_maximalIdeal_map_eq_pow, dvr_maximalIdeal_pow_injective, eval_at_pow_card,
factor_product_continuous, finite_field_frobenius_fixed_points, finite_free_adic_complete,
finite_free_residue_quotient, finite_monoid_idempotent_power, finite_ring_local_of_idempotents,
complete_domain_finite_quotient_local, form_product_maps_to_and_preserves, forms_linear_injective,
forms_linear_bijective, hensel_factor_unique_of_dvd, hensel_family_unique, invariant_orbit_factors,
local_algEquiv_maximalIdeal}`.
-/

noncomputable section

namespace SurfaceBlowup

open Polynomial IsLocalRing MeasureTheory

/-! ### Binary forms -/

section
variable {A : Type} [CommRing A]
/-- The dehomogenized polynomial `∑ a_i X^i` of a degree-`n` binary form with coefficient vector
`a` (the form is `∑ a_i X^i Y^(n-i)`; the multiplicity of its zero at infinity is `n − deg`). -/
def formPoly {n : ℕ} (a : Fin (n + 1) → A) : Polynomial A :=
  ∑ i : Fin (n+1), C (a i) * X ^ (i : ℕ)
/-- Product of a finite family of binary forms of degrees `d i`, as a form of degree `∑ d i`. -/
def formProd {ι : Type} [Fintype ι] (d : ι → ℕ) (a : ∀ i, Fin (d i + 1) → A) :
    Fin ((∑ i, d i) + 1) → A :=
  fun j => (∏ i, formPoly (a i)).coeff j
/-- Pairwise coprimality of a family of binary forms over a field: the dehomogenized polynomials
are pairwise coprime (no common affine zero) and at most one form vanishes at infinity (has
dehomogenized degree below its form degree). -/
def FormsCoprime {ι : Type} [Fintype ι] (d : ι → ℕ) (g : ∀ i, Fin (d i + 1) → A) : Prop :=
  (∀ i j, i ≠ j → IsCoprime (formPoly (g i)) (formPoly (g j))) ∧
    ∀ i j, i ≠ j → (formPoly (g i)).natDegree = d i ∨ (formPoly (g j)).natDegree = d j
end

/-! ### Factor cells -/

section
variable {O : Type} [CommRing O]
/-- The integral monic polynomial `X^n + ∑ a_i X^i` attached to a coefficient vector. -/
def monicPolyO {n : ℕ} (a : Fin n → O) : Polynomial O :=
  X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)
/-- The first `n` coefficients of a polynomial, as a coefficient vector. -/
def coeffVec (n : ℕ) (F : Polynomial O) : Fin n → O := fun i => F.coeff i
/-- Coefficient vector of the product of the monic polynomials attached to a family of vectors. -/
def factorProduct {ι : Type} [Fintype ι] (d : ι → ℕ) (a : ∀ i, Fin (d i) → O) :
    Fin (∑ i, d i) → O :=
  coeffVec (∑ i, d i) (∏ i, monicPolyO (a i))
end
/-- The integral monic polynomial maps to the fraction-field monic polynomial `monicPolynomial`. -/
theorem monicPolyO_map_fraction (O : Type) [CommRing O] [IsDomain O] {n : ℕ} (a : Fin n → O) :
    (monicPolyO a).map (algebraMap O (BaseField O)) = monicPolynomial O a := by
  simp [monicPolyO, monicPolynomial, Polynomial.map_sum]
section
variable (O : Type) [CommRing O] [IsLocalRing O]
/-- The residue cell: coefficient vectors whose monic polynomial reduces to `G`. -/
def residueCell (n : ℕ) (G : Polynomial (ResidueField O)) : Set (Fin n → O) :=
  {a | (monicPolyO a).map (residue O) = G}
end
section
variable (O : Type) [CommRing O] [IsDomain O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [SecondCountableTopology O]
  [MeasurableSpace O] [BorelSpace O]
/-- The normalized coefficient measure of a cell: restriction of `coefficientMeasure` to `S`,
divided by the mass of `S` (junk when the mass is `0` or `∞`; probability otherwise). -/
noncomputable def cellMeasure (n : ℕ) (S : Set (Fin n → O)) : Measure (Fin n → O) :=
  (coefficientMeasure O n S)⁻¹ • (coefficientMeasure O n).restrict S
end

/-! ### Projective cells -/

section
variable {k : Type} [CommRing k]
/-- The nonzero scalar multiples of a coefficient vector. -/
def scalarClass {n : ℕ} (v : Fin (n + 1) → k) : Set (Fin (n+1) → k) :=
  {w | ∃ c : k, c ≠ 0 ∧ w = c • v}
end
section
variable (O : Type) [CommRing O] [IsLocalRing O]
/-- Coordinatewise reduction of a binary coefficient vector to the residue field. -/
def residueVector {n : ℕ} (a : Fin (n + 1) → O) : Fin (n+1) → ResidueField O :=
  fun i => residue O (a i)
/-- The projective residue cell of `v`: primitive vectors whose reduction is a nonzero scalar
multiple of `v`. -/
def projectiveCell (n : ℕ) (v : Fin (n + 1) → ResidueField O) : Set (Fin (n+1) → O) :=
  {a | primitive O a ∧ residueVector O a ∈ scalarClass v}
end

/-! ### Normalized (homogeneous) cells -/

section
variable {A : Type} [CommRing A]
/-- Insert the value `1` at coordinate `ν`: the form with normalized `ν`-coefficient and free
coefficients `b`. -/
def insertOne {d : ℕ} (ν : Fin (d + 1)) (b : Fin d → A) : Fin (d+1) → A := Fin.insertNth ν 1 b
/-- Forget coordinate `μ`. -/
def dropCoord {d : ℕ} (μ : Fin (d + 1)) (a : Fin (d + 1) → A) : Fin d → A := Fin.removeNth μ a
/-- Scale a form by the inverse of its `μ`-coordinate (`Ring.inverse`: junk `0` if that coordinate
is not a unit). -/
def normalizeAt {d : ℕ} (μ : Fin (d + 1)) (a : Fin (d + 1) → A) : Fin (d+1) → A :=
  Ring.inverse (a μ) • a
end
section
variable (O : Type) [CommRing O] [IsLocalRing O]
/-- Normalized factor cell: forms with `ν`-coordinate `1` reducing to the residue form `g` (so
`g ν = 1` if nonempty). -/
def normalizedFormCell (d : ℕ) (ν : Fin (d + 1)) (g : Fin (d + 1) → ResidueField O) :
    Set (Fin (d+1) → O) :=
  {a | a ν = 1 ∧ residueVector O a = g}
/-- The same cell in the `d` free coordinates. -/
def reducedFormCell (d : ℕ) (ν : Fin (d + 1)) (g : Fin (d + 1) → ResidueField O) :
    Set (Fin d → O) :=
  {b | insertOne ν b ∈ normalizedFormCell O d ν g}
open scoped Classical in
/-- The normalized product map in reduced coordinates: multiply the normalized factors, divide by
the `μ`-coordinate of the product, forget coordinate `μ`. Guarded by membership in the product of
the factor cells (junk `0` outside), so that measurability needs no continuity of inversion. -/
def reducedFormProduct {ι : Type} [Fintype ι] (d : ι → ℕ) (ν : ∀ i, Fin (d i + 1))
    (g : ∀ i, Fin (d i + 1) → ResidueField O) (μ : Fin ((∑ i, d i) + 1))
    (a : ∀ i, Fin (d i) → O) : Fin (∑ i, d i) → O :=
  if ∀ i, a i ∈ reducedFormCell O (d i) (ν i) (g i) then
    dropCoord μ (normalizeAt μ (formProd d (fun i => insertOne (ν i) (a i)))) else 0
open scoped Classical in
/-- Normalization of a primitive form in the projective chart `μ`, in reduced coordinates (junk `0`
off the projective residue cell of `G`). -/
def projectiveNormalize (n : ℕ) (G : Fin (n + 1) → ResidueField O) (μ : Fin (n + 1))
    (a : Fin (n + 1) → O) : Fin n → O :=
  if a ∈ projectiveCell O n G then dropCoord μ (normalizeAt μ a) else 0
end

/-! ### The unramified extension and its Frobenius -/

section
variable (O : Type) [CommRing O] [IsLocalRing O]
/-- Number of elements of the residue field of `O` (written q throughout). -/
abbrev residueCard : ℕ := Nat.card (ResidueField O)
/-- Reduction of an integral polynomial to the residue field. -/
abbrev residuePoly (Φ : Polynomial O) : Polynomial (ResidueField O) := Φ.map (residue O)
/-- `Φ` is a monic polynomial over `O` whose reduction is irreducible over the residue field. -/
def IsUnramifiedLift (Φ : Polynomial O) : Prop := Φ.Monic ∧ Irreducible (residuePoly O Φ)
/-- The ideal `m_O · O_δ` generated by the maximal ideal of the base, in `O_δ := O[X]/(Φ)`. -/
def baseIdeal (Φ : Polynomial O) : Ideal (AdjoinRoot Φ) := (maximalIdeal O).map (AdjoinRoot.of Φ)
/-- The residue extension `k_δ := O_δ / m_O O_δ`. -/
abbrev residueExtension (Φ : Polynomial O) : Type := AdjoinRoot Φ ⧸ baseIdeal O Φ
/-- Reduction of `O_δ` to its residue extension. -/
abbrev baseReduce (Φ : Polynomial O) : AdjoinRoot Φ →+* residueExtension O Φ :=
  Ideal.Quotient.mk (baseIdeal O Φ)
open scoped Classical in
/-- The Frobenius root: the root of `Φ` in `O_δ` congruent to `θ^q` modulo `m_O O_δ` when such a
root exists, and `θ` itself otherwise. Existence and uniqueness are theorems, not part of the
data. -/
noncomputable def frobeniusRoot (Φ : Polynomial O) : AdjoinRoot Φ :=
  if h : ∃ a : AdjoinRoot Φ, (Φ.map (AdjoinRoot.of Φ)).IsRoot a ∧
      a - (AdjoinRoot.root Φ) ^ residueCard O ∈ baseIdeal O Φ
  then Classical.choose h else AdjoinRoot.root Φ
/-- Both branches of `frobeniusRoot` are roots of `Φ`; this makes the Frobenius a genuine algebra
map. -/
private theorem frobeniusRoot_eval₂ (Φ : Polynomial O) :
    Φ.eval₂ (AdjoinRoot.of Φ) (frobeniusRoot O Φ) = 0 := by
  unfold frobeniusRoot
  split_ifs with h
  · simpa [Polynomial.IsRoot, Polynomial.eval_map] using (Classical.choose_spec h).1
  · exact AdjoinRoot.eval₂_root Φ
/-- The Frobenius `O`-algebra endomorphism of `O_δ`, sending `θ` to the Frobenius root. -/
noncomputable def unramifiedFrobenius (Φ : Polynomial O) : AdjoinRoot Φ →ₐ[O] AdjoinRoot Φ :=
  AdjoinRoot.liftAlgHom Φ (Algebra.ofId O (AdjoinRoot Φ)) (frobeniusRoot O Φ)
    (frobeniusRoot_eval₂ O Φ)
/-- Iterates `σ^i` of the Frobenius, defined by recursion so that no monoid structure on
endomorphisms is needed. -/
noncomputable def frobeniusIter (Φ : Polynomial O) : ℕ → (AdjoinRoot Φ →ₐ[O] AdjoinRoot Φ)
  | 0 => AlgHom.id O (AdjoinRoot Φ)
  | i+1 => (unramifiedFrobenius O Φ).comp (frobeniusIter Φ i)
end

/-! ### Frobenius descent -/

section
variable (O : Type) [CommRing O] [IsLocalRing O] (Φ : Polynomial O)
/-- The residue embedding `k → k_δ` induced by `O → O_δ`. -/
noncomputable def residueEmbed : ResidueField O →+* residueExtension O Φ :=
  Ideal.quotientMap (I := maximalIdeal O) (baseIdeal O Φ) (AdjoinRoot.of Φ)
    (Ideal.map_le_iff_le_comap.mp le_rfl)
/-- The reduction `θ̄` of the root `θ` to `k_δ`. -/
abbrev rootBar : residueExtension O Φ := baseReduce O Φ (AdjoinRoot.root Φ)
/-- The linear residue factor `X − θ̄^(q^i)` above the `i`-th conjugate root. -/
noncomputable def conjugateFactor (i : ℕ) : Polynomial (residueExtension O Φ) :=
  X - C (rootBar O Φ ^ residueCard O ^ i)
/-- Block cell: coefficient vectors over `O_δ` whose monic polynomial reduces to `(X − θ̄)^r`. -/
def blockCell (r : ℕ) : Set (Fin r → AdjoinRoot Φ) :=
  {b | (monicPolyO b).map (baseReduce O Φ) = conjugateFactor O Φ 0 ^ r}
/-- The `X^r` cell over `O_δ`: coefficient vectors whose monic polynomial reduces to `X^r`. -/
def zeroCell (r : ℕ) : Set (Fin r → AdjoinRoot Φ) :=
  {b | (monicPolyO b).map (baseReduce O Φ) = X ^ r}
/-- The product of the `δ` Frobenius conjugates `B^(σ^i)`, `i < δ = deg Φ`. -/
noncomputable def conjugateProduct (B : Polynomial (AdjoinRoot Φ)) : Polynomial (AdjoinRoot Φ) :=
  ∏ i : Fin Φ.natDegree, B.map (frobeniusIter O Φ i).toRingHom
open scoped Classical in
/-- The element of `O` mapping to `x` when one exists, and `0` otherwise. -/
noncomputable def descendCoeff (x : AdjoinRoot Φ) : O :=
  if h : ∃ c : O, algebraMap O (AdjoinRoot Φ) c = x then Classical.choose h else 0
/-- Descent map: a block over `O_δ` goes to the `O`-coefficient vector of its conjugate
product. -/
noncomputable def descendBlock (r : ℕ) (b : Fin r → AdjoinRoot Φ) : Fin (Φ.natDegree * r) → O :=
  fun j => descendCoeff O Φ ((conjugateProduct O Φ (monicPolyO b)).coeff j)
open scoped Classical in
/-- Block selection: the monic degree-`r` divisor over `O_δ` of the lifted polynomial that reduces
to `(X − θ̄)^r`, when one exists (uniqueness is a theorem); `0` otherwise. -/
noncomputable def selectBlock (r : ℕ) (a : Fin (Φ.natDegree * r) → O) : Fin r → AdjoinRoot Φ :=
  if h : ∃ B : Polynomial (AdjoinRoot Φ), B.Monic ∧ B.natDegree = r ∧
      B.map (baseReduce O Φ) = conjugateFactor O Φ 0 ^ r ∧
      B ∣ (monicPolyO a).map (AdjoinRoot.of Φ)
  then coeffVec r (Classical.choose h) else 0
/-- Translation `X ↦ X + θ` on coefficient vectors over `O_δ`. -/
noncomputable def translateBlock (r : ℕ) (b : Fin r → AdjoinRoot Φ) : Fin r → AdjoinRoot Φ :=
  coeffVec r (Polynomial.taylor (AdjoinRoot.root Φ) (monicPolyO b))
end

/-! ### Commutative algebra toolkit -/

/-- If `J^k ≤ I ≤ J`, then a module is `I`-adically complete iff it is `J`-adically complete. -/
theorem adic_complete_iff_of_pow_le (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Ideal R) (k : ℕ) (h1 : J ^ k ≤ I) (h2 : I ≤ J) :
    IsAdicComplete I M ↔ IsAdicComplete J M := by
  set φ : ℕ → ℕ := fun n => max 1 k * n
  have hle : ∀ n, n ≤ φ n := fun n => Nat.le_mul_of_pos_left n (by omega)
  have hmono : ∀ {m n : ℕ}, m ≤ n → φ m ≤ φ n := fun h => Nat.mul_le_mul_left _ h
  have hIJ : ∀ n, (I ^ n • ⊤ : Submodule R M) ≤ J ^ n • ⊤ :=
    fun n => Submodule.smul_mono_left (Ideal.pow_right_mono h2 n)
  have hJI : ∀ n, (J ^ φ n • ⊤ : Submodule R M) ≤ I ^ n • ⊤ := by
    intro n
    apply Submodule.smul_mono_left
    calc J ^ φ n ≤ J ^ (k * n) := Ideal.pow_le_pow_right (Nat.mul_le_mul_right _ (le_max_right _ _))
      _ = (J ^ k) ^ n := pow_mul _ _ _
      _ ≤ I ^ n := Ideal.pow_right_mono h1 n
  constructor
  · intro hI
    refine { haus' := ?_, prec' := ?_ }
    · exact fun x hx => hI.haus' x fun n => SModEq.mono (hJI n) (hx (φ n))
    · intro f hf
      obtain ⟨L, hL⟩ := hI.prec' (fun n => f (φ n))
        (fun {m n} h => SModEq.mono (hJI m) (hf (hmono h)))
      exact ⟨L, fun n => (hf (hle n)).trans (SModEq.mono (hIJ n) (hL n))⟩
  · intro hJ
    refine { haus' := ?_, prec' := ?_ }
    · exact fun x hx => hJ.haus' x fun n => SModEq.mono (hIJ n) (hx n)
    · intro f hf
      obtain ⟨L, hL⟩ := hJ.prec' f (fun {m n} h => SModEq.mono (hIJ m) (hf h))
      exact ⟨L, fun n => (hf (hle n)).trans (SModEq.mono (hJI n) (hL (φ n)))⟩

/-- Idempotents lift along `A → A/I` when `A` is `I`-adically complete (Hensel applied to
`X² − X`). -/
private theorem adic_idempotent_lift (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (e : A ⧸ I)
    (he : e * e = e) :
    ∃ x : A, x*x=x ∧ Ideal.Quotient.mk I x = e := by
  obtain ⟨x0, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hmon : (X ^ 2 - X : A[X]).Monic := by
    simpa using monic_X_pow_sub (R := A) (p := X) (n := 2)
      (degree_X_le.trans_lt (by exact_mod_cast (by norm_num : 1 < 2)))
  have h1 : (X ^ 2 - X : A[X]).eval x0 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp [sq, he]
  have h2 : IsUnit (Ideal.Quotient.mk I ((X ^ 2 - X : A[X]).derivative.eval x0)) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I ((X ^ 2 - X : A[X]).derivative.eval x0)) ?_
    simp only [derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_pow,
      eval_X, eval_one, eval_natCast, map_sub, map_mul, map_pow, map_one, map_natCast]
    norm_num
    linear_combination (4 : A ⧸ I) * he
  obtain ⟨a, ha, hax⟩ := HenselianRing.is_henselian _ hmon x0 h1 h2
  refine ⟨a, ?_, ?_⟩
  · have := ha.eq_zero
    simp only [eval_sub, eval_pow, eval_X] at this
    linear_combination this
  · exact Ideal.Quotient.eq.mpr hax

/-- Membership in `J • ⊤` is read off coordinatewise in a finite basis. -/
private theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite ι] (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ (J • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  have := Fintype.ofFinite ι
  refine ⟨fun hx => Submodule.smul_induction_on hx
    (fun r hr m _ i => by simpa using J.mul_mem_right _ hr)
    (fun x y hx hy i => by simpa using J.add_mem (hx i) (hy i)), fun h => ?_⟩
  rw [← b.sum_repr x]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial

/-- An element of `O[X]/(Φ)` lies in `(m_O O_δ)^L` iff all its coordinates in the power basis
lie in `m_O^L`. -/
theorem base_ideal_coordinates (O : Type) [CommRing O] [IsLocalRing O] (Φ : Polynomial O)
    (hΦ : Φ.Monic) (L : ℕ) (x : AdjoinRoot Φ) :
    x ∈ (baseIdeal O Φ)^L ↔ ∀ i, (AdjoinRoot.powerBasis' hΦ).basis.repr x i ∈
      (IsLocalRing.maximalIdeal O)^L := by
  rw [← mem_smul_top_iff_repr, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, baseIdeal,
    ← Ideal.map_pow, AdjoinRoot.algebraMap_eq]

/-- A base element `c ∈ O` lies in `(m_O O_δ)^L` iff `c ∈ m_O^L` (for `Φ` monic of positive
degree). -/
theorem base_ideal_pure (O : Type) [CommRing O] [IsLocalRing O] (Φ : Polynomial O) (hΦ : Φ.Monic)
    (hdeg : 0 < Φ.natDegree) (L : ℕ) (c : O) :
    algebraMap O (AdjoinRoot Φ) c ∈ (baseIdeal O Φ)^L ↔ c ∈ (IsLocalRing.maximalIdeal O)^L := by
  rw [SurfaceBlowup.base_ideal_coordinates O Φ hΦ L]
  set b := AdjoinRoot.powerBasis' hΦ
  have h0 : 0 < b.dim := by simpa [b] using hdeg
  have hb : b.basis ⟨0, h0⟩ = 1 := by
    rw [PowerBasis.coe_basis]; simp
  have hrepr : b.basis.repr (algebraMap O (AdjoinRoot Φ) c) = Finsupp.single ⟨0, h0⟩ c := by
    rw [Algebra.algebraMap_eq_smul_one, ← hb, map_smul, Module.Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hrepr]
  constructor
  · intro h; simpa using h ⟨0, h0⟩
  · intro h i
    by_cases hi : i = ⟨0, h0⟩
    · subst hi; simpa using h
    · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]; exact zero_mem _

/-- Frobenius conjugates of the distinct monic irreducible factors of `F` over `Frac O_δ` are
monic irreducible and pairwise distinct, and they factor each conjugate of `F` and the
conjugate product of `F`. -/
private theorem conjugate_irreducible_factors_distinct (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) [IsDomain (AdjoinRoot Φ)]
    (τ : ℕ → (BaseField (AdjoinRoot Φ) ≃+* BaseField (AdjoinRoot Φ)))
    (hτ : ∀ (i : ℕ) (x : AdjoinRoot Φ), τ i
      (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) x) = algebraMap (AdjoinRoot Φ)
      (BaseField (AdjoinRoot Φ)) (frobeniusIter O Φ i x)) (F : Polynomial (AdjoinRoot Φ))
    (gs : List (Polynomial (BaseField (AdjoinRoot Φ))))
    (hgs : ∀ g ∈ gs, g.Monic ∧ Irreducible g) (hd : gs.Pairwise (fun g h => g ≠ h))
    (hprod : F.map (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))) = gs.prod)
    (hcop : ∀ i j : Fin Φ.natDegree, i ≠ j → IsCoprime
      ((fun i : Fin Φ.natDegree => (F.map (frobeniusIter O Φ i).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) i)
      ((fun i : Fin Φ.natDegree => (F.map (frobeniusIter O Φ i).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) j)) :
    (∀ (i : ℕ) (g : Polynomial (BaseField (AdjoinRoot Φ))), g.Monic → Irreducible g →
        (g.map (τ i).toRingHom).Monic ∧ Irreducible (g.map (τ i).toRingHom)) ∧
      (∀ (i j : Fin Φ.natDegree) (a b : Fin gs.length), (gs.get a).map (τ i).toRingHom =
        (gs.get b).map (τ j).toRingHom → i = j ∧ a = b) ∧
      (∀ i : Fin Φ.natDegree,
        (fun i : Fin Φ.natDegree => (F.map (frobeniusIter O Φ i).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) i =
        (gs.map (Polynomial.map (τ i).toRingHom)).prod) ∧ (conjugateProduct O Φ F).map
      (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))) = ∏ i : Fin Φ.natDegree,
      (gs.map (Polynomial.map (τ i).toRingHom)).prod := by
  set L := algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) with hL
  have key : ∀ (i : ℕ) (P : Polynomial (AdjoinRoot Φ)),
      (P.map (frobeniusIter O Φ i).toRingHom).map L = (P.map L).map (τ i).toRingHom := by
    intro i P
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun x => (hτ i x).symm
  have c1 : ∀ (i : ℕ) (g : Polynomial (BaseField (AdjoinRoot Φ))), g.Monic → Irreducible g →
      (g.map (τ i).toRingHom).Monic ∧ Irreducible (g.map (τ i).toRingHom) := by
    intro i g hm hi
    exact ⟨hm.map _, by simpa using (MulEquiv.irreducible_iff (mapEquiv (τ i)).toMulEquiv).mpr hi⟩
  have c3 : ∀ i : Fin Φ.natDegree, (F.map (frobeniusIter O Φ i).toRingHom).map L
      = (gs.map (Polynomial.map (τ i).toRingHom)).prod := fun i => by
    rw [key, hprod, Polynomial.map_list_prod]
  refine ⟨c1, ?_, c3, ?_⟩
  · intro i j a b hab
    have hmem : ∀ (k : Fin Φ.natDegree) (c : Fin gs.length),
        (gs.get c).map (τ k).toRingHom ∣ (F.map (frobeniusIter O Φ k).toRingHom).map L := by
      intro k c
      rw [c3]
      exact List.dvd_prod (List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩)
    have hirr := (c1 i (gs.get a) (hgs _ (List.get_mem gs a)).1 (hgs _ (List.get_mem gs a)).2).2
    have hij : i = j := by
      by_contra hne
      apply hirr.not_isUnit
      exact (hcop i j hne).isUnit_of_dvd' (hmem i a) (hab ▸ hmem j b)
    subst hij
    exact ⟨rfl, (List.Nodup.get_inj_iff hd).mp (Polynomial.map_injective _ (τ i).injective hab)⟩
  · rw [conjugateProduct, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun i _ => c3 i

open scoped Classical in
/-- For pairwise coprime monic `g i` over a field, `∑ h i ∏_{j ≠ i} g j = 0` with
`deg h i < deg g i` forces all `h i = 0`. -/
theorem coprime_family_linear_injective (k ι : Type) [Field k] [Fintype ι] (g : ι → Polynomial k)
    (hg : ∀ i, (g i).Monic) (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (h : ι → Polynomial k)
    (hdeg : ∀ i, (h i).degree < ((g i).natDegree : WithBot ℕ))
    (hsum : ∑ i, h i * ∏ j ∈ Finset.univ.erase i, g j = 0) :
    ∀ i, h i = 0 := by
  intro i
  have hrest : g i ∣ ∑ l ∈ Finset.univ.erase i, h l * ∏ j ∈ Finset.univ.erase l, g j := by
    apply Finset.dvd_sum
    intro l hl
    have hil : i ∈ Finset.univ.erase l :=
      Finset.mem_erase.mpr ⟨fun e => (Finset.mem_erase.mp hl).1 e.symm, Finset.mem_univ _⟩
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hil) _
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun l => h l * ∏ j ∈ Finset.univ.erase l, g j) (Finset.mem_univ i)
  rw [hsum] at hsplit
  have hmain : g i ∣ h i * ∏ j ∈ Finset.univ.erase i, g j := by
    have : h i * ∏ j ∈ Finset.univ.erase i, g j
        = -∑ l ∈ Finset.univ.erase i, h l * ∏ j ∈ Finset.univ.erase l, g j := by
      rw [eq_neg_iff_add_eq_zero]; exact hsplit
    rw [this]; exact (dvd_neg).mpr hrest
  have hcop : IsCoprime (g i) (∏ j ∈ Finset.univ.erase i, g j) :=
    IsCoprime.prod_right fun j hj => hc i j (Finset.mem_erase.mp hj).1.symm
  have hd : g i ∣ h i := hcop.dvd_of_dvd_mul_right hmain
  apply Polynomial.eq_zero_of_dvd_of_degree_lt hd
  rw [Polynomial.degree_eq_natDegree (hg i).ne_zero]
  exact hdeg i

/-- Monic polynomials over a local ring `R` with coprime reductions stay coprime over any
`R`-algebra `K` (classically: the fraction field of a DVR). -/
theorem coprime_of_coprime_residue_dvr (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K]
    [Algebra R K] (A B : Polynomial R) (hA : A.Monic) (hB : B.Monic)
    (hc : IsCoprime (A.map (IsLocalRing.residue R)) (B.map (IsLocalRing.residue R))) :
    IsCoprime (A.map (algebraMap R K)) (B.map (algebraMap R K)) :=
  (isCoprime_of_isCoprime_map_residue hA hB hc).map (Polynomial.mapRingHom (algebraMap R K))

/-- Distinct monic irreducible polynomials over a field are coprime. -/
theorem distinct_monic_irreducible_coprime (K : Type) [Field K] (g h : Polynomial K) (hg : g.Monic)
    (hh : h.Monic) (hgi : Irreducible g) (hhi : Irreducible h) (hne : g ≠ h) :
    IsCoprime g h := by
  rw [hgi.coprime_iff_not_dvd]
  intro hd
  exact hne (Polynomial.eq_of_monic_of_associated hg hh (hgi.associated_of_dvd hhi hd))

/-- For an integral injective extension of DVRs `O → B`, `m_O B = m_B^e` with `e` the
ramification index. -/
theorem dvr_extension_maximalIdeal_map_eq_pow (O B : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O B]
    [Algebra.IsIntegral O B] (hinj : Function.Injective (algebraMap O B)) :
    (IsLocalRing.maximalIdeal O).map (algebraMap O B) =
      (IsLocalRing.maximalIdeal B)^((IsLocalRing.maximalIdeal B).ramificationIdx O) := by
  set p := IsLocalRing.maximalIdeal O
  set q := IsLocalRing.maximalIdeal B
  have hcomap : q.comap (algebraMap O B) = p :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q)
  have : q.LiesOver p := ⟨hcomap.symm⟩
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hq : q ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hp0 : p.map (algebraMap O B) ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p.map (algebraMap O B) = q ^ k := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hp0 hϖ
    refine ⟨k, ?_⟩
    rw [hk, show q = Ideal.span {ϖ} from
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow]
  have hprime : Prime q := Ideal.prime_of_isPrime hq inferInstance
  have he : q.ramificationIdx O = k := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p q hp0, hk,
      UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hprime.irreducible, normalize_eq,
      Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
  rw [he, hk]

/-- In a DVR, `n ↦ m^n` is injective. -/
theorem dvr_maximalIdeal_pow_injective (B : Type) [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] (a b : ℕ)
    (h : (IsLocalRing.maximalIdeal B) ^ a = (IsLocalRing.maximalIdeal B) ^ b) :
    a = b := by
  have h0 : IsLocalRing.maximalIdeal B ≠ ⊥ := by
    intro h0
    exact IsDiscreteValuationRing.not_isField B ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h0)
  have h1 : IsLocalRing.maximalIdeal B ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  exact (Ideal.pow_right_strictAnti _ h0 h1).injective h

/-- Over a finite field `k` with `q` elements, `P(y^q) = P(y)^q` for `P ∈ k[X]`. -/
theorem eval_at_pow_card (k K : Type) [Field k] [Finite k] [CommRing K] (ρ : k →+* K)
    (P : Polynomial k) (y : K) :
    P.eval₂ ρ (y ^ Nat.card k) = (P.eval₂ ρ y) ^ Nat.card k := by
  cases nonempty_fintype k
  rw [Nat.card_eq_fintype_card, Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map,
    ← Polynomial.expand_eval, ← Polynomial.map_expand, FiniteField.expand_card,
    Polynomial.map_pow, Polynomial.eval_pow]

/-- The factor product map (coefficients of a product of monic polynomials) is continuous and
measurable. -/
theorem factor_product_continuous (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] (ι : Type) [Fintype ι]
    (d : ι → ℕ) :
    Continuous (fun a : (∀ i, Fin (d i) → O) => factorProduct d a) ∧ Measurable
      (fun a : (∀ i, Fin (d i) → O) => factorProduct d a) := by
  have key := Finset.prod_induction (s := Finset.univ)
    (fun i (a : ∀ i, Fin (d i) → O) => monicPolyO (a i))
    (fun P => ∀ j, Continuous fun a => (P a).coeff j)
    (fun P Q hP hQ j => by
      simpa [coeff_mul] using continuous_finsetSum _ fun p _ => (hP p.1).mul (hQ p.2))
    (fun j => by simpa using continuous_const) fun i _ m => by
      simp only [monicPolyO, coeff_add, finsetSum_coeff, coeff_C_mul_X_pow]
      refine continuous_const.add (continuous_finsetSum _ fun k _ => ?_)
      split_ifs <;> fun_prop
  simp only [Finset.prod_apply] at key
  have hc : Continuous fun a => factorProduct d a := continuous_pi fun j => key j
  exact ⟨hc, hc.measurable⟩

/-- For a finite field `k ↪ K`, the solutions of `x^q = x` in the field `K` are exactly the image
of `k`. -/
theorem finite_field_frobenius_fixed_points (k K : Type) [Field k] [Finite k] [Field K]
    (ρ : k →+* K) (x : K) :
    x ^ Nat.card k = x ↔ x ∈ Set.range ρ := by
  classical
  cases nonempty_fintype k
  rw [Nat.card_eq_fintype_card]
  set q := Fintype.card k with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  have himg : ∀ c : k, (ρ c) ^ q = ρ c := by
    intro c; rw [← map_pow, FiniteField.pow_card]
  constructor
  · intro hx
    set P : Polynomial K := Polynomial.X ^ q - Polynomial.X with hP
    have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq1
    have hdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
    have hmem : ∀ y : K, y ^ q = y → y ∈ P.roots.toFinset := by
      intro y hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
      simp [hP, Polynomial.IsRoot, hy]
    have hsub : Finset.univ.image ρ ⊆ P.roots.toFinset := by
      intro y hy
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hy
      exact hmem _ (himg c)
    have hcard : P.roots.toFinset.card ≤ (Finset.univ.image ρ).card := by
      rw [Finset.card_image_of_injective _ ρ.injective, Finset.card_univ]
      calc P.roots.toFinset.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' P
        _ = q := hdeg
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have : x ∈ Finset.univ.image ρ := heq ▸ hmem x hx
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp this
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    exact himg c

/-- A finite free module over an `I`-adically complete ring is `I`-adically complete. -/
theorem finite_free_adic_complete (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Free O M] (I : Ideal O) [IsAdicComplete I O] :
    IsAdicComplete I M := by
  let b := Module.Free.chooseBasis O M
  have key := mem_smul_top_iff_repr b
  have keyO : ∀ (J : Ideal O) (x : O), x ∈ (J • ⊤ : Submodule O O) ↔ x ∈ J := by
    intro J x
    rw [smul_eq_mul, Ideal.mul_top]
  have hM : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule O M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule O O)] := by
    intro n x y
    simp only [SModEq.sub_mem, key, keyO, map_sub, Finsupp.sub_apply]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply b.repr.injective
    ext i
    have := IsHausdorff.haus (I := I) (M := O) inferInstance (b.repr x i) fun n =>
      by simpa using (hM n x 0).1 (hx n) i
    simpa using this
  · intro f hf
    have hc : ∀ i, ∃ L : O, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule O O)] :=
      fun i => IsPrecomplete.prec (I := I) inferInstance fun {m n} hmn => (hM m _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨∑ i, L i • b i, fun n => (hM n _ _).2 fun i => ?_⟩
    simpa [Finsupp.single_apply] using hL i n

/-- If `O/I` is finite, then so is `M/IM` for a finite free `O`-module `M`. -/
theorem finite_free_residue_quotient (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Free O M] (I : Ideal O) [Finite (O ⧸ I)] :
    Finite (M ⧸ (I • ⊤ : Submodule O M)) := by
  have : Module.Finite (O ⧸ I) (M ⧸ (I • ⊤ : Submodule O M)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  exact Module.finite_of_finite (O ⧸ I)

/-- Every element of a finite monoid has a positive power that is idempotent. -/
private theorem finite_monoid_idempotent_power (A : Type) [Monoid A] [Finite A] (a : A) :
    ∃ n : ℕ, 0 < n ∧ a^n * a^n = a^n := by
  have key : ∃ i p : ℕ, 0 < p ∧ a^(i+p) = a^i := by
    obtain ⟨x, y, hxy, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a^n)
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact ⟨x, y - x, by omega, by rw [Nat.add_sub_cancel' hlt.le]; exact h.symm⟩
    · exact ⟨y, x - y, by omega, by rw [Nat.add_sub_cancel' hlt.le]; exact h⟩
  obtain ⟨i, p, hp, h⟩ := key
  have per : ∀ m k : ℕ, i ≤ k → a^(k + m*p) = a^k := by
    intro m
    induction m with
    | zero => intro k _; simp
    | succ m ih =>
      intro k hk
      have e : k + (m+1)*p = (k - i) + (i + p) + m*p := by
        rw [Nat.add_mul]; omega
      rw [e, pow_add, pow_add, h, ← pow_add, Nat.sub_add_cancel hk, ← pow_add, ih k hk]
  refine ⟨p*(i+1), Nat.mul_pos hp (Nat.succ_pos _), ?_⟩
  rw [← pow_add]
  have := per (i+1) (p*(i+1)) (by nlinarith)
  rwa [Nat.mul_comm (i+1) p] at this

/-- A nontrivial finite commutative ring whose only idempotents are `0, 1` is local. -/
private theorem finite_ring_local_of_idempotents (A : Type) [CommRing A] [Nontrivial A] [Finite A]
    (he : ∀ e : A, e*e=e → e=0 ∨ e=1) :
    IsLocalRing A := by
  refine ⟨fun {a b} hab => ?_⟩
  obtain ⟨n, hn, hidem⟩ := finite_monoid_idempotent_power A a
  rcases he _ hidem with h | h
  · exact Or.inr (eq_sub_of_add_eq' hab ▸ IsNilpotent.isUnit_one_sub ⟨n, h⟩)
  · exact Or.inl (IsUnit.of_pow_eq_one h hn.ne')

/-- A domain that is `I`-adically complete with `A/I` finite is local. -/
theorem complete_domain_finite_quotient_local (A : Type) [CommRing A] [IsDomain A] (I : Ideal A)
    [IsAdicComplete I A] [Finite (A ⧸ I)] :
    IsLocalRing A := by
  have hjac : I ≤ (⊥ : Ideal A).jacobson := IsAdicComplete.le_jacobson_bot I
  have hI : I ≠ ⊤ := by
    intro h
    have : (⊥ : Ideal A).jacobson = ⊤ := top_le_iff.mp (h ▸ hjac)
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp this)
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (A ⧸ I) := by
    apply SurfaceBlowup.finite_ring_local_of_idempotents
    intro e he
    obtain ⟨x, hx, rfl⟩ := SurfaceBlowup.adic_idempotent_lift A I e he
    have : x * (x - 1) = 0 := by rw [mul_sub, hx]; ring
    rcases mul_eq_zero.mp this with h | h
    · left; simp [h]
    · right; rw [sub_eq_zero.mp h, map_one]
  have := isLocalHom_of_le_jacobson_bot I hjac
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Ideal.Quotient.mk I a) with h | h
  · left; exact isUnit_of_map_unit _ _ h
  · right; exact isUnit_of_map_unit (Ideal.Quotient.mk I) _ (by simpa using h)

/-! ### Coefficients of binary forms -/

section FormPolyLemmas

variable {A : Type} [CommRing A] {n : ℕ}

private theorem coeff_formPoly (a : Fin (n + 1) → A) (j : Fin (n + 1)) :
    (formPoly a).coeff (j : ℕ) = a j := by
  simp [formPoly, finsetSum_coeff, coeff_X_pow, Fin.val_inj]

private theorem natDegree_formPoly_le (a : Fin (n + 1) → A) : (formPoly a).natDegree ≤ n :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.2)

private theorem formPoly_eq_zero (a : Fin (n + 1) → A) (h : formPoly a = 0) : a = 0 :=
  funext fun j => by rw [← coeff_formPoly a j, h, coeff_zero, Pi.zero_apply]

/-- `formPoly` is additive. -/
theorem formPoly_add (a b : Fin (n + 1) → A) :
    formPoly (a + b) = formPoly a + formPoly b := by
  simp [formPoly, add_mul, Finset.sum_add_distrib]

private theorem formPoly_C_smul (c : A) (a : Fin (n + 1) → A) :
    formPoly (c • a) = C c * formPoly a := by
  simp [formPoly, Finset.mul_sum, mul_assoc]

private theorem formProd_map {B : Type} [CommRing B] (f : A →+* B) {ι : Type} [Fintype ι]
    (d : ι → ℕ) (a : ∀ i, Fin (d i + 1) → A) (j : Fin ((∑ i, d i) + 1)) :
    f (formProd d a j) = formProd d (fun i k => f (a i k)) j := by
  have h1 : ∀ i, formPoly (fun k => f (a i k)) = (formPoly (a i)).map f := fun i => by
    simp [formPoly, Polynomial.map_sum]
  simp only [formProd, h1, ← Polynomial.map_prod, Polynomial.coeff_map]

end FormPolyLemmas

/-- The normalized product of factor cells lands in the product cell, has the expected
reduction and unit `μ`-coordinate, and preserves congruences modulo `m^L`. -/
theorem form_product_maps_to_and_preserves (O : Type) [CommRing O] [IsLocalRing O] (ι : Type)
    [Fintype ι] (d : ι → ℕ) (ν : ∀ i, Fin (d i + 1))
    (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (μ : Fin ((∑ i, d i) + 1)) (hμ : formProd d g μ = 1)
    (a a' : ∀ i, Fin (d i) → O)
    (ha : a ∈ Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i)))
    (ha' : a' ∈ Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i))) :
    reducedFormProduct O d ν g μ a ∈ reducedFormCell O (∑ i, d i) μ (formProd d g) ∧
      residueVector O (formProd d (fun i => insertOne (ν i) (a i))) = formProd d g ∧ IsUnit
      (formProd d (fun i => insertOne (ν i) (a i)) μ) ∧ ∀ L : ℕ,
      (∀ i j, a i j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L) → ∀ j,
      reducedFormProduct O d ν g μ a j - reducedFormProduct O d ν g μ a' j ∈
      (IsLocalRing.maximalIdeal O) ^ L := by
  set S := Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i))
  have hres : ∀ b ∈ S,
      residueVector O (formProd d (fun i => insertOne (ν i) (b i))) = formProd d g := by
    intro b hb
    funext j
    simp only [residueVector]
    rw [formProd_map]
    exact congrArg (fun G => formProd d G j) (funext fun i => (Set.mem_univ_pi.mp hb i).2)
  have hunit : ∀ b ∈ S, IsUnit (formProd d (fun i => insertOne (ν i) (b i)) μ) := by
    intro b hb
    have h : IsLocalRing.residue O (formProd d (fun i => insertOne (ν i) (b i)) μ) = 1 := by
      rw [← hμ]; exact congrFun (hres b hb) μ
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hm
    rw [← IsLocalRing.residue_eq_zero_iff, h] at hm
    exact one_ne_zero hm
  have hguard : ∀ b ∈ S, reducedFormProduct O d ν g μ b =
      dropCoord μ (normalizeAt μ (formProd d (fun i => insertOne (ν i) (b i)))) :=
    fun b hb => if_pos fun i => Set.mem_univ_pi.mp hb i
  refine ⟨?_, hres a ha, hunit a ha, ?_⟩
  · rw [hguard a ha]
    have hu := hunit a ha
    set P := formProd d (fun i => insertOne (ν i) (a i)) with hP
    have hPμ : normalizeAt μ P μ = 1 := by
      simp only [normalizeAt, Pi.smul_apply, smul_eq_mul]; exact Ring.inverse_mul_cancel _ hu
    have hins : insertOne μ (dropCoord μ (normalizeAt μ P)) = normalizeAt μ P := by
      simp only [insertOne, dropCoord]
      rw [Fin.insertNth_eq_iff]
      exact ⟨hPμ.symm, rfl⟩
    simp only [reducedFormCell, Set.mem_ofPred_eq]
    rw [hins]
    refine ⟨hPμ, ?_⟩
    funext j
    have h : ∀ m, IsLocalRing.residue O (P m) = formProd d g m := fun m => congrFun (hres a ha) m
    have hμ' : IsLocalRing.residue O (P μ) = 1 := by rw [h, hμ]
    simp only [residueVector, normalizeAt, Pi.smul_apply, smul_eq_mul, map_mul, h]
    have : IsLocalRing.residue O (Ring.inverse (P μ)) = 1 := by
      simpa [hμ'] using congrArg (IsLocalRing.residue O) (Ring.inverse_mul_cancel _ hu)
    rw [this, one_mul]
  · intro L hL j
    set I := (IsLocalRing.maximalIdeal O) ^ L
    rw [hguard a ha, hguard a' ha', ← Ideal.Quotient.eq]
    set P := formProd d (fun i => insertOne (ν i) (a i)) with hP
    set P' := formProd d (fun i => insertOne (ν i) (a' i)) with hP'
    have hA : ∀ i k, Ideal.Quotient.mk I (insertOne (ν i) (a i) k) =
        Ideal.Quotient.mk I (insertOne (ν i) (a' i) k) := by
      intro i k
      simp only [insertOne]
      rcases Fin.eq_self_or_eq_succAbove (ν i) k with rfl | ⟨k, rfl⟩
      · simp
      · simp only [Fin.insertNth_apply_succAbove]
        exact Ideal.Quotient.eq.mpr (hL i k)
    have hPP : ∀ m, Ideal.Quotient.mk I (P m) = Ideal.Quotient.mk I (P' m) := by
      intro m
      rw [hP, hP', formProd_map, formProd_map]
      simp only [hA]
    have hu := hunit a ha
    have hu' := hunit a' ha'
    have hinv : Ideal.Quotient.mk I (Ring.inverse (P μ)) =
        Ideal.Quotient.mk I (Ring.inverse (P' μ)) := by
      have e1 := congrArg (Ideal.Quotient.mk I) (Ring.inverse_mul_cancel _ hu)
      have e2 := congrArg (Ideal.Quotient.mk I) (Ring.mul_inverse_cancel _ hu')
      simp only [map_mul, map_one] at e1 e2
      rw [hPP μ] at e1
      exact left_inv_eq_right_inv e1 e2
    simp only [dropCoord, Fin.removeNth_apply, normalizeAt, Pi.smul_apply, smul_eq_mul, map_mul,
      hinv, hPP]

open scoped Classical in
/-- Injectivity of the partial-fraction map for pairwise coprime binary forms: if
`∑ h i ∏_{j ≠ i} g j = c ∏ g i` with `h i` vanishing at `ν i`, then all `h i = 0`. -/
theorem forms_linear_injective (k ι : Type) [Field k] [Fintype ι] (d : ι → ℕ)
    (g : ∀ i, Fin (d i + 1) → k) (hg : ∀ i, g i ≠ 0) (hc : FormsCoprime d g)
    (ν : ∀ i, Fin (d i + 1)) (hν : ∀ i, g i (ν i) ≠ 0) (h : ∀ i, Fin (d i + 1) → k)
    (hh : ∀ i, h i (ν i) = 0) (c : k)
    (hsum : ∑ i, formPoly (h i) * ∏ j ∈ Finset.univ.erase i, formPoly (g j) = Polynomial.C c * ∏ i,
      formPoly (g i)) :
    ∀ i, h i = 0 := by
  set p : ι → Polynomial k := fun i => formPoly (h i) with hp
  set q : ι → Polynomial k := fun i => formPoly (g i) with hq
  have hq0 : ∀ i, q i ≠ 0 := fun i h0 => hg i (formPoly_eq_zero _ h0)
  have hQ0 : (∏ i, q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hq0 i)
  -- Step 1: divisibility
  have hdvd : ∀ i, q i ∣ p i := by
    intro i
    have hcop : IsCoprime (q i) (∏ j ∈ Finset.univ.erase i, q j) :=
      IsCoprime.prod_right (fun j hj => hc.1 i j (Finset.ne_of_mem_erase hj).symm)
    apply hcop.dvd_of_dvd_mul_right
    have hs := hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hs
    have : p i * ∏ j ∈ Finset.univ.erase i, q j =
        Polynomial.C c * ∏ i, q i - ∑ l ∈ Finset.univ.erase i,
          p l * ∏ j ∈ Finset.univ.erase l, q j := by
      rw [← hs]; ring
    rw [this]
    apply dvd_sub
    · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
    · apply Finset.dvd_sum
      intro l hl
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _
        (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hl).symm, Finset.mem_univ i⟩)) _
  choose u hu using hdvd
  -- Step 2: sum of u equals C c
  have husum : ∑ i, u i = Polynomial.C c := by
    have : (∑ i, u i) * ∏ i, q i = Polynomial.C c * ∏ i, q i := by
      rw [← hsum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      change u i * ∏ i, q i = p i * ∏ j ∈ Finset.univ.erase i, q j
      rw [hu i, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      ring
    exact mul_right_cancel₀ hQ0 this
  have hconst_full : ∀ i, (q i).natDegree = d i → (u i).natDegree = 0 := by
    intro i hi
    by_cases hu0 : u i = 0
    · simp [hu0]
    have h1 : (p i).natDegree ≤ d i := natDegree_formPoly_le _
    rw [hu i, Polynomial.natDegree_mul (hq0 i) hu0, hi] at h1
    omega
  have hconst : ∀ i, (u i).natDegree = 0 := by
    intro i
    by_cases hi : (q i).natDegree = d i
    · exact hconst_full i hi
    have hoth : ∀ j ∈ Finset.univ.erase i, (u j).natDegree = 0 := fun j hj =>
      hconst_full j ((hc.2 i j (Finset.ne_of_mem_erase hj).symm).resolve_left hi)
    have : u i = Polynomial.C c - ∑ j ∈ Finset.univ.erase i, u j := by
      rw [← husum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
    rw [this, ← Nat.le_zero]
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_C, zero_max]
    exact natDegree_sum_le_of_forall_le _ _ fun j hj => (hoth j hj).le
  -- Step 3: normalization
  intro i
  have hC : u i = Polynomial.C ((u i).coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (hconst i)
  have hco := coeff_formPoly (h i) (ν i)
  change (p i).coeff _ = _ at hco
  rw [hu i, hC, Polynomial.coeff_mul_C, hh i] at hco
  change (formPoly (g i)).coeff _ * _ = 0 at hco
  rw [coeff_formPoly] at hco
  have ha : (u i).coeff 0 = 0 := (mul_eq_zero.mp hco).resolve_left (hν i)
  apply formPoly_eq_zero
  change p i = 0
  rw [hu i, hC, ha]
  simp

/-- Degree bound for the partial-fraction map: `∑ h i ∏_{j ≠ i} g j + c ∏ g i` has degree at most
`∑ d i` when `g i, h i` are forms of degree `d i`. -/
private theorem natDegree_partial_fraction_le {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι]
    (d : ι → ℕ) (g h : ∀ i, Fin (d i + 1) → k) (c : k) :
    (∑ i, formPoly (h i) * ∏ j ∈ Finset.univ.erase i, formPoly (g j) +
      C c * ∏ i, formPoly (g i)).natDegree ≤ ∑ i, d i := by
  have hprod : ∀ s : Finset ι, (∏ j ∈ s, formPoly (g j)).natDegree ≤ ∑ j ∈ s, d j := fun s =>
    (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ => natDegree_formPoly_le _)
  apply natDegree_add_le_of_degree_le
  · refine natDegree_sum_le_of_forall_le _ _ fun i _ => natDegree_mul_le.trans ?_
    have h1 := natDegree_formPoly_le (h i)
    have h2 := hprod (Finset.univ.erase i)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    omega
  · refine natDegree_mul_le.trans ?_
    rw [natDegree_C, zero_add]
    exact hprod _

open scoped Classical in
/-- Every binary form of degree `∑ d i` is `∑ h i ∏_{j ≠ i} g j + c ∏ g i` with `h i (ν i) = 0`
(partial fractions for pairwise coprime binary forms). -/
theorem forms_linear_bijective (k ι : Type) [Field k] [Fintype ι] (d : ι → ℕ)
    (g : ∀ i, Fin (d i + 1) → k) (hg : ∀ i, g i ≠ 0) (hc : FormsCoprime d g)
    (ν : ∀ i, Fin (d i + 1)) (hν : ∀ i, g i (ν i) ≠ 0) (w : Fin ((∑ i, d i) + 1) → k) :
    ∃ (h : ∀ i, Fin (d i + 1) → k) (c : k), (∀ i, h i (ν i) = 0) ∧ formPoly w = ∑ i, formPoly
      (h i) * ∏ j ∈ Finset.univ.erase i, formPoly (g j) + Polynomial.C c * ∏ i, formPoly (g i) := by
  let n := ∑ i, d i
  have hn : n = ∑ i, d i := rfl
  let P : ((∀ i, Fin (d i + 1) → k) × k) → k[X] := fun p =>
    ∑ i, formPoly (p.1 i) * ∏ j ∈ Finset.univ.erase i, formPoly (g j) +
      C p.2 * ∏ i, formPoly (g i)
  have hPdeg : ∀ p : (∀ i, Fin (d i + 1) → k) × k, (P p).natDegree ≤ n :=
    fun p => natDegree_partial_fraction_le d g p.1 p.2
  let Φ : ((∀ i, Fin (d i + 1) → k) × k) →ₗ[k] k[X] :=
    { toFun := P
      map_add' := by
        intro p q
        simp only [P, Prod.fst_add, Prod.snd_add, Pi.add_apply, formPoly_add, add_mul,
          Finset.sum_add_distrib, C_add]
        ring
      map_smul' := by
        intro c p
        simp only [P, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, formPoly_C_smul,
          RingHom.id_apply, smul_eq_mul, C_mul, Polynomial.smul_eq_C_mul, mul_add,
          Finset.mul_sum, mul_assoc] }
  let T : k[X] →ₗ[k] (Fin (n + 1) → k) := LinearMap.pi fun j => Polynomial.lcoeff k (j : ℕ)
  let ev : ((∀ i, Fin (d i + 1) → k) × k) →ₗ[k] (ι → k) :=
    { toFun := fun p i => p.1 i (ν i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let V := LinearMap.ker ev
  let L : V →ₗ[k] (Fin (n + 1) → k) := T.comp (Φ.comp V.subtype)
  have hev : Function.Surjective ev := by
    intro y
    refine ⟨(fun i => Pi.single (ν i) (y i), 0), ?_⟩
    funext i
    simp [ev]
  have hVdim : Module.finrank k V = n + 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ev
    rw [LinearMap.range_eq_top.mpr hev, finrank_top] at h1
    have h2 : Module.finrank k ((∀ i, Fin (d i + 1) → k) × k) = ∑ i, (d i + 1) + 1 := by
      simp [Module.finrank_prod, Module.finrank_pi_fintype]
    have h3 : ∑ i, (d i + 1) = n + Fintype.card ι := by
      rw [Finset.sum_add_distrib]
      simp [hn]
    rw [h2, Module.finrank_fintype_fun_eq_card, h3] at h1
    change Module.finrank k (LinearMap.ker ev) = n + 1
    omega
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    obtain ⟨⟨h, c⟩, hpv⟩ := p
    have hnu : ∀ i, h i (ν i) = 0 := fun i => by
      simpa [ev] using congrFun (LinearMap.mem_ker.mp hpv) i
    have hP0 : P (h, c) = 0 := by
      ext m
      rw [coeff_zero]
      by_cases hm : m ≤ n
      · have := congrFun hp ⟨m, Nat.lt_succ_of_le hm⟩
        simpa [L, T, Φ] using this
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hPdeg _) (by omega))
    have hsum : ∑ i, formPoly (h i) * ∏ j ∈ Finset.univ.erase i, formPoly (g j) =
        C (-c) * ∏ i, formPoly (g i) := by
      rw [C_neg, neg_mul, eq_neg_iff_add_eq_zero]
      exact hP0
    have hh0 := SurfaceBlowup.forms_linear_injective k ι d g hg hc ν hν h hnu (-c) hsum
    have hprod : ∏ i, formPoly (g i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ h0 => hg i (formPoly_eq_zero _ h0)
    obtain rfl : h = 0 := funext hh0
    have h3 : ∀ m : ℕ, formPoly (0 : Fin (m + 1) → k) = 0 := fun m => by simp [formPoly]
    obtain rfl : c = 0 := by simpa [P, h3, hprod] using hP0
    rfl
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hVdim, Module.finrank_fin_fun])).mp hL
  obtain ⟨⟨⟨h, c⟩, hpv⟩, hp⟩ := hsurj w
  refine ⟨h, c, fun i => by simpa [ev] using congrFun (LinearMap.mem_ker.mp hpv) i, ?_⟩
  · change formPoly w = P (h, c)
    ext m
    by_cases hm : m ≤ n
    · have := congrFun hp ⟨m, Nat.lt_succ_of_le hm⟩
      have h5 := coeff_formPoly w ⟨m, Nat.lt_succ_of_le hm⟩
      simp only at h5
      rw [h5, ← this]
      simp [L, T, Φ]
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_formPoly_le w) (by omega)),
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hPdeg _) (by omega))]

/-- Over a local ring, a monic factorization `B C = B' C'` with `B ≡ B'` and `B̄, C̄`
coprime is unique. -/
theorem hensel_factor_unique_of_dvd (O : Type) [CommRing O] [IsLocalRing O]
    (B C B' C' : Polynomial O) (hB : B.Monic) (hC : C.Monic) (hB' : B'.Monic) (hC' : C'.Monic)
    (hp : B * C = B' * C')
    (hred : B.map (IsLocalRing.residue O) = B'.map (IsLocalRing.residue O))
    (hc : IsCoprime (B.map (IsLocalRing.residue O)) (C.map (IsLocalRing.residue O))) :
    B = B' ∧ C = C' := by
  have hm := congrArg (Polynomial.map (IsLocalRing.residue O)) hp
  rw [Polynomial.map_mul, Polynomial.map_mul, ← hred] at hm
  have hne : B.map (IsLocalRing.residue O) ≠ 0 := (hB.map _).ne_zero
  have hCC : C.map (IsLocalRing.residue O) = C'.map (IsLocalRing.residue O) :=
    mul_left_cancel₀ hne hm
  exact SurfaceBlowup.hensel_pair_unique O B C B' C' hB hC hB' hC' hred hCC hc hp

/-- Over a local ring, a factorization into monic factors with pairwise coprime reductions
is determined by the reductions. -/
theorem hensel_family_unique (O ι : Type) [CommRing O] [IsLocalRing O] [Fintype ι]
    (G G' : ι → Polynomial O) (hG : ∀ i, (G i).Monic) (hG' : ∀ i, (G' i).Monic)
    (hred : ∀ i, (G i).map (IsLocalRing.residue O) = (G' i).map (IsLocalRing.residue O))
    (hc : ∀ i j, i ≠ j → IsCoprime ((G i).map (IsLocalRing.residue O))
      ((G j).map (IsLocalRing.residue O))) (hp : ∏ i, G i = ∏ i, G' i) :
    G = G' := by
  classical
  have key : ∀ s : Finset ι, ∏ i ∈ s, G i = ∏ i ∈ s, G' i → ∀ i ∈ s, G i = G' i := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ i hi; simp at hi
    | @insert a s ha ih =>
      intro h i hi
      rw [Finset.prod_insert ha, Finset.prod_insert ha] at h
      have hcop : IsCoprime ((G a).map (IsLocalRing.residue O))
          ((∏ j ∈ s, G j).map (IsLocalRing.residue O)) := by
        rw [Polynomial.map_prod]
        exact IsCoprime.prod_right fun j hj => hc a j (fun e => ha (e ▸ hj))
      have hmap : (∏ j ∈ s, G j).map (IsLocalRing.residue O)
          = (∏ j ∈ s, G' j).map (IsLocalRing.residue O) := by
        rw [Polynomial.map_prod, Polynomial.map_prod]
        exact Finset.prod_congr rfl fun j _ => hred j
      obtain ⟨h1, h2⟩ := SurfaceBlowup.hensel_pair_unique O (G a) (∏ j ∈ s, G j) (G' a)
        (∏ j ∈ s, G' j) (hG a) (Polynomial.monic_prod_of_monic _ _ fun j _ => hG j) (hG' a)
        (Polynomial.monic_prod_of_monic _ _ fun j _ => hG' j) (hred a) hmap hcop h
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h1
      · exact ih h2 i hi
  funext i
  exact key Finset.univ hp i (Finset.mem_univ i)

/-- If `τ i` are the iterates of a ring automorphism `τ 1` of `L` of period `δ`, whose fixed points
come from `ι : K → L`, then the orbit product `∏_{i<δ} p^{τ i}` of every polynomial descends
along `ι`. -/
private theorem orbit_product_lifts {K L : Type} [CommRing K] [CommRing L] (ι : K →+* L)
    (τ : ℕ → (L ≃+* L)) (δ : ℕ) (hτ0 : τ 0 = RingEquiv.refl L)
    (hrec : ∀ i : ℕ, τ (i+1) = (τ i).trans (τ 1)) (hτδ : ∀ z : L, τ δ z = z)
    (hfix : ∀ z : L, τ 1 z = z → ∃ y : K, ι y = z) (p : Polynomial L) :
    ∏ i : Fin δ, p.map (τ i).toRingHom ∈ Polynomial.lifts ι := by
  have hτδ' : τ δ = τ 0 := by
    ext z; rw [hτδ, hτ0]; rfl
  have hshift : ∀ i : Fin δ, (τ 1).toRingHom.comp (τ i).toRingHom = (τ (i.val + 1)).toRingHom :=
    fun i => by rw [hrec (i : ℕ)]; rfl
  -- the orbit product is `τ 1`-invariant: applying `τ 1` shifts the orbit cyclically
  have Pinv : (∏ i : Fin δ, p.map (τ i).toRingHom).map (τ 1).toRingHom =
      ∏ i : Fin δ, p.map (τ i).toRingHom := by
    simp only [Polynomial.map_prod, Polynomial.map_map, hshift]
    cases δ with
    | zero => simp
    | succ n =>
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ]
      simp only [Fin.val_castSucc, Fin.val_last, Fin.val_succ, Fin.val_zero]
      rw [hτδ', mul_comm]
  exact (Polynomial.lifts_iff_coeff_lifts _).2 fun n => hfix _ <| by
    simpa [Polynomial.coeff_map] using congrArg (Polynomial.coeff · n) Pinv

/-- A monic polynomial `H` over `K` is irreducible if `H.map ι` is the product of pairwise
distinct monic irreducible conjugates `g^{τ i}` of an irreducible `g ∣ H.map ι`, the `τ i` being
automorphisms fixing the image of `K`. -/
private theorem irreducible_of_map_eq_orbit_product {K L : Type} [Field K] [Field L]
    (ι : K →+* L) (hinj : Function.Injective ι) (τ : ℕ → (L ≃+* L))
    (hτι : ∀ (i : ℕ) (y : K), τ i (ι y) = ι y) {δ : ℕ} {g : Polynomial L} (hgi : Irreducible g)
    (hconj : ∀ i : Fin δ, (g.map (τ i).toRingHom).Monic ∧ Irreducible (g.map (τ i).toRingHom))
    (hdist : ∀ i j : Fin δ, g.map (τ i).toRingHom = g.map (τ j).toRingHom → i = j)
    {H : Polynomial K} (hHm : H.Monic) (hH : H.map ι = ∏ i : Fin δ, g.map (τ i).toRingHom)
    (hgdvd : g ∣ H.map ι) : Irreducible H := by
  have hcomp : ∀ i : ℕ, ((τ i).toRingHom.comp ι) = ι := fun i => RingHom.ext (hτι i)
  -- a factor `A` of `H` with `g ∣ A^ι` absorbs every conjugate, hence all of `H^ι`
  have key : ∀ A B, H = A * B → g ∣ A.map ι → IsUnit B := by
    intro A B hAB hg
    have hA : A ≠ 0 := by rintro rfl; exact hHm.ne_zero (by simp [hAB])
    have hB : B ≠ 0 := by rintro rfl; exact hHm.ne_zero (by simp [hAB])
    have hdvd : H.map ι ∣ A.map ι := by
      rw [hH]
      apply Fintype.prod_dvd_of_coprime
      · exact fun i j hij => distinct_monic_irreducible_coprime _ _ _ (hconj i).1 (hconj j).1
          (hconj i).2 (hconj j).2 fun he => hij (hdist i j he)
      · intro i
        have := Polynomial.map_dvd (τ i).toRingHom hg
        rwa [Polynomial.map_map, hcomp] at this
    have hle := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.map_ne_zero hA)
    rw [Polynomial.natDegree_map_eq_of_injective hinj,
      Polynomial.natDegree_map_eq_of_injective hinj, hAB, Polynomial.natDegree_mul hA hB] at hle
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hB]
    exact_mod_cast (by omega : B.natDegree = 0)
  refine ⟨fun hu => hgi.not_isUnit (isUnit_of_dvd_unit hgdvd ((Polynomial.isUnit_map ι).2 hu)),
    fun A B hAB => ?_⟩
  have : g ∣ A.map ι * B.map ι := by rw [← Polynomial.map_mul, ← hAB]; exact hgdvd
  rcases hgi.prime.dvd_or_dvd this with h | h
  · exact Or.inr (key A B hAB h)
  · exact Or.inl (key B A (by rw [hAB, mul_comm]) h)

/-- The Frobenius orbit products of the irreducible factors of `F` descend to distinct monic
irreducible polynomials over `Frac O` whose product is the conjugate product of `F`. -/
theorem invariant_orbit_factors (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) [IsDomain (AdjoinRoot Φ)]
    (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
    (τ : ℕ → (BaseField (AdjoinRoot Φ) ≃+* BaseField (AdjoinRoot Φ)))
    (hτ : ∀ (i : ℕ) (x : AdjoinRoot Φ), τ i
      (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) x) = algebraMap (AdjoinRoot Φ)
      (BaseField (AdjoinRoot Φ)) (frobeniusIter O Φ i x))
    (hτι : ∀ (i : ℕ) (y : BaseField O), τ i (ι y) = ι y)
    (hτ0 : τ 0 = RingEquiv.refl (BaseField (AdjoinRoot Φ)))
    (hrec : ∀ i : ℕ, τ (i+1) = (τ i).trans (τ 1))
    (hτδ : ∀ z : BaseField (AdjoinRoot Φ), τ Φ.natDegree z = z)
    (hfix : ∀ z : BaseField (AdjoinRoot Φ), τ 1 z = z → ∃ y : BaseField O, ι y = z)
    (hinj : Function.Injective ι) (F : Polynomial (AdjoinRoot Φ))
    (gs : List (Polynomial (BaseField (AdjoinRoot Φ)))) (hgs : ∀ g ∈ gs, g.Monic ∧ Irreducible g)
    (hd : gs.Pairwise (fun g h => g ≠ h))
    (hprod : F.map (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))) = gs.prod)
    (hcop : ∀ i j : Fin Φ.natDegree, i ≠ j → IsCoprime
      ((fun i : Fin Φ.natDegree => (F.map (frobeniusIter O Φ i).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) i)
      ((fun i : Fin Φ.natDegree => (F.map (frobeniusIter O Φ i).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) j)) :
    ∃ H : Fin gs.length → Polynomial (BaseField O), (∀ a, (H a).Monic ∧ Irreducible (H a)) ∧
      Function.Injective H ∧
      (∀ a, (H a).map ι = ∏ i : Fin Φ.natDegree, (gs.get a).map (τ i).toRingHom) ∧
      (∀ a, (H a).natDegree = Φ.natDegree * (gs.get a).natDegree) ∧ (∏ a, H a).map ι =
      (conjugateProduct O Φ F).map (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))) := by
  obtain ⟨h1, h2, _h3, h4⟩ := SurfaceBlowup.conjugate_irreducible_factors_distinct O Φ τ hτ
    F gs hgs hd hprod hcop
  -- positivity of δ
  have hδ : 0 < Φ.natDegree := Nat.pos_of_ne_zero fun h0 => hΦ.2.not_isUnit <| by
    rw [residuePoly, eq_one_of_monic_natDegree_zero (hΦ.1.map _) (by rw [hΦ.1.natDegree_map, h0])]
    exact isUnit_one
  set δ := Φ.natDegree with hδdef
  -- orbit product
  let P : Polynomial (BaseField (AdjoinRoot Φ)) → Polynomial (BaseField (AdjoinRoot Φ)) :=
    fun p => ∏ i : Fin δ, p.map (τ i).toRingHom
  have Plifts : ∀ p, P p ∈ Polynomial.lifts ι := orbit_product_lifts ι τ δ hτ0 hrec hτδ hfix
  choose H hH using fun a : Fin gs.length => Polynomial.mem_lifts _ |>.mp (Plifts (gs.get a))
  have gmem : ∀ a : Fin gs.length, gs.get a ∈ gs := fun a => List.get_mem gs a
  have gmon : ∀ a, (gs.get a).Monic := fun a => (hgs _ (gmem a)).1
  have girr : ∀ a, Irreducible (gs.get a) := fun a => (hgs _ (gmem a)).2
  have Pmon : ∀ a, (P (gs.get a)).Monic := fun a =>
    Polynomial.monic_prod_of_monic _ _ fun (i : Fin δ) _ => (h1 i _ (gmon a) (girr a)).1
  have Pdeg : ∀ a, (P (gs.get a)).natDegree = δ * (gs.get a).natDegree := by
    intro a
    simp only [P]
    rw [Polynomial.natDegree_prod_of_monic (h := fun (i : Fin δ) _ => (h1 i _ (gmon a) (girr a)).1)]
    simp [Polynomial.natDegree_map]
  have Hmon : ∀ a, (H a).Monic := fun a =>
    Polynomial.monic_of_injective hinj (by rw [hH a]; exact Pmon a)
  have Hdeg : ∀ a, (H a).natDegree = δ * (gs.get a).natDegree := by
    intro a
    rw [← Pdeg a, ← hH a, Polynomial.natDegree_map_eq_of_injective hinj]
  have hτ0' : ∀ p : Polynomial (BaseField (AdjoinRoot Φ)), p.map (τ 0).toRingHom = p :=
    fun p => by simp [hτ0]
  have gdvdP : ∀ a, gs.get a ∣ P (gs.get a) := fun a => by
    have h := Finset.dvd_prod_of_mem (fun i : Fin δ => (gs.get a).map (τ i).toRingHom)
      (Finset.mem_univ (⟨0, hδ⟩ : Fin δ))
    rwa [Fin.val_mk, hτ0'] at h
  refine ⟨H, fun a => ⟨Hmon a, ?_⟩, ?_, hH, Hdeg, ?_⟩
  · -- irreducibility
    exact irreducible_of_map_eq_orbit_product ι hinj τ hτι (girr a)
      (fun i => h1 i _ (gmon a) (girr a)) (fun i j he => (h2 i j a a he).1) (Hmon a) (hH a)
      (by rw [hH a]; exact gdvdP a)
  · -- injectivity
    intro a b hab
    have : gs.get a ∣ P (gs.get b) := by
      rw [← hH b, ← hab, hH a]; exact gdvdP a
    obtain ⟨i, -, hi⟩ := ((girr a).prime).exists_mem_finset_dvd this
    have hm := h1 i _ (gmon b) (girr b)
    have heq := Polynomial.eq_of_monic_of_associated (gmon a) hm.1
      ((girr a).associated_of_dvd hm.2 hi)
    exact (h2 ⟨0, hδ⟩ i a b (by rw [Fin.val_mk, hτ0']; exact heq)).2
  · -- product
    rw [h4, Polynomial.map_prod]
    simp only [hH, P]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← Fin.prod_univ_fun_getElem]
    rfl

/-- An algebra isomorphism of local rings identifies the maximal ideals (via `comap` and `map`). -/
theorem local_algEquiv_maximalIdeal (O B B' : Type) [CommRing O] [CommRing B] [CommRing B']
    [IsLocalRing B] [IsLocalRing B'] [Algebra O B] [Algebra O B'] (φ : B ≃ₐ[O] B') :
    (IsLocalRing.maximalIdeal B').comap (φ : B →+* B') = IsLocalRing.maximalIdeal B ∧
      (IsLocalRing.maximalIdeal B).map (φ : B →+* B') = IsLocalRing.maximalIdeal B' := by
  have h1 : (IsLocalRing.maximalIdeal B').comap (φ : B →+* B') = IsLocalRing.maximalIdeal B := by
    have : IsLocalHom (φ : B →+* B') := ⟨fun a ha => by simpa using ha.map φ.symm⟩
    exact IsLocalRing.maximalIdeal_comap _
  refine ⟨h1, ?_⟩
  rw [← h1]
  exact Ideal.map_comap_of_surjective _ φ.surjective _

end SurfaceBlowup
