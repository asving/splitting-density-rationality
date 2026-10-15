/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Basic

/-!
# Closed points and divisors on the exceptional line

For a field `k`, the closed points of the exceptional line `ℙ¹_k` (monic irreducible polynomials
plus the point at infinity), effective divisors on it with their degree and affine polynomial,
the boundary directions of a state and the divisors with a given tangent pattern. These are
elementary definitions, kept apart from the blow-up charts so that counting divisors does not
depend on the chart constructions.

## Main results

* `SurfaceBlowup.count_normalizedFactors_divisorAffinePolynomial`: multiplicities in the affine
  polynomial of a divisor.

Provenance: `Def_SurfaceBlowupV2_{ClosedDirections, DivisorPatterns}`;
`Thm_SurfaceBlowupV2_{count_normalizedFactors_divisorAffinePolynomial}` (moved from
`Blowup/Charts.lean`).
-/

noncomputable section

namespace SurfaceBlowup

/-! ### Closed points and divisors on the exceptional line -/

section
variable (k : Type) [Field k]
/-- Affine closed points of the exceptional line over `k`: monic irreducible polynomials. -/
abbrev AffineDirection := {phi : Polynomial k // phi.Monic ∧ Irreducible phi}
/-- Closed points of the exceptional line `ℙ¹_k`: affine points plus the point at infinity. -/
abbrev ClosedDirection := Option (AffineDirection k)
/-- The residue degree of a closed point of `ℙ¹_k` (`1` at infinity). -/
def directionDegree : ClosedDirection k → ℕ
  | none => 1
  | some phi => phi.val.natDegree
/-- The point at infinity of the exceptional line. -/
def infinityDirection : ClosedDirection k := none
/-- The affine point `Z = 0` of the exceptional line. -/
def zeroDirection : ClosedDirection k :=
  some ⟨Polynomial.X, Polynomial.monic_X, Polynomial.irreducible_X⟩
/-- Effective divisors on the exceptional line `ℙ¹_k`. -/
abbrev ExceptionalDivisor := ClosedDirection k →₀ ℕ
/-- The degree `Σ deg(P)·D(P)` of an effective divisor on `ℙ¹_k`. -/
def exceptionalDegree (D : ExceptionalDivisor k) : ℕ :=
  D.sum fun P r => directionDegree k P * r
/-- The monic polynomial `Π φ^{D(φ)}` over the affine points of a divisor `D`. -/
def divisorAffinePolynomial (D : ExceptionalDivisor k) : Polynomial k :=
  D.prod fun P r => match P with | none => 1 | some phi => phi.val ^ r
/-- The nonzero dehomogenized form `H` of degree `≤ d` has divisor `D` on `ℙ¹_k`
(its affine part is `divisorAffinePolynomial D`, the multiplicity at infinity is `d − deg H`). -/
def HasHomogeneousDivisor (d : ℕ) (H : Polynomial k) (D : ExceptionalDivisor k) : Prop :=
  H ≠ 0 ∧ H.natDegree ≤ d ∧ D none = d - H.natDegree ∧
    H = Polynomial.C H.leadingCoeff * divisorAffinePolynomial k D
end

/-- The affine direction `Z`. -/
def zeroAffine (k : Type) [Field k] : AffineDirection k :=
  ⟨Polynomial.X, Polynomial.monic_X, Polynomial.irreducible_X⟩

/-! ### Divisor patterns -/

section
variable (k : Type) [Field k]
/-- The boundary points of the exceptional line: the old t-boundary is the direction at infinity;
at a crossing the old x-boundary is the direction Z = 0 as well (N184: on the t-chart z = x/t,
t = 0 is infinity and x = 0 is zeroDirection). -/
def boundaryDirections (s : State) : Set (ClosedDirection k) :=
  match s with
  | .single _ _ => {infinityDirection k}
  | .crossing _ _ _ _ => {infinityDirection k, zeroDirection k}
/-- `HasPattern k s D P`: the effective divisor D on the exceptional line has degree P.d,
multiplicity P.rt at the t-boundary (infinity), multiplicity P.rx at the x-boundary (only at a
crossing), and for every (δ, r) exactly P.other (δ−1, r−1) nonboundary closed points of degree δ
and multiplicity r. -/
def HasPattern (s : State) (D : ExceptionalDivisor k) (P : TangentPattern s.degree) : Prop :=
  exceptionalDegree k D = P.d.val ∧ D (infinityDirection k) = P.rt.val ∧
  (match s with
   | .single _ _ => True
   | .crossing _ _ _ _ => D (zeroDirection k) = P.rx.val) ∧
  ∀ ij : Fin s.degree × Fin s.degree,
    Nat.card {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧
      directionDegree k Q = ij.1.val + 1 ∧ D Q = ij.2.val + 1} = (P.other ij).val
/-- The divisors of the pattern P, as a type. -/
abbrev patternDivisors (s : State) (P : TangentPattern s.degree) : Type :=
  {D : ExceptionalDivisor k // HasPattern k s D P}
end

/-! ### Support of a divisor -/

section
variable {k : Type} [Field k]
/-- The closed points of the exceptional line carrying positive multiplicity in `Dv` (N184). -/
def divisorSupport (Dv : ExceptionalDivisor k) : Type := {Q : ClosedDirection k // 0 < Dv Q}
/-- The support of an effective divisor is finite. -/
instance divisorSupport_finite (Dv : ExceptionalDivisor k) : Finite (divisorSupport Dv) :=
  Finite.of_injective (fun Q : divisorSupport Dv =>
      (⟨Q.val, Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp Q.property)⟩ : Dv.support))
    (fun _ _ h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h')
end

/-! ### Exceptional divisors -/

open scoped Classical in
/-- The multiplicity of an affine direction `φ` in `c · divisorAffinePolynomial Dv` is `Dv φ`;
in particular `φ` divides it iff `Dv φ > 0`. -/
theorem count_normalizedFactors_divisorAffinePolynomial (k : Type) [Field k]
    (Dv : ExceptionalDivisor k) (lc : k) (hlc : lc ≠ 0) (φ : AffineDirection k) :
    Multiset.count φ.val (UniqueFactorizationMonoid.normalizedFactors
        (Polynomial.C lc * divisorAffinePolynomial k Dv)) = Dv (some φ) ∧
        (φ.val ∣ divisorAffinePolynomial k Dv ↔ 0 < Dv (some φ)) := by
  set g : ClosedDirection k → ℕ → Polynomial k :=
    fun P r => match P with | none => 1 | some phi => phi.val ^ r with hg
  have hg0 : ∀ P, g P 0 = 1 := by intro P; cases P <;> simp [hg]
  set r := Dv (some φ) with hr
  set Q := (Dv.erase (some φ)).prod g with hQ
  have hG : divisorAffinePolynomial k Dv = φ.val ^ r * Q :=
    (Finsupp.mul_prod_erase' Dv (some φ) g hg0).symm
  have hirr : Irreducible φ.val := φ.2.2
  have hprime : Prime φ.val := hirr.prime
  have hnQ : ¬ φ.val ∣ Q := by
    intro h
    rw [hQ, Finsupp.prod, hprime.dvd_finsetProd_iff] at h
    obtain ⟨P, hP, hd⟩ := h
    have hPne : P ≠ some φ := by rintro rfl; simp at hP
    cases P with
    | none => exact hirr.not_isUnit (isUnit_of_dvd_unit hd isUnit_one)
    | some ψ =>
      exact hPne (congrArg some (Subtype.ext (Polynomial.eq_of_monic_of_associated φ.2.1 ψ.2.1
        (hirr.associated_of_dvd ψ.2.2 (hprime.dvd_of_dvd_pow hd)))).symm)
  refine ⟨?_, ?_⟩
  · apply UniqueFactorizationMonoid.count_normalizedFactors_eq hirr (φ.2.1.normalize_eq_self)
    · rw [hG]; exact Dvd.intro (Polynomial.C lc * Q) (by ring)
    · rintro ⟨c, hc⟩
      rw [hG, pow_succ, mul_assoc] at hc
      have h3 : φ.val ∣ Polynomial.C lc * Q :=
        ⟨c, mul_left_cancel₀ (pow_ne_zero r hirr.ne_zero) (by rw [← hc]; ring)⟩
      rcases hprime.dvd_or_dvd h3 with h | h
      · exact hirr.not_isUnit (isUnit_of_dvd_unit h (Polynomial.isUnit_C.mpr
          (isUnit_iff_ne_zero.mpr hlc)))
      · exact hnQ h
  · refine ⟨fun h ↦ Nat.pos_of_ne_zero fun h0 ↦ hnQ ?_,
      fun h ↦ hG ▸ dvd_mul_of_dvd_left (dvd_pow_self _ h.ne') _⟩
    rwa [hG, h0, pow_zero, one_mul] at h

end SurfaceBlowup
