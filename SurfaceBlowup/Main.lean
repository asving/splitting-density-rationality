/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Assembly.Formulas
import SurfaceBlowup.Reciprocity.Main

/-!
# Main theorems

* `SurfaceBlowup.main_dvr`: for every complete discrete valuation ring `O` with finite residue
  field `k` (any characteristic, any ramification), the monic and projective type densities are the
  values at `q = |k|` of the universal rational expressions `monicExpr n σ`, `projectiveExpr n σ`.
* `SurfaceBlowup.main_field_form`: the rational-function form, for the rings of integers of
  unramified finite extensions `K/ℚ_p` (the published statement).
* `SurfaceBlowup.main_field_form_ramified`: the same for arbitrary finite `K/ℚ_p`.
* `SurfaceBlowup.recip_main` (in `SurfaceBlowup.Reciprocity.Main`): the reciprocity law
  `A_n(q) = B_n(1/q)`, `R_n(1/q) = R_n(q)` of the rational functions.

The densities are the original definitions `monicDensity`, `projectiveDensity` of
`SurfaceBlowup.Basic`; the proof runs on the route-F densities `monicDensityF`, `projectiveDensityF`
(`Assembly.Formulas`) and transfers along the Haar-null bridges `orig_monicDensity_eq`,
`orig_projectiveDensity_eq` (`Assembly.NullBridges`).
-/

open scoped ENNReal

namespace SurfaceBlowup

/-- **Main theorem.** Let `O` be a complete discrete valuation ring with finite residue field `k`
(any characteristic, any ramification), with its maximal-ideal-adic compact topology, Borel
σ-algebra and normalized Haar measure. For every degree `n` and every factorization type `σ`,
the probability that a random monic polynomial of degree `n` over `O` (resp. a random primitive
binary form of degree `n`) has type `σ` is the value at `q = |k|` of the universal rational
expression `monicExpr n σ` (resp. `projectiveExpr n σ`).

The statement carries no hypotheses on `n` and `σ`: the certified form assumed `0 < n`,
`ValidType σ` and `typeDegree σ = n`, none of which the proof uses. -/
theorem main_dvr (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O))
    (n : ℕ) (σ : FactorType) :
    SurfaceBlowup.monicDensity O n σ =
        densityValue (monicExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) ∧
    SurfaceBlowup.projectiveDensity O n σ =
        densityValue (projectiveExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) := by
  rw [orig_monicDensity_eq O htop, orig_projectiveDensity_eq O htop]
  exact ⟨monicDensityF_eq_densityValue O htop n σ, projectiveDensityF_eq_densityValue O htop n σ⟩

/-- **Field form** (unramified `K/ℚ_p`): the densities are values of explicit rational functions
`A = (monicExpr n σ).rational`, `R = (projectiveExpr n σ).rational`, regular at every prime power,
evaluated at the residue cardinality of the ring of integers. -/
theorem main_field_form (n : ℕ) (σ : FactorType) :
    ∃ A R : RatFunc ℚ, A = (monicExpr n σ).rational ∧ R = (projectiveExpr n σ).rational ∧
      (∀ q : ℕ, PrimePower q → RegularAt A q ∧ RegularAt R q) ∧
      (∀ q : ℕ, PrimePower q → RatFunc.eval (RingHom.id ℚ) q A = (monicExpr n σ).eval q ∧
        RatFunc.eval (RingHom.id ℚ) q R = (projectiveExpr n σ).eval q) ∧
      ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
        [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
        [TopologicalSpace (padicIntegers p K)] [IsTopologicalRing (padicIntegers p K)]
        [CompactSpace (padicIntegers p K)] [T2Space (padicIntegers p K)]
        [SecondCountableTopology (padicIntegers p K)] [MeasurableSpace (padicIntegers p K)]
        [BorelSpace (padicIntegers p K)],
        PadicUnramified p K → IsAdic (Ideal.span {(p : padicIntegers p K)}) →
          monicDensity (padicIntegers p K) n σ = densityValue (monicExpr n σ)
            (Nat.card (padicIntegers p K ⧸ Ideal.span {(p : padicIntegers p K)})) ∧
          projectiveDensity (padicIntegers p K) n σ = densityValue (projectiveExpr n σ)
            (Nat.card (padicIntegers p K ⧸ Ideal.span {(p : padicIntegers p K)})) ∧
          monicDensity (padicIntegers p K) n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
            ((Nat.card (padicIntegers p K ⧸ Ideal.span {(p : padicIntegers p K)}) : ℕ) : ℚ) A :
              ℚ) : ℝ) ∧
          projectiveDensity (padicIntegers p K) n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
            ((Nat.card (padicIntegers p K ⧸ Ideal.span {(p : padicIntegers p K)}) : ℕ) : ℚ) R :
              ℚ) : ℝ) := by
  refine ⟨_, _, rfl, rfl, global_formula_regular n σ, global_rational_eval n σ, ?_⟩
  intro p _ K _ _ _ _ _ _ _ _ _ _ _ _ hun had
  have hdvr := padicIntegers_isDVR p K
  have := padicIntegers_maximal_adic_complete p K hdvr
  have := padicIntegers_residueField_finite p K hdvr
  have hmax : IsLocalRing.maximalIdeal (padicIntegers p K) = Ideal.span {(p : padicIntegers p K)} :=
    hun.maximalIdeal_eq
  have hcard : Nat.card (IsLocalRing.ResidueField (padicIntegers p K)) =
      Nat.card (padicIntegers p K ⧸ Ideal.span {(p : padicIntegers p K)}) :=
    Nat.card_congr (Ideal.quotEquivOfEq hmax).toEquiv
  obtain ⟨h1, h2⟩ := main_dvr (padicIntegers p K) (hmax ▸ had) n σ
  rw [hcard] at h1 h2
  obtain ⟨e1, e2⟩ := global_rational_eval n σ _ (hcard ▸ finite_field_card_primePower _)
  exact ⟨h1, h2, by rw [h1, e1], by rw [h2, e2]⟩

/-- **Field form, arbitrary finite `K/ℚ_p`** (ramified allowed): with the maximal-ideal-adic compact
topology on the ring of integers `𝒪_K = padicIntegers p K`, the monic and projective type densities
are the values at `q = |𝒪_K/𝔪|` of the rational functions `(monicExpr n σ).rational`,
`(projectiveExpr n σ).rational`. -/
theorem main_field_form_ramified (n : ℕ) (σ : FactorType) (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K]
    [TopologicalSpace (padicIntegers p K)] [IsTopologicalRing (padicIntegers p K)]
    [CompactSpace (padicIntegers p K)] [T2Space (padicIntegers p K)]
    [SecondCountableTopology (padicIntegers p K)] [MeasurableSpace (padicIntegers p K)]
    [BorelSpace (padicIntegers p K)]
    (had : letI := padicIntegers_isDVR p K; IsAdic (IsLocalRing.maximalIdeal (padicIntegers p K))) :
    letI := padicIntegers_isDVR p K
    monicDensity (padicIntegers p K) n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
        (Nat.card (IsLocalRing.ResidueField (padicIntegers p K)) : ℚ) (monicExpr n σ).rational :
          ℚ) : ℝ) ∧
      projectiveDensity (padicIntegers p K) n σ = ENNReal.ofReal ((RatFunc.eval (RingHom.id ℚ)
        (Nat.card (IsLocalRing.ResidueField (padicIntegers p K)) : ℚ)
          (projectiveExpr n σ).rational : ℚ) : ℝ) := by
  let hdvr := padicIntegers_isDVR p K
  have := padicIntegers_maximal_adic_complete p K hdvr
  have := padicIntegers_residueField_finite p K hdvr
  obtain ⟨h1, h2⟩ := main_dvr (padicIntegers p K) had n σ
  obtain ⟨e1, e2⟩ := global_rational_eval n σ _
    (finite_field_card_primePower (IsLocalRing.ResidueField (padicIntegers p K)))
  exact ⟨by rw [h1, e1], by rw [h2, e2]⟩

end SurfaceBlowup
