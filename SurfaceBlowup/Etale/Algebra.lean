/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import Mathlib.RingTheory.Etale.StandardEtale
import SurfaceBlowup.Etale.Main

/-!
# The étale monic density in algebra language

The étale-convention monic density, with the event phrased through algebras: the `K`-algebra
`K[X]/(f_a)` is étale (`Algebra.Etale`) and the `O`-algebra `O[X]/(f_a)` has algebra type `σ`
(`HasAlgebraType`: its generic fibre is a product of fields with the invariants `σ`).

## Main results

* `SurfaceBlowup.etale_adjoinRoot_of_separable`
* `SurfaceBlowup.etaleMonicDensity_eq_algebraType`
-/

open MeasureTheory Polynomial
open scoped ENNReal

namespace SurfaceBlowup

/-- For a monic separable polynomial `f` over a field `K`, the algebra `K[X]/(f)` is étale. -/
theorem etale_adjoinRoot_of_separable {K : Type} [Field K] (f : K[X]) (hm : f.Monic)
    (hs : f.Separable) : Algebra.Etale K (AdjoinRoot f) := by
  obtain ⟨u, v, huv⟩ := hs
  let P : StandardEtalePair K := ⟨f, hm, 1, ⟨v, u, 0, by rw [pow_zero, ← huv]; ring⟩⟩
  have hu : IsUnit (AdjoinRoot.mk f (1 : K[X])) := by rw [map_one]; exact isUnit_one
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (AdjoinRoot f) (Localization.Away (AdjoinRoot.mk f 1)) _
      hu).symm.restrictScalars K))

/-- The étale monic density, with the event "the algebra `K[X]/(f_a)` is étale and `O[X]/(f_a)`
has algebra type `σ`". -/
theorem etaleMonicDensity_eq_algebraType (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    etaleMonicDensity O n σ = coefficientMeasure O n
      {a | Algebra.Etale (BaseField O) (AdjoinRoot (monicPolynomial O a)) ∧
        HasAlgebraType O (AdjoinRoot (monicPolyO a)) σ} := by
  refine measure_congr <| (measure_eq_zero_iff_ae_notMem.1 (monic_inseparable_null O htop n)).mono
    fun a ha => ?_
  have hs : (monicPolynomial O a).Separable := not_not.1 ha
  have hm := (monic_poly_reconstruct O n a).1
  have ht : HasAlgebraType O (AdjoinRoot (monicPolyO a)) σ ↔
      HasPolynomialType O (monicPolynomial O a) σ := by
    rw [← polynomial_type_iff_algebra_type O _ hm, monicPolyO_map_fraction]
    exact hasPolynomialTypeF_iff_of_separable O hs
  refine propext ⟨fun h => ⟨etale_adjoinRoot_of_separable _
    (monic_polynomial_degree O n a).1 hs, ht.2 h.2⟩, fun h => ⟨hs, ht.1 h.2⟩⟩

end SurfaceBlowup
