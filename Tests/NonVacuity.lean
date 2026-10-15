/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Main
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Separation.Lemmas

/-!
# Non-vacuity of the hypotheses of `main_dvr`

The hypotheses of `SurfaceBlowup.main_dvr` are satisfiable in equal characteristic: for a finite
field `k` with the discrete topology, the power series ring `k⟦X⟧` with Mathlib's coefficientwise
(pi) topology is a complete discrete valuation ring with finite residue field `k`, a compact
Hausdorff second-countable topological ring whose topology is the `(X)`-adic one. Equipping it with
the Borel σ-algebra, `main_dvr` applies and gives the type densities of polynomials over `𝔽_q⟦X⟧`.

## Main results

* `SurfaceBlowup.Tests.isAdic_maximalIdeal_powerSeries`: the pi topology on `k⟦X⟧` is `(X)`-adic.
* `SurfaceBlowup.Tests.main_dvr_powerSeries`: `main_dvr` for `k⟦X⟧`, with `q = |k|`.
* `SurfaceBlowup.Tests.main_dvr_zmod`, `SurfaceBlowup.Tests.main_dvr_galoisField`: the explicit
  cases `𝔽_p⟦X⟧` (`q = p`) and `𝔽_{p^m}⟦X⟧` (`q = p^m`).

Provenance: port of the independent certificate `Monolith/NonVacuityExample.lean` (monolith_gen).
-/

open PowerSeries IsLocalRing Topology Filter
open scoped PowerSeries.WithPiTopology

namespace SurfaceBlowup.Tests

section FiniteField

variable (k : Type) [Field k] [TopologicalSpace k] [DiscreteTopology k]

/-- `k⟦X⟧` is complete for its maximal ideal `(X)`. -/
instance : IsAdicComplete (maximalIdeal k⟦X⟧) k⟦X⟧ := by
  rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance

/-- The residue field of `k⟦X⟧` is `k`, hence finite when `k` is. -/
instance [Finite k] : Finite (ResidueField k⟦X⟧) :=
  .of_equiv k (residueFieldOfPowerSeries (k := k)).symm.toEquiv

/-- Tychonoff: `k⟦X⟧ = k^ℕ` is compact for finite discrete `k`. -/
instance [Finite k] : CompactSpace k⟦X⟧ := inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → k))

/-- A countable product of finite discrete spaces is second countable. -/
instance [Finite k] : SecondCountableTopology k⟦X⟧ :=
  inferInstanceAs (SecondCountableTopology ((Unit →₀ ℕ) → k))

/-- The Borel σ-algebra on `k⟦X⟧`. -/
instance : MeasurableSpace k⟦X⟧ := borel _

/-- The Borel σ-algebra makes `k⟦X⟧` a Borel space. -/
instance : BorelSpace k⟦X⟧ := ⟨rfl⟩

omit [TopologicalSpace k] [DiscreteTopology k] in
private theorem mem_span_X_pow_iff (n : ℕ) (φ : k⟦X⟧) :
    φ ∈ Ideal.span {(X : k⟦X⟧)} ^ n ↔ ∀ m < n, coeff m φ = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, X_pow_dvd_iff]

/-- The pi topology on `k⟦X⟧` is the `(X)`-adic topology. -/
theorem isAdic_maximalIdeal_powerSeries : IsAdic (maximalIdeal k⟦X⟧) := by
  rw [PowerSeries.maximalIdeal_eq_span_X, isAdic_iff]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · have : ((Ideal.span {(X : k⟦X⟧)} ^ n : Ideal k⟦X⟧) : Set k⟦X⟧) =
        ⋂ m ∈ Finset.range n, coeff (R := k) m ⁻¹' {0} := by
      ext φ; simp [mem_span_X_pow_iff]
    rw [this]
    exact isOpen_biInter_finset fun m _ ↦
      (WithPiTopology.continuous_coeff k m).isOpen_preimage _ (isOpen_discrete _)
  · have hs' : s ∈ Filter.pi fun _ : Unit →₀ ℕ ↦ 𝓝 (0 : k) := by
      rw [← nhds_pi]; exact hs
    obtain ⟨I, hI, t, ht, hIt⟩ := Filter.mem_pi.mp hs'
    refine ⟨hI.toFinset.sup (fun d ↦ d ()) + 1, fun φ hφ ↦ hIt (Set.mem_pi.mpr fun d hd ↦ ?_)⟩
    have h0 : (0 : k) ∈ t d := mem_pure.mp (nhds_discrete k ▸ ht d)
    have hcoef : coeff (d ()) φ = 0 := (mem_span_X_pow_iff k _ φ).mp hφ _
      (Nat.lt_succ_of_le (Finset.le_sup (f := fun d : Unit →₀ ℕ ↦ d ()) (hI.mem_toFinset.mpr hd)))
    have hφd : φ d = coeff (d ()) φ := by rw [coeff_def rfl]; rfl
    change φ d ∈ t d
    rwa [hφd, hcoef]

/-- `main_dvr` instantiated at `O = k⟦X⟧` for a finite field `k` with the discrete topology: the
type densities of monic polynomials and primitive binary forms over `k⟦X⟧` are the universal
expressions evaluated at `q = |k|`. -/
theorem main_dvr_powerSeries [Finite k] (n : ℕ) (σ : FactorType) :
    monicDensity k⟦X⟧ n σ = densityValue (monicExpr n σ) (Nat.card k) ∧
      projectiveDensity k⟦X⟧ n σ = densityValue (projectiveExpr n σ) (Nat.card k) := by
  rw [← Nat.card_congr (residueFieldOfPowerSeries (k := k)).toEquiv]
  exact main_dvr k⟦X⟧ (isAdic_maximalIdeal_powerSeries k) n σ

end FiniteField

section Concrete

/-- The discrete topology on `GaloisField p m`. -/
instance (p m : ℕ) [Fact p.Prime] : TopologicalSpace (GaloisField p m) := ⊥

/-- The topology `⊥` on `GaloisField p m` is discrete. -/
instance (p m : ℕ) [Fact p.Prime] : DiscreteTopology (GaloisField p m) := ⟨rfl⟩

/-- Densities over `𝔽_p⟦X⟧`: the universal expressions evaluated at `q = p`. -/
theorem main_dvr_zmod (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (σ : FactorType) :
    monicDensity (ZMod p)⟦X⟧ n σ = densityValue (monicExpr n σ) p ∧
      projectiveDensity (ZMod p)⟦X⟧ n σ = densityValue (projectiveExpr n σ) p := by
  simpa using main_dvr_powerSeries (ZMod p) n σ

/-- Densities over `𝔽_{p^m}⟦X⟧` (`GaloisField p m`, `m ≠ 0`): the universal expressions evaluated
at `q = p^m`. -/
theorem main_dvr_galoisField (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m ≠ 0) (n : ℕ)
    (σ : FactorType) :
    monicDensity (GaloisField p m)⟦X⟧ n σ = densityValue (monicExpr n σ) (p ^ m) ∧
      projectiveDensity (GaloisField p m)⟦X⟧ n σ = densityValue (projectiveExpr n σ) (p ^ m) := by
  simpa [GaloisField.card p m hm] using main_dvr_powerSeries (GaloisField p m) n σ

end Concrete

end SurfaceBlowup.Tests

#print axioms SurfaceBlowup.Tests.main_dvr_zmod
#print axioms SurfaceBlowup.Tests.main_dvr_galoisField
