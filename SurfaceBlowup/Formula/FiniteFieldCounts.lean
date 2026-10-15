/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Surfaces.PowerSeries

/-!
# Counting over finite fields

Elementary counts: the number of monic irreducible polynomials of degree `δ` over a finite field
is the point-count polynomial at `#k`; the cardinality of a finite field is a prime power; and a
module of length `ℓ` over a local ring with finite residue field `k` has `|k|^ℓ` elements.

## Main results

* `SurfaceBlowup.finite_field_irreducible_count`
* `SurfaceBlowup.finite_field_card_primePower`
* `SurfaceBlowup.finite_length_module_card`

Provenance: `Thm_SurfaceBlowupV2_{finite_field_irreducible_count, finite_field_card_primePower,
finite_length_module_card}` (moved from `Unramified/LocalDescent.lean` and
`Blowup/CurveOrders.lean`).
-/

namespace SurfaceBlowup

/-- The number of monic irreducible polynomials of degree `δ > 0` over a finite field `k` is the
value of the point-count polynomial `pointCount δ` at `#k`. -/
theorem finite_field_irreducible_count (k : Type) [Field k] [Finite k] (δ : ℕ) (hδ : 0 < δ) :
    ((Nat.card {g : Polynomial k // g.Monic ∧ Irreducible g
      ∧ g.natDegree = δ} : ℕ) : ℚ) = (pointCount δ).eval (Nat.card k) := by
  rw [pointCount_eval, ← irreducible_count_moebius k δ hδ]
  have : (δ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hδ.ne'
  field_simp

/-- The cardinality of a finite field is a prime power. -/
theorem finite_field_card_primePower (K : Type) [Field K] [Finite K] :
    PrimePower (Nat.card K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
  exact ⟨p, n, hp, n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

/-- A module of length `ℓ` over a local ring with finite residue field `k` has `|k|^ℓ`
elements. -/
theorem finite_length_module_card (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (M : Type) [AddCommGroup M] [Module O M] (ℓ : ℕ)
    (hℓ : Module.length O M = ℓ) :
    Nat.card M = (Nat.card (IsLocalRing.ResidueField O))^ℓ := by
  induction ℓ generalizing M with
  | zero =>
    have : Subsingleton M := Module.length_eq_zero_iff.mp (by simpa using hℓ)
    simp
  | succ n ih =>
    have hfin : IsFiniteLength O M := Module.length_ne_top_iff.mp
        (by rw [hℓ]; exact ENat.natCast_ne_top _)
    have hA : IsArtinian O M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
    have hnt : Nontrivial M := Module.length_pos_iff.mp (by rw [hℓ]; exact_mod_cast Nat.succ_pos n)
    have : IsAtomic (Submodule O M) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule O M)).resolve_left top_ne_bot
    have hS : IsSimpleModule O N := isSimpleModule_iff_isAtom.mpr hN
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hS
    have hIm : I = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
    subst hIm
    have hcardN : Nat.card N = Nat.card (IsLocalRing.ResidueField O) := Nat.card_congr e.toEquiv
    have hlen := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    rw [Module.length_eq_one O N, hℓ] at hlen
    have hQ : Module.length O (M ⧸ N) = n := by
      have : ((n : ℕ∞) + 1) = 1 + Module.length O (M ⧸ N) := by exact_mod_cast hlen
      have h2 : ((n : ℕ∞) + 1) = Module.length O (M ⧸ N) + 1 := by rw [this, add_comm]
      exact (ENat.add_left_injective_of_ne_top ENat.one_ne_top h2).symm
    have := ih (M ⧸ N) hQ
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
    change Nat.card (M ⧸ N) * Nat.card N = _
    rw [this, hcardN, pow_succ]

end SurfaceBlowup
