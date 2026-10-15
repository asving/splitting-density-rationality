/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Measure.AdicCylinders
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Hensel factorization, finite products and coefficient measures

Hensel's lemma in factorization form over a complete local ring (proved from scratch by a
Newton iteration on the coefficient filtration `coeffIdeal (𝔪 ^ k)`), its consequences for
families of pairwise coprime factors and uniqueness, and a collection of lemmas on finite products
of rings and modules (adic completeness, quotients, measurable embeddings, division coordinates)
together with the basic mass computations for the normalized coefficient measure of `O^n`.

## Main results

* `hensel_pair_exists`, `hensel_family_exists`, `hensel_pair_unique`: Hensel factorization.
* `isCoprime_of_isCoprime_map_residue`: monic polynomials with coprime residue reductions are
  coprime over any local ring.
* `maximal_ideal_power_kills`: `𝔪 ^ N` kills a module of length `N` over a local ring.
* `monic_residue_polynomial_count`: there are `q ^ n` monic polynomials of degree `n` over `𝔽_q`.
* `power_coordinates_transport`: the transported structure on `O[X]/(Φ)` is a compact
  second-countable Borel topological ring.
* `coefficient_cylinder_mass`, `coefficient_measure_probability`,
  `coefficient_uniformizer_cylinder_mass`: masses of cylinders for the coefficient measure.

Provenance: `Thm_SurfaceBlowupV2_*`: `hensel_pair_exists`, `hensel_family_exists`,
`hensel_pair_unique`, `isAdicComplete_pi`, `linear_map_preserves_adic_congruence`,
`maximal_ideal_power_kills`, `linear_image_bound_from_cokernel_length`, `measurableEmbedding_pi`,
`monic_residue_polynomial_count`, `normalizing_factor_is_unit`, `pi_algebraMap_mem_jacobson_bot`,
`pi_ideal_mem_iff_map_eval`, `pi_quotient_span_linearEquiv`, `power_coordinates_transport`,
`principal_generator_orbit_count`, `product_coordinates_exist`, `product_division_equiv`,
`quotient_mul_range_equiv`, `regular_principal_generators_associated`, `residue_quotient_card`,
`coefficient_cylinder_mass`, `coefficient_measure_probability`, `chart_measure_total_mass`,
`coefficient_uniformizer_cylinder_mass`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace SurfaceBlowup

/-! ### Hensel's lemma -/

namespace Hensel

open Polynomial IsLocalRing

/-! ## 1. `coeffIdeal` — polynomials with all coefficients in a given ideal -/

section CoeffIdeal

variable {R : Type*} [CommRing R]

/-- **`coeffIdeal J`** — the ideal of `R[X]` consisting of the polynomials all of whose
coefficients lie in `J`.  Defined as `Ideal.map C J`; the coefficient description is
`mem_coeffIdeal`. Being an *ideal* is what makes the bookkeeping cheap: it is automatically closed
under multiplication by arbitrary polynomials. -/
private noncomputable abbrev coeffIdeal (J : Ideal R) : Ideal (Polynomial R) :=
  J.map (Polynomial.C (R := R))

private theorem mem_coeffIdeal {J : Ideal R} {p : Polynomial R} :
    p ∈ coeffIdeal J ↔ ∀ i, p.coeff i ∈ J :=
  Ideal.mem_map_C_iff

private theorem coeffIdeal_mono {J J' : Ideal R} (h : J ≤ J') : coeffIdeal J ≤ coeffIdeal J' := by
  intro p hp
  rw [mem_coeffIdeal] at hp ⊢
  exact fun i => h (hp i)

private theorem C_mem_coeffIdeal {J : Ideal R} {a : R} (ha : a ∈ J) :
    Polynomial.C a ∈ coeffIdeal J :=
  Ideal.mem_map_of_mem _ ha

/-- The multiplicativity of the filtration: `coeffIdeal J * coeffIdeal J' ⊆ coeffIdeal (J * J')`
(in fact `Ideal.map_mul` makes it an equality). -/
private theorem mul_mem_coeffIdeal_mul {J J' : Ideal R} {p q : Polynomial R}
    (hp : p ∈ coeffIdeal J) (hq : q ∈ coeffIdeal J') : p * q ∈ coeffIdeal (J * J') := by
  rw [coeffIdeal, Ideal.map_mul]
  exact Ideal.mul_mem_mul hp hq

/-- Membership in `coeffIdeal J` is exactly vanishing of the reduction mod `J`. -/
private theorem map_mk_eq_zero_iff {J : Ideal R} {p : Polynomial R} :
    p.map (Ideal.Quotient.mk J) = 0 ↔ p ∈ coeffIdeal J := by
  rw [mem_coeffIdeal, Polynomial.ext_iff]
  simp [coeff_map, Ideal.Quotient.eq_zero_iff_mem]

end CoeffIdeal

section CoeffIdealLocal

variable {R : Type*} [CommRing R] [IsLocalRing R]

private theorem map_residue_eq_zero_iff {p : Polynomial R} :
    p.map (residue R) = 0 ↔ p ∈ coeffIdeal (maximalIdeal R) :=
  map_mk_eq_zero_iff

/-- Two polynomials have the same residue reduction iff their difference has all coefficients in
`𝔪`. -/
private theorem sub_mem_coeffIdeal_maximalIdeal_iff {p q : Polynomial R} :
    p - q ∈ coeffIdeal (maximalIdeal R) ↔ p.map (residue R) = q.map (residue R) := by
  rw [← map_residue_eq_zero_iff, Polynomial.map_sub, sub_eq_zero]

end CoeffIdealLocal

/-! ## 2. The residue-field solve

Over a field, a coprime monic pair `(g₀, h₀)` of degrees `m, l` lets one write every polynomial of
degree `< m + l` as `h₀ * u + g₀ * v` with `deg u < m` and `deg v < l`. Note the pairing: the
low-degree factor `u` sits against `h₀`. That is the pairing the Newton correction needs, since
`(g + δg) * (h + δh) = g * h + h * δg + g * δh + δg * δh`. -/

section ResidueSolve

variable {k : Type*} [Field k]

private theorem exists_solve_field {g₀ h₀ : Polynomial k} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) {w : Polynomial k}
    (hw : w.degree < (g₀.natDegree + h₀.natDegree : ℕ)) :
    ∃ u v : Polynomial k, u.degree < (g₀.natDegree : ℕ) ∧ v.degree < (h₀.natDegree : ℕ) ∧
      w = h₀ * u + g₀ * v := by
  obtain ⟨a, b, hab⟩ := hcop
  have hg₀deg : g₀.degree = (g₀.natDegree : WithBot ℕ) := degree_eq_natDegree hg₀.ne_zero
  have hh₀deg : h₀.degree = (h₀.natDegree : WithBot ℕ) := degree_eq_natDegree hh₀.ne_zero
  set u : Polynomial k := (b * w) %ₘ g₀ with hu_def
  set v : Polynomial k := a * w + h₀ * ((b * w) /ₘ g₀) with hv_def
  have hu : u.degree < (g₀.natDegree : WithBot ℕ) := by
    rw [hu_def, ← hg₀deg]; exact degree_modByMonic_lt (b * w) hg₀
  have key : w = h₀ * u + g₀ * v := by
    have hdiv : u + g₀ * ((b * w) /ₘ g₀) = b * w := modByMonic_add_div (b * w) g₀
    have expand : h₀ * u + g₀ * v = h₀ * (u + g₀ * ((b * w) /ₘ g₀)) + a * g₀ * w := by
      rw [hv_def]; ring
    rw [expand, hdiv]
    calc w = (a * g₀ + b * h₀) * w := by rw [hab, one_mul]
    _ = h₀ * (b * w) + a * g₀ * w := by ring
  refine ⟨u, v, hu, ?_, key⟩
  -- the degree bound on `v` is forced by monicity of `g₀`, not chosen
  have h1 : (g₀ * v).degree = (g₀.natDegree : WithBot ℕ) + v.degree := by
    rw [degree_mul, hg₀deg]
  have h2 : (h₀ * u).degree < (g₀.natDegree : WithBot ℕ) + (h₀.natDegree : WithBot ℕ) := by
    rw [degree_mul, hh₀deg, add_comm ((g₀.natDegree : WithBot ℕ))]
    exact WithBot.add_lt_add_left (by simp) hu
  have h3 : (g₀ * v).degree < (g₀.natDegree : WithBot ℕ) + (h₀.natDegree : WithBot ℕ) := by
    have hgv : g₀ * v = w - h₀ * u := by rw [key]; ring
    rw [hgv]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ h2)
    simpa [Nat.cast_add] using hw
  rw [h1] at h3
  exact (WithBot.add_lt_add_iff_left (by simp)).mp h3

end ResidueSolve

/-! ## 3. Truncated expansions -/

section Truncation

variable {R : Type*} [CommRing R]

private theorem coeff_sum_range_C_mul_X_pow (c : ℕ → R) (d j : ℕ) :
    (∑ i ∈ Finset.range d, Polynomial.C (c i) * X ^ i).coeff j = if j < d then c j else 0 := by
  classical
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range d) j c]
  simp [Finset.mem_range]

private theorem degree_C_mul_le_degree (a : R) (p : Polynomial R) :
    (Polynomial.C a * p).degree ≤ p.degree := by
  rw [← smul_eq_C_mul]
  exact degree_smul_le a p

/-- Expanding a linear combination of solved monomials. -/
private theorem sum_C_mul_solve_expand (c : ℕ → R) (A B : ℕ → Polynomial R) (g h : Polynomial R)
    (d : ℕ) :
    ∑ i ∈ Finset.range d, Polynomial.C (c i) * ((X : Polynomial R) ^ i - (h * A i + g * B i))
      = (∑ i ∈ Finset.range d, Polynomial.C (c i) * X ^ i)
        - (h * (∑ i ∈ Finset.range d, Polynomial.C (c i) * A i)
          + g * (∑ i ∈ Finset.range d, Polynomial.C (c i) * B i)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A polynomial of degree `< d` is its own truncated expansion in degrees `< d`. -/
private theorem eq_sum_range_of_degree_lt {p : Polynomial R} {d : ℕ}
    (hp : p.degree < (d : WithBot ℕ)) :
    p = ∑ i ∈ Finset.range d, Polynomial.C (p.coeff i) * X ^ i := by
  ext j
  rw [coeff_sum_range_C_mul_X_pow]
  by_cases hj : j < d
  · rw [if_pos hj]
  · rw [if_neg hj]
    exact coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hp (by exact_mod_cast Nat.le_of_not_lt hj))

private theorem degree_sum_range_C_mul_X_pow_lt (c : ℕ → R) (d : ℕ) :
    (∑ i ∈ Finset.range d, Polynomial.C (c i) * X ^ i).degree < (d : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by simp : (⊥ : WithBot ℕ) < (d : WithBot ℕ))]
  intro i hi
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le i (c i)) (by exact_mod_cast Finset.mem_range.mp hi)

end Truncation

/-! ## 4. Solving the interpolation problem modulo `𝔪`, and one filtration step

`exists_solve_mod` is the residue-field solve transported to `R` by a degree-preserving lift.
`exists_solve_step` upgrades it from "solve mod `𝔪`" to "solve an error in `𝔪 ^ j` up to
`𝔪 ^ (j+1)`, with corrections again in `𝔪 ^ j`" — the Newton step. Its proof is *linearity in the
coefficients of the error*: solve once for each monomial `X ^ i` with `i < n`, then take the
`R`-linear combination with the coefficients of the error. This is what makes the argument work
for a non-principal `𝔪`, where one cannot write the error as `π ^ j` times something. -/

section SolveMod

variable {R : Type*} [CommRing R] [IsLocalRing R]

private theorem exists_solve_mod {g h : Polynomial R} {g₀ h₀ : Polynomial (ResidueField R)}
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀)
    {w : Polynomial R} (hw : w.degree < (g₀.natDegree + h₀.natDegree : ℕ)) :
    ∃ u v : Polynomial R, u.degree < (g₀.natDegree : ℕ) ∧ v.degree < (h₀.natDegree : ℕ) ∧
      w - (h * u + g * v) ∈ coeffIdeal (maximalIdeal R) := by
  have hwmap : (w.map (residue R)).degree < (g₀.natDegree + h₀.natDegree : ℕ) :=
    lt_of_le_of_lt (degree_map_le) hw
  obtain ⟨u₀, v₀, hu₀, hv₀, hkey⟩ := exists_solve_field hg₀ hh₀ hcop hwmap
  obtain ⟨u, humap, hudeg⟩ := Polynomial.exists_degree_eq_of_mem_lifts
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) u₀)
  obtain ⟨v, hvmap, hvdeg⟩ := Polynomial.exists_degree_eq_of_mem_lifts
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) v₀)
  refine ⟨u, v, hudeg ▸ hu₀, hvdeg ▸ hv₀, ?_⟩
  rw [← map_residue_eq_zero_iff, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_mul, hgr, hhr, humap, hvmap, sub_eq_zero]
  exact hkey

private theorem exists_solve_step {g h : Polynomial R} {g₀ h₀ : Polynomial (ResidueField R)}
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀)
    (j : ℕ) {e : Polynomial R} (he : e ∈ coeffIdeal (maximalIdeal R ^ j))
    (hdeg : e.degree < (g₀.natDegree + h₀.natDegree : ℕ)) :
    ∃ u v : Polynomial R, u.degree < (g₀.natDegree : ℕ) ∧ v.degree < (h₀.natDegree : ℕ) ∧
      u ∈ coeffIdeal (maximalIdeal R ^ j) ∧ v ∈ coeffIdeal (maximalIdeal R ^ j) ∧
      e - (h * u + g * v) ∈ coeffIdeal (maximalIdeal R ^ (j + 1)) := by
  classical
  set m := g₀.natDegree with hm
  set l := h₀.natDegree with hl
  have key : ∀ i : ℕ, ∃ uv : Polynomial R × Polynomial R,
      uv.1.degree < (m : WithBot ℕ) ∧ uv.2.degree < (l : WithBot ℕ) ∧
      (i < m + l → (X : Polynomial R) ^ i - (h * uv.1 + g * uv.2)
        ∈ coeffIdeal (maximalIdeal R)) := by
    intro i
    by_cases hi : i < m + l
    · obtain ⟨u, v, h1, h2, h3⟩ := exists_solve_mod hg₀ hh₀ hcop hgr hhr
        (w := (X : Polynomial R) ^ i) (by rw [degree_X_pow]; exact_mod_cast hi)
      exact ⟨(u, v), h1, h2, fun _ => h3⟩
    · exact ⟨(0, 0), by simp, by simp, fun hc => absurd hc hi⟩
  choose UV hU hV hr using key
  set u : Polynomial R := ∑ i ∈ Finset.range (m + l), Polynomial.C (e.coeff i) * (UV i).1 with hu
  set v : Polynomial R := ∑ i ∈ Finset.range (m + l), Polynomial.C (e.coeff i) * (UV i).2 with hv
  have hudeg : u.degree < (m : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by simp : (⊥ : WithBot ℕ) < (m : WithBot ℕ))]
    exact fun i _ => lt_of_le_of_lt (degree_C_mul_le_degree _ _) (hU i)
  have hvdeg : v.degree < (l : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by simp : (⊥ : WithBot ℕ) < (l : WithBot ℕ))]
    exact fun i _ => lt_of_le_of_lt (degree_C_mul_le_degree _ _) (hV i)
  refine ⟨u, v, hudeg, hvdeg, ?_, ?_, ?_⟩
  · exact Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_right _ _ (C_mem_coeffIdeal ((mem_coeffIdeal.mp he) i))
  · exact Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_right _ _ (C_mem_coeffIdeal ((mem_coeffIdeal.mp he) i))
  · have hexp : e - (h * u + g * v)
        = ∑ i ∈ Finset.range (m + l), Polynomial.C (e.coeff i) *
            ((X : Polynomial R) ^ i - (h * (UV i).1 + g * (UV i).2)) := by
      rw [sum_C_mul_solve_expand (fun i => e.coeff i) (fun i => (UV i).1) (fun i => (UV i).2)
        g h (m + l), hu, hv]
      congr 1
      exact eq_sum_range_of_degree_lt hdeg
    rw [hexp]
    refine Ideal.sum_mem _ fun i hi => ?_
    have := mul_mem_coeffIdeal_mul (C_mem_coeffIdeal ((mem_coeffIdeal.mp he) i))
      (hr i (Finset.mem_range.mp hi))
    rwa [← pow_succ] at this

end SolveMod

/-! ## 5. The adic limit of a degree-bounded Cauchy sequence of polynomials -/

section Limit

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]

private theorem exists_adicLimit_of_degree_lt (d : ℕ) (p : ℕ → Polynomial R)
    (hdeg : ∀ k, (p k).degree < (d : WithBot ℕ))
    (hstep : ∀ k, p (k + 1) - p k ∈ coeffIdeal (maximalIdeal R ^ k)) :
    ∃ P : Polynomial R, P.degree < (d : WithBot ℕ) ∧
      ∀ k, P - p k ∈ coeffIdeal (maximalIdeal R ^ k) := by
  classical
  have hCauchy : ∀ (i a b : ℕ), a ≤ b →
      (p a).coeff i - (p b).coeff i ∈ maximalIdeal R ^ a := by
    intro i a b hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    induction c with
    | zero => simp
    | succ c ih =>
      have h2 : (p (a + c)).coeff i - (p (a + c + 1)).coeff i ∈ maximalIdeal R ^ a :=
        Ideal.pow_le_pow_right (Nat.le_add_right a c)
          (by simpa using neg_mem ((mem_coeffIdeal.mp (hstep (a + c))) i))
      rw [show (p a).coeff i - (p (a + (c + 1))).coeff i
          = ((p a).coeff i - (p (a + c)).coeff i)
            + ((p (a + c)).coeff i - (p (a + c + 1)).coeff i) by rw [← Nat.add_assoc]; ring]
      exact Ideal.add_mem _ ih h2
  have hprec : ∀ i : ℕ, ∃ L : R,
      ∀ k, (p k).coeff i ≡ L [SMOD (maximalIdeal R ^ k • ⊤ : Ideal R)] := by
    refine fun i => IsPrecomplete.prec' (fun k => (p k).coeff i) fun hab => ?_
    rw [SModEq.sub_mem, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    exact hCauchy i _ _ hab
  choose L hL using hprec
  refine ⟨∑ i ∈ Finset.range d, Polynomial.C (L i) * X ^ i,
    degree_sum_range_C_mul_X_pow_lt L d, ?_⟩
  refine fun k => mem_coeffIdeal.2 fun i => ?_
  rw [coeff_sub, coeff_sum_range_C_mul_X_pow]
  by_cases hi : i < d
  · have := hL i k
    rw [SModEq.sub_mem, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at this
    simpa [hi] using neg_mem this
  · simp [hi, coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le (hdeg k) (by exact_mod_cast Nat.le_of_not_lt hi))]

end Limit

/-! ## 6. The factorization theorem -/

section Main

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A monic polynomial over the residue field lifts to a monic polynomial of the same degree. -/
private theorem exists_monic_lift {p₀ : Polynomial (ResidueField R)} (hp₀ : p₀.Monic) :
    ∃ p : Polynomial R, p.Monic ∧ p.map (residue R) = p₀ ∧ p.natDegree = p₀.natDegree := by
  obtain ⟨p, hmap, hdeg, hmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) p₀) hp₀
  exact ⟨p, hmonic, hmap, natDegree_eq_of_degree_eq hdeg⟩

/-- The `natDegree` of a monic polynomial is read off its residue reduction. -/
private theorem natDegree_eq_of_map_eq {p : Polynomial R} {p₀ : Polynomial (ResidueField R)}
    (hp : p.Monic) (hmap : p.map (residue R) = p₀) : p.natDegree = p₀.natDegree := by
  rw [← hmap, hp.natDegree_map]

/-- Difference of two monic polynomials of the same degree drops degree. -/
private theorem degree_sub_lt_of_monic_of_natDegree_eq {p q : Polynomial R} (hp : p.Monic)
    (hq : q.Monic) (hd : p.natDegree = q.natDegree) :
    (p - q).degree < (p.natDegree : WithBot ℕ) := by
  have hdd : p.degree = q.degree := by
    rw [degree_eq_natDegree hp.ne_zero, degree_eq_natDegree hq.ne_zero, hd]
  have := degree_sub_lt_left hdd hp.ne_zero (by rw [hp.leadingCoeff, hq.leadingCoeff])
  rwa [degree_eq_natDegree hp.ne_zero] at this

/-- One Newton step of the Hensel iteration: monic lifts `x = (x₁, x₂)` of `(g₀, h₀)` whose product
agrees with `f` modulo `𝔪^(k+1)` are corrected, by terms in `𝔪^(k+1)`, to monic lifts whose product
agrees with `f` modulo `𝔪^(k+2)`. -/
private theorem exists_hensel_newton_step {f : Polynomial R} (hf : f.Monic)
    {g₀ h₀ : Polynomial (ResidueField R)} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hfgh : f.map (residue R) = g₀ * h₀) {G₁ H₁ : Polynomial R}
    (hG₁map : G₁.map (residue R) = g₀) (hH₁map : H₁.map (residue R) = h₀) (k : ℕ)
    {x : Polynomial R × Polynomial R}
    (hx : x.1.Monic ∧ x.2.Monic ∧ x.1.map (residue R) = g₀ ∧ x.2.map (residue R) = h₀ ∧
      f - x.1 * x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1))) :
    ∃ y : Polynomial R × Polynomial R,
      (y.1.Monic ∧ y.2.Monic ∧ y.1.map (residue R) = g₀ ∧ y.2.map (residue R) = h₀ ∧
        f - y.1 * y.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1 + 1))) ∧
      y.1 - x.1 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) ∧
      y.2 - x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) := by
  obtain ⟨hx1, hx3, hx5, hx6, hx7⟩ := hx
  -- the error has degree below `deg f`, since both `f` and `x₁ x₂` are monic of that degree
  have hfdeg : f.natDegree = g₀.natDegree + h₀.natDegree := by
    rw [← hf.natDegree_map (residue R), hfgh, hg₀.natDegree_mul hh₀]
  have hdeglt : (f - x.1 * x.2).degree < ((g₀.natDegree + h₀.natDegree : ℕ) : WithBot ℕ) := by
    have := degree_sub_lt_of_monic_of_natDegree_eq hf (hx1.mul hx3) (by
      rw [hfdeg, hx1.natDegree_mul hx3, natDegree_eq_of_map_eq hx1 hx5,
        natDegree_eq_of_map_eq hx3 hx6])
    rwa [hfdeg] at this
  obtain ⟨δG, δH, hδGdeg, hδHdeg, hδGmem, hδHmem, herr⟩ :=
    exists_solve_step hg₀ hh₀ hcop hG₁map hH₁map (k + 1) hx7 hdeglt
  have hmle : maximalIdeal R ^ (k + 1) ≤ maximalIdeal R := Ideal.pow_le_self (by omega)
  have hδGm : δG ∈ coeffIdeal (maximalIdeal R) := coeffIdeal_mono hmle hδGmem
  have hδHm : δH ∈ coeffIdeal (maximalIdeal R) := coeffIdeal_mono hmle hδHmem
  have hmul : ∀ {a b : Polynomial R}, a ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) →
      b ∈ coeffIdeal (maximalIdeal R) → a * b ∈ coeffIdeal (maximalIdeal R ^ (k + 1 + 1)) :=
    fun ha hb => by have := mul_mem_coeffIdeal_mul ha hb; rwa [← pow_succ] at this
  refine ⟨(x.1 + δG, x.2 + δH), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hx1.add_of_left (by
      rwa [degree_eq_natDegree hx1.ne_zero, natDegree_eq_of_map_eq hx1 hx5])
  · exact hx3.add_of_left (by
      rwa [degree_eq_natDegree hx3.ne_zero, natDegree_eq_of_map_eq hx3 hx6])
  · simp [map_residue_eq_zero_iff.mpr hδGm, hx5]
  · simp [map_residue_eq_zero_iff.mpr hδHm, hx6]
  · -- the error recursion
    have hH₁x : H₁ - x.2 ∈ coeffIdeal (maximalIdeal R) :=
      sub_mem_coeffIdeal_maximalIdeal_iff.mpr (by rw [hH₁map, hx6])
    have hG₁x : G₁ - x.1 ∈ coeffIdeal (maximalIdeal R) :=
      sub_mem_coeffIdeal_maximalIdeal_iff.mpr (by rw [hG₁map, hx5])
    rw [show f - (x.1 + δG) * (x.2 + δH) = ((f - x.1 * x.2) - (H₁ * δG + G₁ * δH))
      + δG * (H₁ - x.2) + δH * (G₁ - x.1) - δG * δH by ring]
    exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.add_mem _ herr (hmul hδGmem hH₁x))
      (hmul hδHmem hG₁x)) (hmul hδGmem hδHm)
  · simpa using hδGmem
  · simpa using hδHmem

variable [IsAdicComplete (maximalIdeal R) R]

/-- Monic approximants with a fixed reduction `p₀`, converging adically, have a monic limit with
the same reduction and degree. -/
private theorem exists_monic_limit {p₀ : Polynomial (ResidueField R)} (B : ℕ → Polynomial R)
    (hB : ∀ k, (B k).Monic) (hBmap : ∀ k, (B k).map (residue R) = p₀)
    (hstep : ∀ k, B (k + 1) - B k ∈ coeffIdeal (maximalIdeal R ^ k)) :
    ∃ G : Polynomial R, G.Monic ∧ G.map (residue R) = p₀ ∧ G.natDegree = p₀.natDegree ∧
      ∀ k, G - B k ∈ coeffIdeal (maximalIdeal R ^ k) := by
  set n := p₀.natDegree
  have htail : ∀ k, (B k - X ^ n).degree < (n : WithBot ℕ) := by
    intro k
    have h2 : (B k).natDegree = n := natDegree_eq_of_map_eq (hB k) (hBmap k)
    have := degree_sub_lt_of_monic_of_natDegree_eq (hB k) (monic_X_pow (R := R) n)
      (by rw [h2, natDegree_X_pow])
    rwa [h2] at this
  obtain ⟨T, hTdeg, hTlim⟩ := exists_adicLimit_of_degree_lt n (fun k => B k - X ^ n) htail
    (by intro k; simpa using hstep k)
  have hlt : T.degree < (X ^ n : Polynomial R).degree := by rwa [degree_X_pow]
  have hlim : ∀ k, X ^ n + T - B k ∈ coeffIdeal (maximalIdeal R ^ k) := fun k => by
    rw [show X ^ n + T - B k = T - (B k - X ^ n) by ring]
    exact hTlim k
  refine ⟨X ^ n + T, (monic_X_pow _).add_of_left hlt, ?_, natDegree_eq_of_degree_eq_some ?_, hlim⟩
  · exact (sub_mem_coeffIdeal_maximalIdeal_iff.1 (by simpa using hlim 1)).trans (hBmap 1)
  · rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]

/-- **Hensel's lemma, factorization form.**  Over a complete local ring, a coprime monic
factorization of the residue reduction of a monic polynomial lifts to a monic factorization.
The degrees of the lifted factors are those of the residual factors. -/
private theorem exists_monic_factorization {f : Polynomial R} (hf : f.Monic)
    {g₀ h₀ : Polynomial (ResidueField R)} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hfgh : f.map (residue R) = g₀ * h₀) :
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ ∧
      g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree := by
  classical
  -- strategy: iterate the Newton step from base lifts, then pass to the adic limit
  -- the base lifts
  obtain ⟨G₁, hG₁mon, hG₁map, -⟩ := exists_monic_lift (R := R) hg₀
  obtain ⟨H₁, hH₁mon, hH₁map, -⟩ := exists_monic_lift (R := R) hh₀
  have hbase : f - G₁ * H₁ ∈ coeffIdeal (maximalIdeal R ^ (0 + 1)) := by
    rw [zero_add, pow_one, ← map_residue_eq_zero_iff, Polynomial.map_sub, Polynomial.map_mul,
      hG₁map, hH₁map, hfgh, sub_self]
  -- the Newton step, made total by `by_cases` so that it can be iterated by `Nat.rec`
  have step : ∀ (k : ℕ) (x : Polynomial R × Polynomial R),
      ∃ y : Polynomial R × Polynomial R,
        (x.1.Monic ∧ x.2.Monic ∧ x.1.map (residue R) = g₀ ∧ x.2.map (residue R) = h₀ ∧
            f - x.1 * x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1))) →
          (y.1.Monic ∧ y.2.Monic ∧ y.1.map (residue R) = g₀ ∧ y.2.map (residue R) = h₀ ∧
            f - y.1 * y.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1 + 1))) ∧
          y.1 - x.1 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) ∧
          y.2 - x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) := by
    intro k x
    by_cases hx : x.1.Monic ∧ x.2.Monic ∧ x.1.map (residue R) = g₀ ∧
        x.2.map (residue R) = h₀ ∧ f - x.1 * x.2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1))
    · obtain ⟨y, hy⟩ :=
        exists_hensel_newton_step hf hg₀ hh₀ hcop hfgh hG₁map hH₁map k hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨x, fun hc => absurd hc hx⟩
  choose next hnext using step
  obtain ⟨A, hA0, hAsucc⟩ : ∃ A : ℕ → Polynomial R × Polynomial R,
      A 0 = (G₁, H₁) ∧ ∀ k, A (k + 1) = next k (A k) :=
    ⟨fun k => Nat.rec (G₁, H₁) (fun j acc => next j acc) k, rfl, fun _ => rfl⟩
  have hInvA : ∀ k, (A k).1.Monic ∧ (A k).2.Monic ∧ (A k).1.map (residue R) = g₀ ∧
      (A k).2.map (residue R) = h₀ ∧
      f - (A k).1 * (A k).2 ∈ coeffIdeal (maximalIdeal R ^ (k + 1)) := by
    intro k
    induction k with
    | zero => rw [hA0]; exact ⟨hG₁mon, hH₁mon, hG₁map, hH₁map, hbase⟩
    | succ k ih => rw [hAsucc k]; exact (hnext k (A k) ih).1
  -- pass to the limit
  obtain ⟨G, hGmon, hGmap, hGdeg, hGlim⟩ := exists_monic_limit (fun k => (A k).1)
    (fun k => (hInvA k).1) (fun k => (hInvA k).2.2.1) fun k =>
      coeffIdeal_mono (Ideal.pow_le_pow_right (Nat.le_succ k))
        (hAsucc k ▸ (hnext k (A k) (hInvA k)).2.1)
  obtain ⟨H, hHmon, hHmap, hHdeg, hHlim⟩ := exists_monic_limit (fun k => (A k).2)
    (fun k => (hInvA k).2.1) (fun k => (hInvA k).2.2.2.1) fun k =>
      coeffIdeal_mono (Ideal.pow_le_pow_right (Nat.le_succ k))
        (hAsucc k ▸ (hnext k (A k) (hInvA k)).2.2)
  have hzero : f - G * H = 0 := by
    have hall : ∀ k, f - G * H ∈ coeffIdeal (maximalIdeal R ^ k) := by
      intro k
      rw [show f - G * H
          = (f - (A k).1 * (A k).2) - (G - (A k).1) * H - (A k).1 * (H - (A k).2) by ring]
      exact Ideal.sub_mem _ (Ideal.sub_mem _
        (coeffIdeal_mono (Ideal.pow_le_pow_right (Nat.le_succ k)) (hInvA k).2.2.2.2)
        (Ideal.mul_mem_right _ _ (hGlim k))) (Ideal.mul_mem_left _ _ (hHlim k))
    ext i
    rw [coeff_zero]
    refine IsHausdorff.haus' (I := maximalIdeal R) ((f - G * H).coeff i) fun n => ?_
    rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    exact (mem_coeffIdeal.mp (hall n)) i
  exact ⟨G, H, hGmon, hHmon, sub_eq_zero.mp hzero, hGmap, hHmap, hGdeg, hHdeg⟩

end Main
end Hensel

/-- Hensel's lemma: over a complete local ring, a coprime monic factorization `g * h` of the
residue reduction of a monic `F` lifts to a monic factorization `F = G * H` with the same
degrees. -/
theorem hensel_pair_exists (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (F : Polynomial O) (hF : F.Monic)
    (g h : Polynomial (IsLocalRing.ResidueField O)) (hg : g.Monic) (hh : h.Monic)
    (hc : IsCoprime g h) (hred : F.map (IsLocalRing.residue O) = g * h) :
    ∃ G H : Polynomial O, G.Monic ∧ H.Monic ∧ F=G*H ∧ G.map (IsLocalRing.residue O)=g ∧
      H.map (IsLocalRing.residue O)=h ∧ G.natDegree=g.natDegree ∧ H.natDegree=h.natDegree :=
  Hensel.exists_monic_factorization hF hg hh hc hred

/-- Hensel's lemma for finitely many pairwise coprime monic residue factors. -/
theorem hensel_family_exists (O ι : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Fintype ι] (F : Polynomial O) (hF : F.Monic)
    (g : ι → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ i, (g i).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (hred : F.map (IsLocalRing.residue O) = ∏ i, g i) :
    ∃ G : ι→Polynomial O, (∀ i, (G i).Monic) ∧ F=∏ i, G i ∧
      (∀ i, (G i).map (IsLocalRing.residue O)=g i) ∧ (∀ i, (G i).natDegree=(g i).natDegree) := by
  classical
  have key : ∀ s : Finset ι, ∀ F : Polynomial O, F.Monic →
      F.map (IsLocalRing.residue O) = ∏ i ∈ s, g i →
      ∃ G : ι → Polynomial O, (∀ i ∈ s, (G i).Monic) ∧ F = ∏ i ∈ s, G i ∧
        (∀ i ∈ s, (G i).map (IsLocalRing.residue O) = g i) ∧
        (∀ i ∈ s, (G i).natDegree = (g i).natDegree) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro F hF hr
      refine ⟨fun _ => 1, by simp, ?_, by simp, by simp⟩
      rw [Finset.prod_empty] at hr
      simpa using hF.eq_one_of_map_eq_one (IsLocalRing.residue O) hr
    | insert a s ha ih =>
      intro F hF hr
      rw [Finset.prod_insert ha] at hr
      have hcop : IsCoprime (g a) (∏ i ∈ s, g i) :=
        IsCoprime.prod_right (fun i hi => hc a i (fun (h : a = i) => ha (h ▸ hi)))
      obtain ⟨G0, H, hG0, hH, hFe, hG0r, hHr, hG0d, hHd⟩ :=
        hensel_pair_exists O F hF (g a) (∏ i ∈ s, g i) (hg a)
          (Polynomial.monic_prod_of_monic _ _ (fun i _ => hg i)) hcop hr
      obtain ⟨G', h1, h2, h3, h4⟩ := ih H hH hHr
      have hs : ∏ i ∈ s, (if i = a then G0 else G' i) = ∏ i ∈ s, G' i :=
        Finset.prod_congr rfl (fun i hi => if_neg (fun (h : i = a) => ha (h ▸ hi)))
      refine ⟨fun i => if i = a then G0 else G' i, ?_, ?_, ?_, ?_⟩
      rotate_left
      · rw [Finset.prod_insert ha, hs, if_pos rfl, hFe, h2]
      all_goals
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa
        · simp [show i ≠ a from fun h => ha (h ▸ hi), *]
  obtain ⟨G, h1, h2, h3, h4⟩ := key Finset.univ F hF hred
  exact ⟨G, fun i => h1 i (Finset.mem_univ i), h2, fun i => h3 i (Finset.mem_univ i),
    fun i => h4 i (Finset.mem_univ i)⟩

/-- Monic polynomials over a local ring whose residue reductions are coprime are coprime. -/
theorem isCoprime_of_isCoprime_map_residue {O : Type*} [CommRing O] [IsLocalRing O]
    {A B : Polynomial O} (hA : A.Monic) (hB : B.Monic)
    (h : IsCoprime (A.map (IsLocalRing.residue O)) (B.map (IsLocalRing.residue O))) :
    IsCoprime A B := by
  rw [← Polynomial.isUnit_resultant_iff_isCoprime hA]
  have h' := (Polynomial.isUnit_resultant_iff_isCoprime (hA.map (IsLocalRing.residue O))).2 h
  rw [hA.natDegree_map, hB.natDegree_map, Polynomial.resultant_map_map] at h'
  exact (isUnit_map_iff (IsLocalRing.residue O) _).1 h'

/-- Uniqueness in Hensel's lemma: monic factorizations with the same coprime residue factors
are equal. -/
theorem hensel_pair_unique (O : Type) [CommRing O] [IsLocalRing O]
    (G H G₁ H₁ : Polynomial O) (hG : G.Monic) (hH : H.Monic) (hG₁ : G₁.Monic) (hH₁ : H₁.Monic)
    (hg : G.map (IsLocalRing.residue O) = G₁.map (IsLocalRing.residue O))
    (hh : H.map (IsLocalRing.residue O) = H₁.map (IsLocalRing.residue O))
    (hc : IsCoprime (G.map (IsLocalRing.residue O)) (H.map (IsLocalRing.residue O)))
    (hp : G * H = G₁ * H₁) :
    G=G₁ ∧ H=H₁ := by
  have deg : ∀ A B : Polynomial O, A.Monic → B.Monic →
      A.map (IsLocalRing.residue O) = B.map (IsLocalRing.residue O) →
        A.natDegree = B.natDegree := by
    intro A B hA hB h
    rw [← hA.natDegree_map (IsLocalRing.residue O), ← hB.natDegree_map (IsLocalRing.residue O), h]
  have c1 : IsCoprime G H₁ := isCoprime_of_isCoprime_map_residue hG hH₁ (by rw [← hh]; exact hc)
  have c2 : IsCoprime G₁ H := isCoprime_of_isCoprime_map_residue hG₁ hH (by rw [← hg]; exact hc)
  have d1 : G ∣ G₁ := c1.dvd_of_dvd_mul_right ⟨H, hp.symm⟩
  have d2 : H ∣ H₁ := c2.symm.dvd_of_dvd_mul_left ⟨G, by rw [hp.symm, mul_comm]⟩
  exact ⟨(Polynomial.eq_of_monic_of_dvd_of_natDegree_le hG hG₁ d1 (deg _ _ hG₁ hG hg.symm).le).symm,
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hH hH₁ d2 (deg _ _ hH₁ hH hh.symm).le).symm⟩

/-- A finite product of `I`-adically complete modules is `I`-adically complete. -/
theorem isAdicComplete_pi (O : Type) [CommRing O] (I : Ideal O) (ι : Type) [Finite ι]
    (M : ι → Type) [∀ j, AddCommGroup (M j)] [∀ j, Module O (M j)] [∀ j, IsAdicComplete I (M j)] :
    IsAdicComplete I (∀ j, M j) := by
  have := Fintype.ofFinite ι
  classical
  have mem : ∀ (J : Ideal O) (x : ∀ j, M j),
      x ∈ J • (⊤ : Submodule O (∀ j, M j)) ↔ ∀ j, x j ∈ J • (⊤ : Submodule O (M j)) := by
    intro J x
    constructor
    · intro hx j
      have h1 : LinearMap.proj (R := O) (φ := M) j x ∈
          (J • (⊤ : Submodule O (∀ j, M j))).map (LinearMap.proj j) :=
        Submodule.mem_map_of_mem hx
      rw [Submodule.map_smul''] at h1
      exact Submodule.smul_mono le_rfl le_top h1
    · intro hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      have h1 : LinearMap.single O M j (x j) ∈
          (J • (⊤ : Submodule O (M j))).map (LinearMap.single O M j) :=
        Submodule.mem_map_of_mem (hx j)
      rw [Submodule.map_smul''] at h1
      exact Submodule.smul_mono le_rfl le_top h1
  have H1 : IsHausdorff I (∀ j, M j) := by
    refine ⟨fun x hx => ?_⟩
    funext j
    refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I)) (x j) (fun n => ?_)
    have := (mem _ _).1 (SModEq.sub_mem.1 (hx n)) j
    simpa [SModEq.sub_mem] using this
  have H2 : IsPrecomplete I (∀ j, M j) := by
    refine ⟨fun {f} hf => ?_⟩
    have hj : ∀ j, ∃ L : M j, ∀ n, f n j ≡ L [SMOD (I ^ n • ⊤ : Submodule O (M j))] := by
      intro j
      refine IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := I)) (fun {m n} hmn => ?_)
      have := (mem _ _).1 (SModEq.sub_mem.1 (hf hmn)) j
      simpa [SModEq.sub_mem] using this
    choose L hL using hj
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem]
    intro j
    simpa [SModEq.sub_mem] using hL j n
  exact { toIsHausdorff := H1, toIsPrecomplete := H2 }

/-- Linear maps preserve adic congruences. -/
theorem linear_map_preserves_adic_congruence (O M N : Type) [CommRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] (I : Ideal O) (L : M →ₗ[O] N) (j : ℕ) (x y : M)
    (h : adicCongr I j x y) :
    adicCongr I j (L x) (L y) := by
  unfold adicCongr at h ⊢
  rw [← map_sub]
  exact Submodule.smul_top_le_comap_smul_top (I ^ j) L h

/-- Over a local ring, `𝔪 ^ N` annihilates every module of length `N`. -/
theorem maximal_ideal_power_kills (R M : Type) [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] (N : ℕ) (hN : Module.length R M = N) :
    (IsLocalRing.maximalIdeal R)^N • (⊤ : Submodule R M)=⊥ := by
  obtain ⟨hNoeth, hArt⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp
    (Module.length_ne_top_iff.mp (by rw [hN]; exact ENat.natCast_ne_top N))
  set m := IsLocalRing.maximalIdeal R
  have key : ∀ k : ℕ, k ≤ N → m ^ k • (⊤ : Submodule R M) = ⊥ ∨
      Order.height (m ^ k • (⊤ : Submodule R M)) + k ≤ N := by
    intro k
    induction k with
    | zero =>
      intro _
      right
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, ← Module.length_eq_height, hN]
      simp
    | succ k ih =>
      intro hk
      rcases ih (by omega) with h | h
      · left
        rw [pow_succ', mul_smul, h, Submodule.smul_bot]
      · by_cases heq : m ^ (k+1) • (⊤ : Submodule R M) = m ^ k • ⊤
        · left
          apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m _ (IsNoetherian.noetherian _)
          · conv_lhs => rw [pow_succ', mul_smul]
            rw [heq]
          · exact IsLocalRing.maximalIdeal_le_jacobson _
        · right
          have hlt : m ^ (k+1) • (⊤ : Submodule R M) < m ^ k • ⊤ := by
            refine lt_of_le_of_ne ?_ heq
            rw [pow_succ', mul_smul]
            exact Submodule.smul_le_right
          have h2 := Order.height_strictMono hlt (Submodule.height_lt_top _)
          have h3 : Order.height (m ^ (k+1) • (⊤ : Submodule R M)) + 1 ≤
              Order.height (m ^ k • (⊤ : Submodule R M)) := Order.add_one_le_of_lt h2
          calc Order.height (m ^ (k+1) • (⊤ : Submodule R M)) + ((k+1 : ℕ) : ℕ∞)
              = (Order.height (m ^ (k+1) • (⊤ : Submodule R M)) + 1) + k := by
                push_cast; ring
            _ ≤ Order.height (m ^ k • (⊤ : Submodule R M)) + k := by gcongr
            _ ≤ N := h
  rcases key N le_rfl with h | h
  · exact h
  · have : Order.height (m ^ N • (⊤ : Submodule R M)) = 0 := by
      have hlt := Submodule.height_lt_top (m ^ N • (⊤ : Submodule R M))
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hlt.ne
      rw [← ha] at h ⊢
      norm_cast at h ⊢
      omega
    rw [Order.height_eq_zero] at this
    exact this.eq_bot

/-- If `coker D` has length `k` over a local ring with principal maximal ideal `(π)`, then
`π ^ k • w ∈ range D` for every `w`. -/
theorem linear_image_bound_from_cokernel_length (O V W : Type) [CommRing O] [IsLocalRing O]
    [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W] (pi : O)
    (hpi : IsLocalRing.maximalIdeal O = Ideal.span {pi}) (D : V →ₗ[O] W) (k : ℕ)
    (hk : Module.length O (W ⧸ D.range) = k) :
    ∀ w : W, (pi^k) • w ∈ D.range := by
  intro w
  have h := maximal_ideal_power_kills O (W ⧸ D.range) k hk
  have hmem : pi ^ k ∈ (IsLocalRing.maximalIdeal O) ^ k := by
    rw [hpi]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self pi) k
  have h2 : (pi ^ k) • (Submodule.Quotient.mk w : W ⧸ D.range) ∈
      (IsLocalRing.maximalIdeal O) ^ k • (⊤ : Submodule O (W ⧸ D.range)) :=
    Submodule.smul_mem_smul hmem Submodule.mem_top
  rw [h, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero] at h2
  exact h2

/-- A countable product of measurable embeddings is a measurable embedding. -/
theorem measurableEmbedding_pi (ι : Type) [Countable ι] (X Y : ι → Type)
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (Y j)] (f : ∀ j, X j → Y j)
    (hf : ∀ j, MeasurableEmbedding (f j)) :
    MeasurableEmbedding (fun (x : ∀ j, X j) (j : ι) => f j (x j)) := by
  have hinj : Function.Injective (fun (x : ∀ j, X j) (j : ι) => f j (x j)) := by
    intro a b h
    funext j
    exact (hf j).injective (congrFun h j)
  have hmeas : Measurable (fun (x : ∀ j, X j) (j : ι) => f j (x j)) :=
    measurable_pi_iff.2 fun j => (hf j).measurable.comp (measurable_pi_apply j)
  refine ⟨hinj, hmeas, ?_⟩
  intro S hS
  by_cases hne : Nonempty (∀ j, X j)
  · obtain ⟨x₀⟩ := hne
    choose r hr hrf using fun j => (hf j).exists_measurable_extend (g := id)
      (hne := fun _ => ⟨x₀ j⟩) measurable_id
    have hrm : Measurable (fun (y : ∀ j, Y j) (j : ι) => r j (y j)) :=
      measurable_pi_iff.2 fun j => (hr j).comp (measurable_pi_apply j)
    have : (fun (x : ∀ j, X j) (j : ι) => f j (x j)) '' S =
        (Set.pi Set.univ fun j => Set.range (f j)) ∩ (fun y j => r j (y j)) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨fun j _ => ⟨x j, rfl⟩, ?_⟩
        have : (fun j => r j (f j (x j))) = x := funext fun j => congrFun (hrf j) (x j)
        simpa [this] using hx
      · rintro ⟨h1, h2⟩
        choose x hx using fun j => h1 j (Set.mem_univ j)
        have : (fun j => r j (y j)) = x := funext fun j => by
          rw [← hx j]; exact congrFun (hrf j) (x j)
        refine ⟨x, ?_, funext hx⟩
        rw [← this]; exact h2
    rw [this]
    refine MeasurableSet.inter (MeasurableSet.univ_pi fun j => ?_) (hrm hS)
    rw [← Set.image_univ]
    exact (hf j).measurableSet_image.2 MeasurableSet.univ
  · rw [not_nonempty_iff] at hne
    have : S = ∅ := Set.eq_empty_of_isEmpty S
    rw [this]; simp

/-- Over a finite field `k` there are `|k| ^ n` monic polynomials of degree `n`. -/
theorem monic_residue_polynomial_count (k : Type) [Field k] [Finite k] (n : ℕ) :
    Nat.card {F : Polynomial k // F.Monic ∧ F.natDegree=n}=(Nat.card k)^n := by
  rw [Nat.card_congr ((Polynomial.monicEquivDegreeLT n).trans
    (Polynomial.degreeLTEquiv k n).toEquiv), Nat.card_fun]
  simp

/-- If `π` maps into the maximal ideal of the local `O`-algebra `R`, then `1 + π • v` is a unit. -/
theorem normalizing_factor_is_unit (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    [IsLocalRing R] (pi : O) (hpi : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) (v : R) :
    IsUnit (1 + pi • v) := by
  have hm : -(pi • v) ∈ IsLocalRing.maximalIdeal R :=
    neg_mem (by rw [Algebra.smul_def]; exact Ideal.mul_mem_right _ _ hpi)
  simpa using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hm

/-- In a finite product of local `O`-algebras in which `π` is non-invertible, `π` lies in the
Jacobson radical, and a componentwise regular element is regular. -/
theorem pi_algebraMap_mem_jacobson_bot (O : Type) [CommRing O] (ι : Type) (C : ι → Type)
    [∀ j, CommRing (C j)] [∀ j, Algebra O (C j)] [∀ j, IsLocalRing (C j)] (pi : O)
    (hpi : ∀ j, algebraMap O (C j) pi ∈ IsLocalRing.maximalIdeal (C j)) (e : ∀ j, C j)
    (he : ∀ j, Function.Injective (fun z : C j => e j * z)) :
    algebraMap O (∀ j, C j) pi ∈ Ideal.jacobson (⊥ : Ideal (∀ j, C j)) ∧
      Function.Injective (fun z : ∀ j, C j => e * z) := by
  refine ⟨Ideal.mem_jacobson_bot.2 fun y => Pi.isUnit_iff.2 fun j => ?_,
    fun z z' h => funext fun j => he j (congrFun h j)⟩
  simpa [Algebra.smul_def, mul_comm, add_comm] using
    normalizing_factor_is_unit O (C j) pi (hpi j) (y j)

/-- An ideal of a finite product of rings is determined by its images in the factors. -/
theorem pi_ideal_mem_iff_map_eval (ι : Type) [Finite ι] (R : ι → Type) [∀ j, CommRing (R j)]
    (I : Ideal (∀ j, R j)) :
    (∀ x : ∀ j, R j, x ∈ I ↔ ∀ j, x j ∈ I.map (Pi.evalRingHom R j)) ∧ ∀ J : Ideal (∀ j, R j),
      (∀ j, I.map (Pi.evalRingHom R j) = J.map (Pi.evalRingHom R j)) → I = J := by
  have := Fintype.ofFinite ι
  classical
  have key : ∀ I : Ideal (∀ j, R j), ∀ x : ∀ j, R j,
      x ∈ I ↔ ∀ j, x j ∈ I.map (Pi.evalRingHom R j) := by
    refine fun I x => ⟨fun hx j => Ideal.mem_map_of_mem (Pi.evalRingHom R j) hx, fun h => ?_⟩
    choose y hy e using fun j => (Ideal.mem_map_iff_of_surjective (Pi.evalRingHom R j)
      (Function.surjective_eval j)).1 (h j)
    rw [← Finset.univ_sum_single x]
    refine Ideal.sum_mem _ fun j _ => ?_
    have : Pi.single j (x j) = Pi.single j (1 : R j) * y j := by
      funext k
      by_cases hk : k = j
      · subst hk; simpa using (e k).symm
      · simp [Pi.single_eq_of_ne hk]
    exact this ▸ Ideal.mul_mem_left _ _ (hy j)
  refine ⟨key I, fun J h => ?_⟩
  ext x
  rw [key I, key J]
  simp [h]

private theorem pi_quotient_linearEquiv_of_mem_iff (O : Type) [CommRing O] (ι : Type)
    (C : ι → Type) [∀ j, CommRing (C j)] [∀ j, Algebra O (C j)] (I : Ideal (∀ j, C j))
    (J : ∀ j, Ideal (C j))
    (hI : ∀ x : ∀ j, C j, x ∈ I ↔ ∀ j, x j ∈ J j) :
    ∃ ψ : ((∀ j, C j) ⧸ I) ≃ₗ[O] (∀ j, C j ⧸ J j), ∀ x : ∀ j, C j,
      ψ (Ideal.Quotient.mk I x) = fun j => Ideal.Quotient.mk (J j) (x j) := by
  let Θ : (∀ j, C j) →ₐ[O] ∀ j, C j ⧸ J j :=
    AlgHom.pi (fun j => (Ideal.Quotient.mkₐ O (J j)).comp (Pi.evalAlgHom O C j))
  have hΘ : ∀ x, Θ x = fun j => Ideal.Quotient.mk (J j) (x j) := fun x => rfl
  have hsurj : Function.Surjective Θ := fun y =>
    ⟨fun j => (Ideal.Quotient.mk_surjective (y j)).choose,
      funext fun j => (Ideal.Quotient.mk_surjective (y j)).choose_spec⟩
  have hker : I = RingHom.ker Θ := by
    ext x
    rw [hI, RingHom.mem_ker, hΘ, funext_iff]
    simp [Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨((Ideal.quotientEquivAlgOfEq O hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)).toLinearEquiv, fun x => rfl⟩

/-- Quotients of a finite product of `O`-algebras by `(g)` and by `(g, e)` are the products of the
componentwise quotients. -/
theorem pi_quotient_span_linearEquiv (O : Type) [CommRing O] (ι : Type) (C : ι → Type)
    [∀ j, CommRing (C j)] [∀ j, Algebra O (C j)] (g e : ∀ j, C j) :
    (∃ ψ : ((∀ j, C j) ⧸ Ideal.span {g}) ≃ₗ[O] (∀ j, C j ⧸ Ideal.span {g j}),
      ∀ x : ∀ j, C j, ψ (Ideal.Quotient.mk (Ideal.span {g}) x) =
        fun j => Ideal.Quotient.mk (Ideal.span {g j}) (x j)) ∧
      ∃ ψ' : ((∀ j, C j) ⧸ (Ideal.span {g} ⊔ Ideal.span {e})) ≃ₗ[O]
        (∀ j, C j ⧸ (Ideal.span {g j} ⊔ Ideal.span {e j})),
      ∀ x : ∀ j, C j, ψ' (Ideal.Quotient.mk (Ideal.span {g} ⊔ Ideal.span {e}) x) =
      fun j => Ideal.Quotient.mk (Ideal.span {g j} ⊔ Ideal.span {e j}) (x j) := by
  refine ⟨pi_quotient_linearEquiv_of_mem_iff O ι C _ _ ?_,
    pi_quotient_linearEquiv_of_mem_iff O ι C _ _ ?_⟩
  · intro x
    simp only [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩ j; exact ⟨a j, rfl⟩
    · intro h
      exact ⟨fun j => Classical.choose (h j), funext fun j => Classical.choose_spec (h j)⟩
  · intro x
    simp only [Submodule.mem_sup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ j
      exact ⟨_, ⟨a j, rfl⟩, _, ⟨b j, rfl⟩, rfl⟩
    · intro h
      choose y hy z hz hyz using h
      choose a ha using hy
      choose b hb using hz
      refine ⟨fun j => a j * g j, ⟨a, rfl⟩, fun j => b j * e j, ⟨b, rfl⟩, ?_⟩
      funext j
      simp [ha, hb, hyz]

/-- With the topology and σ-algebra transported along the power-basis coordinates, `O[X]/(Φ)` is a
compact Hausdorff second-countable Borel topological ring, and the coordinates are a
homeomorphism and a measurable equivalence. -/
theorem power_coordinates_transport (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (Φ : Polynomial O) (hm : Φ.Monic)
    [TopologicalSpace (AdjoinRoot Φ)]
    (hτ : ‹TopologicalSpace (AdjoinRoot Φ)› = unramifiedTopology O Φ hm)
    [MeasurableSpace (AdjoinRoot Φ)]
    (hmeas : ‹MeasurableSpace (AdjoinRoot Φ)› = unramifiedMeasurableSpace O Φ hm) :
    IsTopologicalRing (AdjoinRoot Φ) ∧ CompactSpace (AdjoinRoot Φ) ∧ T2Space (AdjoinRoot Φ) ∧
      SecondCountableTopology (AdjoinRoot Φ) ∧ BorelSpace (AdjoinRoot Φ) ∧
      Continuous (powerCoordinates O Φ hm) ∧ Continuous (powerCoordinates O Φ hm).symm ∧
      Measurable (powerCoordinates O Φ hm) ∧ Measurable (powerCoordinates O Φ hm).symm := by
  set e := powerCoordinates O Φ hm with he
  have hind : Topology.IsInducing e := ⟨by rw [hτ]; rfl⟩
  let h : AdjoinRoot Φ ≃ₜ (Fin Φ.natDegree → O) := e.toEquiv.toHomeomorphOfIsInducing hind
  have hc : Continuous e := h.continuous
  have hcs : Continuous e.symm := h.symm.continuous
  have hborel : BorelSpace (AdjoinRoot Φ) := by
    refine ⟨?_⟩
    rw [hmeas]; unfold unramifiedMeasurableSpace
    rw [BorelSpace.measurable_eq (α := Fin Φ.natDegree → O), ← borel_comap, hτ]
    rfl
  have hadd : IsTopologicalAddGroup (AdjoinRoot Φ) := by
    subst hτ
    exact topologicalAddGroup_induced e.toLinearMap.toAddMonoidHom
  have hmul : ContinuousMul (AdjoinRoot Φ) := by
    refine ⟨?_⟩
    rw [hind.continuous_iff]
    let b := (AdjoinRoot.powerBasis' hm).basis
    have key : ∀ x y : AdjoinRoot Φ, e (x * y) =
        ∑ j, ∑ l, (e x j * e y l) • e (b j * b l) := by
      intro x y
      have hx : x = ∑ j, e x j • b j := (b.sum_equivFun x).symm
      have hy : y = ∑ j, e y j • b j := (b.sum_equivFun y).symm
      conv_lhs => rw [hx, hy]
      rw [Finset.sum_mul_sum]
      simp only [smul_mul_smul_comm, map_sum, map_smul]
    have : (fun p : AdjoinRoot Φ × AdjoinRoot Φ => e (p.1 * p.2)) =
        fun p => ∑ j, ∑ l, (e p.1 j * e p.2 l) • e (b j * b l) := by
      funext p; exact key p.1 p.2
    change Continuous (fun p : AdjoinRoot Φ × AdjoinRoot Φ => e (p.1 * p.2))
    rw [this]
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun l _ => ?_
    exact (((continuous_apply j).comp (hc.comp continuous_fst)).mul
      ((continuous_apply l).comp (hc.comp continuous_snd))).smul continuous_const
  have := h.secondCountableTopology
  refine ⟨{ }, h.symm.compactSpace, h.symm.t2Space, h.secondCountableTopology, hborel,
    hc, hcs, h.measurable, h.symm.measurable⟩

/-- In a finite local ring, `#{generators of (f)} · #{a | a f = 0} = #Bˣ` for `f ≠ 0`. -/
theorem principal_generator_orbit_count (B : Type) [CommRing B] [IsLocalRing B] [Finite B] (f : B)
    (hf : f ≠ 0) :
    Nat.card {g : B // Ideal.span {g}=Ideal.span {f}} * Nat.card {a : B // a*f=0} =
      Nat.card Bˣ := by
  have := Fintype.ofFinite B
  classical
  -- annihilator elements are nonunits
  have hnu : ∀ a : B, a * f = 0 → IsUnit (1 + a) := by
    intro a ha
    have : -a ∈ nonunits B := by
      intro hu
      apply hf
      obtain ⟨v, hv⟩ := (IsUnit.neg_iff a).mp hu |>.exists_left_inv
      calc f = (v * a) * f := by rw [hv, one_mul]
        _ = 0 := by rw [mul_assoc, ha, mul_zero]
    simpa [sub_neg_eq_add] using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ this
  let G := {g : B // Ideal.span {g}=Ideal.span {f}}
  let φ : Bˣ → G := fun u => ⟨u*f, Ideal.span_singleton_mul_left_unit u.isUnit f⟩
  have hsurj : ∀ g : G, ∃ u : Bˣ, φ u = g := by
    rintro ⟨g, hg⟩
    have h1 : g ∈ Ideal.span {f} := hg ▸ Ideal.mem_span_singleton_self g
    have h2 : f ∈ Ideal.span {g} := hg ▸ Ideal.mem_span_singleton_self f
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h2
    have ha : IsUnit a := by
      by_contra hna
      have hba : b * a ∈ nonunits B := fun h => hna (isUnit_of_mul_isUnit_right h)
      have hu := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hba
      apply hf
      have : (1 - b * a) * f = 0 := by
        rw [sub_mul, one_mul, mul_assoc, hb, sub_self]
      exact (hu.mul_right_eq_zero).mp this
    exact ⟨ha.unit, Subtype.ext rfl⟩
  have hfib : ∀ g : G, Nat.card {u : Bˣ // φ u = g} = Nat.card {a : B // a*f=0} := by
    intro g
    obtain ⟨u₀, rfl⟩ := hsurj g
    apply Nat.card_congr
    refine
      { toFun := fun u => ⟨((u₀⁻¹ * u.1 : Bˣ) : B) - 1, ?_⟩
        invFun := fun a => ⟨u₀ * (hnu a.1 a.2).unit, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hu := congrArg Subtype.val u.2
      simp only [φ] at hu
      rw [sub_mul, one_mul, Units.val_mul, mul_assoc, hu, ← mul_assoc, Units.inv_mul, one_mul,
        sub_self]
    · apply Subtype.ext
      simp only [φ, Units.val_mul, IsUnit.unit_spec]
      rw [mul_assoc, add_mul, a.2, one_mul, add_zero]
    · intro u
      apply Subtype.ext; apply Units.ext
      simp
    · intro a
      apply Subtype.ext
      simp
  have := Fintype.card_congr (Equiv.sigmaFiberEquiv φ)
  rw [Fintype.card_sigma] at this
  simp only [← Nat.card_eq_fintype_card] at this
  rw [← this, Finset.sum_congr rfl (fun g _ => hfib g), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card]

/-- Coordinates on a finite product of free extensions: a measurable `O`-linear equivalence
`O^n ≃ ∏ⱼ Oⱼ^(nⱼ)` (with `n = ∑ δⱼ nⱼ`) and representatives `bc` compatible with given
representatives `bc' j` in each factor. -/
theorem product_coordinates_exist (O : Type) [CommRing O] [MeasurableSpace O] (ι : Type) [Fintype ι]
    (Oj : ι → Type) [∀ j, CommRing (Oj j)] [∀ j, Algebra O (Oj j)] [∀ j, MeasurableSpace (Oj j)]
    (R : ι → Type) [∀ j, CommRing (R j)] [∀ j, Algebra O (R j)] [∀ j, Algebra (Oj j) (R j)]
    [∀ j, IsScalarTower O (Oj j) (R j)] (δ nn : ι → ℕ) (pc : ∀ j, Oj j ≃ₗ[O] (Fin (δ j) → O))
    (hpc : ∀ j, Measurable (pc j)) (hpc' : ∀ j, Measurable (pc j).symm) (n : ℕ)
    (hn : ∑ j, δ j * nn j = n) (bc' : ∀ j, Fin (nn j) → R j) :
    ∃ (ρ : (Fin n → O) ≃ₗ[O] (∀ j, Fin (nn j) → Oj j)) (bc : Fin n → ∀ j, R j), Measurable ρ ∧
      Measurable ρ.symm ∧ ∀ (w : Fin n → O) (j : ι), coordinateLift bc w j =
      coordinateLift (bc' j) (ρ w j) := by
  classical
  have hcard : Fintype.card (Σ j : ι, Σ _ : Fin (nn j), Fin (δ j)) = n := by
    simp [Fintype.card_sigma, ← hn, mul_comm]
  let κ := Fintype.equivFinOfCardEq hcard
  let ρ : (Fin n → O) ≃ₗ[O] (∀ j, Fin (nn j) → Oj j) :=
    (LinearEquiv.funCongrLeft O O κ).trans <|
      (LinearEquiv.piCurry O (fun _ _ => O)).trans <|
        (LinearEquiv.piCongrRight fun j => LinearEquiv.piCurry O (fun _ _ => O)).trans <|
          LinearEquiv.piCongrRight fun j => LinearEquiv.piCongrRight fun _ => (pc j).symm
  have hρ : ∀ w j i, ρ w j i = (pc j).symm (fun l => w (κ ⟨j, i, l⟩)) := fun _ _ _ => rfl
  have hρs : ∀ v j i l, ρ.symm v (κ ⟨j, i, l⟩) = pc j (v j i) l := by
    intro v j i l
    simp [ρ, LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply]; rfl
  let bc : Fin n → ∀ j, R j := fun m =>
    (fun s : (Σ j : ι, Σ _ : Fin (nn j), Fin (δ j)) =>
      Pi.single s.1
        (algebraMap (Oj s.1) (R s.1) ((pc s.1).symm (Pi.single s.2.2 1)) * bc' s.1 s.2.1))
      (κ.symm m)
  refine ⟨ρ, bc, ?_, ?_, ?_⟩
  · rw [measurable_pi_iff]; intro j
    rw [measurable_pi_iff]; intro i
    have : (fun w => ρ w j i) = fun w => (pc j).symm (fun l => w (κ ⟨j, i, l⟩)) := rfl
    rw [this]
    exact (hpc' j).comp (measurable_pi_iff.mpr fun l => measurable_pi_apply _)
  · rw [measurable_pi_iff]; intro m
    obtain ⟨⟨j, i, l⟩, rfl⟩ := κ.surjective m
    simp only [hρs]
    exact (measurable_pi_apply l).comp
      ((hpc j).comp ((measurable_pi_apply i).comp (measurable_pi_apply j)))
  · intro w j
    have hbc : ∀ s, bc (κ s) = Pi.single s.1
        (algebraMap (Oj s.1) (R s.1) ((pc s.1).symm (Pi.single s.2.2 1)) * bc' s.1 s.2.1) := by
      intro s
      change (fun s : (Σ j : ι, Σ _ : Fin (nn j), Fin (δ j)) => Pi.single s.1
        (algebraMap (Oj s.1) (R s.1) ((pc s.1).symm (Pi.single s.2.2 1)) * bc' s.1 s.2.1))
          (κ.symm (κ s)) = _
      rw [κ.symm_apply_apply]
    have hθ : ∀ i, ρ w j i = ∑ l, w (κ ⟨j, i, l⟩) • (pc j).symm (Pi.single l 1) := by
      intro i
      simp_rw [hρ, ← map_smul, ← map_sum]
      congr 1
      ext l'
      simp [Finset.sum_apply, Pi.single_apply]
    unfold coordinateLift
    rw [Finset.sum_apply, ← κ.sum_comp]
    simp only [Pi.smul_apply, hbc]
    rw [Fintype.sum_sigma, Finset.sum_eq_single j]
    · rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hθ, Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Pi.single_eq_same]
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply, mul_assoc]
    · intro j' _ hj'
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [Pi.single_eq_of_ne (Ne.symm hj'), smul_zero]
    · simp

/-- Division equivalences in the factors assemble into a division equivalence on the product. -/
theorem product_division_equiv (O : Type) [CommRing O] (ι : Type) (Oj : ι → Type)
    [∀ j, CommRing (Oj j)] [∀ j, Algebra O (Oj j)] (R : ι → Type) [∀ j, CommRing (R j)]
    [∀ j, Algebra O (R j)] [∀ j, Algebra (Oj j) (R j)] [∀ j, IsScalarTower O (Oj j) (R j)]
    (nn : ι → ℕ) (n : ℕ) (ρ : (Fin n → O) ≃ₗ[O] (∀ j, Fin (nn j) → Oj j))
    (bc' : ∀ j, Fin (nn j) → R j) (bc : Fin n → ∀ j, R j)
    (hcompat : ∀ (w : Fin n → O) (j : ι), coordinateLift bc w j = coordinateLift (bc' j) (ρ w j))
    (g : ∀ j, R j) (E' : ∀ j, R j ≃ₗ[Oj j] ((Fin (nn j) → Oj j) × R j))
    (hE' : ∀ j w, (E' j).symm w = divisionMap (g j) (bc' j) w) :
    (letI : Module O (∀ j, R j) := Algebra.toModule;
      ∃ E : (∀ j, R j) ≃ₗ[O] ((Fin n → O) × ∀ j, R j), ∀ w, E.symm w = divisionMap g bc w) := by
  let _ : Module O (∀ j, R j) := Algebra.toModule
  have hcl : ∀ (m : ℕ) (b : Fin m → ∀ j, R j) (z : Fin m → O) (j : ι),
      coordinateLift b z j = ∑ i, z i • b i j := by
    intro m b z j
    simp [coordinateLift, Finset.sum_apply]
  have hadd : ∀ (w w' : Fin n → O),
      coordinateLift bc (w + w') = coordinateLift bc w + coordinateLift bc w' := by
    intro w w'; funext j; simp [hcl, add_smul, Finset.sum_add_distrib]
  have hsm : ∀ (c : O) (w : Fin n → O), coordinateLift bc (c • w) = c • coordinateLift bc w := by
    intro c w; funext j; simp [hcl, Finset.smul_sum, smul_smul]
  let L : ((Fin n → O) × ∀ j, R j) →ₗ[O] ∀ j, R j :=
    { toFun := fun s => divisionMap g bc s
      map_add' := by
        intro a b
        simp only [divisionMap, Prod.fst_add, Prod.snd_add, hadd, mul_add]
        abel
      map_smul' := by
        intro c a
        simp only [divisionMap, Prod.smul_fst, Prod.smul_snd, hsm, RingHom.id_apply, smul_add,
          Algebra.mul_smul_comm] }
  have hL : ∀ s j, L s j = (E' j).symm (ρ s.1 j, s.2 j) := by
    intro s j
    rw [hE']
    change (divisionMap g bc s) j = _
    simp only [divisionMap, Pi.add_apply, Pi.mul_apply, hcompat]
  have hinj : Function.Injective L := by
    intro a b h
    have h1 : ∀ j, (ρ a.1 j, a.2 j) = (ρ b.1 j, b.2 j) := fun j =>
      (E' j).symm.injective (by rw [← hL, ← hL, h])
    have h2 : ρ a.1 = ρ b.1 := funext fun j => congrArg Prod.fst (h1 j)
    have h3 : a.2 = b.2 := funext fun j => congrArg Prod.snd (h1 j)
    exact Prod.ext (ρ.injective h2) h3
  have hsurj : Function.Surjective L := by
    intro x
    refine ⟨(ρ.symm (fun j => (E' j (x j)).1), fun j => (E' j (x j)).2), ?_⟩
    funext j
    rw [hL]
    simp
  exact ⟨(LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).symm, fun w => rfl⟩

/-- `(C/I) / e(C/I) ≃ C/(I + (e))` as `O`-modules, compatibly with the quotient maps. -/
theorem quotient_mul_range_equiv (O C : Type) [CommRing O] [CommRing C] [Algebra O C] (I : Ideal C)
    (e : C) :
    ∃ φ : ((C ⧸ I) ⧸ LinearMap.range (LinearMap.mulLeft O (Ideal.Quotient.mk I e))) ≃ₗ[O]
      (C ⧸ (I ⊔ Ideal.span {e})),
      ∀ x : C, φ (Submodule.Quotient.mk (Ideal.Quotient.mk I x)) =
      Ideal.Quotient.mk (I ⊔ Ideal.span {e}) x := by
  set S : Submodule O C := I.restrictScalars O with hS
  set T : Submodule O C := (I ⊔ Ideal.span {e}).restrictScalars O with hT
  have h : S ≤ T := fun x hx => Ideal.mem_sup_left hx
  let f : (C ⧸ S) ≃ₗ[O] (C ⧸ I) := Submodule.Quotient.restrictScalarsEquiv O I
  let g : (C ⧸ T) ≃ₗ[O] (C ⧸ (I ⊔ Ideal.span {e})) :=
    Submodule.Quotient.restrictScalarsEquiv O (I ⊔ Ideal.span {e})
  have hmap : (T.map S.mkQ).map (f : (C ⧸ S) →ₗ[O] (C ⧸ I)) =
      LinearMap.range (LinearMap.mulLeft O (Ideal.Quotient.mk I e)) := by
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, hzy⟩
      obtain ⟨i, hi, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hw
      refine ⟨Ideal.Quotient.mk I c, ?_⟩
      have : (f : (C ⧸ S) →ₗ[O] (C ⧸ I)) (S.mkQ (i + c * e)) =
        Ideal.Quotient.mk I (i + c * e) := rfl
      rw [← hzy, this, map_add, (Ideal.Quotient.eq_zero_iff_mem).2 hi, zero_add, map_mul, mul_comm]
    · rintro ⟨c', hc'⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
      refine ⟨S.mkQ (e * c), ⟨e * c, ?_, rfl⟩, ?_⟩
      · exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self e))
      · have : (f : (C ⧸ S) →ₗ[O] (C ⧸ I)) (S.mkQ (e * c)) = Ideal.Quotient.mk I (e * c) := rfl
        rw [this, map_mul]; exact hc'
  let E : ((C ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[O]
      ((C ⧸ I) ⧸ LinearMap.range (LinearMap.mulLeft O (Ideal.Quotient.mk I e))) :=
    Submodule.Quotient.equiv _ _ f hmap
  refine ⟨E.symm.trans ((Submodule.quotientQuotientEquivQuotient S T h).trans g), fun x => ?_⟩
  rw [show Submodule.Quotient.mk (Ideal.Quotient.mk I x) = E (Submodule.Quotient.mk (S.mkQ x))
    from rfl]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- Two generators of the same principal ideal, one of them regular, differ by a unit. -/
theorem regular_principal_generators_associated (A : Type) [CommRing A] (f g : A)
    (hf : Function.Injective (fun x : A => x*f)) (hfg : Ideal.span {f} = Ideal.span {g}) :
    ∃ u : Aˣ, g = (u : A)*f := by
  have hg : g ∈ Ideal.span {f} := hfg ▸ Ideal.subset_span rfl
  have hf' : f ∈ Ideal.span {g} := hfg ▸ Ideal.subset_span rfl
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hg
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hf'
  have hab : a * b = 1 := by
    apply hf
    simp only [one_mul]
    rw [mul_assoc, hb, ha]
  refine ⟨⟨b, a, by rw [mul_comm]; exact hab, hab⟩, hb.symm⟩

/-- In a DVR with finite residue field, `#(O/𝔪^L) = q ^ L`. -/
theorem residue_quotient_card (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (L : ℕ) :
    Nat.card (O ⧸ (IsLocalRing.maximalIdeal O)^L)=(Nat.card (IsLocalRing.ResidueField O))^L := by
  have h := cardQuot_pow_of_prime (S := O) (P := IsLocalRing.maximalIdeal O)
    (IsDiscreteValuationRing.not_a_field O) (i := L)
  rwa [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h

/-- The coefficient measure of a ball `a + (𝔪^L)^n` in `O^n` is `q^(-nL)`. -/
theorem coefficient_cylinder_mass (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n L : ℕ) (a : Fin n → O) :
    coefficientMeasure O n {b | ∀ i, b i-a i∈(IsLocalRing.maximalIdeal O)^L} =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(n*L) := by
  set I := (IsLocalRing.maximalIdeal O)^L with hI
  set μ := coefficientMeasure O n with hμ
  have hopen : IsOpen (I : Set O) := (isAdic_iff.mp htop).1 L
  let C0 : Set (Fin n → O) := {b | ∀ i, b i ∈ I}
  have hC0 : MeasurableSet C0 := by
    have : C0 = Set.univ.pi (fun _ => (I : Set O)) := by ext b; simp [C0]
    rw [this]; exact (isOpen_set_pi Set.finite_univ (fun _ _ => hopen)).measurableSet
  have : μ.IsAddLeftInvariant := by rw [hμ, coefficientMeasure]; infer_instance
  have hprob : μ Set.univ = 1 := by
    rw [hμ, coefficientMeasure, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (Measure.measure_univ_pos.mpr (NeZero.ne _)).ne'
      (measure_ne_top _ _)
  -- translate
  have htrans : ∀ x : Fin n → O, μ {b | ∀ i, b i - x i ∈ I} = μ C0 := by
    intro x
    have : {b : Fin n → O | ∀ i, b i - x i ∈ I} = (fun b => -x + b) ⁻¹' C0 := by
      ext b; simp [C0, sub_eq_neg_add]
    rw [this, measure_preimage_add]
  rw [htrans a]
  let π : (Fin n → O) → (Fin n → O ⧸ I) := fun b i => Ideal.Quotient.mk I (b i)
  have hfib : ∀ x : Fin n → O, π ⁻¹' {π x} = {b | ∀ i, b i - x i ∈ I} := by
    intro x; ext b; simp [π, funext_iff, Ideal.Quotient.eq]
  have hsurj : Function.Surjective π := by
    intro c; exact ⟨fun i => (Ideal.Quotient.mk_surjective (c i)).choose,
      funext fun i => (Ideal.Quotient.mk_surjective (c i)).choose_spec⟩
  have : Finite (O ⧸ I) := by
    apply Nat.finite_of_card_ne_zero
    rw [hI, residue_quotient_card]
    exact pow_ne_zero _ Nat.card_pos.ne'
  have : Fintype (Fin n → O ⧸ I) := Fintype.ofFinite _
  have hsum : μ Set.univ = ∑ c : Fin n → O ⧸ I, μ (π ⁻¹' {c}) := by
    rw [← measure_biUnion_finset]
    · congr 1; ext b; simp
    · intro c _ d _ hcd; exact Set.disjoint_left.mpr fun b h1 h2 => hcd (h1.symm.trans h2)
    · intro c _
      obtain ⟨x, rfl⟩ := hsurj c
      rw [hfib]
      have : {b : Fin n → O | ∀ i, b i - x i ∈ I} = (fun b => -x + b) ⁻¹' C0 := by
        ext b; simp [C0, sub_eq_neg_add]
      rw [this]; exact hC0.preimage (measurable_const_add _)
  have hconst : ∀ c, μ (π ⁻¹' {c}) = μ C0 := by
    intro c; obtain ⟨x, rfl⟩ := hsurj c; rw [hfib, htrans]
  simp only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hprob] at hsum
  have hcard : (Fintype.card (Fin n → O ⧸ I) : ℝ≥0∞) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)^(n*L) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n),
      Fintype.card_fin,
      hI, residue_quotient_card]
    push_cast; ring
  rw [hcard] at hsum
  rw [← ENNReal.inv_pow]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum.symm)

/-- The coefficient measure of `O^n` is a probability measure. -/
theorem coefficient_measure_probability (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    MeasureTheory.IsProbabilityMeasure (coefficientMeasure O n) :=
  ⟨by simpa using coefficient_cylinder_mass O htop n 0 0⟩

/-- A chart measure with measurable chart map has total mass one. -/
theorem chart_measure_total_mass (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) [CommRing R] [Algebra O R]
    [MeasurableSpace (Ideal R)] (pi : O) (n : ℕ) (c : IdealChart O R pi n)
    (hc : Measurable (coordinateIdeal pi c.f c.b)) :
    chartMeasure O R pi n c Set.univ = 1 := by
  have := coefficient_measure_probability O htop n
  rw [chartMeasure, Measure.map_apply hc MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- The coefficient measure of a `π`-adic cylinder of level `j` in `O^n` is `q^(-nj)`. -/
theorem coefficient_uniformizer_cylinder_mass (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (pi : O) (hp : Irreducible pi) (j : ℕ)
    (x : Fin n → O) :
    coefficientMeasure O n {z | adicCongr (Ideal.span {pi}) j z x} =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(n*j) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {pi} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hp
  have hset : {z : Fin n → O | adicCongr (Ideal.span {pi}) j z x} =
      {b | ∀ i, b i - x i ∈ (IsLocalRing.maximalIdeal O)^j} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [finite_coordinate_adic_congruence, hm]
  rw [hset]
  exact coefficient_cylinder_mass O htop n j x

end SurfaceBlowup
