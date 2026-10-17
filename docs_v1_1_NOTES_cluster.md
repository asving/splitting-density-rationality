# NOTES_A — Task A (cluster clause)

Verdict: **PROVED.** All targets are proved exactly as stated in BRIEF.md, with no added
hypotheses: `main_dvr_cluster` holds for all `n`, including `n = 0`, without `0 < n`. The
coordinator's addendum `clusterDensity_eq_etale` is proved too, and so is the optional
quadratic regression.

## (a) Verbatim statements

`SurfaceBlowup/Cluster/Defs.lean` (namespace `SurfaceBlowup`):

```lean
variable (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]

/-- The cluster cell `(πO)^n`: coefficient vectors whose monic polynomial reduces to `X^n`
(paper display (1.1), measure `μ_cluster`). -/
def clusterCell (n : ℕ) : Set (Fin n → O) := {a | ∀ i, a i ∈ IsLocalRing.maximalIdeal O}

/-- `B_{n,σ}`: the coefficient of `σ` in the root law, the law of the state `S(1;n)`
(paper display (7.1)). -/
noncomputable def clusterExpr (n : ℕ) (σ : FactorType) : Expr := lawCoeff (rootLaw n) σ

variable (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [SecondCountableTopology O]
  [MeasurableSpace O] [BorelSpace O]

/-- The cluster probability of type `σ` (paper display (1.1)): the normalized restriction of
the coefficient measure to the cluster cell. The event uses `HasPolynomialType` (the
reduced-algebra convention: a factorization into distinct monic irreducible factors, inseparable
factors allowed); the inseparable locus is Haar-null, so the étale convention gives the same
value (`clusterDensity_eq_etale`). -/
noncomputable def clusterDensity (n : ℕ) (σ : FactorType) : ℝ≥0∞ :=
  coefficientMeasure O n (clusterCell O n ∩ {a | HasPolynomialType O (monicPolynomial O a) σ}) /
    coefficientMeasure O n (clusterCell O n)
```

`SurfaceBlowup/Cluster/Main.lean` (namespace `SurfaceBlowup`):

```lean
theorem main_dvr_cluster (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    clusterDensity O n σ =
      densityValue (clusterExpr n σ) (Nat.card (IsLocalRing.ResidueField O))

theorem clusterDensity_eq_etale (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    clusterDensity O n σ =
      coefficientMeasure O n (clusterCell O n ∩
        {a | (monicPolynomial O a).Separable ∧ HasPolynomialType O (monicPolynomial O a) σ}) /
        coefficientMeasure O n (clusterCell O n)

theorem cluster_formula_regular (n : ℕ) (σ : FactorType) :
    ∀ q : ℕ, PrimePower q → RegularAt (clusterExpr n σ).rational q

theorem recip_cluster (n : ℕ) (hn : 0 < n) (σ : FactorType) :
    (monicExpr n σ).rational = ((clusterExpr n σ).subst (.inv .var)).rational
```

Private helpers in Main.lean: `hasPolynomialType_one_iff` (`HasPolynomialType O 1 σ ↔ σ = 0`),
`clusterCell_eq_image` (`clusterCell O n = (fun z => pi • z) '' Set.univ` for irreducible `pi`),
`clusterCell_inter_eq_image` (cluster cell ∩ route-F event = `(pi • ·) ''` root event).

Optional regression, `Tests/Cluster.lean` (namespace `SurfaceBlowup.Tests`, with the measure
variables of `main_dvr` and `open IsLocalRing`):

```lean
theorem clusterDensity_two_ramified (htop : IsAdic (maximalIdeal O)) :
    clusterDensity O 2 {(2,1)} =
      ENNReal.ofReal (Nat.card (ResidueField O) / (Nat.card (ResidueField O) + 1))
theorem clusterDensity_two_split (htop : IsAdic (maximalIdeal O)) :
    clusterDensity O 2 {(1,1),(1,1)} =
      ENNReal.ofReal (1 / (2 * (Nat.card (ResidueField O) + 1)))
theorem clusterDensity_two_inert (htop : IsAdic (maximalIdeal O)) :
    clusterDensity O 2 {(1,2)} =
      ENNReal.ofReal (1 / (2 * (Nat.card (ResidueField O) + 1)))
```
(plus the private `clusterDensity_two` giving all three as one sum of indicators). The three
values sum to `q/(q+1) + 1/(q+1) = 1`.

## (b) Files

New files:
- `SurfaceBlowup/Cluster/Defs.lean` (56 lines; imports `SurfaceBlowup.Basic`)
- `SurfaceBlowup/Cluster/Main.lean` (155 lines; imports `SurfaceBlowup.Cluster.Defs`,
  `SurfaceBlowup.Main`)
- `Tests/Cluster.lean` (optional regression; imports `SurfaceBlowup.Cluster.Main`, `Tests.Regression`)
- `scratch/ClusterAxioms.lean` (the `#print axioms` scratch file; not part of any lean_lib glob)

De-privatized: `SurfaceBlowup.Tests.single_two_law` in `Tests/Regression.lean` (line 1020; only
the `private` modifier was removed). Nothing else was edited. No frozen file was touched.
`SurfaceBlowup.lean` and `Tests.lean` are frozen and therefore do not import the new modules;
the `lean_lib` globs (`.andSubmodules`) still build them under `lake build`.

## (c) Check commands and output

```
$ taskset -c 0-7 lake build SurfaceBlowup.Cluster.Defs
✔ [3202/3202] Built SurfaceBlowup.Cluster.Defs
Build completed successfully (3202 jobs).
$ taskset -c 0-7 lake build Tests.Regression          # after de-privatizing single_two_law
Build completed successfully (3461 jobs).             # (no warnings/errors)
$ taskset -c 0-7 lake build Tests.Cluster SurfaceBlowup.Cluster.Main
✔ [3464/3464] Built Tests.Cluster
Build completed successfully (3464 jobs).
$ taskset -c 0-7 lake env lean SurfaceBlowup/Cluster/Defs.lean   # no output, exit 0
$ taskset -c 0-7 lake env lean SurfaceBlowup/Cluster/Main.lean   # no output, exit 0
$ taskset -c 0-7 lake env lean Tests/Cluster.lean                # no output, exit 0
$ taskset -c 0-7 lake env lean scratch/ClusterAxioms.lean
'SurfaceBlowup.main_dvr_cluster' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.clusterDensity_eq_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.cluster_formula_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.recip_cluster' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.Tests.clusterDensity_two_ramified' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.Tests.clusterDensity_two_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.Tests.clusterDensity_two_inert' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No line over 100 characters, and no `sorry`/`admit`/`native_decide`/`maxHeartbeats`/`axiom` in
the new files (checked with grep and awk).

## (d) Proof sketches

**main_dvr_cluster.** Case `n = 0`: `clusterCell O 0 = univ` and `monicPolynomial O a = 1`.
Also `HasPolynomialType O 1 σ ↔ σ = 0`, because a factor of `1` is a unit, so it cannot be
irreducible, so the factor list is empty. The event is therefore `univ` or `∅`, its measure is
`1` or `0`, and `rootLaw 0 = lawOne` gives `lawCoeff lawOne σ` evaluating to `1` or `0`
correspondingly.

Case `n > 0`: fix a uniformizer `pi` (`IsDiscreteValuationRing.exists_irreducible`).
`maximalIdeal O = span {pi}`, so `clusterCell O n = (pi • ·) '' univ`. On the cell, the
published event `HasPolynomialType` and the route-F event `HasPolynomialTypeF` agree outside
`{a | ¬ Separable}` (`hasPolynomialTypeF_iff_of_separable`), and that set is null
(`monic_inseparable_null`). So the numerator equals μ(cell ∩ route-F event), by `measure_congr`.
That set is `(pi • ·) ''` of the root event `{z | HasPolynomialTypeF (monicPolynomial (pi • z)) σ}`.
The root event is measurable, with mass `densityValue (lawCoeff (stateLaw (.single 1 n)) σ) q`
(`root_cell_law`). `scaling_image_borel_mass` gives numerator `q⁻¹ⁿ · densityValue …` and
denominator `q⁻¹ⁿ · μ univ = q⁻¹ⁿ` (`coefficient_measure_probability`). Cancel the factor with
`ENNReal.mul_div_mul_left` (it is ≠ 0 and ≠ ⊤), then unfold `clusterExpr` and
`rootLaw` (`if_neg`).

**clusterDensity_eq_etale.** On the numerator, `measure_congr` with the a.e. equality from
`monic_inseparable_null`: off the inseparable locus, `Separable ∧ HasPolynomialType` is the same
as `HasPolynomialType`.

**cluster_formula_regular.** `LawSafe (rootLaw n)`: for `n = 0`, `lawOne` has the single
coefficient `const 1`, which is trivially safe. For `n > 0`, apply `local_law_safe (.single 1 n)`
with `⟨one_pos, hn⟩`. Coefficient extraction preserves safety (`expression_sum_safe`, mirroring
`global_coefficients_safe`). Then `expression_regular` at `q ≥ 2` (`prime_power_ge_two`).

**recip_cluster.** `clusterExpr n σ` is by definition `lawCoeff (rootLaw n) σ`, so this is
`(recip_main n hn σ).1`.

**Regression.** Rewrite with `main_dvr_cluster`, unfold `clusterExpr`/`rootLaw`/`densityValue`,
and rewrite with `single_two_law 1 one_pos q hq` (`1 < q` from `Finite.one_lt_card`). Then
`simp +decide` decides the multiset (in)equalities.

## (e) Verdict

**PROVED** — `main_dvr_cluster`, `clusterDensity_eq_etale`, `cluster_formula_regular` and
`recip_cluster` are proved as stated, with no added hypotheses. The optional regression
`Tests/Cluster.lean` is also proved.
