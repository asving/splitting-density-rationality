# SurfaceBlowup — factorization-type densities over complete DVRs

A Lean 4 / Mathlib formalization of the following theorem. Let `O` be a complete discrete valuation
ring with finite residue field of cardinality `q` (any characteristic, any ramification). For every
`n` and every factorization type `σ`, the probability that a Haar-random monic polynomial of degree
`n` over `O` (resp. a random primitive binary form of degree `n`) factors over `Frac O` with type
`σ` equals `A_{n,σ}(q)` (resp. `R_{n,σ}(q)`), where `A_{n,σ}`, `R_{n,σ}` are explicit universal
rational functions, given by a finite recursion over blow-ups of a regular arithmetic surface.
A second result is a reciprocity law for these rational functions.

Toolchain: Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (pinned in
`lakefile.lean` / `lake-manifest.json`).

## Main theorems

All in namespace `SurfaceBlowup`:

| theorem | file | statement (informal) |
|---|---|---|
| `main_dvr` | `SurfaceBlowup/Main.lean` | for `O` as above (adic topology, Borel σ-algebra, normalized Haar measure): `monicDensity O n σ = densityValue (monicExpr n σ) q` and `projectiveDensity O n σ = densityValue (projectiveExpr n σ) q` |
| `main_field_form` | `SurfaceBlowup/Main.lean` | the published rational-function form for rings of integers of unramified finite `K/ℚ_p` |
| `main_field_form_ramified` | `SurfaceBlowup/Main.lean` | the same for arbitrary finite `K/ℚ_p` |
| `recip_main` | `SurfaceBlowup/Reciprocity/Main.lean` | reciprocity: `A_n(q) = B_n(1/q)` and `R_n(1/q) = R_n(q)` |

`#print axioms` for all four: `[propext, Classical.choice, Quot.sound]` (`Checks/Axioms.lean`).

Verbatim statements (proofs omitted):

```lean
theorem main_dvr (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O))
    (n : ℕ) (σ : FactorType) :
    SurfaceBlowup.monicDensity O n σ =
        densityValue (monicExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) ∧
    SurfaceBlowup.projectiveDensity O n σ =
        densityValue (projectiveExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) := by ...

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
              ℚ) : ℝ) := by ...

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
          (projectiveExpr n σ).rational : ℚ) : ℝ) := by ...

theorem recip_main (n : ℕ) (hn : 0 < n) (σ : FactorType) :
    (monicExpr n σ).rational =
      ((lawCoeff (rootLaw n) σ).subst (.inv .var)).rational ∧
    (projectiveExpr n σ).rational =
      ((projectiveExpr n σ).subst (.inv .var)).rational := by ...
```

Compared with the certified (owner-signed) statements, the hypotheses `0 < n`, `ValidType σ`,
`typeDegree σ = n` of `main_dvr` / `main_field_form` / `main_field_form_ramified` and `ValidType σ`,
`typeDegree σ = n` of `recip_main` were dropped in cycle 4a (none was used by the proofs), so the
theorems are strictly stronger; `0 < n` of `recip_main` is used and kept. `Checks/run_checks.sh`
derives each certified statement, with its extra hypotheses, from the unified theorem in the kernel.

## Trust boundary

Lean checks proofs, not statements. Everything a reader must audit to trust the theorems is in
**`SurfaceBlowup/Basic.lean`** (~500 lines): the definitions of factorization types, the rational
expressions `Expr`, laws, recursion states, `stateLaw`, `monicExpr`, `projectiveExpr`, the densities
`monicDensity`, `projectiveDensity`, and `densityValue`, plus the main-theorem statements themselves
in `Main.lean` / `Reciprocity/Main.lean`. Every other file only contains proofs and auxiliary
definitions that do not occur in the main statements.

`Checks/run_checks.sh` verifies, at the kernel level, that the statements of `main_dvr`,
`recip_main` and `main_field_form` as certified in the original one-theorem-per-file trees
(`final/monolith_gen`, `final/monolith_recip`, `final/monolith`; read-only) follow from the unified
theorems: it loads both environments in one Lean process, pairs every certified constant in the
closure of the certified statement with an alpha-identical unified constant, checks that the
conclusions are constant-for-constant identical and that the unified hypotheses are a subsequence of
the certified ones (the rest being the dropped propositions), and type-checks
`certified_statement := fun x₀ … => unified_theorem …` (implication form).

The regression guards in `Tests/` pin the definitions to known numbers, e.g.
`(monicExpr 4 {(4,1)}).eval 2 = 107/1533`, and derive density corollaries from `main_dvr`.
`Tests/NonVacuity.lean` shows that the hypotheses of `main_dvr` are satisfiable in equal
characteristic: `𝔽_q⟦X⟧` with the coefficientwise topology, giving the formulas for `𝔽_p⟦X⟧`.

## License

Released under the Apache 2.0 license (file `LICENSE`); every file carries the Mathlib-style
copyright/authors header. Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI).
**OWNER: confirm license** (Apache 2.0 was chosen to match Mathlib; not yet confirmed).

## Building

    lake exe cache get        # Mathlib oleans (first time only)
    lake build                # builds SurfaceBlowup and Tests (~8800 jobs; ~8 min on 16 cores)
    lake env lean Checks/Axioms.lean
    ./Checks/run_checks.sh    # needs the certified trees next to this one (see the script)

or all of it at once: `tools/release_check.sh` (build, axioms, statement preservation, forbidden-token
grep, warning count; logs in `logs/release_*.log`). Other tools: `tools/StmtDump.lean` (hashes of the
type of every public declaration and the body of every definition; diff two dumps to prove a
refactor changed no statement), `tools/lint_census.sh` (Mathlib standard linters, per file),
`tools/longest_decls.py`, `tools/chk.sh` (check a file against a private frozen olean directory).

## Quality status

- 0 `sorry`/`admit`/`axiom`/`native_decide`, 0 `maxHeartbeats` options, 0 lines over 100 characters,
  no file over 1500 lines.
- Build warnings: 0.
- No module imports all of Mathlib (`import Mathlib`); every module imports only the Mathlib files it
  needs (cycle 4d).
- Mathlib standard linter set (`-Dweak.linter.mathlibStandardSet=true`): 0 hits (`tools/lint_census.sh`).
- No file-level `open Classical`: classical decidability is introduced per proof (`classical`) or per
  declaration (`open scoped Classical in`) exactly where a statement needs it.
- Every proof body is at most ~91 lines; the 5 declarations of 101-120 lines all have statements of
  11-57 lines (table: `logs/longest_decls_c4c.tsv`).
- Slowest modules (clean build, cycle 4c): `TwoChartCurveData` 67 s, `DivisorPoints` 66 s,
  `CurveOrders` 43 s, `Charts` 38 s (cycle 4a: 117, 86, 99, 152 s). No heartbeat options; the
  `TwoChartCurveData` proofs pass with `maxHeartbeats 85000`.

## Module hierarchy

Dependencies flow roughly top to bottom. Each module has a docstring with its main results.

- `Basic` — statement-level definitions (trust boundary).
- `Formula/` — the combinatorial side: law algebra and children of tangent patterns
  (`LawAlgebra`), ranks/safety of the recursion (`StateCombinatorics`), evaluation of the universal
  rational functions (`RationalEval`), finite-field counts (`FiniteFieldCounts`), divisor counts by
  tangent pattern (`PatternCounts`), transport of types and cell measures (`TypeTransport`).
- `Algebra/` — algebra types and integral closures over a DVR (`AlgebraType`), invariance of factor
  invariants (`FactorInvariant`).
- `Measure/` — adic cylinders and division charts, adic congruences and perturbations
  (`AdicTransport`), Hensel factorization and coefficient measures, Haar measures, atlases and state volumes, residue-ideal counts, member charts and boxes, the
  primitive locus.
- `Unramified/` — binary forms, factor cells, unramified extensions and Frobenius descent,
  polynomial types under base change, homogeneous cells.
- `Surfaces/` — the concrete surfaces `O⟦T, X⟧/(π − u·T^a·X^b)` (`u` a unit): lengths, power
  series structure, completeness, regularity, truncations, chart completions, closed points, ideal
  atlases, strict transforms and volumes.
- `Blowup/` — the point blow-up: closed directions and divisors on the exceptional line
  (`Directions`, depends only on `Basic`), charts and the exceptional line, curve orders,
  exceptional layers, point transport, nilpotent gluing, Čech comparison of global sections, strict transforms and the
  strict normalizer, curve sections, two-chart curve data, divisor points, and the bijection of
  strict transforms of a fixed tangent cell (`FixedTangentCellBijection`, Proposition 5.1 of the paper).
- `Recursion/` — the recursion universe: members, order defects, child members, return/exit events,
  termination, and the root cell law.
- `Assembly/` — type events and divisor counts, monic/projective cells, the Haar-null bridges from the
  original densities to the internal ones (`NullBridges`), and the density formulas (`Formulas`).
- `Reciprocity/` — independent of the surface tower (depends only on `Basic` and `Formula/`): series
  calculus, the quantum torus and reciprocal substitution, plethysm, pattern sums, the reciprocity law.
- `Main` — the main theorems.

### Module table

| module | lines | title |
|---|---:|---|
| `Algebra/AlgebraType` | 644 | Algebra types and integral closures over a discrete valuation ring |
| `Algebra/FactorInvariant` | 324 | Invariance of factor invariants and uniqueness of algebra types |
| `Assembly/Formulas` | 139 | The density formulas for the route-F densities |
| `Assembly/MonicCells` | 1342 | Monic, projective and divisor cells |
| `Assembly/NullBridges` | 490 | Strict-transform measures, type events and the projective null bridge |
| `Assembly/TypeEvents` | 1330 | Type events and divisor counts |
| `Basic` | 503 | Statement-level definitions (the trust boundary) |
| `Blowup/CechStability` | 312 | Stability of the finite Čech coefficients |
| `Blowup/Charts` | 1158 | Blow-up charts, the exceptional line, and curve data |
| `Blowup/CurveOrders` | 1050 | Curve orders, the exceptional line, and finitely supported local data |
| `Blowup/CurveSections` | 1110 | Curve sections on the two-chart blow-up |
| `Blowup/Directions` | 154 | Closed points and divisors on the exceptional line |
| `Blowup/DivisorPoints` | 1459 | Exceptional divisor points of two-chart curve data |
| `Blowup/ExceptionalLayers` | 842 | Exceptional layers of the point blow-up |
| `Blowup/FixedTangentCellBijection` | 480 | Strict transforms give a bijection on a fixed tangent cell |
| `Blowup/H0Comparison` | 1245 | Comparing surface functions with Čech data on the blow-up |
| `Blowup/NilpotentGluing` | 1490 | Nilpotent gluing of exceptional levels |
| `Blowup/PointTransport` | 1284 | Transport of points between blow-up charts |
| `Blowup/StrictNormalizer` | 1497 | Strict transforms and the strict normalizer |
| `Blowup/TwoChartCurveData` | 1389 | Two-chart curve data |
| `Formula/FiniteFieldCounts` | 78 | Counting over finite fields |
| `Formula/LawAlgebra` | 914 | Expression and law algebra, children of tangent patterns |
| `Formula/PatternCounts` | 661 | Counting divisors with a given tangent pattern |
| `Formula/RationalEval` | 66 | Evaluating the universal rational functions |
| `Formula/StateCombinatorics` | 611 | Combinatorics of states, ranks and safety of the laws |
| `Formula/TypeTransport` | 281 | Transport of factorization types and cell measures |
| `Main` | 120 | Main theorems |
| `Measure/AdicCylinders` | 989 | Adic congruences, adic cylinders and division charts |
| `Measure/AdicTransport` | 323 | Adic congruences, adic perturbations and transport of cylinder measures |
| `Measure/Atlas` | 315 | Ideal-chart atlases and atlas independence of the state measure |
| `Measure/Haar` | 376 | Haar measures on unramified extensions and strict-transform normalizations |
| `Measure/HenselProducts` | 1267 | Hensel factorization, finite products and coefficient measures |
| `Measure/MemberBoxes` | 601 | Measure of member boxes |
| `Measure/MemberCharts` | 602 | Charts of concrete members and the inseparable locus |
| `Measure/Normalizer` | 381 | Generator normalization and residue-ideal counts |
| `Measure/PrimitiveLocus` | 381 | The primitive locus, state measures, and integral closures |
| `Measure/StateVolumes` | 209 | Single-state residue ideal counts and Haar-measure transport |
| `Reciprocity/Defs` | 1044 | Reciprocity: definitions and basic lemmas |
| `Reciprocity/Main` | 301 | The reciprocity law (Theorem R) |
| `Reciprocity/Patterns` | 1045 | Pattern sums, crossing factorization and unitarity |
| `Reciprocity/Plethysm` | 1034 | Plethystic calculus for the reciprocity law |
| `Reciprocity/Quantum` | 920 | Reciprocity: the quantum torus, dilations and reciprocal substitution |
| `Recursion/ChildMembers` | 1215 | Child members and terminal states of the blowup recursion |
| `Recursion/Events` | 922 | Return and exit events of the blowup recursion |
| `Recursion/Members` | 1427 | Members of the recursion universe |
| `Recursion/OrderDefect` | 1151 | Order defects and child data for the blowup recursion |
| `Recursion/RootCellLaw` | 1365 | The root cell law |
| `Recursion/Termination` | 1316 | Termination of the recursion |
| `Surfaces/ChartCompletions` | 894 | Completions of the blow-up charts of the concrete surface |
| `Surfaces/Completeness` | 414 | Completeness of the concrete surface |
| `Surfaces/ConcreteAtlas` | 725 | Ideal atlases and curve data on the concrete surface |
| `Surfaces/ConcretePoints` | 439 | Closed points on the blow-up of the concrete surface |
| `Surfaces/ConcreteStrictTransforms` | 486 | Volumes and strict transforms on the concrete surface |
| `Surfaces/Lengths` | 1284 | Concrete surfaces, chart substitutions and lengths |
| `Surfaces/PowerSeries` | 1011 | Power series, residue bases and the local structure of concrete surfaces |
| `Surfaces/Regularity` | 691 | Regularity of the concrete surface |
| `Surfaces/TruncatedSeries` | 556 | Truncations of `k⟦T, X⟧` and contacts on the special fibre |
| `Unramified/DescentTypes` | 366 | Types under unramified base change |
| `Unramified/Extension` | 1160 | Binary forms, factor cells and unramified extensions |
| `Unramified/FactorCells` | 547 | Factor cells: residue cells of factor products and root-field isomorphisms |
| `Unramified/FrobeniusDescent` | 1189 | Frobenius descent for unramified extensions |
| `Unramified/HomogeneousCells` | 781 | Measure-preserving maps between homogeneous cells |
| `Unramified/LocalDescent` | 190 | Local lengths and finite quotients of completions |
| `Unramified/PolynomialTypes` | 1251 | Polynomial types, form products and residue cells |

Total: 64 modules, 50141 lines (plus root `SurfaceBlowup.lean`); `Tests/`: 2 files, 2159 lines.

Internally the proof runs on route-F densities (`monicDensityF`, `projectiveDensityF`, defined at the
end of `Basic.lean`, which add the condition that integral closures in root fields are finite); the
bridges `orig_monicDensity_eq`, `orig_projectiveDensity_eq` show they agree with the published
densities because the exceptional loci are Haar-null.

## Provenance

Obtained from a certified tree of ~1200 one-theorem files (`final/monolith_gen`) by mechanical merging
along the usage DAG and three golfing cycles (see `CHANGELOG.md`, `CAPTAIN.md`, `HANDOFF.md`). Module docstrings end
with a `Provenance:` line naming the original nodes.

## Companion paper and site

The informal proof, with every statement linked to its Lean declaration, is at <https://asving.github.io/claude/random-polynomials-local-surfaces/>. The Prove2Me certification of the same development is published under the namespace `TypeDensity`.

## Building

```
lake exe cache get   # Mathlib cache for the pinned commit
lake build           # SurfaceBlowup and Tests
lake env lean Checks/Axioms.lean
```
