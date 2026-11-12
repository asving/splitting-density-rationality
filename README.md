# SurfaceBlowup — factorization-type densities over complete DVRs

A Lean 4 / Mathlib formalization of the following theorem. Let `O` be a complete discrete valuation
ring with finite residue field of cardinality `q` (any characteristic, any ramification). For every
`n` and every factorization type `σ`, the probability that a Haar-random monic polynomial of degree
`n` over `O` (resp. a random primitive binary form of degree `n`) factors over `Frac O` with type
`σ` equals `A_{n,σ}(q)` (resp. `R_{n,σ}(q)`), where `A_{n,σ}`, `R_{n,σ}` are explicit universal
rational functions, given by a finite recursion over blow-ups of a regular arithmetic surface.
A second result is a reciprocity law for these rational functions.

Toolchain: Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag `v4.35.0`; pinned in
`lakefile.lean` / `lake-manifest.json`). Versions up to v1.2.0 use Lean `v4.33.1` with Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, which is also the environment of the Prove2Me tree.

## Main theorems

All in namespace `SurfaceBlowup`:

| theorem | file | statement (informal) |
|---|---|---|
| `main_dvr` | `SurfaceBlowup/Main.lean` | for `O` as above (adic topology, Borel σ-algebra, normalized Haar measure): `monicDensity O n σ = densityValue (monicExpr n σ) q` and `projectiveDensity O n σ = densityValue (projectiveExpr n σ) q` |
| `main_field_form` | `SurfaceBlowup/Main.lean` | the published rational-function form for rings of integers of unramified finite `K/ℚ_p` |
| `main_field_form_ramified` | `SurfaceBlowup/Main.lean` | the same for arbitrary finite `K/ℚ_p` |
| `recip_main` | `SurfaceBlowup/Reciprocity/Main.lean` | reciprocity: `A_n(q) = B_n(1/q)` and `R_n(1/q) = R_n(q)` |
| `main_dvr_cluster` (v1.1) | `SurfaceBlowup/Cluster/Main.lean` | the cluster clause: `clusterDensity O n σ = densityValue (clusterExpr n σ) q`, where `clusterDensity` is the normalized Haar probability on monic polynomials reducing to `X^n` and `clusterExpr n σ = lawCoeff (rootLaw n) σ` is `B_{n,σ}` |
| `cluster_formula_regular`, `recip_cluster` (v1.1) | `SurfaceBlowup/Cluster/Main.lean` | `B_{n,σ}` is regular at every prime power; `A_{n,σ}(q) = B_{n,σ}(1/q)` in the paper's notation |
| `main_dvr_etale` (v1.1) | `SurfaceBlowup/Etale/Main.lean` | the monic and projective laws with the events restricted to étale algebras (`etaleMonicDensity`, `etaleProjectiveDensity`); with `monicDensity_eq_etale`, `projectiveDensity_eq_etale`, `clusterDensity_eq_etale` and `binary_nonEtale_null`: the reduced-algebra and étale type conventions agree off a Haar-null set |
| `universal_type_laws` (v1.2) | `SurfaceBlowup/Corollaries/RationalForm.lean` | Theorem 1.1 in one statement: there are `A, B, R : RatFunc ℚ` (the rational functions of `monicExpr`, `clusterExpr`, `projectiveExpr`), regular and nonnegative at every prime power, such that over every `O` as above each of the three densities satisfies `0 ≤ r ∧ density = ENNReal.ofReal r` with `r` the value at `q` given by `RatFunc.eval` |
| `monicExpr_eval_nonneg`, `projectiveExpr_eval_nonneg`, `clusterExpr_eval_nonneg` (v1.2) | `SurfaceBlowup/Corollaries/Nonneg.lean` | the universal expressions take nonnegative values at every prime power, so the `ENNReal.ofReal` in `main_dvr` and `main_dvr_cluster` never clamps; `main_dvr_toReal`, `main_dvr_cluster_toReal` are the real-valued forms |
| `cluster_rational_eval` (v1.2) | `SurfaceBlowup/Corollaries/RationalForm.lean` | `RatFunc.eval q (clusterExpr n σ).rational = (clusterExpr n σ).eval q` at prime powers (the cluster analogue of `global_rational_eval`) |
| `reciprocity_recipRat`, `reciprocity_ringHom`, `recip_main_all_degrees` (v1.2) | `SurfaceBlowup/Corollaries/RationalForm.lean` | reciprocity in every degree, including `n = 0`: `A = v(B)` and `v(R) = R` for the ring endomorphism `v` of `ℚ(q)` with `v(q) = q⁻¹`; `clusterExpr_subst_inv_rational` identifies the syntactic right side of `recip_main` with `v(B)` |

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

Compared with the certified statements, the hypotheses `0 < n`, `ValidType σ`,
`typeDegree σ = n` of `main_dvr` / `main_field_form` / `main_field_form_ramified` and `ValidType σ`,
`typeDegree σ = n` of `recip_main` were dropped in cycle 4a (none was used by the proofs), so the
theorems are strictly stronger; `0 < n` of `recip_main` is used and kept. `Checks/run_checks.sh`
derived each certified statement, with its extra hypotheses, from the unified theorem in the kernel.
That check last ran for v1.0.0 and cannot be run any more (see "Trust boundary").

## Trust boundary

Lean checks proofs, not statements. Everything a reader must audit to trust the theorems is in
**`SurfaceBlowup/Basic.lean`** (~500 lines): the definitions of factorization types, the rational
expressions `Expr`, laws, recursion states, `stateLaw`, `monicExpr`, `projectiveExpr`, the densities
`monicDensity`, `projectiveDensity`, and `densityValue`, plus the main-theorem statements themselves
in `Main.lean` / `Reciprocity/Main.lean`. Version 1.1 extends the boundary by two short files of
definitions, **`SurfaceBlowup/Cluster/Defs.lean`** (`clusterCell`, `clusterExpr`, `clusterDensity`) and
**`SurfaceBlowup/Etale/Defs.lean`** (`IsEtaleForm`, `etaleMonicDensity`, `etaleProjectiveDensity`), and the
statements in `Cluster/Main.lean` / `Etale/Main.lean`. Every other file only contains proofs and auxiliary
definitions that do not occur in the main statements.

Version 1.2 adds no definition to the boundary. The corollaries in `SurfaceBlowup/Corollaries/` are stated
with the definitions above and Mathlib's `RatFunc.eval`. `reciprocity_recipRat` also mentions `recipRat`
(`Reciprocity/Defs.lean`), the ring endomorphism `q ↦ q⁻¹` of `ℚ(q)`; `reciprocity_ringHom` states the same
fact without it. These corollaries were written after the release of v1.1.0.

**What was lost in November 2026, and what the evidence is now.** The original workspace no longer
exists. With it went the certified one-theorem-per-file trees (`final/monolith_gen`,
`final/monolith_recip`, `final/monolith`), the cycle logs that `CHANGELOG.md` names, the generator of
the companion site and the markdown source of the paper. What remains:

- This repository and its release check, `tools/release_check_local.sh`: a full build, the axioms of
  the main theorems, and a comparison of every statement with the previous release.
- The public Prove2Me tree `TypeDensity`: this codebase at tag `v1.2.0`, one node per theorem, each
  verified by the platform. The platform exports its public trees as Lean files to
  `github.com/prove2me/formalpedia`. On 2026-11-11 that export did not yet hold the v1.2 theorems.
- The copies of the historical certificates on the companion site
  (`https://asving.github.io/claude/splitting-type-density/formalization.html`, section 3): the three
  monolith certificates and the release logs.

The statement-preservation check against the certified trees can no longer be run.
`Checks/run_checks.sh` verified, at the kernel level, that the statements of `main_dvr`,
`recip_main` and `main_field_form` as certified in those trees follow from the unified theorems: it
loaded both environments in one Lean process, paired every certified constant in the closure of the
certified statement with an alpha-identical unified constant, checked that the conclusions are
constant-for-constant identical and that the unified hypotheses are a subsequence of the certified
ones (the rest being the dropped propositions), and type-checked
`certified_statement := fun x₀ … => unified_theorem …` (implication form). Its last successful run is
recorded for v1.0.0: `CHANGELOG.md`, cycle 4d, and the note in the v1.1 release log on the site.
Since then statements are checked from release to release. v1.1.0 left `Basic.lean`, `Main.lean` and
`Reciprocity/Main.lean` byte-identical to v1.0.0. v1.2.0 left the kernel-term hashes of all 1853
constants of v1.1.0 unchanged (`tools/StmtDump.lean`). v1.3.0 changed the toolchain, so it compared the
source text of every statement with v1.2.0 (`tools/stmt_text.py`).

The regression guards in `Tests/` pin the definitions to known numbers, e.g.
`(monicExpr 4 {(4,1)}).eval 2 = 107/1533`, and derive density corollaries from `main_dvr`.
`Tests/Cluster.lean` derives the quadratic cluster law (`q/(q+1)`, `1/(2(q+1))`, `1/(2(q+1))`) from
`main_dvr_cluster`. `Tests/NonVacuity.lean` shows that the hypotheses of `main_dvr` are satisfiable in equal
characteristic: `𝔽_q⟦X⟧` with the coefficientwise topology, giving the formulas for `𝔽_p⟦X⟧`.
`Tests/PadicInt.lean` (v1.2) does the same in mixed characteristic: `ℤ_[p]` with Mathlib's norm topology,
which it proves to be the `(p)`-adic one, giving `main_dvr_padicInt`. No ramified extension of `ℤ_p` is
instantiated.

## License

Released under the Apache 2.0 license (file `LICENSE`); every file carries the Mathlib-style
copyright/authors header. Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). Apache 2.0 was
chosen to match Mathlib and confirmed by the owner on 2026-10-17.

## Building

    lake exe cache get        # Mathlib oleans (first time only)
    lake build                # builds SurfaceBlowup and Tests (~8800 jobs; ~8 min on 16 cores)
    lake env lean Checks/Axioms.lean   # 22 main theorems, each [propext, Classical.choice, Quot.sound]
    lake env lean Checks/AxiomsCorollaries.lean   # all 25 public theorems added in v1.2, same axioms

or all of it at once: `tools/release_check_local.sh`. That script is the release check: build, axioms,
the source text of every statement against v1.2.0 (`tools/stmt_text.py`), kernel-term hashes against
the dump of the current release, forbidden-token grep, warning count; logs in `logs/release_*.log`.

Historical, kept for the record: `tools/release_check.sh`, `Checks/run_checks.sh`,
`Checks/template.lean` and `Checks/SP*.lean`. They need the original workspace and the certified
trees, which no longer exist, so they cannot be run. Their last successful run is recorded for v1.0.0.

`site/` rebuilds the derived parts of the companion site from this repository (`site/README.md`).
`tools/prove2me/` holds the tools that exported the v1.2 theorems to Prove2Me
(`tools/prove2me/README.md`). Other tools: `tools/StmtDump.lean` (hashes of the
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
  strict transforms of a fixed tangent cell (`FixedTangentCellBijection`, Proposition 4.4 of the paper).
- `Recursion/` — the recursion universe: members, order defects, child members, return/exit events,
  termination, and the root cell law.
- `Assembly/` — type events and divisor counts, monic/projective cells, the Haar-null bridges from the
  original densities to the internal ones (`NullBridges`), and the density formulas (`Formulas`).
- `Reciprocity/` — independent of the surface tower (depends only on `Basic` and `Formula/`): series
  calculus, the quantum torus and reciprocal substitution, plethysm, pattern sums, the reciprocity law.
- `Main` — the main theorems.
- `Corollaries/` (v1.2) — nonnegativity of the universal expressions (`Nonneg`); the three laws as
  rational functions, Theorem 1.1 in one statement, and reciprocity as an endomorphism of `ℚ(q)` in
  every degree (`RationalForm`).

### Module table

| module | lines | title |
|---|---:|---|
| `Algebra/AlgebraType` | 645 | Algebra types and integral closures over a discrete valuation ring |
| `Algebra/FactorInvariant` | 324 | Invariance of factor invariants and uniqueness of algebra types |
| `Assembly/Formulas` | 140 | The density formulas for the route-F densities |
| `Assembly/MonicCells` | 1343 | Monic, projective and divisor cells |
| `Assembly/NullBridges` | 490 | Strict-transform measures, type events and the projective null bridge |
| `Assembly/TypeEvents` | 1329 | Type events and divisor counts |
| `Basic` | 503 | Statement-level definitions (the trust boundary) |
| `Blowup/CechStability` | 312 | Stability of the finite Čech coefficients |
| `Blowup/Charts` | 1158 | Blow-up charts, the exceptional line, and curve data |
| `Blowup/CurveOrders` | 1050 | Curve orders, the exceptional line, and finitely supported local data |
| `Blowup/CurveSections` | 1115 | Curve sections on the two-chart blow-up |
| `Blowup/Directions` | 154 | Closed points and divisors on the exceptional line |
| `Blowup/DivisorPoints` | 1461 | Exceptional divisor points of two-chart curve data |
| `Blowup/ExceptionalLayers` | 843 | Exceptional layers of the point blow-up |
| `Blowup/FixedTangentCellBijection` | 480 | Strict transforms give a bijection on a fixed tangent cell |
| `Blowup/H0Comparison` | 1245 | Comparing surface functions with Čech data on the blow-up |
| `Blowup/NilpotentGluing` | 1492 | Nilpotent gluing of exceptional levels |
| `Blowup/PointTransport` | 1283 | Transport of points between blow-up charts |
| `Blowup/StrictNormalizer` | 1497 | Strict transforms and the strict normalizer |
| `Blowup/TwoChartCurveData` | 1390 | Two-chart curve data |
| `Corollaries/Nonneg` | 199 | v1.2: nonnegativity of the universal expressions, real-valued forms of the main theorems |
| `Corollaries/RationalForm` | 230 | v1.2: the three laws as rational functions, and reciprocity as an automorphism of `ℚ(q)` |
| `Cluster/Defs` | 56 | v1.1: the cluster cell, the cluster law `B_{n,σ}` and the cluster density |
| `Cluster/Main` | 155 | v1.1: the cluster clause of the type-law theorem, its regularity and reciprocity |
| `Etale/Defs` | 60 | v1.1: étale binary forms and the étale-convention densities |
| `Etale/Main` | 139 | v1.1: the non-étale locus is null; the published densities equal the étale ones |
| `Etale/Algebra` | 58 | v1.1: the étale monic density with the event phrased by algebra types |
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
| `Measure/Haar` | 375 | Haar measures on unramified extensions and strict-transform normalizations |
| `Measure/HenselProducts` | 1267 | Hensel factorization, finite products and coefficient measures |
| `Measure/MemberBoxes` | 601 | Measure of member boxes |
| `Measure/MemberCharts` | 602 | Charts of concrete members and the inseparable locus |
| `Measure/Normalizer` | 381 | Generator normalization and residue-ideal counts |
| `Measure/PrimitiveLocus` | 382 | The primitive locus, state measures, and integral closures |
| `Measure/StateVolumes` | 209 | Single-state residue ideal counts and Haar-measure transport |
| `Reciprocity/Defs` | 1049 | Reciprocity: definitions and basic lemmas |
| `Reciprocity/Main` | 302 | The reciprocity law (Theorem R) |
| `Reciprocity/Patterns` | 1047 | Pattern sums, crossing factorization and unitarity |
| `Reciprocity/Plethysm` | 1034 | Plethystic calculus for the reciprocity law |
| `Reciprocity/Quantum` | 919 | Reciprocity: the quantum torus, dilations and reciprocal substitution |
| `Recursion/ChildMembers` | 1215 | Child members and terminal states of the blowup recursion |
| `Recursion/Events` | 923 | Return and exit events of the blowup recursion |
| `Recursion/Members` | 1426 | Members of the recursion universe |
| `Recursion/OrderDefect` | 1150 | Order defects and child data for the blowup recursion |
| `Recursion/RootCellLaw` | 1366 | The root cell law |
| `Recursion/Termination` | 1317 | Termination of the recursion |
| `Surfaces/ChartCompletions` | 894 | Completions of the blow-up charts of the concrete surface |
| `Surfaces/Completeness` | 413 | Completeness of the concrete surface |
| `Surfaces/ConcreteAtlas` | 725 | Ideal atlases and curve data on the concrete surface |
| `Surfaces/ConcretePoints` | 439 | Closed points on the blow-up of the concrete surface |
| `Surfaces/ConcreteStrictTransforms` | 488 | Volumes and strict transforms on the concrete surface |
| `Surfaces/Lengths` | 1284 | Concrete surfaces, chart substitutions and lengths |
| `Surfaces/PowerSeries` | 1011 | Power series, residue bases and the local structure of concrete surfaces |
| `Surfaces/Regularity` | 691 | Regularity of the concrete surface |
| `Surfaces/TruncatedSeries` | 556 | Truncations of `k⟦T, X⟧` and contacts on the special fibre |
| `Unramified/DescentTypes` | 366 | Types under unramified base change |
| `Unramified/Extension` | 1160 | Binary forms, factor cells and unramified extensions |
| `Unramified/FactorCells` | 547 | Factor cells: residue cells of factor products and root-field isomorphisms |
| `Unramified/FrobeniusDescent` | 1189 | Frobenius descent for unramified extensions |
| `Unramified/HomogeneousCells` | 782 | Measure-preserving maps between homogeneous cells |
| `Unramified/LocalDescent` | 190 | Local lengths and finite quotients of completions |
| `Unramified/PolynomialTypes` | 1251 | Polynomial types, form products and residue cells |

Total: 71 modules, 51060 lines (plus root `SurfaceBlowup.lean`); `Tests/`: 4 files, 2341 lines.

Internally the proof runs on route-F densities (`monicDensityF`, `projectiveDensityF`, defined at the
end of `Basic.lean`, which add the condition that integral closures in root fields are finite); the
bridges `orig_monicDensity_eq`, `orig_projectiveDensity_eq` show they agree with the published
densities because the exceptional loci are Haar-null.

## Provenance

Obtained from a certified tree of ~1200 one-theorem files (`final/monolith_gen`) by mechanical merging
along the usage DAG and three golfing cycles (see `CHANGELOG.md`, `HANDOFF.md`). Module docstrings end
with a `Provenance:` line naming the original nodes.

That tree was in the original workspace, which was lost in November 2026. So were `CAPTAIN.md`, the
`CYCLE4*_DONE.md` notes and the files under `logs/`, `scratch/` and `export/` that `CHANGELOG.md` and
`HANDOFF.md` cite. They are named there as a record and cannot be consulted. What remains of the
provenance is the history of this repository from v1.0.0, those two files, the public Prove2Me tree
`TypeDensity` and the monolith certificates copied on the companion site.
