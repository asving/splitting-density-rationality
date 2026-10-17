# CHANGELOG — unified `SurfaceBlowup` codebase

All cycles: Lean v4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Main theorems `main_dvr`,
`main_field_form`, `main_field_form_ramified`, `recip_main`, axioms `[propext, Classical.choice,
Quot.sound]` throughout; statements kernel-checked against the certified trees after every wave
(`Checks/run_checks.sh`, 3x KERNEL_OK). Detailed logs: `CAPTAIN.md`.

## v1.1.0 (2026-10-17) — Theorem 1.1 cluster clause and the étale convention

Two gaps between the paper's Theorem 1.1 / Remark 1.3 and the formal statements are closed; no existing
statement changed and no frozen file was edited (`Tests/Regression.lean`: `single_two_law` made public).

- `SurfaceBlowup/Cluster/{Defs,Main}.lean` (211 lines): `clusterCell`, `clusterExpr n σ := lawCoeff (rootLaw n) σ`
  (`B_{n,σ}`), `clusterDensity` (normalized Haar restriction to monic polynomials reducing to `X^n`, published
  type predicate); `main_dvr_cluster` (all `n`, including `n = 0`), `clusterDensity_eq_etale`,
  `cluster_formula_regular`, `recip_cluster`. Proof: cluster cell = image of `Oⁿ` under `z ↦ π·z`; Haar
  scaling by `q⁻ⁿ` cancels in the ratio; null bridge via `monic_inseparable_null`; `root_cell_law`.
- `SurfaceBlowup/Etale/{Defs,Main,Algebra}.lean` (257 lines): `IsEtaleForm` (nonzero, degree drop ≤ 1,
  separable dehomogenization), `etaleMonicDensity`, `etaleProjectiveDensity`; `binary_nonEtale_null`,
  `monicDensity_eq_etale`, `projectiveDensity_eq_etale`, `main_dvr_etale`,
  `etaleMonicDensity_eq_algebraType` (event phrased as `Algebra.Etale` + `HasAlgebraType`).
- `Tests/Cluster.lean` (59 lines): quadratic cluster law `q/(q+1)`, `1/(2(q+1))`, `1/(2(q+1))` from
  `main_dvr_cluster`.
- `Checks/Axioms.lean` now prints 12 theorems; `tools/release_check.sh` expects 12. Statement-preservation
  check unchanged (3 certified statements).
- Provenance: statements designed by the orchestrating session from the paper's (1.1), (7.1), Remark 1.3;
  independent statement review by Codex (`final/codex_checks/STATEMENT_CHECK_astra.md`, PASS); proofs by two
  Opus 5.5 provers in isolated copies (`work_cluster`, `work_etale`; notes `NOTES_A.md`, `NOTES_B.md`).

## Counts

| state | files | lines | non-ws bytes | theorems | warnings | Mathlib-linter hits | decls > 100 lines |
|---|---:|---:|---:|---:|---:|---:|---:|
| certified source `monolith_gen` | 1211 | 71,809 | 4.22 MB (total) | — | — | — | — |
| cycle 1, mechanical merge | 58 | 56,890 | 2.43 M | 1592 | 490 | — | — |
| cycle 1, golfed | 59 | 53,926 | 2.31 M | 1571 | 74 | — | — |
| cycle 2, final | 60 | 49,808 | 2.17 M | 1684 | 5 | 160 | 31 |
| cycle 3, final | 60 | 50,407 | 2.21 M | 1756 | 5 | 12 (all documented exceptions) | 6 (all statement-dominated) |
| cycle 4a | 60 | 50,709 | 2.21 M | 1756 | 0 | 0 | 6 (all statement-dominated) |
| cycle 4c | 64 | 50,105 | — | 1758 (+2) | 0 | 0 | 5 (all statement-dominated) |
| cycle 4d | 64 | 50,141 | — | 1758 (+2) | 0 | 0 | 5 (all statement-dominated) |

(files/lines: `SurfaceBlowup/` without the root file; `Tests/` adds 2 files, 2,128 → 2,138 lines since cycle 2.
Warnings: the 5 remaining are the unused hypotheses `hn`, `hσ`, `hdegree` of `main_dvr` and `hσ`, `hdegree` of
`recip_main`, kept because the statements are frozen. Cycle-3 line growth (+1.2%) is the statements and
docstrings of the named lemmas split out of long proofs.)

## Cycle 1 — unification
- 1211 one-theorem files of the certified general tree merged along the usage DAG into one namespace
  `SurfaceBlowup` with a topic hierarchy (`Basic`, `Formula/`, `Algebra/`, `Measure/`, `Unramified/`,
  `Surfaces/`, `Blowup/`, `Recursion/`, `Assembly/`, `Reciprocity/`, `Main`); 190 dead modules dropped.
- `Basic.lean` = the trust boundary: the 101 statement-closure definitions, kernel-term-identical to the
  certified ones; the published densities are THE definitions, route-F variants internal (`...F`).
- `main_field_form` became a corollary of `main_dvr`; new `main_field_form_ramified` (any finite `K/ℚ_p`).
- Statement-preservation check (`Checks/`) loading the unified and certified environments in one process.
- 18 golf agents: docstrings on every public declaration, wrapped signatures, dead definitions removed.

## Cycle 2 — API cleanup and golf
- ~105 unused binders dropped (internal statements); ~45 Reciprocity conjunction lemmas split into ~150
  named lemmas; paper-label names (`prop_5_1_*`, `lemma_4_2`, `_v2`, `_aux`, `key`) renamed.
- Dedups: shared `Surfaces/TruncatedSeries` (three copies of truncated-series counting), integral-closure
  towers, chart substitutions, level-one kernel polynomials, divisor counts, null-bridge helpers;
  Reciprocity made independent of the surface tower.
- Performance: all 6 `maxHeartbeats` options removed; `curve_sections_quot_equiv_product` kernel 71 s → 6.5 s.
- Hygiene-false local notations replaced by hygienic explicit-argument notations.
- New `Tests/` library: non-vacuity (`𝔽_q⟦X⟧`) and regression guards (e.g. `monicDensity O 4 {(4,1)} =
  107/1533` at `q = 2`).
- 235 file-local declarations privatized; Mathlib standard-linter census (160 hits).

## Cycle 3 — Mathlib standards (finishing cycle)
- Linters 160 → 12: file-level `open scoped Classical` 63 → 0 (per-proof `classical`, per-declaration
  `open scoped Classical in` only where a statement needs it — instance terms unchanged, verified by
  statement hashes), `flexible` 31 → 0, `whitespace` 27 → 4, `unusedFintypeInType` 21 → 0,
  `unusedDecidableInType` 2 → 0, `show` 9 → 0, `multiGoal` 1 → 0. Remaining 12 = documented exceptions
  (5 frozen unused hypotheses, 4 whitespace inside the frozen `Main.lean` statements, 3 copyright `header`).
- Long proofs: 31 declarations over 100 lines → 6 (largest proof body now ~91 lines), by splitting into
  ~65 named (mostly private) lemmas (e.g. `exists_curve_datum_of_sum` 237 → 81 + `exists_curve_datum_points`;
  `member_cell_box_measurableSet_and_measure` 211 → `member_cell_box_measurable` / `_measure` +
  `member_cell_chart_box`; `exit_cell_type_mass` 146 → 55); remaining conjunction conclusions split.
- Cross-file dedups: `monic_coeff_sub_mem_iff`, product-event helpers (TypeEvents/MonicCells), cell-measure
  lemmas (TypeTransport), `curveProduct_*_equiv` → Charts `exists_localQuotient_*_addEquiv`,
  `sum_allowedPatterns_reindex` (Defs/Plethysm), `beta_right_chartBase`, `mk_mem_principalLayer`, a
  duplicated density block in Events.
- Module rename `Blowup/Prop51` → `Blowup/FixedTangentCellBijection`; corrected provenance lines
  (Formulas, CurveSections) and a wrong docstring (`RootCellLaw` is not characteristic-zero-only).
- 19 public statements changed: 17 lost an unused `[Fintype]`/`[Decidable*]` binder (or `Fintype` → `Finite`), and `exit_cell_type_mass` / `exit_event_succ_mass` (conjunction split, unused hypothesis dropped); no other
  public statement changed (`tools/StmtDump.lean` hash diffs: `logs/stmt_diff_c3B.txt`); Basic unchanged.
- New tools: `tools/StmtDump.lean`, `tools/lint_census.sh`, `tools/longest_decls.py`, `tools/release_check.sh`.

## Cycle 4a — housekeeping (owner decisions of 2026-10-12)
- **Main statements strengthened.** Dropped the unused hypotheses `0 < n`, `ValidType σ`,
  `typeDegree σ = n` of `main_dvr`, `main_field_form`, `main_field_form_ramified`, and `ValidType σ`,
  `typeDegree σ = n` of `recip_main` (`0 < n` of `recip_main` is used — `rootLaw 0 = lawOne` — and
  stays). Callers updated: `Tests/NonVacuity` (`main_dvr_powerSeries`, `main_dvr_zmod`,
  `main_dvr_galoisField` lose the same three hypotheses), `Tests/Regression` (8 density corollaries).
  Docstrings updated accordingly.
- **Statement preservation in implication form** (`Checks/template.lean`, `Checks/run_checks.sh`): the
  unified binders are matched to a subsequence of the certified binders, the conclusions must be
  constant-for-constant identical (`CONCLUSION_IDENTICAL`), unmatched certified binders must be
  propositions (printed as dropped hypotheses; their constants are also paired and closure-checked), and
  the kernel accepts `SPCheck.certified_statement : <certified statement, constants mapped> :=
  fun x₀ … => unified_theorem …`. The old full-type identity check is run as a negative control and
  reports `DIFFERS` (expected, since hypotheses were dropped). Results: main_dvr vs monolith_gen
  (107 closure constants, 3 dropped), recip_main vs monolith_recip (92, 2 dropped), main_field_form vs
  monolith (114, 3 dropped): 3x KERNEL_OK. `Checks/SPNegativeControl.lean` regenerated with the new
  template: still FAILS on `HasPolynomialType` (route-F statement), as it must.
- **License and headers.** Mathlib-style copyright header on all 64 `.lean` files of `SurfaceBlowup/`,
  `Tests/`, both roots, and `Checks/template.lean` (Authors: Asvin G, Claude (Anthropic), GPT-6-Astra
  (OpenAI)); `LICENSE` = Apache 2.0 text (copied from Mathlib's). OWNER: confirm license.
- Whitespace tidy in the (formerly frozen) statement text of `Main.lean`.
- `tools/release_check.sh`: preservation step also requires 3x `CONCLUSION_IDENTICAL`; warnings step now
  requires 0 warnings.
- Build warnings 5 → 0; Mathlib-linter hits 12 → 0.

## Cycle 4c — reviewer improvement list (`ASTRA_IMPROVEMENTS.md`), 2026-10-12

Implemented by a captain + 11 worker passes in three waves on disjoint file sets (single-writer
integration; integration builds in `scratch/c4c/itree`, then the main tree). Worker reports:
`scratch/c4c/REPORTS.md`. Snapshot of the starting state: `snapshots/cycle4c_start/`.

**Totals.** Lines 50,709 → 50,105 (−604, −1.2%) in `SurfaceBlowup/` with 4 new modules (60 → 64);
public constants (`tools/StmtDump.lean`) 1805 → 1826; source `theorem`/`lemma` 1757 → 1759, `def`-like
497 → 497. Clean build wall time (16 cores, Mathlib cached) **11 m 34 s → 7 m 54 s**; sum of module
times 997 s → 765 s. Slowest modules (clean build): `Charts` 152 → 38 s, `TwoChartCurveData` 117 → 67 s,
`CurveOrders` 99 → 43 s, `DivisorPoints` 86 → 66 s (logs: `logs/c4a_build1.log` → `logs/c4c_clean_build.log`).
Module check times elsewhere unchanged within noise.

| # | item | disposition | lines (net) | timing |
|---|---|---|---:|---|
| 1 | no injectivity/SizeOf for `TwoChartCurveData` | DONE (`set_option genInjectivity/genSizeOf false in`); no downstream use | +3 | `Charts` 151 → 120 s alone |
| 2 | local quotients from the local-ring family | DONE: `localQuotient := localRing ⧸ (localCurve, localException^j)` (abbrev), new `localSection`, `sectionsToProduct`/`curveProductReduction` ring homs (`RingHom.pi`); 11 `child*` lemmas and the `exists_localQuotient_*_addEquiv` triple deleted. Extra (profiler): field types of `TwoChartCurveData` via new abbrevs `LocallyTransverse`/`FiniteContact` (≈25 s of generated-declaration kernel work gone) | Charts −57, TCD −118 | `Charts` 120 → 38 s, `TCD` 112 → 69 s |
| 3 | one chart-transport theorem | DONE: `mul_injective_quotient_transport` (explicit unit factor), `exists_pow_le_span_pair_transport`, `map_maximalIdeal_localCompletion(_transport, _comap_le)`, `strict_transform_equation_of_kernels` in `CurveSections`; left/right/DivisorPoints/ConcreteAtlas/ConcreteStrictTransforms consumers rewritten (ConcreteAtlas now imports CurveSections; no cycle) | ≈ −230 (incl. wave-2 consumers) | neutral |
| 4 | division charts as data | PARTIAL: `IdealChart.isDivisionChart`, shared completeness/injectivity/degree lemmas in `Members` (4 duplicate copies deleted), local notations in `MemberBoxes`; `member_center_translate_measure_data` 119 → 92 lines. Rejected sub-part (premise wrong): a `DivisionData` record extended by `IdealChart` breaks the flat anonymous constructor used in `OrderDefect` and saves ~nothing | −133 (+ wave-2 uses) | neutral |
| 5 | common product-event measure computation | DONE: `measure_eq_sum_prod_of_preimage`, `sum_prod_densityValue_eq_lawProd` (TypeEvents); `product_cell_type_event_mass` deleted | −52 | neutral |
| 6 | elementary utilities out of geometry modules | DONE (dependency structure only): new `Measure/AdicTransport` (imports only `AdicCylinders`), `Formula/RationalEval`, `Formula/FiniteFieldCounts`, `Blowup/Directions` (imports only `Basic`). `PatternCounts` and `HomogeneousCells` no longer import `Charts`/`CurveOrders`; `LocalDescent` no longer imports `PolynomialTypes`. Reviewer mislocated some blocks (rational eval / counts were in `CurveOrders`, not `Charts`) | +127 (headers, docstrings) | no module got slower; clean-build gain comes from items 2 and the perf pass |
| 7 | prime-ideal argument via kernel into a power-series domain | DONE: `mvPowerSeries_fin_two_span_C_var_isPrime` = `RingHom.ker_isPrime` of `PowerSeries.map mk ∘ substAlgHom` (kill-substitution instead of `finSuccEquiv`), new `coeff_substAlgHom_kill`; `axis_span_isPrime` one line | ≈ −45 | neutral |
| 8 | resultant coprime lifting; drop completeness | DONE: new `isCoprime_of_isCoprime_map_residue` (any local ring); `coprime_of_coprime_residue_dvr` 49 → 1 line; `[IsAdicComplete]` dropped from 3 uniqueness lemmas | ≈ −50 | neutral |
| 9 | shared algebraic interpretation of laws | DONE (smaller than estimated): `lawInterp` + 7 laws in `LawAlgebra`; `lawCoef` (Reciprocity) is definitionally `lawInterp Expr.rational`, its lemmas become one-liners; two inductions and five private lemmas deleted. `Reciprocity/Defs` untouched (would chain it behind `LawAlgebra`). The 50-90-line estimate did not materialize | −13 (−26 with the wave-2 `Events` reuse) | neutral |
| 10 | separable-locus equivalence, a.e. equality | DONE: `HasPolynomialTypeF.to_original`, `hasPolynomialTypeF_iff_of_separable`; both bridges via `measure_congr` on a.e. equal events | −17 | neutral |
| 11 | monic counting via Mathlib | DONE (reviewer's 3-line proof) | −29 | neutral |
| 12 | splitting lemma from the ideal-power characterization | DONE (+ `TruncatedSeries.mem_axisIdeal_iff` now a one-liner) | ≈ −30 | neutral |
| 13 | linear first-isomorphism theorem for truncations | DONE: `truncEval` is a `≃ₗ` from `quotKerEquivOfSurjective`; `truncEval_mk` is `rfl` | −29 | neutral |
| 14 | controlled-normalization golf | PARTIAL: `Plethysm:889` = item 9; `Extension:555` (`factor_product_continuous`) 23 → 14 lines (`split_ifs` kept, as advised); `AdicCylinders:84,180,219,230` premise wrong (stale line numbers, no proofs there) — `coordinateLift_smul_eq_mul` added and reused in 5 files instead | ≈ −20 | neutral |
| — | perf pass (beyond the list) | DONE: `[∀ i, (P i).IsMaximal]` statements made the kernel unfold `CompletedLocalAt` through a derived-`IsPrime` lambda; private cores now take `[∀ i, (P i).IsPrime]` + `hmax`. `exceptional_overlap_is_laurent_line` elaborates in 1.6 s (was 12 s, 176k heartbeats); four `TwoChartCurveData` proofs that needed >100k heartbeats split (now ≤ 87k) | CurveOrders +37, DivisorPoints +9, TCD +64 | `CurveOrders` 97 → 43 s, `DivisorPoints` 84 → 64 s |

**Public statement changes** (`logs/stmt_diff_c4c.txt`, StmtDump hashes start → final; the four main
theorems and `Basic` unchanged):
- Hypothesis removals / generalizations: `hensel_pair_unique`, `hensel_factor_unique_of_dvd`,
  `hensel_family_unique` lose `[IsAdicComplete (maximalIdeal O) O]`; `coprime_of_coprime_residue_dvr`:
  `[IsDomain R] [IsDiscreteValuationRing R] [Field K] [IsFractionRing R K]` → `[IsLocalRing R] [CommRing K]`;
  `axis_span_isPrime`: `[Field k]` → `[CommRing k] [IsDomain k]`.
- Definitional re-presentations (same mathematical content, internal API of `Charts`/`TwoChartCurveData`):
  `sectionsToProduct`, `curveProductReduction` are now ring homs; the fields `transverse(0/inf)`,
  `finite(0/inf)` of `TwoChartCurveData` (and its `mk`/`rec`/`casesOn`/`recOn`/`noConfusion`) are stated
  with the new abbrevs `LocallyTransverse`/`FiniteContact` (defeq to the old types);
  `curve_sections_quot_equiv_product`, `curve_limit_equiv_product_threads` hash-change only because
  `curveProduct`'s additive structure now comes from its ring structure (statement text unchanged);
  `count_normalizedFactors_divisorAffinePolynomial` hash-changes only by moving to `Blowup/Directions`
  (identical text, elaborated with a smaller import set).
- Removed public: `localQuotient_addCommGroup`, `instAddCommGroupCurveProduct`,
  `exists_localQuotient_{inl,inr_inl,inr_inr}_addEquiv`, `truncEval_bijective` (stated about a private
  def; now `.bijective`), and the generated `TwoChartCurveData.mk.inj`/`mk.injEq`/`mk.sizeOf_spec`. None
  had users outside its file.
- 30 new public declarations (listed in `logs/stmt_diff_c4c.txt`); 36 constants changed module (moves of
  item 6, `mvPowerSeries_*` to `Lengths`, plus auxiliary `eq_def`s).

**Checks.** `tools/release_check.sh` ALL PASS (`logs/release_check_c4c.txt`): build, 4/4 axioms
`[propext, Classical.choice, Quot.sound]`, 3/3 KERNEL_OK + CONCLUSION_IDENTICAL (implication form),
no forbidden tokens, 0 warnings. `tools/lint_census.sh logs/lint_c4c`: 0 files with warnings. 0 lines over
100 characters; largest file 1497 lines. New tooling: `tools/chk.sh` accepts `LEANOPTS`.

## Cycle 4d — Prove2Me export alignment (`export/UNIFIED_PATCH.diff`), 2026-10-12

The exporter's source patches (`final/export/exporter/source_patches.py`; rationale in
`final/export/EXPORT_REPORT.md` §4-5) applied to the unified tree: `patch -p1 < ../export/UNIFIED_PATCH.diff`
applied cleanly (13 files, no fuzz, no rejects). Snapshot of the starting state: `snapshots/cycle4d_start/`.
`Basic.lean`, `Main.lean`, `Reciprocity/Main.lean` byte-identical to the snapshot.

**Statement rewrites** (a `by omega` or `match` inside a type creates auxiliary constants named after the
declaration, which broke kernel-type identity of Prove2Me solutions named `solution`):
- `⟨i, by omega⟩` → explicit term proofs, kernel-definitionally equal: `divisor_form_cell_law` (MonicCells,
  4×, `Nat.lt_succ_of_le (Nat.sub_le _ _)`), `divisor_vector_properties` (TypeEvents, same),
  `other_children_count` (LawAlgebra, `Nat.sub_one_lt_of_le`), `Tests.pattern_eq_of_weight_two`
  (Regression, 9×, private).
- `match` → named definition placed before the theorem (equivalent, not definitionally equal: the original
  `match` generalized over a discriminant-dependent hypothesis; both directions proved by the exporter's
  `patch-check`): `allowed_pattern_of_divisor` now takes `(hcontact : DivisorContactCondition k s Dv d)`,
  new `abbrev DivisorContactCondition` (Termination); `Tests.stateLawFuel_succ` now states
  `stateLawFuel (k+1) s = stateLawFuelStep k s`, new `noncomputable def Tests.stateLawFuelStep`
  (Regression; proofs of `stateLawFuel_eq`, `stateLaw_single`, `stateLaw_crossing` unfold it too).
- Indirect: the private `divisor_degree_pattern_weight` (Termination; text unchanged) now shares
  `DivisorContactCondition.match_1` as its matcher, so its type hash changes.

**Targeted imports:** `import Mathlib` in `Measure/HenselProducts` replaced by its `#min_imports` (6 files);
eight modules that relied on the transitive full import now import what they need (`Surfaces/Lengths`,
`Measure/PrimitiveLocus`, `Surfaces/Completeness`, `Unramified/LocalDescent`, `Surfaces/Regularity`,
`Blowup/NilpotentGluing`, `Recursion/Termination`, `Tests/NonVacuity`). No module imports all of Mathlib.

**Statement diff** (`logs/stmt_diff_c4d.txt`: `tools/StmtDump.lean` extended to `Tests` and private
declarations, `scratch/c4d/StmtDumpAll.lean`; start dump = `logs/stmt_dump_c4c_final.tsv` byte-for-byte):
exactly the six rewritten statements + the indirect `divisor_degree_pattern_weight` change type hash; new:
`DivisorContactCondition`, `Tests.stateLawFuelStep` (+ its `match_1.splitter`), and five
auto-generated Mathlib-namespace `congr_simp` lemmas (`MeasureTheory.Measure.addHaar`,
`DoubleQuot.quotQuotEquivQuotOfLE`, `Ideal.quotEquivOfEq`, `MeasureTheory.Measure.addHaarScalarFactor`,
`AdjoinRoot.powerBasis'`) now realized in our modules because the Mathlib module that used to realize them is
no longer imported. Nothing removed. Public constants (`tools/StmtDump.lean`) 1826 → 1832.

**Counts.** Lines `SurfaceBlowup/` 50,105 → 50,141 (+36: imports and the two definitions); `Tests/`
2,146 → 2,159. Release-check incremental build 6 m 22 s (3465 jobs).

**Checks.** `tools/release_check.sh` ALL PASS (`logs/release_check_c4d.txt`): build, 4/4 axioms
`[propext, Classical.choice, Quot.sound]`, 3/3 KERNEL_OK + CONCLUSION_IDENTICAL (implication form),
no forbidden tokens, 0 warnings. `tools/lint_census.sh logs/lint_c4d`: 0 files with warnings.
Export consistency: `normalize.py` (exporter, namespace `TypeDensity`) applied to the patched tree equals
`final/export/work/TypeDensity/src` in all 66 `.lean` files and root files up to the exporter's plan-stage
edits (206 dropped `private` modifiers, 18 named instances); script `scratch/c4d/cmp_export.py`, output
`scratch/c4d/export_cmp.txt` (0 residual differences).
