# NOTES_B — Task B (the étale convention)

## (e) Verdict

**PROVED.** All four target theorems (`binary_nonEtale_null`, `monicDensity_eq_etale`,
`projectiveDensity_eq_etale`, `main_dvr_etale`) are proved with the statements and instance contexts
exactly as in the brief, no added hypotheses. The optional algebra-type corollary is also proved
(`etaleMonicDensity_eq_algebraType`, with helper `etale_adjoinRoot_of_separable`).

## (b) Files

New files (all under `SurfaceBlowup/Etale/`):
- `SurfaceBlowup/Etale/Defs.lean` (60 lines) — definitions, imports only `SurfaceBlowup.Basic`.
- `SurfaceBlowup/Etale/Main.lean` (139 lines) — the four target theorems + bridge lemmas;
  imports `SurfaceBlowup.Etale.Defs`, `SurfaceBlowup.Main`.
- `SurfaceBlowup/Etale/Algebra.lean` (58 lines) — optional corollary; imports
  `Mathlib.RingTheory.Etale.StandardEtale`, `SurfaceBlowup.Etale.Main`.

De-privatized lemmas: **none**. No existing file was edited. The private `affine_bad_null`,
`affine_natDegree`, `affine_snoc_eq` of `Assembly/NullBridges.lean` were re-proved publicly in
`Etale/Main.lean` as `affine_degenerate_null`, `affinePolynomial_natDegree_of_last` (strengthened
to also give `≠ 0`), `affinePolynomial_snoc_one` (+ `affinePolynomial_coeff_last`).
Not added to `SurfaceBlowup.lean` (frozen); the files are built as explicit targets.

## (a) Verbatim statements

### Definitions (`SurfaceBlowup/Etale/Defs.lean`, namespace `SurfaceBlowup`)

Section variables `(O : Type) [CommRing O] [IsDomain O]`:
```lean
/-- The binary form `F_a` is étale of degree `n` (its zero scheme in `ℙ¹_K` is finite étale of
degree `n`): nonzero, degree drop at most one (so the point at infinity has multiplicity at most
one), and separable dehomogenization `F_a(X,1)`. -/
def IsEtaleForm {n : ℕ} (a : Fin (n + 1) → O) : Prop :=
  affinePolynomial O a ≠ 0 ∧ n - (affinePolynomial O a).natDegree ≤ 1 ∧
    (affinePolynomial O a).Separable
```
Section variables `(O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O] [IsTopologicalRing O]
[CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]`:
```lean
/-- The monic probability of type `σ` under the étale convention: the event is restricted to
separable polynomials, i.e. to étale algebras `K[X]/(f_a)`. -/
noncomputable def etaleMonicDensity (n : ℕ) (σ : FactorType) : ℝ≥0∞ :=
  coefficientMeasure O n
    {a | (monicPolynomial O a).Separable ∧ HasPolynomialType O (monicPolynomial O a) σ}

/-- The projective probability of type `σ` under the étale convention. -/
noncomputable def etaleProjectiveDensity (n : ℕ) (σ : FactorType) : ℝ≥0∞ :=
  coefficientMeasure O (n+1) {a | primitive O a ∧ IsEtaleForm O a ∧ HasBinaryType O a σ} /
    coefficientMeasure O (n+1) {a | primitive O a}
```

### Target theorems (`SurfaceBlowup/Etale/Main.lean`)
```lean
/-- The non-étale binary forms are Haar-null. -/
theorem binary_nonEtale_null (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    coefficientMeasure O (n+1) {a | ¬ IsEtaleForm O a} = 0

/-- The published monic density equals the étale-convention density (Remark 1.3). -/
theorem monicDensity_eq_etale (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    monicDensity O n σ = etaleMonicDensity O n σ

/-- The published projective density equals the étale-convention density (Remark 1.3). -/
theorem projectiveDensity_eq_etale (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    projectiveDensity O n σ = etaleProjectiveDensity O n σ

/-- Theorem 1.1 under the étale convention: the monic and projective laws, with the events
restricted to étale algebras, are the universal rational functions. -/
theorem main_dvr_etale (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    etaleMonicDensity O n σ =
        densityValue (monicExpr n σ) (Nat.card (IsLocalRing.ResidueField O)) ∧
    etaleProjectiveDensity O n σ =
        densityValue (projectiveExpr n σ) (Nat.card (IsLocalRing.ResidueField O))
```

### Auxiliary public lemmas (`SurfaceBlowup/Etale/Main.lean`, section vars `(O : Type) [CommRing O] [IsDomain O]`, DVR/measure instances for the last)
```lean
/-- The coefficient of `X^n` in `F_a(X,1)` is `a_n`. -/
theorem affinePolynomial_coeff_last {n : ℕ} (a : Fin (n + 1) → O) :
    (affinePolynomial O a).coeff n = algebraMap O (BaseField O) (a (Fin.last n))

/-- If `a_n ≠ 0` then `F_a(X,1)` is nonzero of degree exactly `n`. -/
theorem affinePolynomial_natDegree_of_last {n : ℕ} (a : Fin (n + 1) → O)
    (ha : a (Fin.last n) ≠ 0) :
    affinePolynomial O a ≠ 0 ∧ (affinePolynomial O a).natDegree = n

/-- Appending the coefficient `1` turns `F_a(X,1)` into the monic polynomial with coefficients `a`.
-/
theorem affinePolynomial_snoc_one {n : ℕ} (a : Fin n → O) :
    affinePolynomial O (Fin.snoc (α := fun _ => O) a 1) = monicPolynomial O a

/-- Off `{a_n = 0} ∪ {disc = 0}` the binary form `F_a` is étale. -/
theorem isEtaleForm_of_good {n : ℕ} (a : Fin (n + 1) → O) (ha : a (Fin.last n) ≠ 0)
    (hd : MvPolynomial.eval a (MvPolynomial.map (Int.castRingHom O) (discAffine n)) ≠ 0) :
    IsEtaleForm O a

/-- The locus `{a_n = 0} ∪ {disc = 0}` is Haar-null. -/
theorem affine_degenerate_null (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    coefficientMeasure O (n+1) ({a : Fin (n+1) → O | a (Fin.last n) = 0} ∪
      {a | MvPolynomial.eval a (MvPolynomial.map (Int.castRingHom O) (discAffine n)) = 0}) =
      0
```

### Optional corollary (`SurfaceBlowup/Etale/Algebra.lean`)
```lean
/-- For a monic separable polynomial `f` over a field `K`, the algebra `K[X]/(f)` is étale. -/
theorem etale_adjoinRoot_of_separable {K : Type} [Field K] (f : K[X]) (hm : f.Monic)
    (hs : f.Separable) : Algebra.Etale K (AdjoinRoot f)

/-- The étale monic density, with the event "the algebra `K[X]/(f_a)` is étale and `O[X]/(f_a)`
has algebra type `σ`". -/
theorem etaleMonicDensity_eq_algebraType (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) (σ : FactorType) :
    etaleMonicDensity O n σ = coefficientMeasure O n
      {a | Algebra.Etale (BaseField O) (AdjoinRoot (monicPolynomial O a)) ∧
        HasAlgebraType O (AdjoinRoot (monicPolyO a)) σ}
```
(`monicPolyO a = X^n + Σ C (a i) X^i : O[X]` is the existing def in `Unramified/Extension.lean`;
`HasAlgebraType` is the existing def in `Algebra/AlgebraType.lean`.)

## (c) Check commands and output

Run from `/data/users/asvin/prove2me_workspace/final/work_etale`:
```
$ taskset -c 8-15 lake build SurfaceBlowup.Etale.Defs
✔ [3202/3202] Built SurfaceBlowup.Etale.Defs (1.0s)
Build completed successfully (3202 jobs).
$ taskset -c 8-15 lake build SurfaceBlowup.Etale.Main
✔ [3449/3449] Built SurfaceBlowup.Etale.Main (2.4s)
Build completed successfully (3449 jobs).
$ taskset -c 8-15 lake build SurfaceBlowup.Etale.Algebra
Build completed successfully (3454 jobs).
$ taskset -c 8-15 lake env lean SurfaceBlowup/Etale/Defs.lean      # no output, exit 0
$ taskset -c 8-15 lake env lean SurfaceBlowup/Etale/Main.lean      # no output, exit 0
$ taskset -c 8-15 lake env lean SurfaceBlowup/Etale/Algebra.lean   # no output, exit 0
$ awk 'length>100' SurfaceBlowup/Etale/*.lean                       # no output
$ rg -n "sorry|admit|native_decide|axiom |maxHeartbeats|open Classical" SurfaceBlowup/Etale/  # none
```
Scratch file `/tmp/etale_axioms_B.lean`:
```lean
import SurfaceBlowup.Etale.Algebra
#print axioms SurfaceBlowup.binary_nonEtale_null
#print axioms SurfaceBlowup.monicDensity_eq_etale
#print axioms SurfaceBlowup.projectiveDensity_eq_etale
#print axioms SurfaceBlowup.main_dvr_etale
#print axioms SurfaceBlowup.etale_adjoinRoot_of_separable
#print axioms SurfaceBlowup.etaleMonicDensity_eq_algebraType
```
```
$ taskset -c 8-15 lake env lean /tmp/etale_axioms_B.lean
'SurfaceBlowup.binary_nonEtale_null' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.monicDensity_eq_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.projectiveDensity_eq_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.main_dvr_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.etale_adjoinRoot_of_separable' depends on axioms: [propext, Classical.choice, Quot.sound]
'SurfaceBlowup.etaleMonicDensity_eq_algebraType' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## (d) Proof sketches

**binary_nonEtale_null.** If `a_n ≠ 0` then the coefficient of `X^n` in `F_a(X,1)` is the image of
`a_n` in `K`, nonzero, so `F_a(X,1) ≠ 0` and has `natDegree = n` (degree drop `0 ≤ 1`). If moreover
`discAffine n` (the generic resultant of `F` and `F'` in degrees `(n, n-1)`) does not vanish at `a`,
`affine_resultant_eq` + `separable_of_resultant` give separability. So `{¬ IsEtaleForm}` ⊆
`{a_n = 0} ∪ {discAffine(a) = 0}`, which is null: the hyperplane by `coordinate_hyperplane_null`,
the discriminant locus by `coefficientMeasure_zero_null` with witness `snoc a₀ 1`, where `a₀` is a
separable monic coefficient vector (`exists_separable_monic`) and `resultant_ne_zero_of_separable`.

**monicDensity_eq_etale.** `measure_congr`: off the null inseparable locus
(`monic_inseparable_null`) the events `HasPolynomialType` and `Separable ∧ HasPolynomialType` agree.

**projectiveDensity_eq_etale.** Same on the numerator, using `binary_nonEtale_null`: off the
non-étale locus, `primitive ∧ HasBinaryType` ↔ `primitive ∧ IsEtaleForm ∧ HasBinaryType`; the
denominators are identical.

**main_dvr_etale.** Rewrite with the two equalities (right to left) and apply `main_dvr`.

**etaleMonicDensity_eq_algebraType (optional).** For separable monic `f` over a field, `IsCoprime f f'`
gives a `StandardEtalePair` with `g = 1`; its ring is étale (Mathlib instance) and is
`≃ₐ (K[X]/f)[1/1] ≃ₐ K[X]/f` (`equivAwayAdjoinRoot`, `IsLocalization.atUnit`), so `Algebra.Etale K
(AdjoinRoot f)` by `Algebra.Etale.of_equiv`. Off the inseparable locus: étale holds, and
`HasAlgebraType O (O[X]/(f_a)) σ ↔ HasPolynomialTypeF O f_a σ ↔ HasPolynomialType O f_a σ`
(`polynomial_type_iff_algebra_type`, `monicPolyO_map_fraction`, `hasPolynomialTypeF_iff_of_separable`);
conclude by `measure_congr`. Note: only separable ⇒ étale was needed (the converse is not formalized).
