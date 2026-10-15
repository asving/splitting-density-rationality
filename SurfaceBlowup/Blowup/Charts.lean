/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Blowup.Directions
import SurfaceBlowup.Measure.AdicTransport
import SurfaceBlowup.Surfaces.Lengths
import SurfaceBlowup.Unramified.Extension

/-!
# Blow-up charts, the exceptional line, and curve data

For a commutative ring `R` and elements `t, x`, the blow-up of `(t, x)` is covered by the `t`-chart
`R[X]/(tX − x)` and the `x`-chart `R[W]/(xW − t)`, glued along the overlap where the slope is
invertible. This file sets up these charts together with their infinitesimal levels, the two-chart
Čech complex and its tower of levels, completed local rings at points, the local data of a curve
on the two charts (multiplicities, degree, curve orders and their limit, the child order), and the
colon strict transforms used to define child ideal sets.
It then proves the basic structural facts about these objects. Closed points and divisors on the
exceptional line `ℙ¹_k` are in `Blowup/Directions.lean`, and the adic congruence rules in
`Measure/AdicTransport.lean`.

## Main results

* `blowup_chart_universal`, `blowup_chart_ringHom_ext`: universal property of a chart.
* `blowup_exceptional_parameter_regular`: `t` is a nonzerodivisor on the `t`-chart when `(t, x)`
  is a regular sequence.
* `boundary_chart_quotient_equiv`: the `x`-chart modulo its slope is `R/(t)`.
* `actual_cech_preserves_exceptional_lattices`, `actual_cech_reductions_surjective`: the Čech
  differential respects the exceptional filtrations, whose reduction maps are surjective.
* `coordinate_coset_representatives_exist`, `coefficient_space_strict_instances`: adic
  congruences on coordinate spaces.
* `concrete_surface_special_fiber_length_transport`: lengths modulo `π` computed on the special
  fibre.

Provenance: `Def_SurfaceBlowupV2_{BlowupCharts, CompletedLocalPoints, FiniteBlowupCharts,
ActualCechLevels, ActualCechThreads, FiniteSupport, GluedGenerators, CurveSections,
PrincipalPowerLayers, StrictChartCoordinates, StrictNormalization, StrictPullback, SurfaceSections,
TangentCells, TwoChartCurveData, CurveDataDegree, CurveOrderLimit, ChildOrder, DivisorPoints,
ChildIdealSets}`; `Thm_SurfaceBlowupV2_{actual_cech_differentials_commute_with_reduction,
actual_cech_reductions_surjective, blowup_chart_relation,
actual_cech_preserves_exceptional_lattices, blowup_chart_ringHom_ext, blowup_chart_universal,
blowup_exceptional_parameter_regular, boundary_chart_quotient_equiv, child_coordinate_map_scaled,
coefficient_space_strict_instances, completed_point_power_contraction,
concrete_surface_special_fiber_length_transport, contracted_ideal_map_localization_top,
coordinate_coset_representatives_exist}`.
-/

noncomputable section

namespace SurfaceBlowup

/-! ### The two charts of a blow-up -/

section
variable (R : Type) [CommRing R]
/-- The relation `t·X − x` cutting out the `t`-chart of the blow-up of `(t, x)`. -/
def blowupRelation (t x : R) : Polynomial R := Polynomial.C t * Polynomial.X - Polynomial.C x
/-- The `t`-chart `R[X]/(tX − x)` of the blow-up of `R` at the ideal `(t, x)`. -/
abbrev BlowupChart (t x : R) := Polynomial R ⧸ Ideal.span {blowupRelation R t x}
/-- The structure map `R → R[X]/(tX − x)`. -/
def chartBase (t x : R) : R →+* BlowupChart R t x :=
  (Ideal.Quotient.mk (Ideal.span {blowupRelation R t x})).comp Polynomial.C
/-- The slope coordinate `X = x/t` on the `t`-chart. -/
def chartSlope (t x : R) : BlowupChart R t x :=
  Ideal.Quotient.mk (Ideal.span {blowupRelation R t x}) Polynomial.X
/-- The exceptional ideal `(t)` of the `t`-chart. -/
def chartExceptional (t x : R) : Ideal (BlowupChart R t x) :=
  Ideal.span {chartBase R t x t}
/-- The overlap of the two charts: the `t`-chart with its slope inverted. -/
abbrev BlowupOverlap (t x : R) := Localization.Away (chartSlope R t x)
end

/-! ### Completed local rings at points -/

section
section Completion
variable (A : Type) [CommRing A] [IsLocalRing A]
/-- The completion of a local ring at its maximal ideal. -/
abbrev LocalCompletion := AdicCompletion (IsLocalRing.maximalIdeal A) A
/-- The canonical map from a local ring to its completion. -/
def localCompletionMap : A →+* LocalCompletion A :=
  by exact @algebraMap A (LocalCompletion A) inferInstance inferInstance inferInstance
end Completion
section Point
variable (A : Type) [CommRing A] (P : Ideal A) [P.IsPrime]
/-- The completed local ring of `A` at the prime `P`. -/
abbrev CompletedLocalAt := LocalCompletion (Localization.AtPrime P)
/-- The canonical map `A → (A_P)^`. -/
def completedPointMap : A →+* CompletedLocalAt A P :=
  (localCompletionMap (Localization.AtPrime P)).comp (algebraMap A (Localization.AtPrime P))
/-- The ideal `(g, e^j)` of the completed local ring at `P`. -/
def finiteLocalCurveIdeal (e : A) (g : CompletedLocalAt A P) (j : ℕ) :
    Ideal (CompletedLocalAt A P) :=
  Ideal.span {g, (completedPointMap A P e)^j}
/-- The contraction to `A` of the ideal `(g, e^j)` of the completed local ring at `P`. -/
def contractedLocalCurveIdeal (e : A) (g : CompletedLocalAt A P) (j : ℕ) : Ideal A :=
  (finiteLocalCurveIdeal A P e g j).comap (completedPointMap A P)
/-- The local equation `g` at `P` is transverse to `e`: multiplication by `e` is injective
modulo `g`. -/
abbrev LocallyTransverse (e : A) (g : CompletedLocalAt A P) : Prop :=
  Function.Injective (fun a : CompletedLocalAt A P ⧸ Ideal.span {g} =>
    Ideal.Quotient.mk (Ideal.span {g}) (completedPointMap A P e) * a)
/-- The local equation `g` at `P` has finite contact with `e`: the ideal `(g, e)` contains a power
of the maximal ideal. -/
abbrev FiniteContact (e : A) (g : CompletedLocalAt A P) : Prop :=
  ∃ L : ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
    (localCompletionMap (Localization.AtPrime P)))^L ≤ finiteLocalCurveIdeal A P e g 1
end Point
end

/-! ### Infinitesimal levels of the charts; the ring Čech differential -/

section
section FiniteCharts
variable (R : Type) [CommRing R]
/-- The ideal `(t^j)` of the `t`-chart. -/
def exceptionalLevelIdeal (t x : R) (j : ℕ) : Ideal (BlowupChart R t x) :=
  Ideal.span {(chartBase R t x t)^j}
/-- The `j`-th infinitesimal level `A/(t^j)` of the `t`-chart. -/
abbrev ExceptionalChartLevel (t x : R) (j : ℕ) :=
  BlowupChart R t x ⧸ exceptionalLevelIdeal R t x j
/-- The structure map `R → A/(t^j)` of the `j`-th level of the `t`-chart. -/
def levelBase (t x : R) (j : ℕ) : R →+* ExceptionalChartLevel R t x j :=
  (Ideal.Quotient.mk (exceptionalLevelIdeal R t x j)).comp (chartBase R t x)
/-- The slope coordinate on the `j`-th level of the `t`-chart. -/
def levelSlope (t x : R) (j : ℕ) : ExceptionalChartLevel R t x j :=
  Ideal.Quotient.mk (exceptionalLevelIdeal R t x j) (chartSlope R t x)
/-- The `j`-th level of the overlap: the `j`-th chart level with its slope inverted. -/
abbrev ExceptionalOverlapLevel (t x : R) (j : ℕ) :=
  Localization.Away (levelSlope R t x j)
/-- The localization map from the `j`-th chart level to the `j`-th overlap level. -/
def levelOverlapMap (t x : R) (j : ℕ) :
    ExceptionalChartLevel R t x j →+* ExceptionalOverlapLevel R t x j :=
  by exact @algebraMap (ExceptionalChartLevel R t x j) (ExceptionalOverlapLevel R t x j)
      inferInstance inferInstance inferInstance
end FiniteCharts
section Complex
variable {O U V W : Type} [CommRing O] [CommRing U] [CommRing V] [CommRing W]
  [Algebra O U] [Algebra O V] [Algebra O W]
/-- The two-chart Čech differential `(u, v) ↦ left u − transition · right v`. -/
def ringCechDifferential (left : U →ₐ[O] W) (right : V →ₐ[O] W) (transition : W) :
    (U × V) →ₗ[O] W where
  toFun z := left z.1 - transition * right z.2
  map_add' := by
    intro z w
    simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add]
    abel
  map_smul' := by
    intro c z
    simp [smul_sub]
end Complex
end

/-! ### Levels of the Čech complex -/

section
variable (R : Type) [CommRing R] (t x : R)
/-- A restriction map from the `x`-chart to the overlap, sending its slope to the inverse
of the slope of the `t`-chart. -/
structure BlowupRestriction where
  right : BlowupChart R x t →ₐ[R] BlowupOverlap R t x
  slope : right (chartSlope R x t) = IsLocalization.Away.invSelf (chartSlope R t x)
/-- The Čech differential of the two blow-up charts twisted by the `d`-th power of the
inverse slope. -/
def fullCechDifferential (beta : BlowupRestriction R t x) (d : ℕ) :
    (BlowupChart R t x × BlowupChart R x t) →ₗ[R] BlowupOverlap R t x :=
  ringCechDifferential (IsScalarTower.toAlgHom R (BlowupChart R t x) (BlowupOverlap R t x))
    beta.right ((IsLocalization.Away.invSelf (chartSlope R t x))^d)
/-- The lattice `(t^j) × (x^j)` in the product of the two charts. -/
def cechInputLattice (j : ℕ) : Submodule R (BlowupChart R t x × BlowupChart R x t) :=
  (((chartExceptional R t x)^j).restrictScalars R).prod
    (((chartExceptional R x t)^j).restrictScalars R)
/-- The lattice `(t^j)` in the overlap. -/
def cechOutputLattice (j : ℕ) : Submodule R (BlowupOverlap R t x) :=
  ((Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
      (chartBase R t x t)})^j).restrictScalars R
/-- The `j`-th level of the Čech source. -/
abbrev CechLevelInput (j : ℕ) :=
  (BlowupChart R t x × BlowupChart R x t) ⧸ cechInputLattice R t x j
/-- The `j`-th level of the Čech target. -/
abbrev CechLevelOutput (j : ℕ) :=
  BlowupOverlap R t x ⧸ cechOutputLattice R t x j
/-- The Čech differential induced on the `j`-th levels. -/
def finiteCechDifferential (beta : BlowupRestriction R t x) (d j : ℕ)
    (h : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
        (fullCechDifferential R t x beta d)) :
    CechLevelInput R t x j →ₗ[R] CechLevelOutput R t x j :=
  (cechInputLattice R t x j).mapQ (cechOutputLattice R t x j)
    (fullCechDifferential R t x beta d) h
/-- The reduction map from level `j + 1` to level `j` of the Čech source. -/
def cechInputReduction (j : ℕ) : CechLevelInput R t x (j+1) →ₗ[R] CechLevelInput R t x j :=
  (cechInputLattice R t x (j+1)).mapQ (cechInputLattice R t x j) LinearMap.id (by
    rintro z hz
    exact ⟨(Ideal.pow_le_pow_right (Nat.le_succ j)) hz.1,
      (Ideal.pow_le_pow_right (Nat.le_succ j)) hz.2⟩)
/-- The reduction map from level `j + 1` to level `j` of the Čech target. -/
def cechOutputReduction (j : ℕ) : CechLevelOutput R t x (j+1) →ₗ[R] CechLevelOutput R t x j :=
  (cechOutputLattice R t x (j+1)).mapQ (cechOutputLattice R t x j) LinearMap.id (by
    intro z hz
    exact (Ideal.pow_le_pow_right (Nat.le_succ j)) hz)
end

/-! ### Threads of the Čech complex -/

section
variable (R : Type) [CommRing R] (t x : R)
/-- Compatible threads in the tower of levels of the Čech source. -/
def CechInputThreads : Type :=
  towerThreads R (fun j => CechLevelInput R t x j) (cechInputReduction R t x)
/-- Additive group structure on Čech-source threads. -/
instance : AddCommGroup (CechInputThreads R t x) :=
  inferInstanceAs (AddCommGroup (towerThreads R (fun j => CechLevelInput R t x j)
      (cechInputReduction R t x)))
/-- `R`-module structure on Čech-source threads. -/
instance : Module R (CechInputThreads R t x) :=
  inferInstanceAs (Module R (towerThreads R (fun j => CechLevelInput R t x j)
      (cechInputReduction R t x)))
end

/-! ### Kernels of finitely supported local data -/

section
section FiniteSupport
variable (A : Type) [CommRing A] (ι : Type) (P : ι → Ideal A)
variable [∀ i, (P i).IsPrime]
variable (J : ∀ i, Ideal (CompletedLocalAt A (P i)))
/-- The kernel `⋂ᵢ J_i ∩ A` of the map from `A` to finitely many completed local
quotients. -/
def finiteSupportKernel : Ideal A :=
  ⨅ i, (J i).comap (completedPointMap A (P i))
/-- The map from `A` to the product of the completed local quotients `(A_{P_i})^/J_i`. -/
def finiteSupportQuotientMap : A →+* (∀ i, CompletedLocalAt A (P i) ⧸ J i) :=
  RingHom.pi fun i => (Ideal.Quotient.mk (J i)).comp (completedPointMap A (P i))
/-- The image of `finiteSupportKernel` in `A/(e)^j`. -/
def finiteSupportLevelKernel (e : A) (j : ℕ) : Ideal (A ⧸ (Ideal.span {e})^j) :=
  (finiteSupportKernel A ι P J).map (Ideal.Quotient.mk ((Ideal.span {e})^j))
end FiniteSupport
end

/-! ### Glued generators -/

section
variable (R : Type) [CommRing R] (t x : R)
/-- The slope of the `t`-chart, as an element of the overlap. -/
def overlapSlope : BlowupOverlap R t x :=
  algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x)
/-- The exceptional parameter `t`, as an element of the overlap. -/
def overlapException : BlowupOverlap R t x :=
  algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t)
/-- Compatible systems of local generators on the two charts that glue, up to the twist
`slope^d`, on the overlap modulo powers of the exceptional ideal. -/
structure GluedGenerators (beta : BlowupRestriction R t x) (d : ℕ) where
  left : ℕ → BlowupChart R t x
  right : ℕ → BlowupChart R x t
  left_compat : ∀ j : ℕ, left (j+1) - left j ∈ (chartExceptional R t x)^j
  right_compat : ∀ j : ℕ, right (j+1) - right j ∈ (chartExceptional R x t)^j
  overlap : ∀ j : ℕ, algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (left j) -
    (overlapSlope R t x)^d * beta.right (right j) ∈ (Ideal.span {overlapException R t x})^j
/-- The pair `(t^d · left j, x^d · right j)` of chart functions attached to glued generators. -/
def gluedFunctionPair {beta : BlowupRestriction R t x} {d : ℕ} (G : GluedGenerators R t x beta d)
    (j : ℕ) : BlowupChart R t x × BlowupChart R x t :=
  ((chartBase R t x t)^d * G.left j, (chartBase R x t x)^d * G.right j)
end

/-! ### Curve sections -/

section
variable (R : Type) [CommRing R] (t x : R) (beta : BlowupRestriction R t x) {d : ℕ}
  (G : GluedGenerators R t x beta d) (j : ℕ)
/-- The ideal `(left j) + (t)^j` of the `t`-chart. -/
def leftCurveIdeal : Ideal (BlowupChart R t x) :=
  Ideal.span {G.left j} ⊔ (chartExceptional R t x)^j
/-- The ideal `(right j) + (x)^j` of the `x`-chart. -/
def rightCurveIdeal : Ideal (BlowupChart R x t) :=
  Ideal.span {G.right j} ⊔ (chartExceptional R x t)^j
/-- The ideal `(left j) + (t)^j` of the overlap. -/
def overlapCurveIdeal : Ideal (BlowupOverlap R t x) :=
  Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (G.left j)} ⊔
    (Ideal.span {overlapException R t x})^j
/-- The product lattice `leftCurveIdeal × rightCurveIdeal`. -/
def curveIdealLattice : Submodule R (BlowupChart R t x × BlowupChart R x t) :=
  ((leftCurveIdeal R t x beta G j).restrictScalars R).prod
    ((rightCurveIdeal R t x beta G j).restrictScalars R)
/-- Pairs of chart functions whose untwisted Čech difference lies in the overlap curve ideal. -/
def curveSections : Submodule R (BlowupChart R t x × BlowupChart R x t) :=
  ((overlapCurveIdeal R t x beta G j).restrictScalars R).comap (fullCechDifferential R t x beta 0)
/-- The image of `curveSections` modulo the curve ideal lattice. -/
def curveSectionsQuot : Submodule R ((BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t
    x beta G j) :=
  (curveSections R t x beta G j).map (curveIdealLattice R t x beta G j).mkQ
end

/-! ### Principal power layers -/

section
variable (A : Type) [CommRing A]
/-- `(t, x)` is a regular sequence: `t` is a nonzerodivisor on `A` and `x` on `A/(t)`. -/
def RegularParameterPair (t x : A) : Prop :=
  Function.Injective (fun a : A => t*a) ∧
    Function.Injective (fun a : A ⧸ Ideal.span {t} => Ideal.Quotient.mk (Ideal.span {t}) x * a)
/-- The quotient `A/(e)^j`. -/
abbrev PrincipalPowerQuotient (e : A) (j : ℕ) := A ⧸ (Ideal.span {e})^j
/-- The reduction `A/(e)^{j+1} → A/(e)^j`. -/
def principalPowerReduction (e : A) (j : ℕ) :
    PrincipalPowerQuotient A e (j+1) →ₐ[A] PrincipalPowerQuotient A e j :=
  Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.le_succ j))
/-- The map `a ↦ a · e^j` into `A/(e)^{j+1}`. -/
def principalLayerMap (e : A) (j : ℕ) : A →ₗ[A] PrincipalPowerQuotient A e (j+1) :=
  LinearMap.toSpanSingleton A (PrincipalPowerQuotient A e (j+1))
    (Ideal.Quotient.mk ((Ideal.span {e})^(j+1)) (e^j))
/-- The layer `(e)^j/(e)^{j+1}`, as the kernel of the reduction map. -/
abbrev PrincipalLayer (e : A) (j : ℕ) :=
  LinearMap.ker (principalPowerReduction A e j).toLinearMap
end

/-! ### Strict chart coordinates -/

section
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
/-- The coordinate map of the child chart: the normal form of `H z`, rescaled by `π^(a−1)`. -/
def childCoordinateMap {n : ℕ} (pi : O) (a : ℕ) (b : Fin n → R)
    (E : R ≃ₗ[O] ((Fin n → O) × R)) (H : (Fin n → O) →ₗ[O] R) (z : Fin n → O) : Fin n → O :=
  (pi^(a-1)) • (generatorNormalForm (pi^a) b E (H z)).1
/-- Scaling a coordinate vector by `π^m`. -/
def coordinateScale {n : ℕ} (pi : O) (m : ℕ) (z : Fin n → O) : Fin n → O := (pi^m) • z
/-- The coset of coordinate vectors congruent to `z₀` modulo `π^m`. -/
def coordinateCoset {n : ℕ} (pi : O) (m : ℕ) (z₀ : Fin n → O) : Set (Fin n → O) :=
  {z | adicCongr (Ideal.span {pi}) m z z₀}
/-- The colon strict transform `(J·C) : e^d` of an ideal `J` along `alpha`. -/
def strictTransformIdeal {C : Type} [CommRing C] [Algebra O C] (alpha : R →ₐ[O] C) (e : C) (d : ℕ)
    (J : Ideal R) : Ideal C :=
  (J.map alpha.toRingHom).colon {e^d}
end

/-! ### Strict normalization -/

section
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
/-- The linear part `fst ∘ E ∘ H` of the strict normalization. -/
def normalizationLinearPart {n : ℕ}
    (E : R ≃ₗ[O] ((Fin n → O) × R)) (H : (Fin n → O) →ₗ[O] R) :
    (Fin n → O) →ₗ[O] (Fin n → O) :=
  (LinearMap.fst O (Fin n → O) R).comp (E.toLinearMap.comp H)
/-- The quadratic correction term of the strict normalization. -/
def normalizationQuadratic {n : ℕ} (b : Fin n → R)
    (E : R ≃ₗ[O] ((Fin n → O) × R)) (s : (Fin n → O) × R) : Fin n → O :=
  (E (s.2 * coordinateLift b s.1)).1
/-- The correction `−π^(a−k) · Q(quadratic term)` of the strict normalization. -/
def normalizationCorrection {n : ℕ} (pi : O) (a k : ℕ) (b : Fin n → R)
    (E : R ≃ₗ[O] ((Fin n → O) × R)) (H : (Fin n → O) →ₗ[O] R)
    (Q : (Fin n → O) →ₗ[O] (Fin n → O)) (z : Fin n → O) : Fin n → O :=
  -(pi^(a-k)) • Q (normalizationQuadratic b E
    (generatorNormalForm (pi^a) b E (H z)))
/-- The coordinate part of the normal form of `H z`, scaled by `π^a`. -/
def scaledStrictMap {n : ℕ} (pi : O) (a : ℕ) (b : Fin n → R)
    (E : R ≃ₗ[O] ((Fin n → O) × R)) (H : (Fin n → O) →ₗ[O] R)
    (z : Fin n → O) : Fin n → O :=
  (pi^a) • (generatorNormalForm (pi^a) b E (H z)).1
end

/-! ### Strict pullback -/

section
variable {O R C : Type} [CommRing O] [CommRing R] [CommRing C] [Algebra O R] [Algebra O C]
/-- The `O`-linear map `z ↦ Σ zᵢ bᵢ`. -/
def coordinateLinear {n : ℕ} (b : Fin n → R) : (Fin n → O) →ₗ[O] R :=
  ∑ i : Fin n, (LinearMap.proj i : (Fin n → O) →ₗ[O] O).smulRight (b i)
/-- The variation `z ↦ c · alpha (Σ zᵢ bᵢ)` pulled back along `alpha`. -/
def pulledVariation {n : ℕ} (alpha : R →ₐ[O] C) (c : C) (b : Fin n → R) :
    (Fin n → O) →ₗ[O] C :=
  (LinearMap.mulLeft O c).comp (alpha.toLinearMap.comp (coordinateLinear b))
end

/-! ### Surface sections -/

section
variable (R : Type) [CommRing R] (t x : R)
/-- The diagonal map from `R` to the product of the two charts. -/
def surfaceToChartPair : R →ₗ[R] (BlowupChart R t x × BlowupChart R x t) :=
  LinearMap.prod (Algebra.linearMap R (BlowupChart R t x)) (Algebra.linearMap R (BlowupChart R x t))
/-- The diagonal map from `R` to the `j`-th level of the Čech source. -/
def surfaceToCechInput (j : ℕ) : R →ₗ[R] CechLevelInput R t x j :=
  (cechInputLattice R t x j).mkQ.comp (surfaceToChartPair R t x)
/-- The `j`-th component of a thread of the Čech source. -/
def cechInputThreadLinear (j : ℕ) : CechInputThreads R t x →ₗ[R] CechLevelInput R t x j :=
  (LinearMap.proj j).comp
    (towerThreads R (fun j => CechLevelInput R t x j) (cechInputReduction R t x)).subtype
/-- The diagonal map from `R` to threads of the Čech source. -/
def surfaceThreads : R →ₗ[R] CechInputThreads R t x :=
  LinearMap.codRestrict
    (towerThreads R (fun j => CechLevelInput R t x j) (cechInputReduction R t x))
    (LinearMap.pi fun j => surfaceToCechInput R t x j) (fun r => by
      rw [towerThreads, LinearMap.mem_ker]
      ext j
      change surfaceToCechInput R t x j r -
        cechInputReduction R t x j (surfaceToCechInput R t x (j+1) r) = 0
      rw [sub_eq_zero]
      rfl)
end

/-! ### Tangent cells -/

section
variable (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
/-- A chosen lift of a residue class. -/
def residueRepresentative (c : IsLocalRing.ResidueField R) : R :=
  Function.invFun (IsLocalRing.residue R) c
/-- A lift `Σ hᵢ t^(d−i) x^i` of a degree-`d` form with dehomogenization `H`. -/
def tangentLift (S : SurfaceData O R) (d : ℕ) (H : Polynomial (IsLocalRing.ResidueField R)) : R :=
  ∑ i : Fin (d+1), residueRepresentative R (H.coeff i.val) * S.t^(d-i.val) * S.x^i.val
/-- The principal ideal `J` has tangent cone of degree `d` with divisor `D` on the
exceptional line. -/
def HasTangentDivisor (S : SurfaceData O R) (J : Ideal R) (d : ℕ)
    (D : ExceptionalDivisor (IsLocalRing.ResidueField R)) : Prop :=
  ∃ f : R, ∃ H : Polynomial (IsLocalRing.ResidueField R),
    J = Ideal.span {f} ∧ HasHomogeneousDivisor (IsLocalRing.ResidueField R) d H D ∧
      f - tangentLift O R S d H ∈ (IsLocalRing.maximalIdeal R)^(d+1)
/-- Ideals in state `s` whose tangent cone has degree `d` and divisor `D`. -/
def fixedTangentCell (S : SurfaceData O R) (s : State) (d : ℕ)
    (D : ExceptionalDivisor (IsLocalRing.ResidueField R)) : Set (Ideal R) :=
  {J | J ∈ surfaceStateSet O R S s ∧ HasTangentDivisor O R S J d D}
end

/-! ### Curve data on the two charts -/

section
variable (R : Type) [CommRing R] (t x : R) (beta : BlowupRestriction R t x)
-- The generated injectivity and `SizeOf` declarations are unused and cost ~30 s of kernel time.
set_option genInjectivity false in
set_option genSizeOf false in
/-- Local data of a curve on the blow-up: finitely many points on the overlap, at `Z = 0` and
at infinity, with local equations transverse to the exceptional divisor and finite contact with it.
-/
structure TwoChartCurveData where
  ι : Type
  [fin : Finite ι]
  Q : ι → Ideal (BlowupOverlap R t x)
  [maximal : ∀ i, (Q i).IsMaximal]
  inj : Function.Injective Q
  onE : ∀ i, overlapException R t x ∈ Q i
  g : ∀ i, CompletedLocalAt (BlowupOverlap R t x) (Q i)
  transverse : ∀ i, LocallyTransverse (BlowupOverlap R t x) (Q i) (overlapException R t x) (g i)
  finite : ∀ i, FiniteContact (BlowupOverlap R t x) (Q i) (overlapException R t x) (g i)
  leftIso : ∀ i, CompletedLocalAt (BlowupOverlap R t x) (Q i) ≃+*
    CompletedLocalAt (BlowupChart R t x) ((Q i).comap (algebraMap (BlowupChart R t x)
        (BlowupOverlap R t x)))
  leftIso_compat : ∀ i (a : BlowupChart R t x), leftIso i
      (completedPointMap (BlowupOverlap R t x) (Q i)
    (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) a)) =
    completedPointMap (BlowupChart R t x) ((Q i).comap (algebraMap (BlowupChart R t x)
        (BlowupOverlap R t x))) a
  rightIso : ∀ i, CompletedLocalAt (BlowupOverlap R t x) (Q i) ≃+*
    CompletedLocalAt (BlowupChart R x t) ((Q i).comap beta.right.toRingHom)
  rightIso_compat : ∀ i (b : BlowupChart R x t), rightIso i
      (completedPointMap (BlowupOverlap R t x) (Q i)
    (beta.right b)) = completedPointMap (BlowupChart R x t) ((Q i).comap beta.right.toRingHom) b
  ι0 : Type
  [fin0 : Finite ι0]
  P0 : ι0 → Ideal (BlowupChart R t x)
  [maximal0 : ∀ k, (P0 k).IsMaximal]
  inj0 : Function.Injective P0
  slope0 : ∀ k, chartSlope R t x ∈ P0 k
  onE0 : ∀ k, chartBase R t x t ∈ P0 k
  g0 : ∀ k, CompletedLocalAt (BlowupChart R t x) (P0 k)
  transverse0 : ∀ k, LocallyTransverse (BlowupChart R t x) (P0 k) (chartBase R t x t) (g0 k)
  finite0 : ∀ k, FiniteContact (BlowupChart R t x) (P0 k) (chartBase R t x t) (g0 k)
  ιinf : Type
  [fininf : Finite ιinf]
  Pinf : ιinf → Ideal (BlowupChart R x t)
  [maximalinf : ∀ l, (Pinf l).IsMaximal]
  injinf : Function.Injective Pinf
  slopeinf : ∀ l, chartSlope R x t ∈ Pinf l
  onEinf : ∀ l, chartBase R x t x ∈ Pinf l
  ginf : ∀ l, CompletedLocalAt (BlowupChart R x t) (Pinf l)
  transverseinf : ∀ l, LocallyTransverse (BlowupChart R x t) (Pinf l) (chartBase R x t x) (ginf l)
  finiteinf : ∀ l, FiniteContact (BlowupChart R x t) (Pinf l) (chartBase R x t x) (ginf l)
attribute [instance] TwoChartCurveData.fin TwoChartCurveData.maximal TwoChartCurveData.fin0
  TwoChartCurveData.maximal0 TwoChartCurveData.fininf TwoChartCurveData.maximalinf
variable {R t x beta} (D : TwoChartCurveData R t x beta)
/-- The points of the curve on the `t`-chart. -/
def leftPoint : D.ι ⊕ D.ι0 → Ideal (BlowupChart R t x)
  | Sum.inl i => (D.Q i).comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))
  | Sum.inr k => D.P0 k
/-- The points of the curve on the `t`-chart are prime. -/
instance leftPoint_isPrime : ∀ s, (leftPoint D s).IsPrime
  | Sum.inl _ => Ideal.IsPrime.comap _
  | Sum.inr k => Ideal.IsMaximal.isPrime (D.maximal0 k)
/-- The local equations of the curve on the `t`-chart. -/
def leftData : ∀ s, CompletedLocalAt (BlowupChart R t x) (leftPoint D s)
  | Sum.inl i => D.leftIso i (D.g i)
  | Sum.inr k => D.g0 k
/-- The points of the curve on the `x`-chart. -/
def rightPoint : D.ι ⊕ D.ιinf → Ideal (BlowupChart R x t)
  | Sum.inl i => (D.Q i).comap beta.right.toRingHom
  | Sum.inr l => D.Pinf l
/-- The points of the curve on the `x`-chart are prime. -/
instance rightPoint_isPrime : ∀ s, (rightPoint D s).IsPrime
  | Sum.inl _ => Ideal.IsPrime.comap _
  | Sum.inr l => Ideal.IsMaximal.isPrime (D.maximalinf l)
/-- The local equations of the curve on the `x`-chart. -/
def rightData : ∀ s, CompletedLocalAt (BlowupChart R x t) (rightPoint D s)
  | Sum.inl i => D.rightIso i (D.g i)
  | Sum.inr l => D.ginf l
/-- The local ideal `(g, t^j)` at a point of the `t`-chart. -/
def leftLevelIdeal (j : ℕ) (s : D.ι ⊕ D.ι0) : Ideal (CompletedLocalAt (BlowupChart R t x)
    (leftPoint D s)) :=
  finiteLocalCurveIdeal (BlowupChart R t x) (leftPoint D s) (chartBase R t x t) (leftData D s) j
/-- The local ideal `(g, x^j)` at a point of the `x`-chart. -/
def rightLevelIdeal (j : ℕ) (s : D.ι ⊕ D.ιinf) : Ideal (CompletedLocalAt (BlowupChart R x t)
    (rightPoint D s)) :=
  finiteLocalCurveIdeal (BlowupChart R x t) (rightPoint D s) (chartBase R x t x) (rightData D s) j
/-- The local ideal `(g, t^j)` at a point of the overlap. -/
def commonLevelIdeal (j : ℕ) (i : D.ι) : Ideal (CompletedLocalAt (BlowupOverlap R t x) (D.Q i)) :=
  finiteLocalCurveIdeal (BlowupOverlap R t x) (D.Q i) (overlapException R t x) (D.g i) j
/-- The kernel of the `t`-chart in the product of its local level quotients. -/
def leftKernel (j : ℕ) : Ideal (BlowupChart R t x) :=
  finiteSupportKernel (BlowupChart R t x) (D.ι ⊕ D.ι0) (leftPoint D) (leftLevelIdeal D j)
/-- The kernel of the `x`-chart in the product of its local level quotients. -/
def rightKernel (j : ℕ) : Ideal (BlowupChart R x t) :=
  finiteSupportKernel (BlowupChart R x t) (D.ι ⊕ D.ιinf) (rightPoint D) (rightLevelIdeal D j)
/-- The kernel of the overlap in the product of its local level quotients. -/
def commonKernel (j : ℕ) : Ideal (BlowupOverlap R t x) :=
  finiteSupportKernel (BlowupOverlap R t x) D.ι D.Q (commonLevelIdeal D j)
/-- The image of `leftKernel` in `A/(t)^j`. -/
def leftLevelKernel (j : ℕ) : Ideal (BlowupChart R t x ⧸ (Ideal.span {chartBase R t x t})^j) :=
  finiteSupportLevelKernel (BlowupChart R t x) (D.ι ⊕ D.ι0) (leftPoint D) (leftLevelIdeal D j)
      (chartBase R t x t) j
/-- The image of `rightKernel` in `B/(x)^j`. -/
def rightLevelKernel (j : ℕ) : Ideal (BlowupChart R x t ⧸ (Ideal.span {chartBase R x t x})^j) :=
  finiteSupportLevelKernel (BlowupChart R x t) (D.ι ⊕ D.ιinf) (rightPoint D) (rightLevelIdeal D j)
      (chartBase R x t x) j
end

/-! ### Degree of curve data -/

section
variable {R : Type} [CommRing R] {t x : R} {beta : BlowupRestriction R t x}
    (D : TwoChartCurveData R t x beta)
/-- The local intersection multiplicity with the exceptional divisor at a `t`-chart point. -/
noncomputable def leftMultiplicity (s : D.ι ⊕ D.ι0) : ℕ :=
  (Module.length (CompletedLocalAt (BlowupChart R t x) (leftPoint D s))
    (CompletedLocalAt (BlowupChart R t x) (leftPoint D s) ⧸ leftLevelIdeal D 1 s)).toNat
/-- The local intersection multiplicity with the exceptional divisor at an `x`-chart point. -/
noncomputable def rightMultiplicity (s : D.ι ⊕ D.ιinf) : ℕ :=
  (Module.length (CompletedLocalAt (BlowupChart R x t) (rightPoint D s))
    (CompletedLocalAt (BlowupChart R x t) (rightPoint D s) ⧸ rightLevelIdeal D 1 s)).toNat
/-- The local intersection multiplicity with the exceptional divisor at an overlap point. -/
noncomputable def commonMultiplicity (i : D.ι) : ℕ :=
  (Module.length (CompletedLocalAt (BlowupOverlap R t x) (D.Q i))
    (CompletedLocalAt (BlowupOverlap R t x) (D.Q i) ⧸ commonLevelIdeal D 1 i)).toNat
/-- The residue degree of a `t`-chart point (length of its residue ring over `R`). -/
noncomputable def leftResidueDegree (s : D.ι ⊕ D.ι0) : ℕ :=
  (Module.length R (BlowupChart R t x ⧸ leftPoint D s)).toNat
/-- The residue degree of an `x`-chart point (length of its residue ring over `R`). -/
noncomputable def rightResidueDegree (s : D.ι ⊕ D.ιinf) : ℕ :=
  (Module.length R (BlowupChart R x t ⧸ rightPoint D s)).toNat
/-- The total intersection number of the curve with the exceptional divisor. -/
noncomputable def curveDataDegree : ℕ :=
  (∑ᶠ s : D.ι ⊕ D.ι0, leftResidueDegree D s * leftMultiplicity D s) +
    ∑ᶠ l : D.ιinf, rightMultiplicity D (Sum.inr l)
end

/-! ### The curve order limit -/

section
section Limit
variable (R : Type) [CommRing R] (t x : R) (beta : BlowupRestriction R t x) {d : ℕ}
  (G : GluedGenerators R t x beta d)
/-- The product of the two charts. -/
abbrev ChartPair := BlowupChart R t x × BlowupChart R x t
/-- Sequences of curve sections compatible modulo the curve ideal lattices. -/
def curveThreads : Submodule R (ℕ → ChartPair R t x) :=
  Submodule.pi Set.univ (fun j => curveSections R t x beta G j) ⊓
    (Submodule.pi Set.univ (fun j => curveIdealLattice R t x beta G j)).comap
      (towerDelta R (fun _ => ChartPair R t x) (fun _ => LinearMap.id))
/-- Sequences lying levelwise in the curve ideal lattices. -/
def curveNull : Submodule R (ℕ → ChartPair R t x) :=
  Submodule.pi Set.univ (fun j => curveIdealLattice R t x beta G j)
/-- Null sequences among the curve threads. -/
def curveNullThreads : Submodule R (curveThreads R t x beta G) :=
  (curveNull R t x beta G).comap (curveThreads R t x beta G).subtype
/-- The inverse limit of the curve orders: curve threads modulo null threads. -/
def CurveOrderLimit : Type := (curveThreads R t x beta G) ⧸ curveNullThreads R t x beta G
/-- Additive group structure on the curve order limit. -/
instance : AddCommGroup (CurveOrderLimit R t x beta G) :=
  inferInstanceAs (AddCommGroup ((curveThreads R t x beta G) ⧸ curveNullThreads R t x beta G))
/-- `R`-module structure on the curve order limit. -/
instance : Module R (CurveOrderLimit R t x beta G) :=
  inferInstanceAs (Module R ((curveThreads R t x beta G) ⧸ curveNullThreads R t x beta G))
/-- `O`-module structure on the curve order limit, by restriction of scalars. -/
instance (O : Type) [CommRing O] [Algebra O R] : Module O (CurveOrderLimit R t x beta G) :=
  inferInstanceAs (Module O ((curveThreads R t x beta G) ⧸ curveNullThreads R t x beta G))
/-- Scalar tower `O → R → CurveOrderLimit`. -/
instance (O : Type) [CommRing O] [Algebra O R] : IsScalarTower O R (CurveOrderLimit R t x beta G) :=
  inferInstanceAs (IsScalarTower O R ((curveThreads R t x beta G) ⧸ curveNullThreads R t x beta G))
/-- The quotient map from curve threads to the curve order limit. -/
def curveLimitMk : curveThreads R t x beta G →ₗ[R] CurveOrderLimit R t x beta G :=
  (curveNullThreads R t x beta G).mkQ
end Limit
section Product
variable {S : Type} [CommRing S]
/-- The reduction `S/(g, e^{j+1}) → S/(g, e^j)`. -/
def levelReduction (e g : S) (j : ℕ) : S ⧸ Ideal.span {g, e^(j+1)} →+* S ⧸ Ideal.span {g, e^j} :=
  Ideal.Quotient.factor (Ideal.span_le.mpr (by
    rintro y (rfl | rfl)
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [pow_succ]
      exact Ideal.mul_mem_right e _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))))
end Product
section CurveProduct
variable {R : Type} [CommRing R] {t x : R} {beta : BlowupRestriction R t x}
  (D : TwoChartCurveData R t x beta)
/-- All points of the curve: overlap points, the point `Z = 0`, and the point at infinity. -/
abbrev AllPoints := D.ι ⊕ (D.ι0 ⊕ D.ιinf)
/-- The completed local ring at each point of the curve. -/
def localRing : AllPoints D → Type
  | Sum.inl i => CompletedLocalAt (BlowupOverlap R t x) (D.Q i)
  | Sum.inr (Sum.inl k) => CompletedLocalAt (BlowupChart R t x) (leftPoint D (Sum.inr k))
  | Sum.inr (Sum.inr l) => CompletedLocalAt (BlowupChart R x t) (rightPoint D (Sum.inr l))
/-- Ring structure on the completed local rings. -/
instance localRing_commRing : ∀ p, CommRing (localRing D p)
  | Sum.inl i => inferInstanceAs (CommRing (CompletedLocalAt (BlowupOverlap R t x) (D.Q i)))
  | Sum.inr (Sum.inl k) => inferInstanceAs (CommRing (CompletedLocalAt (BlowupChart R t x)
      (leftPoint D (Sum.inr k))))
  | Sum.inr (Sum.inr l) => inferInstanceAs (CommRing (CompletedLocalAt (BlowupChart R x t)
      (rightPoint D (Sum.inr l))))
/-- The local equation of the curve at each point. -/
def localCurve : ∀ p, localRing D p
  | Sum.inl i => D.g i
  | Sum.inr (Sum.inl k) => leftData D (Sum.inr k)
  | Sum.inr (Sum.inr l) => rightData D (Sum.inr l)
/-- The local exceptional parameter at each point. -/
def localException : ∀ p, localRing D p
  | Sum.inl i => completedPointMap (BlowupOverlap R t x) (D.Q i) (overlapException R t x)
  | Sum.inr (Sum.inl k) => completedPointMap (BlowupChart R t x) (leftPoint D (Sum.inr k))
      (chartBase R t x t)
  | Sum.inr (Sum.inr l) => completedPointMap (BlowupChart R x t) (rightPoint D (Sum.inr l))
      (chartBase R x t x)
/-- The localization map from pairs of chart functions to the completed local ring at each point
(through the `t`-chart at the overlap points and at `Z = 0`, through the `x`-chart at infinity). -/
def localSection : ∀ p, ChartPair R t x →+* localRing D p
  | Sum.inl i => ((completedPointMap (BlowupOverlap R t x) (D.Q i)).comp
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))).comp (RingHom.fst _ _)
  | Sum.inr (Sum.inl k) =>
      (completedPointMap (BlowupChart R t x) (leftPoint D (Sum.inr k))).comp (RingHom.fst _ _)
  | Sum.inr (Sum.inr l) =>
      (completedPointMap (BlowupChart R x t) (rightPoint D (Sum.inr l))).comp (RingHom.snd _ _)
variable (j : ℕ)
/-- The local level quotient `(g, e^j)` at each point of the curve. -/
abbrev localQuotient (p : AllPoints D) : Type :=
  localRing D p ⧸ Ideal.span {localCurve D p, localException D p ^ j}
/-- The product of the local level quotients over all points of the curve. -/
abbrev curveProduct : Type := ∀ p : AllPoints D, localQuotient D j p
/-- The localization map from pairs of chart functions to the product of local quotients. -/
def sectionsToProduct : ChartPair R t x →+* curveProduct D j :=
  RingHom.pi fun p => (Ideal.Quotient.mk _).comp (localSection D p)
/-- The reduction from level `j + 1` to level `j` of the local product. -/
def curveProductReduction : curveProduct D (j + 1) →+* curveProduct D j :=
  RingHom.pi fun p => (levelReduction (localException D p) (localCurve D p) j).comp
    (Pi.evalRingHom _ p)
/-- Compatible threads in the tower of local products. -/
def curveProductThreads : Type :=
  {u : ∀ j, curveProduct D j // ∀ j, curveProductReduction D j (u (j+1)) = u j}
end CurveProduct
end

/-! ### The child order -/

section
variable {R : Type} [CommRing R] {t x : R} {beta : BlowupRestriction R t x}
    (D : TwoChartCurveData R t x beta)
/-- The map from `R` to the completed local ring at each point. -/
def localFromSurface : ∀ p, R →+* localRing D p
  | Sum.inl i => ((completedPointMap (BlowupOverlap R t x) (D.Q i)).comp
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))).comp (chartBase R t x)
  | Sum.inr (Sum.inl k) => (completedPointMap (BlowupChart R t x) (leftPoint D (Sum.inr k))).comp
      (chartBase R t x)
  | Sum.inr (Sum.inr l) => (completedPointMap (BlowupChart R x t) (rightPoint D (Sum.inr l))).comp
      (chartBase R x t)
/-- The product of the completed local rings of the curve at its points. -/
def childOrder : Type := ∀ p : AllPoints D, localRing D p ⧸ Ideal.span {localCurve D p}
/-- Ring structure on the child order. -/
instance : CommRing (childOrder D) := inferInstanceAs (CommRing
    (∀ p : AllPoints D, localRing D p ⧸ Ideal.span {localCurve D p}))
/-- The diagonal map from `R` to the child order. -/
def childOrderMap : R →+* childOrder D :=
  RingHom.pi fun p => (Ideal.Quotient.mk (Ideal.span {localCurve D p})).comp (localFromSurface D p)
/-- Algebra structure on the child order. -/
instance (O : Type) [CommRing O] [∀ p : AllPoints D, Algebra O (localRing D p)] : Algebra O
    (childOrder D) :=
  inferInstanceAs (Algebra O (∀ p : AllPoints D, localRing D p ⧸ Ideal.span {localCurve D p}))
end

/-! ### Points above a divisor -/

section
section Points
variable (R : Type) [CommRing R] (t x : R) [IsLocalRing R]
/-- The point of the `t`-chart above an affine direction `φ` of the exceptional line. -/
def directionPoint (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial
    (IsLocalRing.ResidueField R))
    (φ : AffineDirection (IsLocalRing.ResidueField R)) : Ideal (BlowupChart R t x) :=
  (Ideal.span {φ.val}).comap (e.toRingHom.comp (Ideal.Quotient.mk (chartExceptional R t x)))
/-- The point at infinity `(x, W)` of the `x`-chart. -/
def infinityPoint : Ideal (BlowupChart R x t) := Ideal.span {chartBase R x t x, chartSlope R x t}
/-- The colon strict transform `(J·R_P) : t^d` at a point `P` of the `t`-chart. -/
def strictTransformAt (P : Ideal (BlowupChart R t x)) [P.IsPrime] (d : ℕ) (J : Ideal R) :
    Ideal (CompletedLocalAt (BlowupChart R t x) P) :=
  (J.map ((completedPointMap (BlowupChart R t x) P).comp (chartBase R t x))).colon
    {(completedPointMap (BlowupChart R t x) P (chartBase R t x t))^d}
end Points
section Matching
variable {R : Type} [CommRing R] {t x : R} [IsLocalRing R] {beta : BlowupRestriction R t x}
/-- The points and multiplicities of the curve data match the divisor `Dv` on the
exceptional line. -/
structure MatchesDivisor (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial
    (IsLocalRing.ResidueField R))
    (D : TwoChartCurveData R t x beta) (Dv : ExceptionalDivisor (IsLocalRing.ResidueField R)) : Prop
        where
  common : ∀ i : D.ι, ∃ φ : AffineDirection (IsLocalRing.ResidueField R), φ ≠ zeroAffine
      (IsLocalRing.ResidueField R) ∧
    D.Q i = (directionPoint R t x e φ).map (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) ∧
    Dv (some φ) = commonMultiplicity D i
  common_surj : ∀ φ : AffineDirection (IsLocalRing.ResidueField R), φ ≠ zeroAffine
      (IsLocalRing.ResidueField R) →
    0 < Dv (some φ) → ∃ i : D.ι, D.Q i = (directionPoint R t x e φ).map
        (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))
  zero : ∀ k : D.ι0, D.P0 k = directionPoint R t x e (zeroAffine (IsLocalRing.ResidueField R)) ∧
    Dv (zeroDirection (IsLocalRing.ResidueField R)) = leftMultiplicity D (Sum.inr k)
  zero_surj : 0 < Dv (zeroDirection (IsLocalRing.ResidueField R)) → Nonempty D.ι0
  inf : ∀ l : D.ιinf, D.Pinf l = infinityPoint R t x ∧ Dv none = rightMultiplicity D (Sum.inr l)
  inf_surj : 0 < Dv none → Nonempty D.ιinf
end Matching
end

/-! ### Child ideal sets -/

section
section StateContacts
/-- The contact with the old boundary t = 0 recorded by a state (N002). -/
def stateContactT : State → ℕ
  | .single _ c => c
  | .crossing _ _ c _ => c
/-- The contact with the old boundary x = 0 recorded by a crossing state; `none` for a
single-boundary state. -/
def stateContactX : State → Option ℕ
  | .single _ _ => none
  | .crossing _ _ _ h => some h
end StateContacts
section Points
variable (R : Type) [CommRing R] (t x : R) [IsLocalRing R]
  (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (IsLocalRing.ResidueField R))
/-- The point above a monic irreducible φ (N881) is prime: it is the preimage of the maximal ideal
(φ) of k[Z]. -/
instance directionPoint_isPrime (φ : AffineDirection (IsLocalRing.ResidueField R)) :
    (directionPoint R t x e φ).IsPrime := by
  have : (Ideal.span {φ.val}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible φ.property.2).isPrime
  exact Ideal.IsPrime.comap _
variable (Dv : ExceptionalDivisor (IsLocalRing.ResidueField R))
    (hinf : (infinityPoint R t x).IsPrime)
/-- The completed local ring (N274) at a point of the support: of the right chart B = R[W]/(xW − t)
at the point
∞ = (x, W), of the left chart A = R[Z]/(tZ − x) at the point above an affine direction φ. -/
def divisorLocalRing : divisorSupport Dv → Type
  | ⟨none, _⟩ => @CompletedLocalAt (BlowupChart R x t) _ (infinityPoint R t x) hinf
  | ⟨some φ, _⟩ => CompletedLocalAt (BlowupChart R t x) (directionPoint R t x e φ)
/-- Ring structure on the completed local rings at the support points. -/
instance divisorLocalRing_commRing : ∀ Q, CommRing (divisorLocalRing R t x e Dv hinf Q)
  | ⟨none, _⟩ => inferInstanceAs (CommRing (@CompletedLocalAt (BlowupChart R x t) _
      (infinityPoint R t x) hinf))
  | ⟨some φ, _⟩ => inferInstanceAs (CommRing (CompletedLocalAt (BlowupChart R t x)
      (directionPoint R t x e φ)))
/-- The exceptional equation at a point of the support: the image of x at ∞, the image of t
elsewhere. -/
def divisorException : ∀ Q, divisorLocalRing R t x e Dv hinf Q
  | ⟨none, _⟩ => @completedPointMap (BlowupChart R x t) _ (infinityPoint R t x) hinf
      (chartBase R x t x)
  | ⟨some φ, _⟩ => completedPointMap (BlowupChart R t x) (directionPoint R t x e φ)
      (chartBase R t x t)
/-- The boundary equation at a point of the support: the image of the slope W at ∞ (there W = 0 is
the strict
transform of the old boundary t = 0) and the image of the slope Z at an affine point (at Z = 0 this
is the strict
transform of the old boundary x = 0; at every other affine point Z is a unit of the local ring). -/
def divisorBoundary : ∀ Q, divisorLocalRing R t x e Dv hinf Q
  | ⟨none, _⟩ => @completedPointMap (BlowupChart R x t) _ (infinityPoint R t x) hinf
      (chartSlope R x t)
  | ⟨some φ, _⟩ => completedPointMap (BlowupChart R t x) (directionPoint R t x e φ)
      (chartSlope R t x)
/-- The colon strict transform (J·R_P) : e_P^d (N881) of a parent ideal J at each point of the
support. -/
def divisorStrictTransform (d : ℕ) (J : Ideal R) : ∀ Q, Ideal (divisorLocalRing R t x e Dv hinf Q)
  | ⟨none, _⟩ => @strictTransformAt R _ x t (infinityPoint R t x) hinf d J
  | ⟨some φ, _⟩ => strictTransformAt R t x (directionPoint R t x e φ) d J
/-- The child ideal set at a point Q of the support, for the parent state s and multiplicity d:
principal ideals I
whose contact with the exceptional equation is the multiplicity Dv Q, whose contact with the old
boundary W = 0 is
c − d at ∞ (c the t-contact of s), and whose contact with the old boundary Z = 0 is h − d at the
point Z = 0 when
s is a crossing state with x-contact h. -/
def childIdealSet (s : State) (d : ℕ) (Q : divisorSupport Dv) :
    Set (Ideal (divisorLocalRing R t x e Dv hinf Q)) :=
  {I | (∃ g, I = Ideal.span {g}) ∧
    Module.length (divisorLocalRing R t x e Dv hinf Q)
      (divisorLocalRing R t x e Dv hinf Q ⧸ (I ⊔ Ideal.span {divisorException R t x e Dv hinf Q})) =
        (Dv Q.val : ℕ∞) ∧
    (Q.val = none → Module.length (divisorLocalRing R t x e Dv hinf Q)
      (divisorLocalRing R t x e Dv hinf Q ⧸ (I ⊔ Ideal.span {divisorBoundary R t x e Dv hinf Q})) =
        ((stateContactT s - d : ℕ) : ℕ∞)) ∧
    (Q.val = zeroDirection (IsLocalRing.ResidueField R) → ∀ h : ℕ, stateContactX s = some h →
      Module.length (divisorLocalRing R t x e Dv hinf Q)
        (divisorLocalRing R t x e Dv hinf Q ⧸ (I ⊔ Ideal.span {divisorBoundary R t x e Dv hinf Q}))
            =
          ((h - d : ℕ) : ℕ∞))}
end Points
end

/-! ### Blow-up charts -/

/-- On the `t`-chart, `t · X = x`. -/
theorem blowup_chart_relation (R : Type) [CommRing R] (t x : R) :
    chartBase R t x t * chartSlope R t x = chartBase R t x x := by
  have h : Ideal.Quotient.mk (Ideal.span {blowupRelation R t x}) (blowupRelation R t x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  simp only [blowupRelation] at h
  exact sub_eq_zero.mp h

/-- Ring maps out of a blow-up chart agree once they agree on `R` and on the slope. -/
theorem blowup_chart_ringHom_ext (R S : Type) [CommRing R] [CommRing S] (t x : R)
    (f g : BlowupChart R t x →+* S) (hbase : ∀ r : R, f (chartBase R t x r) = g (chartBase R t x r))
    (hslope : f (chartSlope R t x) = g (chartSlope R t x)) :
    f = g :=
  Ideal.Quotient.ringHom_ext (Polynomial.ringHom_ext hbase hslope)

/-- Universal property of the `t`-chart: a map `φ : R → S` with an element `z` satisfying
`φ t · z = φ x` extends uniquely through `R[X]/(tX − x)` sending the slope to `z`. -/
theorem blowup_chart_universal (R S : Type) [CommRing R] [CommRing S] (t x : R) (phi : R →+* S)
    (z : S) (hz : phi t * z = phi x) :
    ∃ psi : BlowupChart R t x →+* S, (∀ a : R, psi (chartBase R t x a) = phi a) ∧ psi
        (chartSlope R t x) = z := by
  have hker : ∀ p ∈ Ideal.span {blowupRelation R t x}, Polynomial.eval₂RingHom phi z p = 0 := by
    intro p hp
    rw [Ideal.mem_span_singleton'] at hp
    obtain ⟨q, rfl⟩ := hp
    simp [blowupRelation, hz]
  exact ⟨Ideal.Quotient.lift _ (Polynomial.eval₂RingHom phi z) hker, fun a => by simp [chartBase],
    by simp [chartSlope]⟩

/-- If `(t, x)` is a regular sequence, then `t` is a nonzerodivisor on the `t`-chart. -/
theorem blowup_exceptional_parameter_regular (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) :
    Function.Injective (fun a : BlowupChart R t x => chartBase R t x t * a) := by
  obtain ⟨ht, hx⟩ := hreg
  have hCt : ∀ P P' : Polynomial R, Polynomial.C t * P = Polynomial.C t * P' → P = P' :=
    fun P P' h ↦ Polynomial.ext fun n ↦
      ht (by simpa only [Polynomial.coeff_C_mul] using congrArg (Polynomial.coeff · n) h)
  have key : ∀ P : Polynomial R,
      Ideal.Quotient.mk (Ideal.span {blowupRelation R t x}) (Polynomial.C t * P) = 0 →
      Ideal.Quotient.mk (Ideal.span {blowupRelation R t x}) P = 0 := by
    intro P hP
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hP
    obtain ⟨Q, hQ⟩ := hP
    have hQt : Q ∈ Ideal.map Polynomial.C (Ideal.span {t}) := by
      rw [Ideal.mem_map_C_iff]
      intro i
      have e : Polynomial.C x * Q = Polynomial.C t * (Polynomial.X * Q - P) := by
        unfold blowupRelation at hQ
        linear_combination -hQ
      have := congrArg (fun F => Polynomial.coeff F i) e
      simp only [Polynomial.coeff_C_mul] at this
      have h0 : Ideal.Quotient.mk (Ideal.span {t}) x * Ideal.Quotient.mk (Ideal.span {t})
          (Q.coeff i) = Ideal.Quotient.mk (Ideal.span {t}) x * 0 := by
        rw [← map_mul, this, mul_zero, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)
      exact Ideal.Quotient.eq_zero_iff_mem.1 (hx h0)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hQt
    obtain ⟨Q1, hQ1⟩ := hQt
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨Q1, hCt _ _ ?_⟩
    rw [← hQ, ← hQ1]; ring
  intro a b hab
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨P', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [chartBase, RingHom.comp_apply, ← map_mul] at hab
  rw [← sub_eq_zero, ← map_sub]
  exact key _ (by rw [mul_sub, map_sub, hab, sub_self])

/-- The `x`-chart modulo its slope `W` is `R/(t)`, compatibly with the structure maps. -/
theorem boundary_chart_quotient_equiv (R : Type) [CommRing R] (t x : R) :
    ∃ ρ : (BlowupChart R x t ⧸ Ideal.span {chartSlope R x t}) ≃+* (R ⧸ Ideal.span {t}),
        (∀ r : R, ρ (Ideal.Quotient.mk (Ideal.span {chartSlope R x t}) (chartBase R x t r)) =
        Ideal.Quotient.mk (Ideal.span {t}) r) ∧ ρ (Ideal.Quotient.mk (Ideal.span {chartSlope R x t})
        (chartSlope R x t)) = 0 := by
  let φ : Polynomial R →+* R ⧸ Ideal.span {t} :=
    Polynomial.eval₂RingHom (Ideal.Quotient.mk (Ideal.span {t})) 0
  have hφ : ∀ r, φ (Polynomial.C r) = Ideal.Quotient.mk (Ideal.span {t}) r := fun r => by
    simp [φ]
  have hX : φ Polynomial.X = 0 := by simp [φ]
  have hrel : φ (blowupRelation R x t) = 0 := by
    simp [blowupRelation, φ]
  let f1 : BlowupChart R x t →+* R ⧸ Ideal.span {t} :=
    Ideal.Quotient.lift _ φ (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [hrel])
  have hf1 : ∀ p, f1 (Ideal.Quotient.mk _ p) = φ p := fun p => rfl
  let f : (BlowupChart R x t ⧸ Ideal.span {chartSlope R x t}) →+* R ⧸ Ideal.span {t} :=
    Ideal.Quotient.lift _ f1 (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
      simp [chartSlope, hf1, hX])
  let g0 : R →+* (BlowupChart R x t ⧸ Ideal.span {chartSlope R x t}) :=
    (Ideal.Quotient.mk _).comp (chartBase R x t)
  have hW : Ideal.Quotient.mk (Ideal.span {chartSlope R x t}) (chartSlope R x t) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hgt : g0 t = 0 := by
    change Ideal.Quotient.mk _ (chartBase R x t t) = 0
    rw [← blowup_chart_relation R x t, map_mul, hW]
    exact mul_zero (Ideal.Quotient.mk (Ideal.span {chartSlope R x t}) (chartBase R x t x))
  let g : (R ⧸ Ideal.span {t}) →+* (BlowupChart R x t ⧸ Ideal.span {chartSlope R x t}) :=
    Ideal.Quotient.lift _ g0 (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      change g0 (b * t) = 0
      rw [map_mul, hgt]; exact mul_zero (g0 b))
  have hfg : f.comp g = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp [f, g, g0, f1, φ, chartBase]
  have hgf : g.comp f = RingHom.id _ := by
    refine Ideal.Quotient.ringHom_ext <| Ideal.Quotient.ringHom_ext <| Polynomial.ringHom_ext
      (fun r ↦ by simp [f, g, g0, f1, φ, chartBase]) ?_
    · change g (f (Ideal.Quotient.mk _ (chartSlope R x t))) = _
      rw [hW, map_zero, map_zero]
      exact hW.symm
  refine ⟨RingEquiv.ofRingHom f g hfg hgf, fun r ↦ by simp [f, f1, φ, chartBase], ?_⟩
  change f (Ideal.Quotient.mk _ (chartSlope R x t)) = 0
  rw [hW, map_zero]

/-! ### The Čech complex of the two charts -/

/-- The twisted Čech differential maps the lattice `(t^j) × (x^j)` into `(t^j)`. -/
theorem actual_cech_preserves_exceptional_lattices (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ) :
    cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d)
        := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  have ha' : a ∈ Ideal.span {chartBase R t x t ^ j} := by
    rw [← Ideal.span_singleton_pow]; exact ha
  have hb' : b ∈ Ideal.span {chartBase R x t x ^ j} := by
    rw [← Ideal.span_singleton_pow]; exact hb
  rw [Ideal.mem_span_singleton'] at ha' hb'
  clear ha hb
  obtain ⟨a0, rfl⟩ := ha'
  obtain ⟨b0, rfl⟩ := hb'
  simp only [Submodule.mem_comap, cechOutputLattice, Submodule.restrictScalars_mem,
    Ideal.span_singleton_pow, fullCechDifferential, ringCechDifferential]
  change (IsScalarTower.toAlgHom R (BlowupChart R t x) (BlowupOverlap R t x)) _ -
    IsLocalization.Away.invSelf (chartSlope R t x) ^ d * beta.right _ ∈ _
  have hx : beta.right (chartBase R x t x) =
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x t) *
        algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x) := by
    rw [← map_mul, blowup_chart_relation]
    exact beta.right.commutes x
  apply Ideal.sub_mem
  · rw [Ideal.mem_span_singleton']
    refine ⟨IsScalarTower.toAlgHom R (BlowupChart R t x) (BlowupOverlap R t x) a0, ?_⟩
    simp
  · rw [Ideal.mem_span_singleton']
    refine ⟨IsLocalization.Away.invSelf (chartSlope R t x) ^ d *
      (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartSlope R t x)) ^ j *
      beta.right b0, ?_⟩
    rw [map_mul, map_pow, hx]
    ring

/-- The level Čech differentials commute with the reduction maps. -/
theorem actual_cech_differentials_commute_with_reduction (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ) (hnext : cechInputLattice R t x (j + 1) ≤
    (cechOutputLattice R t x (j + 1)).comap (fullCechDifferential R t x beta d))
    (hnow : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta d)) :
    (cechOutputReduction R t x j).comp (finiteCechDifferential R t x beta d (j+1) hnext) =
        (finiteCechDifferential R t x beta d j hnow).comp (cechInputReduction R t x j) :=
  LinearMap.ext fun q => Submodule.Quotient.induction_on _ q fun _ => rfl

/-- The reduction maps of the Čech source and target towers are surjective. -/
theorem actual_cech_reductions_surjective (R : Type) [CommRing R] (t x : R) (j : ℕ) :
    Function.Surjective (cechInputReduction R t x j) ∧ Function.Surjective
        (cechOutputReduction R t x j) := by
  constructor <;>
  · intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.mkQ _ z, rfl⟩

/-! ### Coordinates and adic cylinders -/

/-- Coordinate vectors over a DVR with finite residue field admit a finite set of unique
representatives modulo `π^M`. -/
theorem coordinate_coset_representatives_exist (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (n M : ℕ) :
    ∃ reps : Finset (Fin n → O), ∀ z : Fin n → O, ∃! z₀, z₀ ∈ reps ∧ adicCongr (Ideal.span {pi}) M z
        z₀ := by
  classical
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {pi} := hpi.maximalIdeal_eq
  have hc := residue_quotient_card O M
  rw [hmax] at hc
  have : Finite (O ⧸ (Ideal.span {pi})^M) := by
    apply Nat.finite_of_card_ne_zero
    rw [hc]
    have : 0 < Nat.card (IsLocalRing.ResidueField O) := Nat.card_pos
    positivity
  have : Finite (((Fin n → O)) ⧸ ((Ideal.span {pi})^M • ⊤ : Submodule O (Fin n → O))) :=
    finite_free_residue_quotient O (Fin n → O) ((Ideal.span {pi})^M)
  have := Fintype.ofFinite (((Fin n → O)) ⧸ ((Ideal.span {pi})^M • ⊤ : Submodule O (Fin n → O)))
  refine ⟨Finset.univ.image (fun c : ((Fin n → O)) ⧸ ((Ideal.span {pi})^M • ⊤ : Submodule O
      (Fin n → O)) => Quotient.out c), fun z => ?_⟩
  have key : ∀ w : Fin n → O, adicCongr (Ideal.span {pi}) M z w ↔
      Submodule.Quotient.mk z = (Submodule.Quotient.mk w :
        ((Fin n → O)) ⧸ ((Ideal.span {pi})^M • ⊤ : Submodule O (Fin n → O))) := by
    intro w
    rw [Submodule.Quotient.eq]
    rfl
  refine ⟨Quotient.out (Submodule.Quotient.mk z :
    ((Fin n → O)) ⧸ ((Ideal.span {pi})^M • ⊤ : Submodule O (Fin n → O))), ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
  · rw [key]
    exact (Submodule.Quotient.mk_out _).symm
  · rintro y ⟨hy, hz⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
    rw [key] at hz
    have : Submodule.Quotient.mk z = c := by
      rw [hz]; exact Submodule.Quotient.mk_out c
    rw [this]

/-- Structural facts on the coefficient space `O^n`: its Borel σ-algebra is generated by
`π`-adic cylinders, the coefficient measure is a Haar probability measure, its `π`-adic quotients
are finite, and scaled linear maps are continuous. -/
theorem coefficient_space_strict_instances (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (pi : O) (hpi : Irreducible pi) (n : ℕ) :
    (inferInstance : MeasurableSpace (Fin n → O)) = adicCylinderSpace (Ideal.span {pi}) (Fin n → O)
        ∧ MeasureTheory.Measure.IsAddHaarMeasure (coefficientMeasure O n) ∧
        MeasureTheory.IsProbabilityMeasure (coefficientMeasure O n) ∧
        (∀ j, Finite (AdicQuotient (Ideal.span {pi}) (Fin n → O) j)) ∧ ∀ (a : ℕ)
        (L : (Fin n → O) →ₗ[O] (Fin n → O)), Continuous (fun z : Fin n → O => (pi^a) • L z) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {pi} := hpi.maximalIdeal_eq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hm]
    exact finite_coordinate_borel_cylinders O _ htop n
  · have h1 : MeasureTheory.Measure.addHaar (G := Fin n → O) Set.univ ≠ ⊤ :=
      isCompact_univ.measure_lt_top.ne
    have h2 : MeasureTheory.Measure.addHaar (G := Fin n → O) Set.univ ≠ 0 :=
      (MeasureTheory.Measure.measure_pos_of_nonempty_interior _ (by simp)).ne'
    unfold coefficientMeasure
    exact MeasureTheory.Measure.IsAddHaarMeasure.smul _ (by simp [h1]) (by simp [h2])
  · exact coefficient_measure_probability O htop n
  · intro j
    have : Finite (O ⧸ (Ideal.span {pi}) ^ j) := by
      rw [← hm]
      have hpos : 0 < Nat.card (IsLocalRing.ResidueField O) := Nat.card_pos
      exact Nat.finite_of_card_ne_zero (by rw [residue_quotient_card O j]; positivity)
    exact finite_free_residue_quotient O (Fin n → O) ((Ideal.span {pi}) ^ j)
  · exact fun a L => finite_coordinate_linear_continuous O n n ((pi ^ a) • L)

/-- The scaled strict map is `π` times the child coordinate map; hence its range and
preimages are those of the child coordinate map transported by `w ↦ π • w`. -/
theorem child_coordinate_map_scaled (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R)) (H : (Fin n → O) →ₗ[O] R)
    (ha : 1 ≤ a) (hinj : Function.Injective (fun w : Fin n → O => pi • w)) :
    (∀ z : Fin n → O, pi • childCoordinateMap pi a b E H z = scaledStrictMap pi a b E H z) ∧
        Set.range (scaledStrictMap pi a b E H) = (fun w : Fin n → O => pi • w) '' Set.range
        (childCoordinateMap pi a b E H) ∧ ∀ T : Set (Fin n → O), scaledStrictMap pi a b E H ⁻¹'
        ((fun w : Fin n → O => pi • w) '' T) = childCoordinateMap pi a b E H ⁻¹' T := by
  have h1 : ∀ z : Fin n → O, pi • childCoordinateMap pi a b E H z = scaledStrictMap pi a b E H z :=
      by
    intro z
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    simp only [childCoordinateMap, scaledStrictMap, Nat.add_sub_cancel, smul_smul, pow_succ,
        mul_comm]
  refine ⟨h1, ?_, ?_⟩
  · rw [← Set.range_comp]
    ext x; constructor <;> rintro ⟨z, rfl⟩ <;> exact ⟨z, by simp [Function.comp, h1]⟩
  · intro T
    ext z
    simp only [Set.mem_preimage, ← h1]
    exact hinj.mem_set_image

/-! ### Completed local rings and lengths -/

/-- If `m̂^L ⊆ J` in the completed local ring at a maximal ideal `P`, then `P^L` is contained
in the contraction of `J`. -/
theorem completed_point_power_contraction (A : Type) [CommRing A] (P : Ideal A) [P.IsMaximal]
    (L : ℕ) (J : Ideal (CompletedLocalAt A P)) (hJ : ((IsLocalRing.maximalIdeal
    (Localization.AtPrime P)).map (localCompletionMap (Localization.AtPrime P))) ^ L ≤ J) :
    P^L ≤ J.comap (completedPointMap A P) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  refine le_trans (le_of_eq ?_) hJ
  congr 1
  unfold completedPointMap
  rw [← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]

/-- If `P^L ⊆ I` and `P` meets the localizing submonoid, then `I` extends to the unit ideal. -/
theorem contracted_ideal_map_localization_top (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] (P I : Ideal A) (L : ℕ) (hPI : P ^ L ≤ I) (m : A)
    (hm : m ∈ M) (hmP : m ∈ P) :
    I.map (algebraMap A S) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (hPI (Ideal.pow_mem_pow hmP L))) ?_
  rw [map_pow]
  exact (IsLocalization.map_units S ⟨m, hm⟩).pow L

/-- The length of `R/(π, f)` for a concrete surface `R` equals the length of the special fibre
modulo the image of `f`. -/
theorem concrete_surface_special_fiber_length_transport (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (f : ConcreteSurface O pi u a b) (e : (ConcreteSurface O pi u a b ⧸ Ideal.span
    {algebraMap O (ConcreteSurface O pi u a b) pi}) ≃+* SpecialFiber (IsLocalRing.ResidueField O) a
    b) :
    Module.length (ConcreteSurface O pi u a b) (ConcreteSurface O pi u a b ⧸ Ideal.span
        {algebraMap O (ConcreteSurface O pi u a b) pi, f}) = Module.length
        (SpecialFiber (IsLocalRing.ResidueField O) a b) (SpecialFiber (IsLocalRing.ResidueField O) a
        b ⧸ Ideal.span {e (Ideal.Quotient.mk (Ideal.span
        {algebraMap O (ConcreteSurface O pi u a b) pi}) f)}) := by
  let R := ConcreteSurface O pi u a b
  let SF := SpecialFiber (IsLocalRing.ResidueField O) a b
  let I : Ideal R := Ideal.span {algebraMap O R pi}
  let g : SF := e (Ideal.Quotient.mk I f)
  let φ : R →+* SF := e.toRingHom.comp (Ideal.Quotient.mk I)
  have hφ : Function.Surjective φ :=
    e.surjective.comp Ideal.Quotient.mk_surjective
  let _ : Algebra R SF := φ.toAlgebra
  have hsurj : Function.Surjective (algebraMap R SF) := hφ
  rw [← Module.length_eq_of_surjective (S := R) hsurj]
  let ψ : R →ₐ[R] SF ⧸ Ideal.span {g} := Algebra.ofId R _
  have hψ : Function.Surjective ψ := fun y ↦ by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, rfl⟩ := hφ z
    exact ⟨x, rfl⟩
  have hker : RingHom.ker ψ = Ideal.span {algebraMap O R pi, f} := by
    ext x
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (φ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    change e (Ideal.Quotient.mk I f) ∣ e (Ideal.Quotient.mk I x) ↔ _
    rw [map_dvd_iff]
    have h1 : Ideal.span {Ideal.Quotient.mk I f} = (Ideal.span {f}).map (Ideal.Quotient.mk I) := by
      rw [Ideal.map_span, Set.image_singleton]
    refine (Ideal.mem_span_singleton (x := Ideal.Quotient.mk I x)).symm.trans ?_
    rw [h1, Ideal.mem_quotient_iff_mem_sup, Ideal.span_insert, sup_comm]
  exact ((Submodule.quotEquivOfEq _ _ hker).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective hψ).toLinearEquiv).length_eq

end SurfaceBlowup
