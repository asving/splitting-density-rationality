/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup.Main
import SurfaceBlowup.Cluster.Main
import SurfaceBlowup.Etale.Algebra

/-!
# SurfaceBlowup

Root of the `SurfaceBlowup` library: factorization-type densities of Haar-random monic polynomials
and primitive binary forms over a complete discrete valuation ring with finite residue field, and
the reciprocity law for the universal rational functions computing them.

The main theorems are `SurfaceBlowup.main_dvr`, `SurfaceBlowup.main_field_form`,
`SurfaceBlowup.main_field_form_ramified` (in `SurfaceBlowup.Main`) and `SurfaceBlowup.recip_main`
(in `SurfaceBlowup.Reciprocity.Main`); the definitions occurring in their statements are in
`SurfaceBlowup.Basic`. Version 1.1 adds the cluster clause of the type-law theorem
(`SurfaceBlowup.main_dvr_cluster`, `SurfaceBlowup.cluster_formula_regular`,
`SurfaceBlowup.recip_cluster` in `SurfaceBlowup.Cluster.Main`, definitions in
`SurfaceBlowup.Cluster.Defs`) and the étale-convention form of the densities
(`SurfaceBlowup.main_dvr_etale`, `SurfaceBlowup.monicDensity_eq_etale`,
`SurfaceBlowup.projectiveDensity_eq_etale` in `SurfaceBlowup.Etale.Main`, definitions in
`SurfaceBlowup.Etale.Defs`).
-/
