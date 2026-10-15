/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import Tests.NonVacuity
import Tests.Regression

/-!
# Tests for `SurfaceBlowup`

Root of the `Tests` library: non-vacuity of the hypotheses of `SurfaceBlowup.main_dvr`
(`Tests.NonVacuity`) and regression guards pinning the universal density expressions to known values
(`Tests.Regression`).

Provenance: the regression guards are ported from the certified tree's quadratic/cubic/quartic
helper files; the non-vacuity examples are new.
-/
