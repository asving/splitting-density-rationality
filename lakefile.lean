import Lake
open Lake DSL

package «surfaceBlowup» where
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- Mathlib (from v4.35.0) asks importers to use the module system; these files do not.
  -- This is Lake's opt-out; it changes nothing about elaboration or checking.
  allowNonModules := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

/-- The unified formalization: rationality of type densities over complete DVRs, and reciprocity. -/
@[default_target]
lean_lib «SurfaceBlowup» where
  globs := #[.andSubmodules `SurfaceBlowup]

/-- Regression guards and the non-vacuity example (depend only on `Basic` and the main theorems). -/
@[default_target]
lean_lib «Tests» where
  globs := #[.one `Tests, .andSubmodules `Tests]
