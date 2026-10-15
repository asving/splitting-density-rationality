import Lake
open Lake DSL

package «surfaceBlowup» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

/-- The unified formalization: rationality of type densities over complete DVRs, and reciprocity. -/
@[default_target]
lean_lib «SurfaceBlowup» where
  globs := #[.andSubmodules `SurfaceBlowup]

/-- Regression guards and the non-vacuity example (depend only on `Basic` and the main theorems). -/
@[default_target]
lean_lib «Tests» where
  globs := #[.one `Tests, .andSubmodules `Tests]
