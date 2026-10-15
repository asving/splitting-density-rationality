import Theorems.Thm_SurfaceBlowupV2_recip_main
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let ci := env.find? ``SurfaceBlowupV2.recip_main |>.get!
  IO.println s!"{ci.isTheorem} {ci.value?.isSome} {(ci.value? (allowOpaque := true)).isSome}"
  match ci with
  | .thmInfo t => IO.println s!"{t.value.getUsedConstants.size}"
  | _ => pure ()
