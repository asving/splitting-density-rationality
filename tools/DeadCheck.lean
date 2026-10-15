import SurfaceBlowup
/-! Dead-declaration report for the unified tree: public/private constants in `SurfaceBlowup.*` modules not in
the type+value closure of the main theorems. Output: logs/dead_unified.tsv -/
open Lean

def dcMod (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString
  | none => "<current>"

def dcLocal (env : Environment) (n : Name) : Bool := (dcMod env n).startsWith "SurfaceBlowup"

partial def dcClosure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work := roots
  while !work.isEmpty do
    let c := work.head!
    work := work.tail!
    if seen.contains c then continue
    seen := seen.insert c
    if dcLocal env c then
      if let some ci := env.find? c then
        let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
        let extra : Array Name := match ci with | .inductInfo iv => iv.ctors.toArray | _ => #[]
        for u in used ++ extra do
          if !seen.contains u then work := u :: work
  return seen

#eval show CoreM Unit from do
  let env ← getEnv
  let cl := dcClosure env [``SurfaceBlowup.main_dvr, ``SurfaceBlowup.main_field_form,
    ``SurfaceBlowup.main_field_form_ramified, ``SurfaceBlowup.recip_main]
  let h ← IO.FS.Handle.mk "/data/users/asvin/prove2me_workspace/final/unified/logs/dead_unified.tsv" .write
  let mut nd := 0
  for (n, ci) in env.constants.toList do
    if dcLocal env n && !n.isInternalDetail && !cl.contains n then
      match ci with
      | .thmInfo _ | .defnInfo _ | .inductInfo _ =>
        nd := nd + 1
        h.putStrLn s!"{dcMod env n}\t{n}"
      | _ => pure ()
  h.flush
  IO.println s!"dead (thm/def/induct, non-internal): {nd}"
