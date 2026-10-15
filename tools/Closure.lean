import Theorems.Thm_Gen_MainDvr
import Theorems.Thm_SurfaceBlowupV2_recip_main
import Theorems.Thm_SurfaceBlowupV2_main_field_form
/-! Closure inventory (run read-only in monolith_gen): every project constant (module `Definitions.*` or
`Theorems.*`) in the transitive type+value closure of the unified main theorems. -/
open Lean Meta Elab Command

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString
  | none => "<current>"

def isLocal (env : Environment) (n : Name) : Bool :=
  let m := modOf env n; m.startsWith "Definitions." || m.startsWith "Theorems."

partial def projClosure (env : Environment) (roots : List Name) (stop : NameSet) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work := roots
  while !work.isEmpty do
    let c := work.head!
    work := work.tail!
    if seen.contains c || stop.contains c then continue
    seen := seen.insert c
    if isLocal env c then
      if let some ci := env.find? c then
        let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
        -- inductives: constructors; structures: projections reached via terms anyway
        let extra : Array Name := match ci with
          | .inductInfo iv => iv.ctors.toArray
          | _ => #[]
        for u in used ++ extra do
          if !seen.contains u then work := u :: work
  return seen

#eval show CoreM Unit from do
  let env ← getEnv
  let ff := env.find? ``SurfaceBlowupV2.main_field_form |>.get!
  let ffroots := (ff.type.getUsedConstants ++ (ff.value? (allowOpaque := true)).get!.getUsedConstants).toList.filter (· != ``SurfaceBlowupV2.main)
  let roots := [``SurfaceBlowupV2Gen.main_dvr, ``SurfaceBlowupV2.recip_main,
    ``SurfaceBlowupV2.global_rational_eval, ``SurfaceBlowupV2.global_formula_regular] ++ ffroots
  let cl := projClosure env roots {}
  let h ← IO.FS.Handle.mk "/data/users/asvin/prove2me_workspace/final/unified/logs/closure.tsv" .write
  -- all local constants, marked live/dead
  let mut nLive := 0
  let mut nDead := 0
  for (n, ci) in env.constants.toList do
    if isLocal env n && !n.isInternalDetail then
      let live := cl.contains n
      if live then nLive := nLive + 1 else nDead := nDead + 1
      let kind := match ci with
        | .thmInfo _ => "thm" | .axiomInfo _ => "axiom" | .defnInfo _ => "def"
        | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
      h.putStrLn s!"{if live then "LIVE" else "DEAD"}\t{kind}\t{modOf env n}\t{n}"
  h.flush
  -- module-level dependency edges induced by constant usage (live constants only)
  let mut edges : Std.HashSet (String × String) := {}
  for (n, _) in env.constants.toList do
    if isLocal env n then
      if let some ci := env.find? n then
        let m := modOf env n
        let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
        for u in used do
          if isLocal env u then
            let mu := modOf env u
            if mu != m then edges := edges.insert (m, mu)
  let he ← IO.FS.Handle.mk "/data/users/asvin/prove2me_workspace/final/unified/logs/edges_all.tsv" .write
  for (a, b) in edges.toList do he.putStrLn s!"{a}\t{b}"
  he.flush
  IO.println s!"live {nLive} dead {nDead} edges {edges.size}"
