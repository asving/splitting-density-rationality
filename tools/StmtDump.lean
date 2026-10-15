import SurfaceBlowup
/-! Dump `module  name  kind  typeHash  valueHash` for every non-internal constant of the
`SurfaceBlowup` modules (value hash only for definitions/instances, `-` for theorems) to the file
named by the environment variable `STMT_DUMP` (default `logs/stmt_dump.tsv`). Used to verify that a
refactor left statements (and data definitions) kernel-term-identical: diff two dumps. -/
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`SurfaceBlowup).isPrefixOf m do continue
    if n.isInternalDetail then continue
    let (kind, v) := match ci with
      | .thmInfo _ => ("thm", "-")
      | .defnInfo d => ("def", toString d.value.hash)
      | .opaqueInfo d => ("opaque", toString d.value.hash)
      | .inductInfo _ => ("ind", "-")
      | .ctorInfo _ => ("ctor", "-")
      | .recInfo _ => ("rec", "-")
      | .axiomInfo _ => ("AXIOM", "-")
      | .quotInfo _ => ("quot", "-")
    rows := rows.push s!"{m}\t{n}\t{kind}\t{ci.type.hash}\t{v}"
  let path := (← IO.getEnv "STMT_DUMP").getD "logs/stmt_dump.tsv"
  IO.FS.writeFile path (String.intercalate "\n" (rows.qsort (· < ·)).toList ++ "\n")
  logInfo m!"wrote {rows.size} rows to {path}"
