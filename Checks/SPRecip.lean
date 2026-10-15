/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import SurfaceBlowup
import Theorems.Thm_SurfaceBlowupV2_recip_main
/-!
# Statement preservation check: SurfaceBlowupV2.recip_main (certified, monolith_recip) vs SurfaceBlowup.recip_main (unified)

Both environments are loaded into ONE Lean environment (module names are disjoint:
`Definitions.*`/`Theorems.*` vs `SurfaceBlowup.*`; declaration names are disjoint: `SurfaceBlowupV2*`/`SolN*`
vs `SurfaceBlowup.*`). Every certified constant is renamed by the namespace map
`SurfaceBlowupV2(Orig|Gen)? ↦ SurfaceBlowup`, `SolN* ↦ SurfaceBlowup.SolN*`.

**Implication form** (cycle 4a). The unified theorem may have dropped hypotheses of the certified
statement (it is then strictly stronger). The checker
1. telescopes the certified statement into binders `x₀ … x_{m-1}` and conclusion `C`, and matches the
   binders of the unified statement, in order, to a subsequence of them (binder types alpha-equal under
   the constant correspondence below); every unmatched certified binder must be a proposition — a
   *dropped hypothesis* — and is printed;
2. checks that the two conclusions are identical under the correspondence (`CONCLUSION_IDENTICAL`);
3. walks the definitional closure of every constant occurring in the certified statement — including
   the dropped hypotheses — and pairs each certified constant with the unified constant of the renamed
   name, checking alpha-equivalence of types and values, equal kinds, universe parameters and inductive
   shapes (auxiliary `match_N`/`_proof_N`/... constants, whose names depend on elaboration order, are
   paired structurally, coinductively). Mathlib constants are leaves (shared by both trees);
4. replaces every certified constant of the certified statement by its verified unified counterpart and
   asks the KERNEL to accept
   `theorem SPCheck.certified_statement : <certified statement> := fun x₀ … x_{m-1} => SurfaceBlowup.recip_main x_{i₀} …`
   (`KERNEL_OK`): the certified statement, with all its hypotheses, follows from the unified theorem.

Negative control: the old identity check (the full certified type alpha-equal to the full unified type)
is still run and must report `DIFFERS` exactly when some hypothesis was dropped (and `IDENTICAL`
otherwise); the conclusions, which did not change, must be identical.
-/
open Lean Meta Elab Command

def spRename (n : Name) : Name :=
  let comps := n.components
  match comps with
  | [] => n
  | c :: rest =>
    let s := c.toString
    if s == "SurfaceBlowupV2" || s == "SurfaceBlowupV2Orig" || s == "SurfaceBlowupV2Gen" then
      rest.foldl (fun acc x => acc ++ x) `SurfaceBlowup
    else if s.startsWith "SolN" then
      comps.foldl (fun acc x => acc ++ x) `SurfaceBlowup
    else n

def spRenameExpr (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => some (.const (spRename n) ls)
    | _ => none

def spModOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString
  | none => "<current>"

def spIsCert (env : Environment) (n : Name) : Bool :=
  let m := spModOf env n
  m.startsWith "Definitions." || m.startsWith "Theorems."

def spKind : ConstantInfo → String
  | .thmInfo _ => "thm" | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- Auxiliary constants whose NAMES depend on elaboration order (matcher/aux-lemma deduplication):
they are matched up structurally rather than by name. -/
def spIsAux (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "match_" || s.startsWith "_proof_" || s == "_f" || s.startsWith "_sparseCasesOn"
      || s.startsWith "_unary" || s.startsWith "_binary" || s == "proof_1" || s.startsWith "eq_"
  | _ => false

structure SPState where
  pairs : Std.HashMap Name Name := {}
  todo : List (Name × Name) := []

abbrev SPM := StateT SPState MetaM

/-- Does certified constant `a` correspond to unified constant `b`?  Non-auxiliary constants
correspond iff `spRename a = b`; auxiliary ones are paired up on first use (coinductively) and the
pair is queued for a structural check of types and values. Mathlib constants must be identical. -/
def spConstCorr (a b : Name) : SPM Bool := do
  let env ← getEnv
  if !spIsCert env a then return a == b
  if let some b' := (← get).pairs.get? a then return b' == b
  if spRename a == b || (spIsAux a && spIsAux b && !spIsCert env b) then
    modify fun st => { st with pairs := st.pairs.insert a b, todo := (a, b) :: st.todo }
    return true
  return false

partial def spEq (e f : Expr) : SPM Bool := do
  match e, f with
  | .mdata _ e', _ => spEq e' f
  | _, .mdata _ f' => spEq e f'
  | .bvar i, .bvar j => return i == j
  | .fvar a, .fvar b => return a == b
  | .sort u, .sort v => return u == v
  | .lit l, .lit l' => return l == l'
  | .const a ls, .const b ls' => return ls == ls' && (← spConstCorr a b)
  | .app g x, .app g' x' => return (← spEq g g') && (← spEq x x')
  | .lam _ t b _, .lam _ t' b' _ => return (← spEq t t') && (← spEq b b')
  | .forallE _ t b _, .forallE _ t' b' _ => return (← spEq t t') && (← spEq b b')
  | .letE _ t v b _, .letE _ t' v' b' _ => return (← spEq t t') && (← spEq v v') && (← spEq b b')
  | .proj s i x, .proj s' i' x' => return i == i' && (← spConstCorr s s') && (← spEq x x')
  | _, _ => return false

def spCheckPair (a b : Name) : SPM (Option String) := do
  let env ← getEnv
  let some ci := env.find? a | return some s!"{a}: missing"
  let some ni := env.find? b | return some s!"{a} ↦ {b}: missing in unified env"
  if spIsCert env b then return some s!"{a} ↦ {b}: target is not a unified constant"
  if spKind ci != spKind ni then return some s!"{a} ↦ {b}: kind {spKind ci} vs {spKind ni}"
  if ci.levelParams != ni.levelParams then return some s!"{a} ↦ {b}: level params"
  if !(← spEq ci.type ni.type) then return some s!"{a} ↦ {b}: TYPE differs"
  match ci, ni with
  | .defnInfo d, .defnInfo d' =>
    if !(← spEq d.value d'.value) then return some s!"{a} ↦ {b}: VALUE differs"
  | .opaqueInfo d, .opaqueInfo d' =>
    if !(← spEq d.value d'.value) then return some s!"{a} ↦ {b}: VALUE differs"
  | .inductInfo d, .inductInfo d' =>
    if d.numParams != d'.numParams || d.numIndices != d'.numIndices || d.isRec != d'.isRec ||
        d.ctors.length != d'.ctors.length || d.all.length != d'.all.length then
      return some s!"{a}: inductive shape differs"
    for (c, c') in d.ctors.zip d'.ctors do
      if !(← spConstCorr c c') then return some s!"{a}: constructor {c} vs {c'}"
    for (c, c') in d.all.zip d'.all do
      if !(← spConstCorr c c') then return some s!"{a}: mutual block {c} vs {c'}"
  | .ctorInfo d, .ctorInfo d' =>
    if d.cidx != d'.cidx || d.numParams != d'.numParams || d.numFields != d'.numFields then
      return some s!"{a}: constructor shape differs"
    if !(← spConstCorr d.induct d'.induct) then return some s!"{a}: constructor of a different type"
  | .recInfo d, .recInfo d' =>
    if d.numMotives != d'.numMotives || d.numMinors != d'.numMinors || d.numParams != d'.numParams ||
        d.numIndices != d'.numIndices || d.k != d'.k then
      return some s!"{a}: recursor shape differs"
  | _, _ => pure ()  -- theorems: proof irrelevance, types suffice
  return none

/-- Process the queue of paired constants: check every pair structurally (this may queue more). -/
def spDrain : SPM (Array String × Nat) := do
  let mut bad : Array String := #[]
  let mut n := 0
  repeat
    let st ← get
    match st.todo with
    | [] => break
    | (a, b) :: rest =>
      set { st with todo := rest }
      n := n + 1
      if let some msg ← spCheckPair a b then bad := bad.push msg
  return (bad, n)

def spCheck (certThm newThm : Name) : MetaM Unit := do
  let env ← getEnv
  let some cthm := env.find? certThm | throwError "missing {certThm}"
  let some nthm := env.find? newThm | throwError "missing {newThm}"
  if cthm.levelParams != nthm.levelParams then throwError "main level params differ"
  -- negative control: the old identity check on the full statements
  let (ident, _) ← (spEq cthm.type nthm.type).run {}
  -- (1)+(2): match the unified binders to a subsequence of the certified binders, compare conclusions
  let (matched, dropped, concl, st) ← forallTelescope cthm.type fun xs cbody => do
    let mut st : SPState := {}
    let mut t := nthm.type
    let mut j := 0
    let mut matched : Array Nat := #[]
    let mut dropped : Array Nat := #[]
    while t.isForall do
      let .forallE _ d b _ := t | unreachable!
      let mut found : Option Nat := none
      while j < xs.size && found.isNone do
        let (ok, st') ← (spEq (← inferType xs[j]!) d).run st
        if ok then
          found := some j; st := st'
        else
          dropped := dropped.push j
        j := j + 1
      let some k := found | throwError "unified binder {d} has no certified counterpart"
      matched := matched.push k
      t := b.instantiate1 xs[k]!
    for k in [j:xs.size] do dropped := dropped.push k
    let (concl, st') ← (spEq cbody t).run st
    st := st'
    -- dropped binders must be propositions; pair the constants of their types by rename
    for k in dropped do
      let ty ← inferType xs[k]!
      unless ← isProp ty do throwError "dropped certified binder {xs[k]!} : {ty} is not a proposition"
      let (ok, st') ← (spEq ty (spRenameExpr ty)).run st
      unless ok do throwError "dropped hypothesis {ty}: constants have no unified counterpart"
      st := st'
      IO.println s!"dropped certified hypothesis: {← ppExpr xs[k]!} : {← ppExpr ty}"
    return (matched, dropped, concl, st)
  -- (3): definitional closure
  let ((bad, n), st) ← spDrain.run st
  let renamedByName := st.pairs.toList.filter (fun (a, b) => spRename a == b) |>.length
  IO.println s!"certified closure constants paired: {n} ({renamedByName} by namespace rename, {n - renamedByName} auxiliary matcher/aux-lemma constants paired structurally); problems: {bad.size}"
  for b in bad do IO.println s!"  PROBLEM {b}"
  for (a, b) in st.pairs.toList do
    if spRename a != b then IO.println s!"  aux pairing: {a} ~ {b}"
  if bad.size != 0 then throwError "closure mismatches"
  IO.println s!"binders: certified {matched.size + dropped.size}, unified {matched.size} (matched to certified binders {matched.toList}), dropped {dropped.size}"
  IO.println s!"NEGATIVE_CONTROL: old identity check on the full statements: {if ident then "IDENTICAL" else "DIFFERS"} (expected {if dropped.isEmpty then "IDENTICAL" else "DIFFERS"})"
  if ident != dropped.isEmpty then throwError "negative control inconsistent"
  if !concl then throwError "CONCLUSIONS DIFFER"
  IO.println s!"CONCLUSION_IDENTICAL: the conclusion of {certThm} is, constant-for-constant, the conclusion of {newThm}"
  -- (4): kernel check of the implication, in unified vocabulary
  let pm := st.pairs
  let mapped := cthm.type.replace fun
    | .const c ls => (pm.get? c).map (fun c' => .const c' ls)
    | _ => none
  let env ← getEnv
  if mapped.getUsedConstants.any (spIsCert env) then
    throwError "mapped certified statement still mentions certified constants"
  let lvls := nthm.levelParams.map Level.param
  let value ← forallTelescope mapped fun ys _ =>
    mkLambdaFVars ys (mkAppN (.const newThm lvls) (matched.map (ys[·]!)))
  let tv : TheoremVal :=
    { name := Name.mkStr `SPCheck "certified_statement"
      levelParams := nthm.levelParams
      type := mapped
      value := value }
  addDecl (.thmDecl tv)
  IO.println s!"KERNEL_OK: SPCheck.certified_statement : (certified type, constants mapped) := fun <{matched.size + dropped.size} binders> => {newThm} <{matched.size} of them>"

#eval spCheck ``SurfaceBlowupV2.recip_main ``SurfaceBlowup.recip_main
