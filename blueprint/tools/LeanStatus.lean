/-
Write `lean_status.json` for the progress dashboard.

For every Lean name referenced by a `\lean{...}` in the blueprint, record whether the
declaration exists and whether it (transitively) depends on `sorryAx`.

Run from the Lean project root after `lake build`, with the blueprint data already built
(`python3 blueprint/tools/build_site.py`):

    lake env lean --run blueprint/tools/LeanStatus.lean GSQG blueprint/site/data/blueprint.json lean_status.json

The first argument is the root module to import. Then rebuild the site with
`LEAN_STATUS=lean_status.json blueprint/build.sh`.
-/
import Lean
open Lean

def leanNames (j : Json) : Except String (Array Name) := do
  let nodes ← (← j.getObjVal? "nodes").getArr?
  let mut out := #[]
  for n in nodes do
    for l in ← (← n.getObjVal? "lean").getArr? do
      out := out.push (← l.getStr?).toName
  return out

/-- Does `n` use `sorryAx` *locally*, i.e. reachable through its own type/value and helper
declarations in `GSQG`, without passing through another blueprint declaration (those are the
dependency-graph cut points)? This is leanblueprint's "proved" (`\leanok` on the proof),
as opposed to "fully proved" (no `sorryAx` anywhere, reported by `sorry`). -/
def projectConstant (n : Name) : Bool :=
  (`GSQG).isPrefixOf (privateToUserName n)

def standardAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

/-- Follow private and public helpers; stop at *other* blueprint declarations.
Return both unfinished local proof obligations and the actual blueprint dependencies. -/
def localDependencies (env : Environment) (bp : NameSet) (n : Name) :
    StateM (NameMap (Array Name)) (Bool × Array Name) := do
  let mut todo := #[n]
  let mut seen : NameSet := {}
  let mut deps : NameSet := {}
  let mut sorryFound := false
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let used ← match (← get).find? c with
      | some used => pure used
      | none => do
        let some ci := env.find? c | pure #[]
        let used := ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
        modify (·.insert c used)
        pure used
    for d in used do
      if d == ``sorryAx then sorryFound := true
      if bp.contains d && d != n then
        deps := deps.insert d
      else if projectConstant d then
        todo := todo.push d
  return (sorryFound, deps.toArray)

unsafe def main (args : List String) : IO UInt32 := do
  let [root, input, output] := args
    | IO.eprintln "usage: LeanStatus <RootModule> <blueprint.json> <lean_status.json>"; return 1
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let rawNames ← IO.ofExcept (leanNames json)
  let names := (rawNames.foldl (fun s n => s.insert n) ({} : NameSet)).toArray
  initSearchPath (← findSysroot)
  enableInitializersExecution
  IO.eprintln s!"Importing {root} for {names.size} declarations…"
  -- Axiom summaries are persistent environment extensions. Without loadExts the
  -- collector re-walks the entire Mathlib proof graph for each GSQG declaration.
  let env ← importModules #[{ module := root.toName }] {} (trustLevel := 1024) (loadExts := true)
  IO.eprintln "Imported; scanning proof dependencies…"
  let mut fields : Array (String × Json) := #[]
  let mut nExists := 0
  let mut nSorryFree := 0
  let mut nLocal := 0
  let bp : NameSet := names.foldl (·.insert ·) {}
  let mut depsCache : NameMap (Array Name) := {}
  for n in names do
    if env.contains n then
      let (axioms, _) ← (collectAxioms n : CoreM (Array Name)).toIO
        { fileName := "LeanStatus", fileMap := default } { env }
      let hasSorry := axioms.contains ``sorryAx
      let expectedAxioms := axioms.all fun a => standardAxiom a || a == ``sorryAx
      nExists := nExists + 1
      if !hasSorry && expectedAxioms then nSorryFree := nSorryFree + 1
      let ((loc, deps), cache) := (localDependencies (env.setExporting false) bp n).run depsCache
      depsCache := cache
      if !loc && expectedAxioms then nLocal := nLocal + 1
      fields := fields.push (n.toString,
        Json.mkObj [("exists", true), ("sorry", hasSorry), ("local_sorry", loc),
                    ("axioms", toJson (axioms.map Name.toString)),
                    ("blueprint_deps", toJson (deps.map Name.toString))])
    else
      fields := fields.push (n.toString, Json.mkObj [("exists", false), ("sorry", true), ("local_sorry", true)])
    if fields.size % 50 == 0 then IO.eprintln s!"Scanned {fields.size}/{names.size} declarations"
  IO.FS.writeFile output ((Json.mkObj fields.toList).pretty)
  IO.println s!"{names.size} blueprint names: {nExists} exist in Lean, {nSorryFree} sorry-free with standard axioms, {nLocal} locally complete"
  return 0
