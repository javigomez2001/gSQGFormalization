module
import all Lean.Util.CollectAxioms
import Lean
open Lean

/-- The logical axioms permitted by this formalization. -/
def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

/-- Audit every kernel declaration owned by an imported GSQG module, not only blueprint names. -/
public unsafe def main (args : List String) : IO UInt32 := do
  let [root, output] := args
    | IO.eprintln "usage: AllAxioms <root module> <output.json>"; return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := root.toName }] {} (trustLevel := 0) (loadExts := true)
  let env := env.setExporting false
  let projectOwned := fun (e : Environment) (n : Name) =>
    match e.getModuleIdxFor? n with
    | some i => (`GSQG).isPrefixOf e.header.moduleNames[i]!
    | none => false
  let externalAxioms := fun (e : Environment) (n : Name) =>
    if projectOwned e n then none else (exportedAxiomsExt.getState e).find? e n
  let mut axiomState : CollectAxioms.State := {}
  let mut seen : NameSet := {}
  let mut count := 0
  let mut theoremCount := 0
  let mut privateCount := 0
  let mut projectAxioms : Array Json := #[]
  let mut opaqueDecls : Array Json := #[]
  let mut bad : Array Json := #[]
  let mut modules : Array Json := #[]
  let mut usedAxioms : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if !(`GSQG).isPrefixOf modName then continue
    let data := env.header.moduleData[i]!
    let mut moduleCount := 0
    for n in data.constNames do
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.checked.get.find? n
        | bad := bad.push (Json.mkObj [("declaration", toJson n.toString),
            ("error", "module declaration absent from kernel environment")]); continue
      count := count + 1
      moduleCount := moduleCount + 1
      if isPrivateName n then privateCount := privateCount + 1
      match ci with
      | .thmInfo _ => theoremCount := theoremCount + 1
      | .axiomInfo _ => projectAxioms := projectAxioms.push (toJson n.toString)
      | .opaqueInfo _ => opaqueDecls := opaqueDecls.push (toJson n.toString)
      | _ => pure ()
      let (axioms, nextState) :=
        ((CollectAxioms.collectAndGet externalAxioms n).run env).run axiomState
      axiomState := nextState
      for a in axioms do usedAxioms := usedAxioms.insert a
      if axioms.any (fun a => !allowedAxiom a) then
        bad := bad.push (Json.mkObj [("declaration", toJson n.toString),
          ("module", toJson modName.toString), ("axioms", toJson (axioms.map Name.toString))])
    modules := modules.push (Json.mkObj [("module", toJson modName.toString),
      ("declarations", toJson moduleCount)])
    IO.eprintln s!"Audited {modName}: {moduleCount} kernel declarations"
  let result := Json.mkObj [
    ("root_module", toJson root), ("import_trust_level", toJson (0 : Nat)),
    ("scope", "Every kernel declaration in imported GSQG modules, including private/generated helpers"),
    ("recomputed_project_bodies", true),
    ("external_dependencies", "Pinned Mathlib/toolchain axiom summaries"),
    ("declarations", toJson count), ("theorems", toJson theoremCount),
    ("private_declarations", toJson privateCount), ("modules", toJson modules),
    ("project_axioms", toJson projectAxioms), ("opaque_declarations", toJson opaqueDecls),
    ("transitive_axioms", toJson (usedAxioms.toArray.map Name.toString)),
    ("failures", toJson bad)]
  IO.FS.writeFile output result.pretty
  IO.println s!"{count} declarations, {theoremCount} theorem constants, {privateCount} private declarations; {bad.size} axiom failures"
  return if bad.isEmpty && projectAxioms.isEmpty then 0 else 1
