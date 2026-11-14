import Lean.Elab.Command
import Lean.Util.FoldConsts
import ArtinRibbons
import ArtinLandmarks

/-!
Read-only observer of compiled declarations. It proves no mathematics and is
not imported by any scientific target. Run in the combined chambers environment.
-/
set_option autoImplicit false
set_option maxHeartbeats 0

open Lean Elab Command

private def declarationKind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient-builtin"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def acceptedProjectModule (m : Name) : Bool :=
  #["ArtinNormalisers.", "ArtinLandmarks.", "ArtinRibbons."].any (fun pfx => m.toString.startsWith pfx)

private def structuralReferences (ci : ConstantInfo) : NameSet := Id.run do
  let mut refs : NameSet := {}
  match ci with
  | .inductInfo info =>
    for n in info.all ++ info.ctors do refs := refs.insert n
  | .ctorInfo info => refs := refs.insert info.induct
  | .recInfo info =>
    for n in info.all do refs := refs.insert n
    for rule in info.rules do
      refs := refs.insert rule.ctor
      refs := refs ++ rule.rhs.getUsedConstantsAsSet
  | .defnInfo info =>
    for n in info.all do refs := refs.insert n
  | .thmInfo info =>
    for n in info.all do refs := refs.insert n
  | .opaqueInfo info =>
    for n in info.all do refs := refs.insert n
  | _ => pure ()
  return refs

run_cmd do
  let env ← getEnv
  let mut rootNames : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      if acceptedProjectModule env.header.moduleNames[index]! then
        rootNames := rootNames.push name
  if rootNames.isEmpty then throwError "No accepted project declarations loaded"
  let mut pending := rootNames.toList
  let mut visited : NameSet := {}
  let mut rows : Array Json := #[]
  let mut edgeCount := 0
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless visited.contains name do
      visited := visited.insert name
      let some ci := env.find? name |
        throwError "Dependency absent from compiled environment: {name}"
      let owner := match env.getModuleIdxFor? name with
        | some index => env.header.moduleNames[index]!.toString
        | none => "<no-imported-module>"
      let typeRefs := ci.type.getUsedConstantsAsSet
      let value := ci.value? (allowOpaque := true)
      let valueRefs := match value with
        | some term => term.getUsedConstantsAsSet
        | none => ({} : NameSet)
      let structureRefs := structuralReferences ci
      let refs := typeRefs ++ valueRefs ++ structureRefs
      for ref in refs do
        unless visited.contains ref do pending := ref :: pending
      edgeCount := edgeCount + refs.size
      let row := Json.mkObj [
        ("name", toJson name.toString), ("module", toJson owner),
        ("kind", toJson (declarationKind ci)),
        ("is_project_root", toJson (rootNames.contains name)),
        ("is_unsafe", toJson ci.isUnsafe), ("is_partial", toJson ci.isPartial),
        ("has_value", toJson value.isSome),
        ("type_dependencies", toJson (typeRefs.toList.map Name.toString)),
        ("value_dependencies", toJson (valueRefs.toList.map Name.toString)),
        ("structural_dependencies", toJson (structureRefs.toList.map Name.toString))]
      rows := rows.push row
  let mut artifacts : Array Json := #[]
  for mod in env.header.moduleNames do
    let file ← Lean.findOLean mod
    let mut files := #[file]
    let server := OLeanLevel.server.adjustFileName file
    if ← server.pathExists then files := files.push server
    let privatePart := OLeanLevel.private.adjustFileName file
    if ← privatePart.pathExists then files := files.push privatePart
    artifacts := artifacts.push (Json.mkObj [
      ("module", toJson mod.toString),
      ("object_paths", toJson (files.toList.map System.FilePath.toString))])
  let path := (← IO.getEnv "GITHUB_PROOF_GRAPH_OUT").getD "../docs/provenance/dependency-graph.raw.json"
  let result := Json.mkObj [
    ("kind", toJson "compiled-type-value-and-structure-dependency-graph"),
    ("root_selection", toJson "Defining module starts ArtinNormalisers., ArtinLandmarks., ArtinRibbons.; accepted contexts only"),
    ("imported_modules", toJson (env.header.moduleNames.toList.map Name.toString)),
    ("artifact_paths", Json.arr artifacts),
    ("roots", toJson (rootNames.toList.map Name.toString)),
    ("declaration_count", toJson rows.size), ("edge_count", toJson edgeCount),
    ("nodes", Json.arr rows)]
  IO.FS.writeFile path (result.pretty ++ "\n")
  logInfo m!"DEPENDENCY_GRAPH_EXPORTED roots={rootNames.size} declarations={rows.size} edges={edgeCount} path={path}"
