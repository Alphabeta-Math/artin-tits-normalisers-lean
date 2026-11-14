import Lean.Elab.Command
import Lean.Util.FoldConsts
import ArtinRibbons
import ArtinLandmarks
import ArtinChambers
import ArtinSequences
import ArtinAsphericity
import ArtinHomotopy
import ArtinDeligne

/-!
Read-only observer of compiled declarations. It proves no mathematics and is
not imported by any scientific target. Run in the combined Deligne environment.
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

private def deligneProjectModule (m : Name) : Bool :=
  #["ArtinNormalisers.", "ArtinLandmarks.", "ArtinRibbons.", "ArtinChambers.", "ArtinSequences.", "ArtinAsphericity.", "ArtinHomotopy.", "ArtinDeligne."].any (fun pfx => m.toString.startsWith pfx)

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
      if deligneProjectModule env.header.moduleNames[index]! then
        rootNames := rootNames.push name
  if rootNames.isEmpty then throwError "No project declarations loaded"
  -- Check every serialized project occurrence, including private/generated names
  -- and any identical theorem aliases whose canonical owner is another module.
  let mut physicalModules : Array Json := #[]
  let mut physicalNames : NameSet := {}
  let mut aliases : Array Json := #[]
  let mut physicalCount := 0
  for module in env.header.moduleNames do
    if deligneProjectModule module ||
        #[`ArtinNormalisers, `ArtinNormalisersFull, `ArtinTheorem18,
          `ArtinLandmarks, `ArtinRibbons, `ArtinChambers, `ArtinSequences, `ArtinAsphericity, `ArtinHomotopy, `ArtinDeligne].contains module then
      let file ← Lean.findOLean module
      let mut files := #[file]
      let server := OLeanLevel.server.adjustFileName file
      if ← server.pathExists then
        files := files.push server
      let privatePart := OLeanLevel.private.adjustFileName file
      if ← privatePart.pathExists then
        unless ← server.pathExists do throwError "Private project part lacks server part: {module}"
        files := files.push privatePart
      let parts ← Lean.readModuleDataParts files
      if h : parts.size = 0 then throwError "Empty physical project module: {module}" else
        let last := parts[parts.size - 1]
        unless last.1.constNames.size == last.1.constants.size do
          throwError "Physical array mismatch: {module}"
        let mut names : Array String := #[]
        for name in last.1.constNames, ci in last.1.constants do
          unless name == ci.name do throwError "Physical name mismatch: {module} {name}"
          let some canonical := env.find? name | throwError "Physical name absent from environment: {name}"
          unless ci.type == canonical.type &&
              ci.value? (allowOpaque := true) == canonical.value? (allowOpaque := true) &&
              ci.levelParams == canonical.levelParams do
            throwError "Physical/canonical type, value or universes differ: {module} {name}"
          let some index := env.getModuleIdxFor? name | throwError "Physical name has no owner: {name}"
          let owner := env.header.moduleNames[index]!
          if owner != module then
            match ci, canonical with
            | .thmInfo _, .thmInfo _ => pure ()
            | _, _ => throwError "Non-theorem physical overlap: {module} {name}"
            aliases := aliases.push (Json.mkObj [
              ("name", toJson name.toString), ("physical_module", toJson module.toString),
              ("canonical_module", toJson owner.toString), ("same_type", toJson true),
              ("same_proof", toJson true), ("same_universe_parameters", toJson true)])
          physicalNames := physicalNames.insert name
          if !rootNames.contains name then rootNames := rootNames.push name
          names := names.push name.toString
          physicalCount := physicalCount + 1
        physicalModules := physicalModules.push (Json.mkObj [
          ("module", toJson module.toString), ("names", toJson names.toList),
          ("object_paths", toJson (files.toList.map System.FilePath.toString)),
          ("physical_occurrences", toJson names.size)])
  for name in rootNames do
    unless physicalNames.contains name do throwError "Canonical project root lacks a physical occurrence: {name}"
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
  let path := (← IO.getEnv "GITHUB_PROOF_GRAPH_OUT").getD "../docs/provenance/deligne/graph.raw.json"
  let result := Json.mkObj [
    ("kind", toJson "compiled-type-value-and-structure-dependency-graph"),
    ("root_selection", toJson "All physical/canonical project declarations in ArtinNormalisers., ArtinLandmarks., ArtinRibbons., ArtinChambers., ArtinSequences., ArtinAsphericity., ArtinHomotopy., ArtinDeligne.; supplier declarations arise through actual type/value/structural references"),
    ("imported_modules", toJson (env.header.moduleNames.toList.map Name.toString)),
    ("artifact_paths", Json.arr artifacts),
    ("roots", toJson (rootNames.toList.map Name.toString)),
    ("physical_project_modules", Json.arr physicalModules),
    ("physical_project_occurrences", toJson physicalCount),
    ("physical_project_distinct_names", toJson physicalNames.size),
    ("physical_project_identical_theorem_aliases", Json.arr aliases),
    ("declaration_count", toJson rows.size), ("edge_count", toJson edgeCount),
    ("nodes", Json.arr rows)]
  IO.FS.writeFile path (result.pretty ++ "\n")
  logInfo m!"DELIGNE_DEPENDENCY_GRAPH_EXPORTED roots={rootNames.size} declarations={rows.size} edges={edgeCount} path={path}"
