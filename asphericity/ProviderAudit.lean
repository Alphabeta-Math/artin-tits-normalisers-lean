import Lean.Elab.Command
import Lean.Util.CollectAxioms
import ArtinAsphericityVendor.AlgebraicTopology.SemilocallySimplyConnected.Basic
import ArtinAsphericityVendor.Topology.Homotopy.TubeNeighborhood
import ArtinAsphericityVendor.AlgebraicTopology.SemilocallySimplyConnected.On
import ArtinAsphericityVendor.AlgebraicTopology.UniversalCover.BasedPath
import ArtinAsphericityVendor.AlgebraicTopology.UniversalCover.Basic
import ArtinAsphericityVendor.Topology.SeparatedMap
import ArtinAsphericityVendor.Topology.IsLocalHomeomorph
import ArtinAsphericityVendor.AlgebraicTopology.UniversalCover.Covering
import ArtinAsphericityVendor.Topology.Homotopy.HomotopyEquiv
import ArtinAsphericityVendor.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
import ArtinAsphericityVendor.Topology.Algebra.Module.LocallyContractible

#check TauCeti.UniversalCover.isCoveringMap
#check TauCeti.UniversalCover.simplyConnectedSpace
#check HomotopyGroup.subsingleton_of_contractibleSpace
#check TauCeti.RealTopologicalVectorSpace.stronglyLocallyContractibleSpace

/-!
# Physical provider declaration coverage

Read the same serialized parts as exact single-module kernel replay and compare
all physical constants to the canonical imported declarations whose transitive
axioms are checked here. Overlap is permitted only for structurally identical
theorems, with identical types, values and universe parameters. This harness
adds no mathematical assumptions and does not repeat kernel replay.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

/-- Same physical-part reader used by the reviewed project audit. -/
def asphericityProviderReadParts (module : Lean.Name) : IO (Array (Lean.ModuleData × Lean.CompactedRegion)) := do
  let file ← Lean.findOLean module
  unless (← file.pathExists) do
    throw <| IO.userError s!"Missing provider compiled module: {module}"
  let mut files := #[file]
  let server := Lean.OLeanLevel.server.adjustFileName file
  if (← server.pathExists) then
    files := files.push server
    let privatePart := Lean.OLeanLevel.private.adjustFileName file
    if (← privatePart.pathExists) then files := files.push privatePart
  Lean.readModuleDataParts files

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected := env.header.moduleNames.filter fun mod => mod.toString.startsWith "ArtinAsphericityVendor."
  unless expected.size == 11 do
    throwError "Expected 11 imported provider module, found {expected.size}"
  let mut canonicalNames : Std.HashMap Name Name := {}
  let mut canonicalCount : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx]!
      if expected.contains mod then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Forbidden canonical provider axiom {ax} in {name} ({mod})"
        let row := Json.mkObj [("module", toJson mod.toString), ("name", toJson name.toString),
          ("axioms", toJson (axioms.toList.map Name.toString))]
        logInfo m!"ASPHERICITY_PROVIDER_DECL_JSON {row.compress}"
        canonicalNames := canonicalNames.insert name mod
        canonicalCount := canonicalCount + 1
  if canonicalCount == 0 then throwError "Empty canonical provider audit"
  let mut physicalNames : Std.HashMap Name Nat := {}
  let mut physicalCount : Nat := 0
  let mut duplicateCount : Nat := 0
  for mod in expected do
    let parts ← asphericityProviderReadParts mod
    if empty : parts.size = 0 then
      throwError "Empty physical provider module data: {mod}"
    else
      let last := parts[parts.size - 1]
      unless last.1.constNames.size == last.1.constants.size do
        throwError "Physical name/constant array length mismatch: {mod}"
      let mut names : Array String := #[]
      for name in last.1.constNames, ci in last.1.constants do
        unless name == ci.name do throwError "Compiled name/constant mismatch in {mod}"
        let some owner := canonicalNames.get? name |
          throwError "Physical declaration outside canonical provider axiom coverage: {name} ({mod})"
        let some imported := env.find? name |
          throwError "Physical declaration absent from imported audit environment: {name} ({mod})"
        unless ci.type == imported.type && ci.value? == imported.value? &&
            ci.levelParams == imported.levelParams do
          throwError "Physical/imported declaration content mismatch: {name} ({mod})"
        unless owner == mod do
          match ci, imported with
          | .thmInfo _, .thmInfo _ => pure ()
          | _, _ => throwError "Unexpected non-theorem declaration overlap: {name} ({mod}, {owner})"
          unless expected.contains owner do
            throwError "Overlapping provider declaration owned outside audited modules: {name} ({owner})"
          duplicateCount := duplicateCount + 1
          let row := Json.mkObj [
            ("name", toJson name.toString), ("physical_module", toJson mod.toString),
            ("canonical_module", toJson owner.toString), ("same_type", toJson true),
            ("same_proof", toJson true), ("same_universe_parameters", toJson true),
            ("theorem_in_both", toJson true)]
          logInfo m!"ASPHERICITY_PROVIDER_PHYSICAL_DUPLICATE_JSON {row.compress}"
        names := names.push name.toString
        physicalNames := physicalNames.insert name (physicalNames.getD name 0 + 1)
        physicalCount := physicalCount + 1
      if names.isEmpty then
        throwError "Provider module has no physical declarations: {mod}"
      let row := Json.mkObj [
        ("module", toJson mod.toString), ("declarations", toJson names.size),
        ("names", toJson names.toList)]
      logInfo m!"ASPHERICITY_PROVIDER_PHYSICAL_MODULE_JSON {row.compress}"
  for (name, _) in canonicalNames.toList do
    unless physicalNames.contains name do
      throwError "Canonical provider declaration has no physical occurrence: {name}"
  unless physicalNames.size == canonicalCount && physicalCount == canonicalCount + duplicateCount do
    throwError "Physical/canonical provider declaration coverage mismatch"
  let row := Json.mkObj [
    ("modules", toJson expected.size), ("canonical_declarations", toJson canonicalCount),
    ("physical_occurrences", toJson physicalCount),
    ("distinct_physical_names", toJson physicalNames.size),
    ("identical_theorem_duplicates", toJson duplicateCount),
    ("canonical_axioms_checked", toJson true),
    ("all_physical_type_value_universe_parameters_identical", toJson true)]
  logInfo m!"ASPHERICITY_PROVIDER_PHYSICAL_SUMMARY_JSON {row.compress}"
