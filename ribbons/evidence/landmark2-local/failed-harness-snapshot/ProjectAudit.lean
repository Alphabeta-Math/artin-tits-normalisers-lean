import Lean.Elab.Command
import Lean.Util.CollectAxioms
import ArtinRibbons
import ArtinRibbons.AtomicCoxeter
import ArtinRibbons.CofinalRibbons
import ArtinRibbons.CoxeterProjection
import ArtinRibbons.DeltaDivisibility
import ArtinRibbons.FractionNormalForms
import ArtinRibbons.Fundamental
import ArtinRibbons.Landmark2
import ArtinRibbons.NormalizerSplitting
import ArtinRibbons.ParabolicReduction
import ArtinRibbons.Positive
import ArtinRibbons.PositiveEmbedding
import ArtinRibbons.PositiveReindex
import ArtinRibbons.PositiveRibbons
import ArtinRibbons.PositiveSupport
import ArtinRibbons.Presentation
import ArtinRibbons.ReducedRibbons
import ArtinRibbons.RibbonGroupoid
import ArtinRibbons.RibbonLcm
import ArtinRibbons.RibbonPositiveCalculus
import ArtinRibbons.RibbonRelations
import ArtinRibbons.RibbonUniversal
import ArtinRibbons.RibbonWords
import ArtinRibbons.SphericalPositive

/-!
# Exhaustive defining-module audit for the landmark 2 project

This legacy harness inspects all constants defined in the exact project modules,
including private declarations and generated auxiliaries. Imported provider and
parent declarations are traversed for transitive axioms but have separate full
validation. The aggregate has no scientific declarations; it must be imported,
while every one of the 23 scientific leaf modules must have declarations.
-/

set_option autoImplicit false

#check ArtinNormalisers.Ribbon2.landmark_2
#check ArtinNormalisers.Ribbon2.landmark_2_positive_presentation
#check ArtinNormalisers.Ribbon2.landmark_2_groupoid_presentation
#check ArtinNormalisers.Ribbon2.reducedRibbonNormalizerQuotientEquiv
#check ArtinNormalisers.Ribbon2.normalizerSemidirectEquiv
#check ArtinNormalisers.Ribbon2.reducedRibbon_projection_compatible
#print axioms ArtinNormalisers.Ribbon2.landmark_2
#print axioms ArtinNormalisers.Ribbon2.landmark_2_positive_presentation
#print axioms ArtinNormalisers.Ribbon2.landmark_2_groupoid_presentation

open Lean Elab Command in
run_cmd do
  let expected : Array Name := #[
    `ArtinRibbons.AtomicCoxeter, `ArtinRibbons.CofinalRibbons,
    `ArtinRibbons.CoxeterProjection, `ArtinRibbons.DeltaDivisibility,
    `ArtinRibbons.FractionNormalForms, `ArtinRibbons.Fundamental,
    `ArtinRibbons.Landmark2, `ArtinRibbons.NormalizerSplitting,
    `ArtinRibbons.ParabolicReduction, `ArtinRibbons.Positive,
    `ArtinRibbons.PositiveEmbedding, `ArtinRibbons.PositiveReindex,
    `ArtinRibbons.PositiveRibbons, `ArtinRibbons.PositiveSupport,
    `ArtinRibbons.Presentation, `ArtinRibbons.ReducedRibbons,
    `ArtinRibbons.RibbonGroupoid, `ArtinRibbons.RibbonLcm,
    `ArtinRibbons.RibbonPositiveCalculus, `ArtinRibbons.RibbonRelations,
    `ArtinRibbons.RibbonUniversal, `ArtinRibbons.RibbonWords,
    `ArtinRibbons.SphericalPositive]
  let env ← getEnv
  for mod in expected.push `ArtinRibbons do
    unless env.header.moduleNames.contains mod do
      throwError "Missing imported project module: {mod}"
  let mut counts : Std.HashMap Name Nat := {}
  let mut total : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx]!
      if mod == `ArtinRibbons || mod.toString.startsWith "ArtinRibbons." then
        unless mod == `ArtinRibbons || expected.contains mod do
          throwError "Unexpected project module in audit environment: {mod}"
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Forbidden transitive project axiom {ax} in {name} ({mod})"
        counts := counts.insert mod (counts.getD mod 0 + 1)
        total := total + 1
        logInfo m!"PROJECT_TYPE {mod} {name}: {ci.type}"
        let row := Json.mkObj [
          ("module", toJson mod.toString), ("name", toJson name.toString),
          ("axioms", toJson (axioms.toList.map Name.toString))]
        logInfo m!"PROJECT_DECL_JSON {row.compress}"
  if total == 0 then throwError "Empty project axiom audit"
  for mod in expected do
    if counts.getD mod 0 == 0 then
      throwError "Scientific project module has no audited declarations: {mod}"
  for mod in expected.push `ArtinRibbons do
    let row := Json.mkObj [
      ("module", toJson mod.toString), ("declarations", toJson (counts.getD mod 0)),
      ("imported", toJson true), ("import_only_aggregate", toJson (mod == `ArtinRibbons))]
    logInfo m!"PROJECT_MODULE_JSON {row.compress}"
  logInfo m!"PROJECT_AUDIT_PASSED {total} declarations; 23 scientific modules and aggregate imported"
