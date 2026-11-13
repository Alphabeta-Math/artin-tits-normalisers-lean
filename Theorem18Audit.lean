module

meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms
import ArtinTheorem18
import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Product
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.CategoryTheory.Groupoid.SingleObj
import TauCeti.GroupTheory.Coxeter.Artin
import TauCeti.GroupTheory.Coxeter.Basic
import TauCeti.GroupTheory.Coxeter.BraidEquivalence
import TauCeti.GroupTheory.Coxeter.Dihedral
import TauCeti.GroupTheory.Coxeter.Geometric.Basic
import TauCeti.GroupTheory.Coxeter.Matsumoto
import TauCeti.GroupTheory.Coxeter.Parabolic
import TauCeti.GroupTheory.Coxeter.StrongExchange
import TauCeti.Topology.Homotopy.Covering
import TauCeti.Topology.Homotopy.Cube.Basic
import TauCeti.Topology.Homotopy.Cube.OpenBox
import TauCeti.Topology.Homotopy.Cube.Radius
import TauCeti.Topology.Homotopy.Extension.Ball
import TauCeti.Topology.Homotopy.Extension.Basic
import TauCeti.Topology.Homotopy.GenLoop.Covering
import TauCeti.Topology.Homotopy.GenLoop.Map
import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
import TauCeti.Topology.Homotopy.HomotopyGroup.Collar
import TauCeti.Topology.Homotopy.HomotopyGroup.Covering
import TauCeti.Topology.Homotopy.HomotopyGroup.Map
import TauCeti.Topology.Homotopy.HomotopyGroup.Product
import TauCeti.Topology.Homotopy.Path
import TauCeti.Topology.PiCurry
import TauCeti.Topology.UnitInterval

set_option autoImplicit false

-- This audit certifies prerequisites only. There is no `theorem_1_8` here.
#check ArtinNormalisers.Theorem18.quotientCovering_fundamentalGroup_shortExact
#check ArtinNormalisers.Theorem18.Complement
#check ArtinNormalisers.Theorem18.OrbitSpace
#check ArtinNormalisers.Theorem18.isOpen_complementSet
#check ArtinNormalisers.Theorem18.mem_relativeSubspace_iff_fixed
#check ArtinNormalisers.Theorem18.quotientComplementAction
#check ArtinNormalisers.Theorem18.isPathConnected_complementSet
#check TauCeti.isAspherical_iff
#check TauCeti.isEilenbergMacLaneSpaceOne_iff
#check IsCoveringMap.isAspherical
#check IsCoveringMap.homotopyGroupPiMulEquiv
#check TauCeti.FundamentalGroup.map_range_eq_bot_of_subsingleton
#check TauCeti.FundamentalGroup.map_range_le_of_subsingleton
#check TauCeti.FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut projectCount : Nat := 0
  let mut providerCount : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx]!
      let project := mod.toString.startsWith "ArtinNormalisers.Theorem18."
      let provider := mod.toString.startsWith "TauCeti."
      if project || provider then
        if project then projectCount := projectCount + 1
        if provider then providerCount := providerCount + 1
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Forbidden axiom {ax} in {name} ({mod})"
        if project then
          logInfo m!"FOUNDATION_TYPE {mod} {name}: {ci.type}"
        logInfo m!"FOUNDATION_AXIOMS {mod} {name}: {axioms}"
  if projectCount == 0 || providerCount == 0 then
    throwError "Empty project or supplier audit"
  logInfo m!"Audited {projectCount} new foundation declarations and {providerCount} supplier declarations"
  logInfo "PREREQUISITES ONLY: Theorem 1.8 is not proved by this audit"
