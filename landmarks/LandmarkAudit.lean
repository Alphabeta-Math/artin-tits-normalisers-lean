module

meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms
import ArtinLandmarks
import ArtinLandmarkVendor.Geometric.RankTwo
import ArtinLandmarkVendor.Geometric.Sign
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

#check ArtinNormalisers.Landmark1.dominant_fixed_iff
#check ArtinNormalisers.Landmark1.pointwise_flat_fixed_iff
#check ArtinNormalisers.Landmark1.exists_dominant_dualAction
#check ArtinNormalisers.Landmark1.realRelativeRegular_fixed_iff
#check ArtinNormalisers.Landmark1.complement_pair_stabilizer_iff
#check ArtinNormalisers.Landmark1.quotientComplement_smul_fixed_iff
#check ArtinNormalisers.Landmark1.isQuotientCoveringMap_orbitProjection
#check ArtinNormalisers.Landmark1.orbitFundamentalGroup_shortExact
#print axioms ArtinNormalisers.Landmark1.orbitFundamentalGroup_shortExact

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut projectCount : Nat := 0
  let mut providerCount : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx]!
      let project := mod.toString.startsWith "ArtinLandmarks."
      let provider := mod.toString.startsWith "TauCeti." ||
        mod.toString.startsWith "ArtinLandmarkVendor."
      if project || provider then
        if project then projectCount := projectCount + 1
        if provider then providerCount := providerCount + 1
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Forbidden axiom {ax} in {name} ({mod})"
        if project then logInfo m!"LANDMARK_TYPE {mod} {name}: {ci.type}"
        logInfo m!"LANDMARK_AXIOMS {mod} {name}: {axioms}"
  if projectCount == 0 || providerCount == 0 then
    throwError "Empty landmark or supplier audit"
  logInfo m!"Audited {projectCount} landmark declarations and {providerCount} supplier declarations"
  logInfo "LANDMARK 1 ONLY: full Theorem 1.8 remains unproved"
