import ArtinSequences.StandardComparison
import ArtinNormalisers.Theorem18.ArrangementTopology
import ArtinAsphericityVendor.Topology.Algebra.Module.LocallyContractible
import ArtinAsphericityVendor.AlgebraicTopology.UniversalCover.Covering
import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering

/-!
# The actual relative complement and its actual universal cover

The original complement is an open subset of its real topological vector
space, hence strongly locally contractible, locally path connected and
semilocally simply connected. Its universal cover is TauCeti's genuine
endpoint/path-homotopy-class construction, with the topology coinduced from
the compact-open based-path space, based at the existing landmark-4 point.

The actual endpoint projection is a surjective covering map, and its total
space is path connected and simply connected. No contractibility or
asphericity theorem for this total space is asserted. The higher-homotopy
equivalences and the final asphericity iff identify an actual remaining
obligation; simple connectedness alone does not discharge it.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Asphericity5

open Theorem18 Sequence4
open scoped Topology Topology.Homotopy

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- Local contractibility concerns the actual open complement with its
inherited topology, not a replacement combinatorial model. -/
noncomputable instance complementStronglyLocallyContractibleSpace :
    StronglyLocallyContractibleSpace (Complement M J) := by
  change StronglyLocallyContractibleSpace ↥(complementSet M J)
  exact (isOpen_complementSet M J).stronglyLocallyContractibleSpace

instance complementLocallyPathConnectedSpace : LocallyPathConnectedSpace (Complement M J) :=
  inferInstance

instance complementSemilocallySimplyConnectedSpace :
    TauCeti.SemilocallySimplyConnectedSpace (Complement M J) := inferInstance

/-- The genuine based-path universal cover of the original complement,
at exactly the already constructed standard geometric point. -/
abbrev ComplementUniversalCover := TauCeti.UniversalCover (standardComplementPoint M J)

/-- The actual endpoint projection of the based-path universal cover. -/
def complementUniversalCoverProjection : ComplementUniversalCover M J → Complement M J :=
  TauCeti.UniversalCover.proj

theorem continuous_complementUniversalCoverProjection :
    Continuous (complementUniversalCoverProjection M J) :=
  TauCeti.UniversalCover.continuous_proj (standardComplementPoint M J)

theorem isCoveringMap_complementUniversalCoverProjection :
    IsCoveringMap (complementUniversalCoverProjection M J) :=
  TauCeti.UniversalCover.isCoveringMap (standardComplementPoint M J)

/-- Every point has an actual path from the existing basepoint, hence an
actual endpoint/path-class preimage under the universal-cover projection. -/
theorem complementUniversalCoverProjection_surjective :
    Function.Surjective (complementUniversalCoverProjection M J) := by
  intro x
  exact ⟨⟨x, .mk (PathConnectedSpace.somePath (standardComplementPoint M J) x)⟩, rfl⟩

noncomputable instance complementUniversalCoverPathConnectedSpace :
    PathConnectedSpace (ComplementUniversalCover M J) :=
  TauCeti.UniversalCover.pathConnectedSpace (standardComplementPoint M J)

noncomputable instance complementUniversalCoverSimplyConnectedSpace :
    SimplyConnectedSpace (ComplementUniversalCover M J) :=
  TauCeti.UniversalCover.simplyConnectedSpace (standardComplementPoint M J)

/-- The literal constant-path point in the actual universal cover. -/
noncomputable def complementUniversalCoverBasepoint : ComplementUniversalCover M J :=
  (TauCeti.UniversalCover.basepointLift (standardComplementPoint M J)).val

@[simp]
theorem complementUniversalCoverProjection_basepoint :
    complementUniversalCoverProjection M J (complementUniversalCoverBasepoint M J) =
      standardComplementPoint M J :=
  TauCeti.UniversalCover.proj_basepointLift (standardComplementPoint M J)

/-- Higher homotopy groups are identified by the actual covering map.
Their vanishing is not assumed or concluded here. -/
noncomputable def complementUniversalCover_higherHomotopyEquiv
    (z : ComplementUniversalCover M J) (n : ℕ) :
    π_ (n + 2) (ComplementUniversalCover M J) z ≃*
      π_ (n + 2) (Complement M J) (complementUniversalCoverProjection M J z) :=
  IsCoveringMap.homotopyGroupPiMulEquiv
    (isCoveringMap_complementUniversalCoverProjection M J) z n

/-- Actual asphericity of the complement is equivalent to asphericity of
its actual universal cover. This is a reduction, not an asphericity proof. -/
theorem complementUniversalCover_aspherical_iff (z : ComplementUniversalCover M J) :
    TauCeti.IsAspherical (ComplementUniversalCover M J) z ↔
      TauCeti.IsAspherical (Complement M J) (complementUniversalCoverProjection M J z) := by
  constructor
  · exact (isCoveringMap_complementUniversalCoverProjection M J).isAspherical
      (complementUniversalCoverProjection_surjective M J) rfl
  · exact (isCoveringMap_complementUniversalCoverProjection M J).isAspherical_totalSpace rfl

end ArtinNormalisers.Asphericity5
