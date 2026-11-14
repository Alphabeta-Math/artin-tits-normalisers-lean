module

public import ArtinHomotopy.ComplementConnector
public import ArtinHomotopyVendor.Topology.Realization.MetricRealizationDomination

/-!
# The actual small-ball nerve and its complement domination maps

The nerve is the ordered nerve of a named metric-ball refinement of the actual
finite sign-cell cover. The forward map uses a chosen subordinate partition
of unity; the return map is the supplier's ordered connector interpolation.
Their literal composite homotopy has the original complement as its domain.
No identification with a Deligne complex and no asphericity is asserted.
-/

@[expose] public section
noncomputable section

namespace ArtinNormalisers.Homotopy5

open Theorem18 Chamber3 Asphericity5 Topology
open Topology.NumerableConnectorCover SSet CategoryTheory
open scoped Topology Simplicial

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The metric is only a compatible choice for the existing topology. -/
local instance actualComplementMetric : MetricSpace (Complement M J) :=
  complementMetricSpace M J

/-- An order on the vertex set; no order topology is put on the complement. -/
local instance actualComplementVertexOrder : LinearOrder (Complement M J) :=
  IsWellOrder.linearOrder (@WellOrderingRel (Complement M J))

/-- The supplier's positive cover-radius construction applied to the actual cover. -/
def actualNerveRadius : Complement M J → ℝ :=
  MetricCoverRadius.radius (actualConvexCoverSet M J)

theorem actualNerveRadius_pos (x : Complement M J) : 0 < actualNerveRadius M J x :=
  MetricCoverRadius.radius_pos (actualConvexCoverSet M J)
    (isOpen_actualConvexCoverSet M J) (exists_mem_actualConvexCoverSet M J) x

/-- Actual balls centered at the original complement points. -/
def actualNerveCover (x : Complement M J) : Set (Complement M J) :=
  Metric.ball x (actualNerveRadius M J x / 8)

theorem isOpen_actualNerveCover (x : Complement M J) : IsOpen (actualNerveCover M J x) :=
  Metric.isOpen_ball

theorem center_mem_actualNerveCover (x : Complement M J) : x ∈ actualNerveCover M J x := by
  change dist x x < actualNerveRadius M J x / 8
  simpa only [dist_self] using div_pos (actualNerveRadius_pos M J x) (by norm_num : (0 : ℝ) < 8)

theorem exists_mem_actualNerveCover (x : Complement M J) :
    ∃ y, x ∈ actualNerveCover M J y :=
  ⟨x, center_mem_actualNerveCover M J x⟩

theorem actualNerveCover_pointStarRefines :
    PointStarRefines (actualNerveCover M J) (actualConvexCoverSet M J) :=
  pointStarRefines_radius (actualConvexCoverSet M J) (actualNerveRadius M J)
    (actualNerveRadius_pos M J)
    (MetricCoverRadius.lipschitz_radius (actualConvexCoverSet M J)
      (exists_mem_actualConvexCoverSet M J))
    (MetricCoverRadius.half_radius_subordinate (actualConvexCoverSet M J)
      (isOpen_actualConvexCoverSet M J) (exists_mem_actualConvexCoverSet M J))

theorem exists_actualNervePartition :
    ∃ ρ : PartitionOfUnity (Complement M J) (Complement M J),
      ρ.IsSubordinate (actualNerveCover M J) := by
  apply PartitionOfUnity.exists_isSubordinate isClosed_univ (actualNerveCover M J)
    (isOpen_actualNerveCover M J)
  intro x _
  exact Set.mem_iUnion.mpr (exists_mem_actualNerveCover M J x)

/-- A subordinate partition chosen on the explicit ball cover. -/
def actualNervePartition : PartitionOfUnity (Complement M J) (Complement M J) :=
  Classical.choose (exists_actualNervePartition M J)

theorem actualNervePartition_subordinate :
    (actualNervePartition M J).IsSubordinate (actualNerveCover M J) :=
  Classical.choose_spec (exists_actualNervePartition M J)

/-- The actual ordered cover nerve, not an arbitrary simplicial replacement. -/
def actualMetricNerve : SSet := (orderedNerve (actualNerveCover M J)).toSSet

/-- The supplier's actual partition-coefficient classifier into this named nerve. -/
def actualNerveForward : C(Complement M J, |actualMetricNerve M J|) :=
  partitionNerveMap (actualNerveCover M J) (actualNervePartition M J)
    (actualNervePartition_subordinate M J)

/-- The actual ordered interpolation of the original center vertices. -/
def actualNerveReturn : C(|actualMetricNerve M J|, Complement M J) :=
  nerveReturnMap (actualLocalEquiconnection M J) (actualNerveCover M J)
    (actualConvexCoverSet M J) (actualConvexCover_isConnectorConvex M J)
    (actualNerveCover_pointStarRefines M J) id (center_mem_actualNerveCover M J)

/-- The constructed return/classifier composite is homotopic to the original identity. -/
def actualNerveDominationHomotopy :
    ((actualNerveReturn M J).comp (actualNerveForward M J)).Homotopy
      (ContinuousMap.id (Complement M J)) :=
  numerableDominationHomotopy (actualLocalEquiconnection M J) (actualNerveCover M J)
    (actualConvexCoverSet M J) (actualConvexCover_isConnectorConvex M J)
    (actualNerveCover_pointStarRefines M J) (exists_mem_actualNerveCover M J)
    id (center_mem_actualNerveCover M J) (actualNervePartition M J)
    (actualNervePartition_subordinate M J)

end ArtinNormalisers.Homotopy5
