import ArtinDeligne.LiftedPartition
import ArtinDeligne.NumerableWeights

/-!
# The actual universal-cover partition classifier

The chosen order only enumerates the lifted-cover indices. It puts no new
topology on the original complement or universal cover. The weight-space
topology and the classifier are exactly the previously constructed ones.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open Theorem18 Asphericity5
open scoped Topology

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- Fix a single common enumeration order for every subsequent cover construction. -/
noncomputable instance liftedCanonicalIndexLinearOrder :
    LinearOrder (LiftedCanonicalIndex M J) :=
  IsWellOrder.linearOrder (@WellOrderingRel (LiftedCanonicalIndex M J))

/-- The literal common-intersection weight subspace of the actual lifted cover. -/
abbrev ActualCoverWeights := CoverWeights (liftedCanonicalSet M J)

/-- Original lifted-partition coefficients classify the actual universal cover. -/
noncomputable def universalCoverWeightsClassifier :
    C(ComplementUniversalCover M J, ActualCoverWeights M J) :=
  numerableCoverClassifier (liftedCanonicalSet M J) (actualLiftedCanonicalPartition M J)
    (actualLiftedCanonicalPartition_subordinate M J)

@[simp] theorem universalCoverWeightsClassifier_apply
    (q : ComplementUniversalCover M J) (A : LiftedCanonicalIndex M J) :
    (universalCoverWeightsClassifier M J q).val.weights A =
      actualLiftedCanonicalPartition M J A q :=
  partitionWeightsValue_apply (actualLiftedCanonicalPartition M J) q A

end ArtinNormalisers.Deligne5
