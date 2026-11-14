import ArtinDeligne.PacketCarrierCompatibility
import ArtinDeligne.NumerableCarrierHomotopy
import ArtinDeligne.GlobalNullity
import ArtinHomotopy.Domination

/-!
# Comparison with the original universal cover

The actual lifted partition classifies the original universal cover. Its
canonical Garside map and the actual tube-carrier return have a composite
homotopic to the identity, by the proved numerable carrier theorem. Thus the
already proved higher-homotopy vanishing of the Garside model transfers to
the original cover. No comparison or asphericity premise is supplied.
-/

set_option autoImplicit false

noncomputable section

namespace ArtinNormalisers.Deligne5

open Ribbon2 Theorem18 Asphericity5
open Topology.NumerableConnectorCover

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The continuous forward map on the original universal cover. -/
def actualGarsideForward :
    C(ComplementUniversalCover M J, GarsideWeights M (⟨J⟩ : RibbonObject M)) :=
  (canonicalGarsideMap M J).comp (universalCoverWeightsClassifier M J)

/-- The actual return and forward composite is homotopic to the identity.
The finite carrier homotopies are constructed, rather than assumed. -/
def actualUniversalCoverComparisonHomotopy :
    ((actualGarsideReturn M J).comp (actualGarsideForward M J)).Homotopy
      (ContinuousMap.id (ComplementUniversalCover M J)) := by
  exact numerableCarrierHomotopy (liftedCanonicalSet M J)
    (isOpen_liftedCanonicalSet M J) (actualLiftedCanonicalPartition M J)
    (actualLiftedCanonicalPartition_subordinate M J)
    (canonicalPacketCarrier M J)
    (fun F hF hface => contractibleSpace_canonicalPacketCarrier M J F hF
      (by obtain ⟨q, hq⟩ := hface
          exact ⟨q, (mem_canonicalPacketOverlapSet_iff M J F q).mpr hq⟩))
    (fun {_ _} hFG hF hface =>
      canonicalPacketCarrier_mono M J hFG hF (hF.mono hFG)
        (by obtain ⟨q, hq⟩ := hface
            exact ⟨q, (mem_canonicalPacketOverlapSet_iff M J _ q).mpr hq⟩))
    (fun F hF _ q hq => mem_canonicalPacketCarrier_of_common M J F hF q hq)
    ((actualGarsideReturn M J).comp (canonicalGarsideMap M J))
    (fun F hF hface w hw => canonicalGarsideMap_return_carried M J w F hF hface hw)

/-- Asphericity of the original path-class universal cover, at every point,
for the arbitrary finite Coxeter group and arbitrary parabolic subset. -/
theorem actualUniversalCover_isAspherical (q : ComplementUniversalCover M J) :
    TauCeti.IsAspherical (ComplementUniversalCover M J) q :=
  Homotopy5.isAspherical_of_dominated_by_aspherical
    (actualGarsideForward M J) (actualGarsideReturn M J)
    (actualUniversalCoverComparisonHomotopy M J) q
    (garside_isAspherical M (⟨J⟩ : RibbonObject M) (actualGarsideForward M J q))

end ArtinNormalisers.Deligne5
