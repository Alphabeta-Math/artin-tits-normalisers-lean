import ArtinDeligne.CanonicalCoverWeights
import ArtinDeligne.SheetIntervals
import ArtinDeligne.IncomingMeets
import ArtinDeligne.GarsideTopology
import ArtinDeligne.CarrierDescent

/-!
# The actual canonical-cover to Garside map

A nonempty common-intersection face has actual incoming labels inside one
simple phase interval. Their genuine lattice meet and join therefore bound
a contractible interval carrier in the original Garside weight space.
These carriers are monotone, so the proved coherent finite-simplex
construction descends to a continuous map on the actual cover weights.
No contraction or comparison map is supplied as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5 Theorem18 Asphericity5 OAI.HarmonicArtin
open Topology.NumerableConnectorCover
attribute [local instance] Classical.decEq Classical.propDecidable

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- Actual common-intersection faces retain their common lift. -/
theorem canonicalNerveFace_commonPoint (F : Finset (LiftedCanonicalIndex M J))
    (hF : IsNerveFace (liftedCanonicalSet M J) F) :
    ∃ q : ComplementUniversalCover M J, ∀ A ∈ F, q ∈ liftedCanonicalSet M J A := by
  obtain ⟨q, hq⟩ := hF
  exact ⟨q, fun A hA => hq A hA⟩

/-- The actual meet/join factor of the labels of any nonempty nerve face
is simple, as a consequence of geometric sheet incidence. -/
theorem canonicalPacketMeetJoin_simple (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (hface : IsNerveFace (liftedCanonicalSet M J) F) :
    SimpleRibbon M
      (IncomingVertex.finiteMeet (canonicalPacketLabels M J F)
        (canonicalPacketLabels_nonempty M J F hF)).source
      (IncomingVertex.finiteJoin (canonicalPacketLabels M J F)
        (canonicalPacketLabels_nonempty M J F hF)).source
      ((IncomingVertex.finiteMeet (canonicalPacketLabels M J F)
        (canonicalPacketLabels_nonempty M J F hF)).difference
        (IncomingVertex.finiteJoin (canonicalPacketLabels M J F)
          (canonicalPacketLabels_nonempty M J F hF))) := by
  obtain ⟨q, hq⟩ := canonicalNerveFace_commonPoint M J F hface
  have hb : ∀ u ∈ canonicalPacketLabels M J F,
      sheetLowerVertex M J q ≤ u ∧ u ≤ sheetPhaseUpperVertex M J q := by
    intro u hu
    obtain ⟨A, hAF, rfl⟩ := Finset.mem_image.mp hu
    exact canonicalIncomingLabel_phase_bounds M J A q (hq A hAF)
  exact (IncomingVertex.finiteMeetJoin_simple_interval
    (canonicalPacketLabels M J F) (canonicalPacketLabels_nonempty M J F hF)
    (sheetLowerVertex M J q) (sheetPhaseUpperVertex M J q)
    (fun u hu => (hb u hu).1) (fun u hu => (hb u hu).2)
    (sheetPhaseInterval_simple M J q)).2.2.2

/-- The literal Garside subspace carried by the meet/join interval. The
empty face has no simplex and is assigned the empty set. -/
def canonicalGarsideCarrier (F : Finset (LiftedCanonicalIndex M J)) :
    Set (GarsideWeights M (⟨J⟩ : RibbonObject M)) :=
  if hF : F.Nonempty then
    garsideIntervalCarrier M ⟨J⟩
      (IncomingVertex.finiteMeet (canonicalPacketLabels M J F)
        (canonicalPacketLabels_nonempty M J F hF))
      (IncomingVertex.finiteJoin (canonicalPacketLabels M J F)
        (canonicalPacketLabels_nonempty M J F hF))
  else ∅

theorem canonicalGarsideCarrier_eq (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty) :
    canonicalGarsideCarrier M J F = garsideIntervalCarrier M ⟨J⟩
      (IncomingVertex.finiteMeet (canonicalPacketLabels M J F)
        (canonicalPacketLabels_nonempty M J F hF))
      (IncomingVertex.finiteJoin (canonicalPacketLabels M J F)
        (canonicalPacketLabels_nonempty M J F hF)) := dite_eq_left hF

theorem contractibleSpace_canonicalGarsideCarrier (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (hface : IsNerveFace (liftedCanonicalSet M J) F) :
    ContractibleSpace (canonicalGarsideCarrier M J F) := by
  rw [canonicalGarsideCarrier_eq M J F hF]
  exact contractibleSpace_garsideIntervalCarrier M ⟨J⟩ (canonicalPacketMeetJoin_simple M J F hF hface)

theorem canonicalGarsideCarrier_mono {F G : Finset (LiftedCanonicalIndex M J)}
    (hFG : F ⊆ G) (hF : F.Nonempty) :
    canonicalGarsideCarrier M J F ⊆ canonicalGarsideCarrier M J G := by
  have hG : G.Nonempty := hF.mono hFG
  rw [canonicalGarsideCarrier_eq M J F hF, canonicalGarsideCarrier_eq M J G hG]
  exact garsideIntervalCarrier_mono M ⟨J⟩
    (IncomingVertex.finiteMeet_antitone (Finset.image_subset_image hFG) _ _)
    (IncomingVertex.finiteJoin_mono (Finset.image_subset_image hFG) _ _)

/-- Every field is proved from the actual cover and actual ribbon lattice.
The generic family construction will construct the maps and all coherence. -/
def canonicalGarsideCarrierData :
    FiniteCarrierData (LiftedCanonicalIndex M J) (GarsideWeights M (⟨J⟩ : RibbonObject M)) where
  admissible := IsNerveFace (liftedCanonicalSet M J)
  hereditary hAB hB := hB.mono hAB
  carrier := canonicalGarsideCarrier M J
  contractible := contractibleSpace_canonicalGarsideCarrier M J
  monotone hAB hA _ := canonicalGarsideCarrier_mono M J hAB hA

/-- The genuine all-dimensional coherent family, constructed through
contractible interval carriers rather than chosen independently on faces. -/
def canonicalGarsideFamily : CarrierFamily (canonicalGarsideCarrierData M J) :=
  (canonicalGarsideCarrierData M J).family

/-- The continuous forward map on the literal actual-cover weight space.
It uses the single cover-index order fixed in `CanonicalCoverWeights`. -/
def canonicalGarsideMap :
    C(ActualCoverWeights M J, GarsideWeights M (⟨J⟩ : RibbonObject M)) :=
  (canonicalGarsideFamily M J).descend (IsNerveFace (liftedCanonicalSet M J))
    (fun {_ _} hAB hB => hB.mono hAB) (fun _ _ h => h)

/-- Any original nerve face containing the support carries the map value.
No chain premise is needed on this containing face. -/
theorem canonicalGarsideMap_carried (w : ActualCoverWeights M J)
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (hface : IsNerveFace (liftedCanonicalSet M J) F) (hw : w.val.weights.support ⊆ F) :
    canonicalGarsideMap M J w ∈ canonicalGarsideCarrier M J F :=
  (canonicalGarsideFamily M J).descend_carried_of_admissible
    (IsNerveFace (liftedCanonicalSet M J)) (fun {_ _} hAB hB => hB.mono hAB)
    (fun _ _ h => h) w F hF hface hw


/-- The carried conclusion in literal support coordinates of the existing
Garside space, with the actual meet and join as its endpoints. -/
theorem canonicalGarsideMap_support (w : ActualCoverWeights M J)
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (hface : IsNerveFace (liftedCanonicalSet M J) F) (hw : w.val.weights.support ⊆ F) :
    ∀ u ∈ (canonicalGarsideMap M J w).val.weights.support,
      IncomingVertex.finiteMeet (canonicalPacketLabels M J F)
          (canonicalPacketLabels_nonempty M J F hF) ≤ u ∧
        u ≤ IncomingVertex.finiteJoin (canonicalPacketLabels M J F)
          (canonicalPacketLabels_nonempty M J F hF) := by
  have h := canonicalGarsideMap_carried M J w F hF hface hw
  rw [canonicalGarsideCarrier_eq M J F hF] at h
  exact h

end ArtinNormalisers.Deligne5

