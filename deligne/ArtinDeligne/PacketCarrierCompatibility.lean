import ArtinDeligne.CanonicalPacketCarriers
import ArtinDeligne.CanonicalGarsideMap
import ArtinDeligne.GarsideTubeCarriers

/-!
# The actual Garside return respects canonical packet carriers

The interval between packet labels has the correct real signs on every
hyperplane where its admissible upper chambers disagree. Actual sheet gauges
and the proved component criterion therefore put every interval vertex in
the literal packet carrier. Component monotonicity then controls every
small-chain return carrier and the constructed continuous return map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

noncomputable section

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5 Chamber3 Theorem18 Asphericity5 Topology OAI.HarmonicArtin
open Topology.NumerableConnectorCover
attribute [local instance] Classical.decEq Classical.propDecidable

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The already defined actual lattice interval of packet labels. -/
abbrev canonicalPacketVertexInterval (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty) :=
  IncomingVertex.packetInterval (canonicalPacketLabels M J F) (canonicalPacketLabels_nonempty M J F hF)

theorem common_mem_packetUpperIntersection (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (q : ComplementUniversalCover M J)
    (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A) :
    q ∈ canonicalPacketUpperIntersection M J F :=
  liftedCanonicalSet_subset_packetUpperIntersection M J F hF.choose hF.choose_spec
    (hq hF.choose hF.choose_spec)

theorem common_mem_packetUpperTubeIntersection (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (q : ComplementUniversalCover M J)
    (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A) :
    q ∈ liftedTubeIntersection M J (canonicalPacketUpperTubeFamily M J F) := by
  rw [← canonicalPacketUpperIntersection_eq]
  exact common_mem_packetUpperIntersection M J F hF q hq

/-- Every interval vertex precedes every actual admissible upper label,
inside the one actual simple sheet interval through a common lift. -/
theorem packet_interval_upper_simple (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (q : ComplementUniversalCover M J)
    (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A)
    {v u : IncomingVertex M (⟨J⟩ : RibbonObject M)}
    (hv : v ∈ canonicalPacketVertexInterval M J F hF)
    (hu : u ∈ canonicalPacketAdmissibleUpper M J F) :
    sheetLowerVertex M J q ≤ v ∧ v ≤ u ∧
      SimpleRibbon M v.source u.source (v.difference u) ∧
      ChamberBetween (sheetLowerVertex M J q).chamber v.chamber u.chamber := by
  have hlabels : ∀ l ∈ canonicalPacketLabels M J F,
      sheetLowerVertex M J q ≤ l := by
    intro l hl
    obtain ⟨A, hAF, rfl⟩ := Finset.mem_image.mp hl
    exact (canonicalIncomingLabel_phase_bounds M J A q (hq A hAF)).1
  have hlower : sheetLowerVertex M J q ≤ v :=
    (IncomingVertex.le_finiteMeet (canonicalPacketLabels M J F)
      (canonicalPacketLabels_nonempty M J F hF) hlabels).trans hv.1
  have hupper : v ≤ u := hv.2.trans
    (IncomingVertex.finiteJoin_le (canonicalPacketLabels M J F)
      (canonicalPacketLabels_nonempty M J F hF) (by
        intro l hl
        obtain ⟨A, hAF, rfl⟩ := Finset.mem_image.mp hl
        exact (hu A hAF).1))
  have hqu : q ∈ incomingLiftedTubeSheet M J u :=
    (hu hF.choose hF.choose_spec).2.2 (hq hF.choose hF.choose_spec)
  have hub := (sheet_mem_implies_interval M J q u hqu).2
  have hsu := IncomingVertex.simple_difference_of_interval (sheetInterval_simple M J q)
    le_rfl (hlower.trans hupper) hub
  exact ⟨hlower, hupper,
    IncomingVertex.simple_difference_of_interval (sheetInterval_simple M J q) hlower hupper hub,
    incoming_chamberBetween M hlower hupper hsu⟩

/-- The lower chamber records the exact real signs of the common point
on every form where those real evaluations are nonzero. -/
theorem sheetLowerVertex_signs_real (q : ComplementUniversalCover M J)
    {R : RelativeRoot M J}
    (hr : actualForms M J R (liftedTubeProjectionPoint M J q).val.1 ≠ 0) :
    (sheetLowerVertex M J q).chamber.signs R = liftedTubeRealSigns M J q R := by
  rw [sheetLowerVertex_chamber]
  exact tubeLowerChamber_signs_real (E := relativeSubspace J) (actualForms M J)
    (liftedTubeProjectionPoint M J q) hr

/-- Every interval vertex has the common point's real signs at every
actual disagreement among the full admissible upper family. -/
theorem packet_interval_signs (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (q : ComplementUniversalCover M J)
    (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A)
    {v : IncomingVertex M (⟨J⟩ : RibbonObject M)}
    (hv : v ∈ canonicalPacketVertexInterval M J F hF) (R : RelativeRoot M J)
    (hd : tubeDisagreement (liftedTubeChambers M J (canonicalPacketUpperTubeFamily M J F)) R) :
    v.chamber.signs R = liftedTubeRealSigns M J q R := by
  have hqI := common_mem_packetUpperTubeIntersection M J F hF q hq
  have hreal := tubeIntersection_real_ne_zero (projectionPoint_mem_tubeIntersection M J hqI) hd
  have hsign := sheetLowerVertex_signs_real M J q hreal
  obtain ⟨C, hC, D, hD, hCD⟩ := hd
  obtain ⟨A, ⟨u, hu, rfl⟩, hAC⟩ := hC
  obtain ⟨B, ⟨u', hu', rfl⟩, hBD⟩ := hD
  have hCu : u.chamber = C := (incomingLiftedTubeIndex_chamber M J u).symm.trans hAC
  have hDu : u'.chamber = D := (incomingLiftedTubeIndex_chamber M J u').symm.trans hBD
  subst C
  subst D
  have hbet := (packet_interval_upper_simple M J F hF q hq hv hu).2.2.2
  have hbet' := (packet_interval_upper_simple M J F hF q hq hv hu').2.2.2
  have he : v.chamber.signs R = (sheetLowerVertex M J q).chamber.signs R := by
    by_cases hs : (sheetLowerVertex M J q).chamber.signs R = u.chamber.signs R
    · exact hbet R hs
    · have hs' : (sheetLowerVertex M J q).chamber.signs R = u'.chamber.signs R := by
        cases ha : (sheetLowerVertex M J q).chamber.signs R <;>
          cases hb : u.chamber.signs R <;> cases hc : u'.chamber.signs R <;> simp_all
      exact hbet' R hs'
  exact he.trans hsign


/-- The projected actual vertex lies in the exact real sign component
selected by the common overlap point. -/
theorem packet_interval_vertex_basePiece (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (q : ComplementUniversalCover M J)
    (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A)
    {v : IncomingVertex M (⟨J⟩ : RibbonObject M)}
    (hv : v ∈ canonicalPacketVertexInterval M J F hF) :
    complementUniversalCoverProjection M J (incomingVertexPoint M J v) ∈
      liftedTubeBasePiece M J (canonicalPacketUpperTubeFamily M J F) q := by
  change actualComplementHomeomorph M J
      (complementUniversalCoverProjection M J (incomingVertexPoint M J v)) ∈
    tubeIntersectionPiece (liftedTubeChambers M J (canonicalPacketUpperTubeFamily M J F))
      (liftedTubeRealSigns M J q)
  rw [incomingVertexPoint_projection]
  change chamberBasepoint (actualChamberPointFamily M J) v.chamber ∈
    tubeIntersectionPiece (liftedTubeChambers M J (canonicalPacketUpperTubeFamily M J F))
      (liftedTubeRealSigns M J q)
  constructor
  · intro C _hC
    exact chamberBasepoint_mem_tubeSet (actualChamberPointFamily M J) v.chamber C
  · intro R hd
    have hs := packet_interval_signs M J F hF q hq hv R hd
    change (actualChamberPointFamily M J v.chamber).val ∈
      signHalfSpace (actualForms M J R) (liftedTubeRealSigns M J q R)
    rw [← hs]
    exact (actualChamberPointFamily M J v.chamber).property R

/-- Actual packet interval vertices belong to the literal packet carrier,
including its chosen component upstairs, rather than just all projected tubes. -/
theorem incomingVertexPoint_mem_canonicalPacketCarrier
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (q : ComplementUniversalCover M J) (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A)
    {v : IncomingVertex M (⟨J⟩ : RibbonObject M)}
    (hv : v ∈ canonicalPacketVertexInterval M J F hF) :
    incomingVertexPoint M J v ∈ canonicalPacketCarrier M J F := by
  have hover : (canonicalPacketOverlapSet M J F).Nonempty :=
    ⟨q, (mem_canonicalPacketOverlapSet_iff M J F q).mpr hq⟩
  rw [canonicalPacketCarrier_eq_component_of_mem_cell M J F hF hover
    hF.choose hF.choose_spec q (hq hF.choose hF.choose_spec), canonicalPacketUpperIntersection_eq]
  let u := canonicalPacketJoin M J F hF
  have hu : u ∈ canonicalPacketAdmissibleUpper M J F :=
    canonicalPacketJoin_mem_admissible M J F hF q hq
  have hUF : (canonicalPacketUpperTubeFamily M J F).Nonempty :=
    ⟨incomingLiftedTubeIndex M J u, ⟨u, hu, rfl⟩⟩
  have hqI := common_mem_packetUpperTubeIntersection M J F hF q hq
  apply (mem_liftedTubeIntersectionComponent_iff M J hUF hqI
    (incomingLiftedTubeIndex M J u) ⟨u, hu, rfl⟩ _).mpr
  exact ⟨incomingVertexPoint_mem_upperSheet M J
      (packet_interval_upper_simple M J F hF q hq hv hu).2.2.1,
    packet_interval_vertex_basePiece M J F hF q hq hv⟩

/-- Packet admissible upper labels are simple upper labels of every
finite collection of vertices in the packet interval. -/
theorem packetUpper_subset_simpleUpper
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (q : ComplementUniversalCover M J) (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A)
    (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M)))
    (hs : ∀ v ∈ s, v ∈ canonicalPacketVertexInterval M J F hF) :
    canonicalPacketAdmissibleUpper M J F ⊆ simpleUpperSet M J s := by
  intro u hu v hv
  have h := packet_interval_upper_simple M J F hF q hq (hs v hv) hu
  exact ⟨h.2.1, h.2.2.1⟩

/-- The actual simple-upper intersection is contained in the packet upper
intersection; this includes all sheets, rather than just projected tubes. -/
theorem simpleUpperIntersection_subset_packetUpperIntersection
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (q : ComplementUniversalCover M J) (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A)
    (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M)))
    (hs : ∀ v ∈ s, v ∈ canonicalPacketVertexInterval M J F hF) :
    simpleUpperIntersection M J s ⊆ canonicalPacketUpperIntersection M J F := by
  intro z hz
  rw [canonicalPacketUpperIntersection_eq]
  apply (mem_liftedTubeIntersection_iff M J _ _).mpr
  rintro A ⟨u, hu, rfl⟩
  exact (mem_liftedTubeIntersection_iff M J _ _).mp hz _
    ⟨u, packetUpper_subset_simpleUpper M J F hF q hq s hs hu, rfl⟩

/-- The selected component for any small chain in a packet interval lies
in the literal canonical packet carrier. -/
theorem garsideTubeCarrier_subset_canonicalPacketCarrier
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (q : ComplementUniversalCover M J) (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A)
    (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M)))
    (hne : s.Nonempty) (hs : garsideTubeAdmissible M J s)
    (hpacket : ∀ v ∈ s, v ∈ canonicalPacketVertexInterval M J F hF) :
    garsideTubeCarrier M J s ⊆ canonicalPacketCarrier M J F := by
  have hanchor := incomingVertexPoint_mem_canonicalPacketCarrier M J F hF q hq
    (hpacket _ (finiteMeet_mem_of_garsideTubeAdmissible M J hne hs))
  rw [garsideTubeCarrier_eq M J s hne, canonicalPacketCarrier_eq M J F hF]
  rw [canonicalPacketCarrier_eq M J F hF] at hanchor
  rw [connectedComponentIn_eq hanchor]
  exact connectedComponentIn_mono _
    (simpleUpperIntersection_subset_packetUpperIntersection M J F hF q hq s hpacket)

/-- The constructed continuous return takes the entire actual Garside
interval carrier into the corresponding actual component upstairs. -/
theorem actualGarsideReturn_mem_canonicalPacketCarrier
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (hover : (canonicalPacketOverlapSet M J F).Nonempty)
    (w : GarsideWeights M (⟨J⟩ : RibbonObject M))
    (hw : w ∈ canonicalGarsideCarrier M J F) :
    actualGarsideReturn M J w ∈ canonicalPacketCarrier M J F := by
  obtain ⟨q, hq⟩ := hover
  have hq' := (mem_canonicalPacketOverlapSet_iff M J F q).mp hq
  have hne := w.val.support_nonempty
  have hc : IsChain (· ≤ ·) (↑w.val.weights.support :
      Set (IncomingVertex M (⟨J⟩ : RibbonObject M))) :=
    fun a ha b hb _hne => w.val.chain a ha b hb
  rw [canonicalGarsideCarrier_eq M J F hF] at hw
  exact garsideTubeCarrier_subset_canonicalPacketCarrier M J F hF q hq'
    w.val.weights.support hne ⟨hc, w.property⟩ hw
    (actualGarsideReturn_carried M J w w.val.weights.support hc hne w.property
      (Finset.Subset.refl _))

/-- The return composed with the canonical continuous forward map obeys
all nonempty canonical nerve-face carriers, including proper containing faces. -/
theorem canonicalGarsideMap_return_carried (w : ActualCoverWeights M J)
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (hface : IsNerveFace (liftedCanonicalSet M J) F) (hw : w.val.weights.support ⊆ F) :
    actualGarsideReturn M J (canonicalGarsideMap M J w) ∈ canonicalPacketCarrier M J F := by
  obtain ⟨q, hq⟩ := canonicalNerveFace_commonPoint M J F hface
  exact actualGarsideReturn_mem_canonicalPacketCarrier M J F hF
    ⟨q, (mem_canonicalPacketOverlapSet_iff M J F q).mpr hq⟩ _
    (canonicalGarsideMap_carried M J w F hF hface hw)

end ArtinNormalisers.Deligne5
