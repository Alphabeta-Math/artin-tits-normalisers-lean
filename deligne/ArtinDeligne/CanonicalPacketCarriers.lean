import ArtinDeligne.SheetIntervals
import ArtinDeligne.LiftedTubeComponents

/-!
# Literal connected-component carriers for canonical packets

Admissible upper labels carry every whole lifted canonical cell in the packet.
Their actual tube sheets are intersected, and the component containing the
actual center of any one packet cell is the carrier. Overlap, simple incoming
joins, and the proved component charts establish contractibility; it is not
part of the definition. All choices of a packet cell give the same component.
No linear order on the cover index is selected here.
-/

set_option autoImplicit false

noncomputable section

namespace ArtinNormalisers.Deligne5

open Theorem18 Chamber3 Asphericity5 Ribbon2 Homotopy5 Topology

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The literal common intersection of a finite packet of lifted canonical cells. -/
def canonicalPacketOverlapSet (F : Finset (LiftedCanonicalIndex M J)) :
    Set (ComplementUniversalCover M J) := ⋂ A ∈ F, liftedCanonicalSet M J A

theorem mem_canonicalPacketOverlapSet_iff (F : Finset (LiftedCanonicalIndex M J))
    (q : ComplementUniversalCover M J) :
    q ∈ canonicalPacketOverlapSet M J F ↔ ∀ A ∈ F, q ∈ liftedCanonicalSet M J A := by
  simp only [canonicalPacketOverlapSet, Set.mem_iInter]

/-- All actual simple upper labels that carry every whole packet cell. -/
def canonicalPacketAdmissibleUpper (F : Finset (LiftedCanonicalIndex M J)) :
    Set (IncomingVertex M (⟨J⟩ : RibbonObject M)) :=
  {u | ∀ A ∈ F, canonicalIncomingLabel M J A ≤ u ∧
    SimpleRibbon M (canonicalIncomingLabel M J A).source u.source
      ((canonicalIncomingLabel M J A).difference u) ∧
    liftedCanonicalSet M J A ⊆ incomingLiftedTubeSheet M J u}

/-- The genuine finite join is admissible whenever the actual packet overlaps. -/
theorem canonicalPacketJoin_mem_admissible (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (q : ComplementUniversalCover M J)
    (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A) :
    canonicalPacketJoin M J F hF ∈ canonicalPacketAdmissibleUpper M J F := by
  classical
  have hj := canonicalPacketJoin_carrier M J F hF q hq
  intro A hAF
  have hle : canonicalIncomingLabel M J A ≤ canonicalPacketJoin M J F hF :=
    IncomingVertex.le_finiteJoin _ _ (Finset.mem_image.mpr ⟨A, hAF, rfl⟩)
  exact ⟨hle, IncomingVertex.simple_difference_of_interval (sheetPhaseInterval_simple M J q)
    (canonicalIncomingLabel_phase_bounds M J A q (hq A hAF)).1 hle hj.2.1,
    hj.2.2.2.2 A hAF⟩

theorem canonicalPacketAdmissibleUpper_nonempty (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (hover : (canonicalPacketOverlapSet M J F).Nonempty) :
    (canonicalPacketAdmissibleUpper M J F).Nonempty := by
  obtain ⟨q, hq⟩ := hover
  exact ⟨canonicalPacketJoin M J F hF, canonicalPacketJoin_mem_admissible M J F hF q
    ((mem_canonicalPacketOverlapSet_iff M J F q).mp hq)⟩

/-- More packet cells impose more conditions on the actual admissible upper labels. -/
theorem canonicalPacketAdmissibleUpper_antitone {F G : Finset (LiftedCanonicalIndex M J)}
    (hFG : F ⊆ G) :
    canonicalPacketAdmissibleUpper M J G ⊆ canonicalPacketAdmissibleUpper M J F :=
  fun _ hu A hA => hu A (hFG hA)

/-- The literal intersection of all admissible actual tube sheets. -/
def canonicalPacketUpperIntersection (F : Finset (LiftedCanonicalIndex M J)) :
    Set (ComplementUniversalCover M J) :=
  ⋂ u ∈ canonicalPacketAdmissibleUpper M J F, incomingLiftedTubeSheet M J u

/-- The actual sheet indices of all admissible upper labels; this family may be infinite. -/
def canonicalPacketUpperTubeFamily (F : Finset (LiftedCanonicalIndex M J)) :
    Set (LiftedTubeIndex M J) :=
  incomingLiftedTubeIndex M J '' canonicalPacketAdmissibleUpper M J F

theorem canonicalPacketUpperIntersection_eq (F : Finset (LiftedCanonicalIndex M J)) :
    canonicalPacketUpperIntersection M J F =
      liftedTubeIntersection M J (canonicalPacketUpperTubeFamily M J F) := by
  ext q
  simp only [canonicalPacketUpperIntersection, liftedTubeIntersection, Set.mem_iInter]
  constructor
  · rintro h A ⟨u, hu, rfl⟩
    exact h u hu
  · intro h u hu
    exact h _ ⟨u, hu, rfl⟩

/-- Every whole packet cell is contained in the intersection defining its carrier. -/
theorem liftedCanonicalSet_subset_packetUpperIntersection
    (F : Finset (LiftedCanonicalIndex M J)) (A : LiftedCanonicalIndex M J) (hA : A ∈ F) :
    liftedCanonicalSet M J A ⊆ canonicalPacketUpperIntersection M J F := by
  intro q hq
  apply Set.mem_iInter.mpr
  intro u
  apply Set.mem_iInter.mpr
  intro hu
  exact (hu A hA).2.2 hq

theorem canonicalPacketUpperIntersection_mono {F G : Finset (LiftedCanonicalIndex M J)}
    (hFG : F ⊆ G) :
    canonicalPacketUpperIntersection M J F ⊆ canonicalPacketUpperIntersection M J G := by
  intro q hq
  simp only [canonicalPacketUpperIntersection, Set.mem_iInter] at hq ⊢
  intro u hu
  exact hq u (canonicalPacketAdmissibleUpper_antitone M J hFG hu)

/-- Exactly the actual lifted center of a selected packet cell. No new geometric point is chosen. -/
def canonicalPacketCenter (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty) :
    ComplementUniversalCover M J := liftedCanonicalCenter M J hF.choose

theorem canonicalPacketCenter_mem (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty) :
    canonicalPacketCenter M J F hF ∈ canonicalPacketUpperIntersection M J F :=
  liftedCanonicalSet_subset_packetUpperIntersection M J F hF.choose hF.choose_spec
    (liftedCanonicalCenter_mem M J hF.choose)

/-- The literal actual connected component. Empty packets are assigned the empty set;
no contractibility assertion is made for that default. -/
def canonicalPacketCarrier (F : Finset (LiftedCanonicalIndex M J)) :
    Set (ComplementUniversalCover M J) :=
  if hF : F.Nonempty then
    connectedComponentIn (canonicalPacketUpperIntersection M J F) (canonicalPacketCenter M J F hF)
  else ∅

theorem canonicalPacketCarrier_eq (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty) :
    canonicalPacketCarrier M J F =
      connectedComponentIn (canonicalPacketUpperIntersection M J F) (canonicalPacketCenter M J F hF) := by
  simp only [canonicalPacketCarrier, dite_eq_left hF]

theorem canonicalPacketCenter_mem_carrier (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) : canonicalPacketCenter M J F hF ∈ canonicalPacketCarrier M J F := by
  rw [canonicalPacketCarrier_eq M J F hF]
  exact mem_connectedComponentIn (canonicalPacketCenter_mem M J F hF)

theorem canonicalPacketCarrier_subset_upperIntersection
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty) :
    canonicalPacketCarrier M J F ⊆ canonicalPacketUpperIntersection M J F := by
  rw [canonicalPacketCarrier_eq M J F hF]
  exact connectedComponentIn_subset _ _

/-- Every admissible upper sheet contains the entire actual carrier. -/
theorem canonicalPacketCarrier_subset_incomingSheet
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (u : IncomingVertex M (⟨J⟩ : RibbonObject M))
    (hu : u ∈ canonicalPacketAdmissibleUpper M J F) :
    canonicalPacketCarrier M J F ⊆ incomingLiftedTubeSheet M J u := by
  intro q hq
  exact Set.mem_iInter.mp (Set.mem_iInter.mp
    (canonicalPacketCarrier_subset_upperIntersection M J F hF hq) u) hu

/-- Contractibility is proved using the actual chart for a component of a nonempty
family of genuine tube sheets. Neither total-space contractibility nor a nerve theorem is used. -/
theorem contractibleSpace_canonicalPacketCarrier (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (hover : (canonicalPacketOverlapSet M J F).Nonempty) :
    ContractibleSpace (canonicalPacketCarrier M J F) := by
  rw [canonicalPacketCarrier_eq M J F hF, canonicalPacketUpperIntersection_eq M J F]
  apply contractibleSpace_liftedTubeIntersectionComponent M J
    (canonicalPacketUpperTubeFamily M J F)
    ((canonicalPacketAdmissibleUpper_nonempty M J F hF hover).image _) _
  rw [← canonicalPacketUpperIntersection_eq M J F]
  exact canonicalPacketCenter_mem M J F hF

/-- All packet cells lie in the component at any actual common overlap point. -/
theorem liftedCanonicalSet_subset_packetComponent (F : Finset (LiftedCanonicalIndex M J))
    (q : ComplementUniversalCover M J) (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A)
    (A : LiftedCanonicalIndex M J) (hA : A ∈ F) :
    liftedCanonicalSet M J A ⊆ connectedComponentIn (canonicalPacketUpperIntersection M J F) q := by
  have hconn : IsConnected (liftedCanonicalSet M J A) :=
    isConnected_iff_connectedSpace.mpr inferInstance
  exact hconn.isPreconnected.subset_connectedComponentIn (hq A hA)
    (liftedCanonicalSet_subset_packetUpperIntersection M J F A hA)

/-- Every whole packet cell, and thus their union, belongs to the chosen carrier. -/
theorem liftedCanonicalSet_subset_packetCarrier (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (hover : (canonicalPacketOverlapSet M J F).Nonempty)
    (A : LiftedCanonicalIndex M J) (hA : A ∈ F) :
    liftedCanonicalSet M J A ⊆ canonicalPacketCarrier M J F := by
  obtain ⟨q, hq⟩ := hover
  have hq' := (mem_canonicalPacketOverlapSet_iff M J F q).mp hq
  have hc := liftedCanonicalSet_subset_packetComponent M J F q hq' hF.choose hF.choose_spec
    (liftedCanonicalCenter_mem M J hF.choose)
  have he := connectedComponentIn_eq hc
  rw [canonicalPacketCarrier_eq M J F hF, canonicalPacketCenter, ← he]
  exact liftedCanonicalSet_subset_packetComponent M J F q hq' A hA

theorem canonicalPacketUnion_subset_carrier (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (hover : (canonicalPacketOverlapSet M J F).Nonempty) :
    (⋃ A ∈ F, liftedCanonicalSet M J A) ⊆ canonicalPacketCarrier M J F := by
  intro q hq
  obtain ⟨A, hqA⟩ := Set.mem_iUnion.mp hq
  obtain ⟨hA, hqA⟩ := Set.mem_iUnion.mp hqA
  exact liftedCanonicalSet_subset_packetCarrier M J F hF hover A hA hqA

theorem canonicalPacketOverlapSet_subset_carrier (F : Finset (LiftedCanonicalIndex M J))
    (hF : F.Nonempty) (hover : (canonicalPacketOverlapSet M J F).Nonempty) :
    canonicalPacketOverlapSet M J F ⊆ canonicalPacketCarrier M J F := by
  intro q hq
  exact liftedCanonicalSet_subset_packetCarrier M J F hF hover hF.choose hF.choose_spec
    ((mem_canonicalPacketOverlapSet_iff M J F q).mp hq hF.choose hF.choose_spec)

/-- Point containment directly from the actual common-point witnesses. -/
theorem mem_canonicalPacketCarrier_of_common
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (q : ComplementUniversalCover M J) (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A) :
    q ∈ canonicalPacketCarrier M J F := by
  have hmem := (mem_canonicalPacketOverlapSet_iff M J F q).mpr hq
  exact canonicalPacketOverlapSet_subset_carrier M J F hF ⟨q, hmem⟩ hmem

/-- Any actual point of any packet cell selects exactly the same component. -/
theorem canonicalPacketCarrier_eq_component_of_mem_cell
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (hover : (canonicalPacketOverlapSet M J F).Nonempty)
    (A : LiftedCanonicalIndex M J) (hA : A ∈ F)
    (q : ComplementUniversalCover M J) (hq : q ∈ liftedCanonicalSet M J A) :
    canonicalPacketCarrier M J F = connectedComponentIn (canonicalPacketUpperIntersection M J F) q := by
  have hqC := liftedCanonicalSet_subset_packetCarrier M J F hF hover A hA hq
  rw [canonicalPacketCarrier_eq M J F hF] at hqC ⊢
  exact connectedComponentIn_eq hqC

/-- Independence of the selected packet cell in the literal component definition. -/
theorem canonicalPacketCarrier_eq_component_at_center
    (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (hover : (canonicalPacketOverlapSet M J F).Nonempty)
    (A : LiftedCanonicalIndex M J) (hA : A ∈ F) :
    canonicalPacketCarrier M J F = connectedComponentIn (canonicalPacketUpperIntersection M J F)
      (liftedCanonicalCenter M J A) :=
  canonicalPacketCarrier_eq_component_of_mem_cell M J F hF hover A hA _
    (liftedCanonicalCenter_mem M J A)

/-- Faces of an actual overlapping packet have nested actual carriers. -/
theorem canonicalPacketCarrier_mono {F G : Finset (LiftedCanonicalIndex M J)}
    (hFG : F ⊆ G) (hF : F.Nonempty) (hG : G.Nonempty)
    (hover : (canonicalPacketOverlapSet M J G).Nonempty) :
    canonicalPacketCarrier M J F ⊆ canonicalPacketCarrier M J G := by
  rw [canonicalPacketCarrier_eq M J F hF,
    canonicalPacketCarrier_eq_component_at_center M J G hG hover hF.choose (hFG hF.choose_spec)]
  exact connectedComponentIn_mono _ (canonicalPacketUpperIntersection_mono M J hFG)

/-- Face compatibility in the form supplied by an actual overlap point. -/
theorem canonicalPacketCarrier_mono_of_common {F G : Finset (LiftedCanonicalIndex M J)}
    (hFG : F ⊆ G) (hF : F.Nonempty) (hG : G.Nonempty)
    (q : ComplementUniversalCover M J) (hq : ∀ A ∈ G, q ∈ liftedCanonicalSet M J A) :
    canonicalPacketCarrier M J F ⊆ canonicalPacketCarrier M J G :=
  canonicalPacketCarrier_mono M J hFG hF hG
    ⟨q, (mem_canonicalPacketOverlapSet_iff M J G q).mpr hq⟩

end ArtinNormalisers.Deligne5
