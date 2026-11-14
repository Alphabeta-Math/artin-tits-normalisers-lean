import ArtinDeligne.CarrierDescent
import ArtinDeligne.GarsideTopology
import ArtinDeligne.IncomingMeets
import ArtinDeligne.SheetIntervals
import ArtinDeligne.LiftedTubeComponents

/-!
# Actual tube carriers and the Garside return map

Finite simple chains determine intersections of their actual simple-upper
sheets. The component containing their least actual lifted vertex is
contractible, contains every lifted vertex, and grows under face inclusion.
The proved coherent-carrier descent constructs an actual continuous return
map into the original universal cover, without assuming a comparison map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

noncomputable section

namespace ArtinNormalisers.Deligne5

open CategoryTheory Ribbon2 Homotopy5 Chamber3 Theorem18 Asphericity5 Topology
attribute [local instance] Classical.decEq Classical.propDecidable

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The original fiber point of the actual tube labelled by an incoming vertex. -/
def incomingVertexPoint (v : IncomingVertex M (⟨J⟩ : RibbonObject M)) :
    ComplementUniversalCover M J := (incomingLiftedTubeIndex M J v).fiberPoint.val

@[simp] theorem incomingVertexPoint_projection (v : IncomingVertex M (⟨J⟩ : RibbonObject M)) :
    complementUniversalCoverProjection M J (incomingVertexPoint M J v) =
      tubeBasepoint M J v.chamber := by
  exact (incomingLiftedTubeIndex M J v).fiberPoint.property.trans
    (congrArg (tubeBasepoint M J) (incomingLiftedTubeIndex_chamber M J v))

theorem incomingVertexPoint_mem_ownSheet (v : IncomingVertex M (⟨J⟩ : RibbonObject M)) :
    incomingVertexPoint M J v ∈ incomingLiftedTubeSheet M J v :=
  fiberPoint_mem_liftedTubeSheet M J _

private theorem faceChamber_tubeBasepoint (C : ActualChamber M J) :
    faceChamber (actualForms M J) (tubeBasepoint M J C).val.1 C = C := by
  change faceChamber (actualForms M J) (actualChamberPointFamily M J C).val C = C
  exact (faceChamber_eq_chamberOfRegular (E := relativeSubspace J) (actualForms M J) _ C
    (C.region_subset_regularSet (actualChamberPointFamily M J C).property)).trans
    (Chamber.eq_chamberOfRegular (actualChamberPointFamily M J C).property).symm

/-- A simple actual factor places the actual source fiber point in the
actual target sheet. This is a genuine path-gauge conclusion. -/
theorem incomingVertexPoint_mem_upperSheet
    {v u : IncomingVertex M (⟨J⟩ : RibbonObject M)}
    (hs : SimpleRibbon M v.source u.source (v.difference u)) :
    incomingVertexPoint M J v ∈ incomingLiftedTubeSheet M J u := by
  let A := incomingLiftedTubeIndex M J v
  let B := incomingLiftedTubeIndex M J u
  have hs' : SimpleRibbon M (liftedTubeIndexEquivIncoming M J A).source
      (liftedTubeIndexEquivIncoming M J B).source
      ((liftedTubeIndexEquivIncoming M J A).difference (liftedTubeIndexEquivIncoming M J B)) := by
    simpa only [A, B, incomingLiftedTubeIndex, Equiv.apply_symm_apply] using hs
  have hpB : complementUniversalCoverProjection M J (incomingVertexPoint M J v) ∈
      actualTubeSet M J B.chamber := by
    rw [incomingVertexPoint_projection]
    exact actualChamberBasepoint_mem_tube M J (actualChamberPointFamily M J) v.chamber B.chamber
  apply (mem_liftedTubeSheet_iff_connector M J A B (incomingVertexPoint M J v)
    (incomingVertexPoint_mem_ownSheet M J v) hpB).mpr
  have he : faceIntervalConnector (actualForms M J)
      (complementUniversalCoverProjection M J (incomingVertexPoint M J v)).val.1
      A.chamber B.chamber = intervalPositive A.chamber B.chamber := by
    rw [incomingVertexPoint_projection, show v.chamber = A.chamber from
      (incomingLiftedTubeIndex_chamber M J v).symm]
    have hf := congrArg (fun C : ActualChamber M J =>
      inv (intervalPositive C A.chamber) ≫ intervalPositive C B.chamber)
      (faceChamber_tubeBasepoint M J A.chamber)
    exact hf.trans (by simp only [intervalPositive_self, IsIso.inv_id, Category.id_comp])
  rw [he]
  exact liftedTubePathClass_comp_positive M J A B hs'

/-- Genuine simple upper bounds of every vertex of a finite packet. -/
def simpleUpperSet (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))) :
    Set (IncomingVertex M (⟨J⟩ : RibbonObject M)) :=
  {u | ∀ v ∈ s, v ≤ u ∧ SimpleRibbon M v.source u.source (v.difference u)}

def simpleUpperSheets (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))) :
    Set (LiftedTubeIndex M J) := incomingLiftedTubeIndex M J '' simpleUpperSet M J s

def simpleUpperIntersection (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))) :
    Set (ComplementUniversalCover M J) := liftedTubeIntersection M J (simpleUpperSheets M J s)

theorem simpleUpperSet_antitone {s t : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))}
    (hst : s ⊆ t) : simpleUpperSet M J t ⊆ simpleUpperSet M J s :=
  fun _ hu v hv => hu v (hst hv)

theorem simpleUpperIntersection_mono {s t : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))}
    (hst : s ⊆ t) : simpleUpperIntersection M J s ⊆ simpleUpperIntersection M J t := by
  intro q hq
  apply (mem_liftedTubeIntersection_iff M J _ _).mpr
  rintro A ⟨u, hu, rfl⟩
  exact (mem_liftedTubeIntersection_iff M J _ _).mp hq _
    ⟨u, simpleUpperSet_antitone M J hst hu, rfl⟩

theorem incomingVertexPoint_mem_simpleUpperIntersection
    {s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))}
    {v : IncomingVertex M (⟨J⟩ : RibbonObject M)} (hv : v ∈ s) :
    incomingVertexPoint M J v ∈ simpleUpperIntersection M J s := by
  apply (mem_liftedTubeIntersection_iff M J _ _).mpr
  rintro A ⟨u, hu, rfl⟩
  exact incomingVertexPoint_mem_upperSheet M J (hu v hv).2

/-- Admissibility is exactly the finite chain and actual simple-pair predicates. -/
def garsideTubeAdmissible (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))) : Prop :=
  IsChain (· ≤ ·) (↑s : Set (IncomingVertex M (⟨J⟩ : RibbonObject M))) ∧
    garsideSupportPredicate M (⟨J⟩ : RibbonObject M) s

theorem garsideTubeAdmissible_hereditary
    {s t : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))} (hst : s ⊆ t)
    (ht : garsideTubeAdmissible M J t) : garsideTubeAdmissible M J s :=
  ⟨ht.1.mono hst, garsideSupportPredicate_hereditary M _ hst ht.2⟩

theorem simpleUpperSet_nonempty
    {s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))}
    (hne : s.Nonempty) (hs : garsideTubeAdmissible M J s) : (simpleUpperSet M J s).Nonempty := by
  obtain ⟨a, ha, b, hb, hbounds, _⟩ :=
    exists_simple_interval_of_garsideSupport M (⟨J⟩ : RibbonObject M) s hs.1 hne hs.2
  exact ⟨b, fun v hv => ⟨(hbounds v hv).2, hs.2 v hv b hb (hbounds v hv).2⟩⟩

theorem simpleUpperSheets_nonempty
    {s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))}
    (hne : s.Nonempty) (hs : garsideTubeAdmissible M J s) : (simpleUpperSheets M J s).Nonempty :=
  (simpleUpperSet_nonempty M J hne hs).image _

/-- The finite meet of an admissible nonempty chain is its actual least vertex. -/
theorem finiteMeet_mem_of_garsideTubeAdmissible
    {s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))}
    (hne : s.Nonempty) (hs : garsideTubeAdmissible M J s) : IncomingVertex.finiteMeet s hne ∈ s := by
  obtain ⟨a, ha, b, hb, hbounds, _⟩ :=
    exists_simple_interval_of_garsideSupport M (⟨J⟩ : RibbonObject M) s hs.1 hne hs.2
  have he : IncomingVertex.finiteMeet s hne = a := le_antisymm
    (IncomingVertex.finiteMeet_le s hne ha)
    (IncomingVertex.le_finiteMeet s hne (fun v hv => (hbounds v hv).1))
  rw [he]
  exact ha


/-- Genuine positive paths to a chain vertex lift simultaneously inside
all simple-upper sheets, with their actual source and target fiber points. -/
theorem exists_path_simpleUpperIntersection
    {s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))}
    (hne : s.Nonempty) (hs : garsideTubeAdmissible M J s)
    (a v : IncomingVertex M (⟨J⟩ : RibbonObject M)) (ha : a ∈ s) (hv : v ∈ s)
    (hle : ∀ w ∈ s, a ≤ w) :
    ∃ Γ : Path (incomingVertexPoint M J a) (incomingVertexPoint M J v),
      ∀ t, Γ t ∈ simpleUpperIntersection M J s := by
  let U : Set (ActualChamber M J) := (fun u => u.chamber) '' simpleUpperSet M J s
  have hb : ∀ C ∈ U, ChamberBetween a.chamber v.chamber C := by
    rintro C ⟨u, hu, rfl⟩
    exact incoming_chamberBetween M (hle v hv) (hu v hv).1 (hu a ha).2
  obtain ⟨γ, hγ⟩ := exists_actualPositivePath_sharedUpper M J
    (actualChamberPointFamily M J) a.chamber v.chamber U hb
  have hγu (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) (hu : u ∈ simpleUpperSet M J s)
      (t : unitInterval) : γ t ∈ actualTubeSet M J (incomingLiftedTubeIndex M J u).chamber := by
    rw [incomingLiftedTubeIndex_chamber]
    exact hγ t u.chamber (Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩)
  let f (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) (hu : u ∈ simpleUpperSet M J s) :
      C(unitInterval, ComplementUniversalCover M J) :=
    (liftedTubeSection M J (incomingLiftedTubeIndex M J u)).comp
      ⟨fun t => ⟨γ t, hγu u hu t⟩, γ.continuous.subtype_mk _⟩
  have hstart (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) (hu : u ∈ simpleUpperSet M J s) :
      f u hu 0 = incomingVertexPoint M J a := by
    have hmem := incomingVertexPoint_mem_upperSheet M J (hu a ha).2
    change liftedTubeSection M J (incomingLiftedTubeIndex M J u) ⟨γ 0, _⟩ = _
    have he : (⟨γ 0, hγu u hu 0⟩ : actualTubeSet M J (incomingLiftedTubeIndex M J u).chamber) =
        ⟨complementUniversalCoverProjection M J (incomingVertexPoint M J a),
          liftedTubeSheet_subset_projection_preimage M J _ hmem⟩ :=
      Subtype.ext (γ.source.trans (incomingVertexPoint_projection M J a).symm)
    rw [he]
    exact liftedTubeSection_projection_eq M J _ _ hmem
  have hend (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) (hu : u ∈ simpleUpperSet M J s) :
      f u hu 1 = incomingVertexPoint M J v := by
    have hmem := incomingVertexPoint_mem_upperSheet M J (hu v hv).2
    change liftedTubeSection M J (incomingLiftedTubeIndex M J u) ⟨γ 1, _⟩ = _
    have he : (⟨γ 1, hγu u hu 1⟩ : actualTubeSet M J (incomingLiftedTubeIndex M J u).chamber) =
        ⟨complementUniversalCoverProjection M J (incomingVertexPoint M J v),
          liftedTubeSheet_subset_projection_preimage M J _ hmem⟩ :=
      Subtype.ext (γ.target.trans (incomingVertexPoint_projection M J v).symm)
    rw [he]
    exact liftedTubeSection_projection_eq M J _ _ hmem
  obtain ⟨u₀, hu₀⟩ := simpleUpperSet_nonempty M J hne hs
  have heq (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) (hu : u ∈ simpleUpperSet M J s) :
      f u₀ hu₀ = f u hu := by
    apply ContinuousMap.coe_injective
    apply (isCoveringMap_complementUniversalCoverProjection M J).eq_of_comp_eq
      (f u₀ hu₀).continuous (f u hu).continuous
      (funext fun t => (liftedTubeSection_projection M J _ ⟨γ t, hγu u₀ hu₀ t⟩).trans
        (liftedTubeSection_projection M J _ ⟨γ t, hγu u hu t⟩).symm) (0 : unitInterval)
    exact (hstart u₀ hu₀).trans (hstart u hu).symm
  let Γ : Path (incomingVertexPoint M J a) (incomingVertexPoint M J v) :=
    ⟨f u₀ hu₀, hstart u₀ hu₀, hend u₀ hu₀⟩
  refine ⟨Γ, ?_⟩
  intro t
  apply (mem_liftedTubeIntersection_iff M J _ _).mpr
  rintro A ⟨u, hu, rfl⟩
  change f u₀ hu₀ t ∈ liftedTubeSheet M J (incomingLiftedTubeIndex M J u)
  rw [heq u hu]
  exact (liftedTubeHomeomorph M J _ _).property


/-- The actual component selected by the least vertex. The empty face has
empty carrier; contractibility is asserted only for nonempty admissible faces. -/
def garsideTubeCarrier (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))) :
    Set (ComplementUniversalCover M J) :=
  if hne : s.Nonempty then connectedComponentIn (simpleUpperIntersection M J s)
    (incomingVertexPoint M J (IncomingVertex.finiteMeet s hne)) else ∅

theorem garsideTubeCarrier_eq (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M)))
    (hne : s.Nonempty) : garsideTubeCarrier M J s =
      connectedComponentIn (simpleUpperIntersection M J s)
        (incomingVertexPoint M J (IncomingVertex.finiteMeet s hne)) := by
  simp only [garsideTubeCarrier, dite_eq_left hne]

theorem incomingVertexPoint_mem_garsideTubeCarrier
    {s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))}
    (hne : s.Nonempty) (hs : garsideTubeAdmissible M J s)
    {v : IncomingVertex M (⟨J⟩ : RibbonObject M)} (hv : v ∈ s) :
    incomingVertexPoint M J v ∈ garsideTubeCarrier M J s := by
  rw [garsideTubeCarrier_eq M J s hne]
  have ha := finiteMeet_mem_of_garsideTubeAdmissible M J hne hs
  obtain ⟨Γ, hΓ⟩ := exists_path_simpleUpperIntersection M J hne hs
    (IncomingVertex.finiteMeet s hne) v ha hv (fun w hw => IncomingVertex.finiteMeet_le s hne hw)
  exact (isPreconnected_range Γ.continuous).subset_connectedComponentIn
    ⟨0, Γ.source⟩ (by rintro y ⟨t, rfl⟩; exact hΓ t) ⟨1, Γ.target⟩

theorem contractibleSpace_garsideTubeCarrier
    {s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))}
    (hne : s.Nonempty) (hs : garsideTubeAdmissible M J s) :
    ContractibleSpace (garsideTubeCarrier M J s) := by
  rw [garsideTubeCarrier_eq M J s hne]
  exact contractibleSpace_liftedTubeIntersectionComponent M J (simpleUpperSheets M J s)
    (simpleUpperSheets_nonempty M J hne hs) _
    (incomingVertexPoint_mem_simpleUpperIntersection M J
      (finiteMeet_mem_of_garsideTubeAdmissible M J hne hs))

theorem garsideTubeCarrier_subset_intersection
    {s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))} (hne : s.Nonempty) :
    garsideTubeCarrier M J s ⊆ simpleUpperIntersection M J s := by
  rw [garsideTubeCarrier_eq M J s hne]
  exact connectedComponentIn_subset _ _

/-- Face inclusion enlarges the upper-sheet intersection. All actual face
vertices already lie in the larger selected component, so components nest. -/
theorem garsideTubeCarrier_mono
    {s t : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M))}
    (hst : s ⊆ t) (hne : s.Nonempty) (ht : garsideTubeAdmissible M J t) :
    garsideTubeCarrier M J s ⊆ garsideTubeCarrier M J t := by
  have hnet : t.Nonempty := hne.mono hst
  have hs := garsideTubeAdmissible_hereditary M J hst ht
  have hanchor := incomingVertexPoint_mem_garsideTubeCarrier M J hnet ht
    (hst (finiteMeet_mem_of_garsideTubeAdmissible M J hne hs))
  rw [garsideTubeCarrier_eq M J s hne, garsideTubeCarrier_eq M J t hnet]
  rw [garsideTubeCarrier_eq M J t hnet] at hanchor
  rw [connectedComponentIn_eq hanchor]
  exact connectedComponentIn_mono _ (simpleUpperIntersection_mono M J hst)

/-- Fully proved acyclic data on actual simple chains, with no extension,
comparison map, or homotopy furnished as an extra field. -/
def garsideTubeCarrierData :
    FiniteCarrierData (IncomingVertex M (⟨J⟩ : RibbonObject M)) (ComplementUniversalCover M J) where
  admissible := garsideTubeAdmissible M J
  hereditary := garsideTubeAdmissible_hereditary M J
  carrier := garsideTubeCarrier M J
  contractible _ := contractibleSpace_garsideTubeCarrier M J
  monotone := garsideTubeCarrier_mono M J

/-- The coherent family is computed by the proved contractible-carrier
extension construction in every finite dimension. -/
def garsideTubeReturnFamily : CarrierFamily (garsideTubeCarrierData M J) :=
  (garsideTubeCarrierData M J).family

/-- The actual continuous Garside return into the original universal cover. -/
def actualGarsideReturn :
    C(GarsideWeights M (⟨J⟩ : RibbonObject M), ComplementUniversalCover M J) :=
  (garsideTubeReturnFamily M J).descend
    (garsideSupportPredicate M (⟨J⟩ : RibbonObject M))
    (garsideSupportPredicate_hereditary M (⟨J⟩ : RibbonObject M))
    (fun _ hc hs => ⟨hc, hs⟩)

/-- Any admissible containing finite face controls the actual return value,
including proper faces and zero barycentric coordinates. -/
theorem actualGarsideReturn_carried
    (w : GarsideWeights M (⟨J⟩ : RibbonObject M))
    (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M)))
    (hc : IsChain (· ≤ ·) (↑s : Set (IncomingVertex M (⟨J⟩ : RibbonObject M))))
    (hne : s.Nonempty) (hs : garsideSupportPredicate M (⟨J⟩ : RibbonObject M) s)
    (hw : w.val.weights.support ⊆ s) :
    actualGarsideReturn M J w ∈ garsideTubeCarrier M J s :=
  (garsideTubeReturnFamily M J).descend_carried
    (garsideSupportPredicate M (⟨J⟩ : RibbonObject M))
    (garsideSupportPredicate_hereditary M (⟨J⟩ : RibbonObject M))
    (fun _ hc hs => ⟨hc, hs⟩) w s hc hne hs hw

/-- In particular the return lies in every actual simple-upper sheet of
any admissible containing face. -/
theorem actualGarsideReturn_mem_upperSheet
    (w : GarsideWeights M (⟨J⟩ : RibbonObject M))
    (s : Finset (IncomingVertex M (⟨J⟩ : RibbonObject M)))
    (hc : IsChain (· ≤ ·) (↑s : Set (IncomingVertex M (⟨J⟩ : RibbonObject M))))
    (hne : s.Nonempty) (hs : garsideSupportPredicate M (⟨J⟩ : RibbonObject M) s)
    (hw : w.val.weights.support ⊆ s)
    (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) (hu : u ∈ simpleUpperSet M J s) :
    actualGarsideReturn M J w ∈ incomingLiftedTubeSheet M J u :=
  (mem_liftedTubeIntersection_iff M J _ _).mp
    (garsideTubeCarrier_subset_intersection M J hne
      (actualGarsideReturn_carried M J w s hc hne hs hw)) _ ⟨u, hu, rfl⟩

end ArtinNormalisers.Deligne5
