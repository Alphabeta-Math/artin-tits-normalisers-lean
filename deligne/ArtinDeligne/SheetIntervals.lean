import ArtinDeligne.LiftedTubeLabels
import ArtinDeligne.IncomingJoins
import ArtinDeligne.LiftedCanonicalCover
import ArtinHomotopy.TubeIntervals

/-!
# Actual sheet gauges and incoming chamber intervals

The path classes below are the original classes stored in the accepted actual
universal cover. Local tube classes and signed interval connectors provide
their gauges. No sheet-intersection or asphericity conclusion is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ArtinNormalisers.Deligne5

open CategoryTheory Ribbon2 Homotopy5 Chamber3 Theorem18 Sequence4 Asphericity5
open scoped Topology unitInterval

section General

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
  [TauCeti.SemilocallySimplyConnectedSpace X] {x₀ : X}

/-- The endpoint class of a genuine path in the original universal cover.
This follows from the accepted explicit appended-path lift and uniqueness. -/
theorem universalCover_path_endpoint {e z : TauCeti.UniversalCover x₀} (Γ : Path e z) :
    z.path = e.path.trans (Path.Homotopic.Quotient.mk
      (Γ.map (TauCeti.UniversalCover.continuous_proj x₀))) := by
  obtain ⟨α, rfl⟩ := TauCeti.UniversalCover.surjective_ofBasedPath x₀ e
  let γ := Γ.map (TauCeti.UniversalCover.continuous_proj x₀)
  have hΓ : Γ.toContinuousMap = (TauCeti.UniversalCover.isCoveringMap x₀).liftPath
      γ.toContinuousMap (TauCeti.UniversalCover.ofBasedPath x₀ α) γ.source := by
    apply ((TauCeti.UniversalCover.isCoveringMap x₀).eq_liftPath_iff' γ.source).mpr
    exact ⟨rfl, Γ.source⟩
  have he : z = TauCeti.UniversalCover.ofBasedPath x₀ (α.append γ) :=
    Γ.target.symm.trans ((congrArg (fun f : C(I, TauCeti.UniversalCover x₀) => f 1) hΓ).trans
      (TauCeti.UniversalCover.liftPath_apply_one_eq_ofBasedPath_append γ))
  rw [BasedPath.append, TauCeti.UniversalCover.ofBasedPath_ofPath] at he
  change z.path = (Path.Homotopic.Quotient.mk α.toPath).trans (Path.Homotopic.Quotient.mk γ)
  exact (eq_of_heq (TauCeti.UniversalCover.ext_iff.mp he).2).trans
    (Path.Homotopic.Quotient.mk_trans α.toPath γ)

end General

variable {ι : Type*} (M : CoxeterMatrix ι) [Finite M.Group] (J : Set ι)

/-- The actual tube's unique local class, transported by the existing
identity-coordinate homeomorphism to the original complement. -/
def actualClassInTube (C : ActualChamber M J) {p q : Complement M J}
    (hp : p ∈ actualTubeSet M J C) (hq : q ∈ actualTubeSet M J C) :
    FundamentalGroupoid.mk p ⟶ FundamentalGroupoid.mk q :=
  (FundamentalGroupoid.map (show C(ComplexComplement (E := relativeSubspace J) (actualForms M J),
      Complement M J) from ⟨(actualComplementHomeomorph M J).symm,
    (actualComplementHomeomorph M J).symm.continuous⟩)).map
      (X := FundamentalGroupoid.mk (actualComplementHomeomorph M J p))
      (Y := FundamentalGroupoid.mk (actualComplementHomeomorph M J q))
      (IntervalForward.classInTube C hp hq)

omit [Finite M.Group] in
theorem actualClassInTube_eq_path (C : ActualChamber M J) {p q : Complement M J}
    (hp : p ∈ actualTubeSet M J C) (hq : q ∈ actualTubeSet M J C)
    (γ : Path p q) (hγ : ∀ t, γ t ∈ actualTubeSet M J C) :
    actualClassInTube M J C hp hq = Path.Homotopic.Quotient.mk γ := by
  unfold actualClassInTube
  rw [IntervalForward.classInTube_eq_path C hp hq
    (γ.map (actualComplementHomeomorph M J).continuous) hγ]
  change (Path.Homotopic.Quotient.mk
    (γ.map (actualComplementHomeomorph M J).continuous)).map _ = _
  rw [← Path.Homotopic.Quotient.mk_map]
  congr 1

/-- Exactly one actual sheet over a fixed tube contains a specified lift. -/
theorem existsUnique_liftedTubeIndex_at (q : ComplementUniversalCover M J)
    (C : ActualChamber M J) (hC : complementUniversalCoverProjection M J q ∈ actualTubeSet M J C) :
    ∃! A : LiftedTubeIndex M J, A.chamber = C ∧ q ∈ liftedTubeSheet M J A := by
  have hcover := TauCeti.UniversalCover.sheet_exhaustive
    (isSimplyConnected_actualTube M J C).isPathConnected (tubeBasepoint_mem M J C) hC
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hcover
  let A : LiftedTubeIndex M J :=
    ⟨C, (universalCoverFiberEquivPathClasses (standardComplementPoint M J)
      (tubeBasepoint M J C)).symm r⟩
  have hA : q ∈ liftedTubeSheet M J A := by
    change q ∈ TauCeti.UniversalCover.sheet (actualTubeSet M J C) (tubeBasepoint_mem M J C)
      ((universalCoverFiberEquivPathClasses _ _) ((universalCoverFiberEquivPathClasses _ _).symm r))
    rwa [Equiv.apply_symm_apply]
  refine ⟨A, ⟨rfl, hA⟩, ?_⟩
  rintro ⟨D, e⟩ ⟨hD, he⟩
  dsimp only at hD
  subst D
  have hef : e = A.fiberPoint := by
    by_contra hne
    have hd := disjoint_liftedTubeSheet_same_chamber M J C hne
    exact Set.disjoint_left.mp hd he hA
  cases hef
  rfl

/-- The unique actual fiber point indexing the sheet over `C` through `q`. -/
theorem existsUnique_fiberPoint_at (q : ComplementUniversalCover M J) (C : ActualChamber M J)
    (hC : complementUniversalCoverProjection M J q ∈ actualTubeSet M J C) :
    ∃! e : {z : ComplementUniversalCover M J //
      complementUniversalCoverProjection M J z = tubeBasepoint M J C},
      q ∈ liftedTubeSheet M J ⟨C, e⟩ := by
  obtain ⟨⟨D, e⟩, ⟨hD, he⟩, _⟩ := existsUnique_liftedTubeIndex_at M J q C hC
  dsimp only at hD
  subst D
  refine ⟨e, he, ?_⟩
  intro f hf
  by_contra hne
  exact Set.disjoint_left.mp (disjoint_liftedTubeSheet_same_chamber M J C hne) hf he

/-- The unique original sheet over `C` through the actual lift `q`. Its
chamber is definitionally `C`; only the actual canonical fiber point is chosen. -/
def pointTubeIndex (q : ComplementUniversalCover M J) (C : ActualChamber M J)
    (hC : complementUniversalCoverProjection M J q ∈ actualTubeSet M J C) : LiftedTubeIndex M J :=
  ⟨C, Classical.choose (existsUnique_fiberPoint_at M J q C hC)⟩

@[simp] theorem pointTubeIndex_chamber (q : ComplementUniversalCover M J) (C : ActualChamber M J)
    (hC : complementUniversalCoverProjection M J q ∈ actualTubeSet M J C) :
    (pointTubeIndex M J q C hC).chamber = C := rfl

theorem mem_pointTubeIndex (q : ComplementUniversalCover M J) (C : ActualChamber M J)
    (hC : complementUniversalCoverProjection M J q ∈ actualTubeSet M J C) :
    q ∈ liftedTubeSheet M J (pointTubeIndex M J q C hC) :=
  (Classical.choose_spec (existsUnique_fiberPoint_at M J q C hC)).1

/-- Membership in an original sheet gives its actual stored path equation. -/
theorem liftedTubeSheet_pathClass (A : LiftedTubeIndex M J) (q : ComplementUniversalCover M J)
    (hp : complementUniversalCoverProjection M J q ∈ actualTubeSet M J A.chamber)
    (hq : q ∈ liftedTubeSheet M J A) :
    q.path = (liftedTubePathClass M J A).trans
      (actualClassInTube M J A.chamber (tubeBasepoint_mem M J A.chamber) hp) := by
  rcases A with ⟨C, ⟨⟨x, r⟩, hx⟩⟩
  change x = tubeBasepoint M J C at hx
  subst x
  let A : LiftedTubeIndex M J := ⟨C, ⟨⟨tubeBasepoint M J C, r⟩, rfl⟩⟩
  let S := liftedTubeSheet M J A
  let ξ : Path (⟨A.fiberPoint.val, fiberPoint_mem_liftedTubeSheet M J A⟩ : S) ⟨q, hq⟩ :=
    PathConnectedSpace.somePath _ _
  let Γ := ξ.map continuous_subtype_val
  let γ := Γ.map (TauCeti.UniversalCover.continuous_proj (standardComplementPoint M J))
  have hγ : ∀ t, γ t ∈ actualTubeSet M J C := fun t =>
    liftedTubeSheet_subset_projection_preimage M J A (ξ t).property
  have hend := universalCover_path_endpoint Γ
  change q.path = r.trans (Path.Homotopic.Quotient.mk γ) at hend
  change q.path = r.trans (actualClassInTube M J C (tubeBasepoint_mem M J C) hp)
  rw [actualClassInTube_eq_path M J C _ _ γ hγ]
  exact hend

/-- The actual sheet condition is exactly its original path-class gauge. -/
theorem mem_liftedTubeSheet_iff_pathClass (A : LiftedTubeIndex M J)
    (q : ComplementUniversalCover M J)
    (hp : complementUniversalCoverProjection M J q ∈ actualTubeSet M J A.chamber) :
    q ∈ liftedTubeSheet M J A ↔ q.path = (liftedTubePathClass M J A).trans
      (actualClassInTube M J A.chamber (tubeBasepoint_mem M J A.chamber) hp) := by
  constructor
  · exact liftedTubeSheet_pathClass M J A q hp
  · intro h
    obtain ⟨⟨z, r⟩, hz, he⟩ := TauCeti.UniversalCover.proj_surjOn_sheet
      (isSimplyConnected_actualTube M J A.chamber).isPathConnected
      (tubeBasepoint_mem M J A.chamber) (liftedTubePathClass M J A) hp
    change z = complementUniversalCoverProjection M J q at he
    subst z
    have hpath := liftedTubeSheet_pathClass M J A
      (⟨complementUniversalCoverProjection M J q, r⟩ : ComplementUniversalCover M J) hp hz
    have heq : (⟨complementUniversalCoverProjection M J q, r⟩ : ComplementUniversalCover M J) = q := by
      exact TauCeti.UniversalCover.ext_iff.mpr ⟨rfl, heq_of_eq (hpath.trans h.symm)⟩
    exact heq ▸ hz

omit [Finite M.Group] in
theorem actualClassInTube_self (C : ActualChamber M J) {p : Complement M J}
    (hp : p ∈ actualTubeSet M J C) : actualClassInTube M J C hp hp = 𝟙 _ := by
  rw [actualClassInTube_eq_path M J C hp hp (Path.refl p) (fun _ => hp)]
  rfl

omit [Finite M.Group] in
theorem actualClassInTube_comp (C : ActualChamber M J) {p q r : Complement M J}
    (hp : p ∈ actualTubeSet M J C) (hq : q ∈ actualTubeSet M J C)
    (hr : r ∈ actualTubeSet M J C) :
    actualClassInTube M J C hp hq ≫ actualClassInTube M J C hq hr =
      actualClassInTube M J C hp hr := by
  unfold actualClassInTube
  rw [← CategoryTheory.Functor.map_comp, IntervalForward.classInTube_comp]

omit [Finite M.Group] in
theorem actualClassInTube_inv (C : ActualChamber M J) {p q : Complement M J}
    (hp : p ∈ actualTubeSet M J C) (hq : q ∈ actualTubeSet M J C) :
    inv (actualClassInTube M J C hp hq) = actualClassInTube M J C hq hp := by
  unfold actualClassInTube
  rw [← CategoryTheory.Functor.map_inv, IntervalEquivalence.classInTube_inv]

/-- The accepted local connector identity in the original actual complement. -/
theorem actualForward_faceIntervalConnector (p : Complement M J) (C D : ActualChamber M J)
    (hpC : p ∈ actualTubeSet M J C) (hpD : p ∈ actualTubeSet M J D) :
    (actualIntervalForward M J).map
      (faceIntervalConnector (actualForms M J) p.val.1 C D) =
      actualClassInTube M J C (tubeBasepoint_mem M J C) hpC ≫
        actualClassInTube M J D hpD (tubeBasepoint_mem M J D) := by
  have h := IntervalEquivalence.forward_faceIntervalConnector
    (actualChamberPointFamily M J) (p := actualComplementHomeomorph M J p) hpC hpD
  have hm := congrArg (fun f :
      FundamentalGroupoid.mk (chamberBasepoint (actualChamberPointFamily M J) C) ⟶
        FundamentalGroupoid.mk (chamberBasepoint (actualChamberPointFamily M J) D) =>
      (FundamentalGroupoid.map (show C(ComplexComplement (E := relativeSubspace J) (actualForms M J),
        Complement M J) from ⟨(actualComplementHomeomorph M J).symm,
          (actualComplementHomeomorph M J).symm.continuous⟩)).map f) h
  simpa only [actualIntervalForward, actualIntervalForwardOfPoints, CategoryTheory.Functor.comp_map,
    CategoryTheory.Functor.comp_obj, intervalForward_obj, actualComplementHomeomorph_val,
    actualClassInTube, CategoryTheory.Functor.map_comp] using hm

/-- The exact local gauge for two original sheets over a common point. -/
theorem mem_liftedTubeSheet_iff_connector (A B : LiftedTubeIndex M J)
    (q : ComplementUniversalCover M J) (hA : q ∈ liftedTubeSheet M J A)
    (hpB : complementUniversalCoverProjection M J q ∈ actualTubeSet M J B.chamber) :
    q ∈ liftedTubeSheet M J B ↔
      (show FundamentalGroupoid.mk (standardComplementPoint M J) ⟶
          FundamentalGroupoid.mk (tubeBasepoint M J B.chamber) from
        liftedTubePathClass M J A ≫ (actualIntervalForward M J).map
          (X := intervalObject A.chamber) (Y := intervalObject B.chamber)
          (faceIntervalConnector (actualForms M J)
            (complementUniversalCoverProjection M J q).val.1 A.chamber B.chamber)) =
        liftedTubePathClass M J B := by
  have hpA := liftedTubeSheet_subset_projection_preimage M J A hA
  have hpathA := liftedTubeSheet_pathClass M J A q hpA hA
  rw [mem_liftedTubeSheet_iff_pathClass M J B q hpB,
    actualForward_faceIntervalConnector M J _ A.chamber B.chamber hpA hpB,
    ← actualClassInTube_inv M J B.chamber (tubeBasepoint_mem M J B.chamber) hpB]
  constructor
  · intro hpathB
    apply (cancel_mono (actualClassInTube M J B.chamber (tubeBasepoint_mem M J B.chamber) hpB)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact hpathA.symm.trans hpathB
  · intro h
    have he := congrArg (fun f : FundamentalGroupoid.mk (standardComplementPoint M J) ⟶
      FundamentalGroupoid.mk (tubeBasepoint M J B.chamber) =>
      f ≫ actualClassInTube M J B.chamber (tubeBasepoint_mem M J B.chamber) hpB) h
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] at he
    exact hpathA.trans he

/-- The lower and upper actual tube chambers at an original complement point. -/
def sheetLowerChamber (p : Complement M J) : ActualChamber M J :=
  tubeLowerChamber (E := relativeSubspace J) (actualForms M J) (actualComplementHomeomorph M J p)

def sheetUpperChamber (p : Complement M J) : ActualChamber M J :=
  tubeUpperChamber (E := relativeSubspace J) (actualForms M J) (actualComplementHomeomorph M J p)

theorem mem_actualTubeSet_iff_sheetBetween (p : Complement M J) (C : ActualChamber M J) :
    p ∈ actualTubeSet M J C ↔ ChamberBetween (sheetLowerChamber M J p) C (sheetUpperChamber M J p) :=
  mem_tubeSet_iff_chamberBetween (E := relativeSubspace J) (actualForms M J) (actualComplementHomeomorph M J p) C

theorem mem_sheetLowerChamber (p : Complement M J) : p ∈ actualTubeSet M J (sheetLowerChamber M J p) :=
  (mem_actualTubeSet_iff_sheetBetween M J p _).mpr (chamberBetween_left _ _)

theorem mem_sheetUpperChamber (p : Complement M J) : p ∈ actualTubeSet M J (sheetUpperChamber M J p) :=
  (mem_actualTubeSet_iff_sheetBetween M J p _).mpr (chamberBetween_right _ _)

theorem faceChamber_eq_sheetLower (p : Complement M J) (C : ActualChamber M J)
    (hp : p ∈ actualTubeSet M J C) :
    faceChamber (actualForms M J) p.val.1 C = sheetLowerChamber M J p := by
  simpa only [sheetLowerChamber, tubeLowerChamber, actualComplementHomeomorph_val] using
    faceChamber_eq_of_mem_tubes (E := relativeSubspace J) (actualForms M J) (p := actualComplementHomeomorph M J p)
      hp (mem_tubeWitness (E := relativeSubspace J) (actualForms M J) (actualComplementHomeomorph M J p))

/-- A local connector between chambers ordered from the common lower face
is the actual positive interval generator. -/
theorem faceConnector_eq_positive_of_between (p : Complement M J) (C D : ActualChamber M J)
    (hpC : p ∈ actualTubeSet M J C)
    (hbet : ChamberBetween (sheetLowerChamber M J p) C D) :
    faceIntervalConnector (actualForms M J) p.val.1 C D = intervalPositive C D := by
  have he := congrArg (fun F : ActualChamber M J =>
    inv (intervalPositive F C) ≫ intervalPositive F D) (faceChamber_eq_sheetLower M J p C hpC)
  change inv (intervalPositive (faceChamber (actualForms M J) p.val.1 C) C) ≫
    intervalPositive (faceChamber (actualForms M J) p.val.1 C) D = _
  refine he.trans ?_
  rw [intervalPositive_comp _ _ _ hbet]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- Shared sheet membership turns an ordered local chamber connector into
the actual simple positive ribbon factor between the incoming labels. -/
theorem sheet_simple_difference_of_between (A B : LiftedTubeIndex M J)
    (q : ComplementUniversalCover M J) (hA : q ∈ liftedTubeSheet M J A)
    (hB : q ∈ liftedTubeSheet M J B)
    (hbet : ChamberBetween (sheetLowerChamber M J (complementUniversalCoverProjection M J q))
      A.chamber B.chamber) :
    SimpleRibbon M (liftedTubeIndexEquivIncoming M J A).source
      (liftedTubeIndexEquivIncoming M J B).source
      ((liftedTubeIndexEquivIncoming M J A).difference (liftedTubeIndexEquivIncoming M J B)) := by
  have hpA := liftedTubeSheet_subset_projection_preimage M J A hA
  have hpB := liftedTubeSheet_subset_projection_preimage M J B hB
  have hpath := (mem_liftedTubeSheet_iff_connector M J A B q hA hpB).mp hB
  rw [faceConnector_eq_positive_of_between M J _ A.chamber B.chamber hpA hbet] at hpath
  have hvalue := (liftedTubePathClass_comp_iff M J A B
    (intervalPositive A.chamber B.chamber)).mp hpath
  have hdiff : (liftedTubeIndexEquivIncoming M J A).difference (liftedTubeIndexEquivIncoming M J B) =
      ((intervalRibbonFunctor M J).map (intervalPositive A.chamber B.chamber)).val.val := by
    dsimp only [IncomingVertex.difference]
    rw [hvalue]
    group
  rw [hdiff, liftedTubeIndexEquivIncoming_source, liftedTubeIndexEquivIncoming_source,
    intervalRibbonFunctor_positive, intervalRibbonPositive_value]
  exact simpleRibbon_intervalPositive M J A.chamber B.chamber

/-- The actual incoming endpoints of all sheets through the lift. -/
def sheetLowerVertex (q : ComplementUniversalCover M J) : IncomingVertex M (⟨J⟩ : RibbonObject M) :=
  liftedTubeIndexEquivIncoming M J (pointTubeIndex M J q
    (sheetLowerChamber M J (complementUniversalCoverProjection M J q)) (mem_sheetLowerChamber M J _))

def sheetUpperVertex (q : ComplementUniversalCover M J) : IncomingVertex M (⟨J⟩ : RibbonObject M) :=
  liftedTubeIndexEquivIncoming M J (pointTubeIndex M J q
    (sheetUpperChamber M J (complementUniversalCoverProjection M J q)) (mem_sheetUpperChamber M J _))

@[simp] theorem sheetLowerVertex_chamber (q : ComplementUniversalCover M J) :
    (sheetLowerVertex M J q).chamber = sheetLowerChamber M J (complementUniversalCoverProjection M J q) := by
  rw [sheetLowerVertex, liftedTubeIndexEquivIncoming_chamber, pointTubeIndex_chamber]

@[simp] theorem sheetUpperVertex_chamber (q : ComplementUniversalCover M J) :
    (sheetUpperVertex M J q).chamber = sheetUpperChamber M J (complementUniversalCoverProjection M J q) := by
  rw [sheetUpperVertex, liftedTubeIndexEquivIncoming_chamber, pointTubeIndex_chamber]

theorem sheetInterval_simple (q : ComplementUniversalCover M J) :
    SimpleRibbon M (sheetLowerVertex M J q).source (sheetUpperVertex M J q).source
      ((sheetLowerVertex M J q).difference (sheetUpperVertex M J q)) := by
  apply sheet_simple_difference_of_between M J _ _ q
    (mem_pointTubeIndex M J q _ _) (mem_pointTubeIndex M J q _ _)
  exact chamberBetween_left _ _

/-- Every sheet through the actual lift has incoming label in its one actual
simple interval. This direction uses actual path gauges, not only projection. -/
theorem sheet_mem_implies_interval (q : ComplementUniversalCover M J)
    (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) (hu : q ∈ incomingLiftedTubeSheet M J u) :
    sheetLowerVertex M J q ≤ u ∧ u ≤ sheetUpperVertex M J q := by
  let A := pointTubeIndex M J q (sheetLowerChamber M J (complementUniversalCoverProjection M J q))
    (mem_sheetLowerChamber M J _)
  let B := pointTubeIndex M J q (sheetUpperChamber M J (complementUniversalCoverProjection M J q))
    (mem_sheetUpperChamber M J _)
  let U := incomingLiftedTubeIndex M J u
  have hU : q ∈ liftedTubeSheet M J U := hu
  have hAU := sheet_simple_difference_of_between M J A U q
    (mem_pointTubeIndex M J q _ _) hU (chamberBetween_left _ _)
  have hUB := sheet_simple_difference_of_between M J U B q hU
    (mem_pointTubeIndex M J q _ _)
    ((mem_actualTubeSet_iff_sheetBetween M J _ U.chamber).mp
      (liftedTubeSheet_subset_projection_preimage M J U hU))
  constructor
  · simpa only [sheetLowerVertex, IncomingVertex.le_iff, IncomingVertex.difference, A, U, incomingLiftedTubeIndex, Equiv.apply_symm_apply] using hAU.1
  · simpa only [sheetUpperVertex, IncomingVertex.le_iff, IncomingVertex.difference, B, U, incomingLiftedTubeIndex, Equiv.apply_symm_apply] using hUB.1

/-- Conversely every incoming vertex of the actual simple interval labels
the original sheet through this lift. -/
theorem interval_implies_sheet_mem (q : ComplementUniversalCover M J)
    (u : IncomingVertex M (⟨J⟩ : RibbonObject M))
    (hau : sheetLowerVertex M J q ≤ u) (hub : u ≤ sheetUpperVertex M J q) :
    q ∈ incomingLiftedTubeSheet M J u := by
  let A := pointTubeIndex M J q (sheetLowerChamber M J (complementUniversalCoverProjection M J q))
    (mem_sheetLowerChamber M J _)
  let U := incomingLiftedTubeIndex M J u
  have hgeom := incoming_chamberBetween M hau hub (sheetInterval_simple M J q)
  rw [sheetLowerVertex_chamber, sheetUpperVertex_chamber] at hgeom
  have hpU : complementUniversalCoverProjection M J q ∈ actualTubeSet M J U.chamber := by
    rw [incomingLiftedTubeIndex_chamber]
    exact (mem_actualTubeSet_iff_sheetBetween M J _ u.chamber).mpr hgeom
  have hs := IncomingVertex.simple_difference_of_interval (sheetInterval_simple M J q) le_rfl hau hub
  have hs' : SimpleRibbon M (liftedTubeIndexEquivIncoming M J A).source
      (liftedTubeIndexEquivIncoming M J U).source
      ((liftedTubeIndexEquivIncoming M J A).difference (liftedTubeIndexEquivIncoming M J U)) := by
    simpa only [sheetLowerVertex, A, U, incomingLiftedTubeIndex, Equiv.apply_symm_apply] using hs
  have hpath := liftedTubePathClass_comp_positive M J A U hs'
  apply (mem_liftedTubeSheet_iff_connector M J A U q (mem_pointTubeIndex M J q _ _) hpU).mpr
  rw [faceConnector_eq_positive_of_between M J _ A.chamber U.chamber
    (mem_sheetLowerChamber M J _) (chamberBetween_left _ _)]
  exact hpath

/-- Exact classification of all original lifted tubes through an actual
universal-cover point by one actual incoming simple interval. -/
theorem mem_incomingLiftedTubeSheet_iff_interval (q : ComplementUniversalCover M J)
    (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) :
    q ∈ incomingLiftedTubeSheet M J u ↔
      sheetLowerVertex M J q ≤ u ∧ u ≤ sheetUpperVertex M J q :=
  ⟨sheet_mem_implies_interval M J q u, fun h => interval_implies_sheet_mem M J q u h.1 h.2⟩


/-- The upper phase chamber is itself one of the actual tubes at the point. -/
def sheetPhaseUpperChamber (p : Complement M J) : ActualChamber M J :=
  phaseUpperChamber (E := relativeSubspace J) (actualForms M J)
    (actualComplementHomeomorph M J p)

theorem mem_sheetPhaseUpperChamber (p : Complement M J) :
    p ∈ actualTubeSet M J (sheetPhaseUpperChamber M J p) := by
  intro h hr
  have hi : actualForms M J h p.val.2 ≠ 0 := by
    exact fun hz => (actualComplementHomeomorph M J p).property h ⟨hr, hz⟩
  change p.val.2 ∈ signHalfSpace (actualForms M J h)
    ((faceChamber (actualForms M J) p.val.2 (sheetLowerChamber M J p)).signs h)
  rw [faceChamber_signs_nonzero (actualForms M J) p.val.2 _ hi]
  change (if decide (0 < actualForms M J h p.val.2) then
    0 < actualForms M J h p.val.2 else actualForms M J h p.val.2 < 0)
  split_ifs with hs
  · exact of_decide_eq_true hs
  · apply lt_of_le_of_ne _ hi
    apply le_of_not_gt
    intro hp
    exact hs (decide_eq_true hp)

/-- The actual incoming upper endpoint for the narrower phase interval. -/
def sheetPhaseUpperVertex (q : ComplementUniversalCover M J) : IncomingVertex M (⟨J⟩ : RibbonObject M) :=
  liftedTubeIndexEquivIncoming M J (pointTubeIndex M J q
    (sheetPhaseUpperChamber M J (complementUniversalCoverProjection M J q))
    (mem_sheetPhaseUpperChamber M J _))

@[simp] theorem sheetPhaseUpperVertex_chamber (q : ComplementUniversalCover M J) :
    (sheetPhaseUpperVertex M J q).chamber =
      sheetPhaseUpperChamber M J (complementUniversalCoverProjection M J q) := by
  rw [sheetPhaseUpperVertex, liftedTubeIndexEquivIncoming_chamber, pointTubeIndex_chamber]

theorem sheetPhaseInterval_simple (q : ComplementUniversalCover M J) :
    SimpleRibbon M (sheetLowerVertex M J q).source (sheetPhaseUpperVertex M J q).source
      ((sheetLowerVertex M J q).difference (sheetPhaseUpperVertex M J q)) := by
  apply sheet_simple_difference_of_between M J _ _ q
    (mem_pointTubeIndex M J q _ _) (mem_pointTubeIndex M J q _ _)
  exact chamberBetween_left _ _

/-- Within the phase interval, original sheet membership is equivalently
its actual chamber's phase betweenness. -/
theorem mem_sheet_phase_interval_iff (q : ComplementUniversalCover M J)
    (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) :
    sheetLowerVertex M J q ≤ u ∧ u ≤ sheetPhaseUpperVertex M J q ↔
      q ∈ incomingLiftedTubeSheet M J u ∧
      ChamberBetween (sheetLowerChamber M J (complementUniversalCoverProjection M J q))
        u.chamber (sheetPhaseUpperChamber M J (complementUniversalCoverProjection M J q)) := by
  constructor
  · rintro ⟨hau, hub⟩
    have hB : q ∈ incomingLiftedTubeSheet M J (sheetPhaseUpperVertex M J q) := by
      simpa only [sheetPhaseUpperVertex, incomingLiftedTubeSheet, incomingLiftedTubeIndex,
        Equiv.symm_apply_apply] using (mem_pointTubeIndex M J q
          (sheetPhaseUpperChamber M J (complementUniversalCoverProjection M J q))
          (mem_sheetPhaseUpperChamber M J _))
    have hfull := (sheet_mem_implies_interval M J q _ hB).2
    refine ⟨interval_implies_sheet_mem M J q u hau (hub.trans hfull), ?_⟩
    simpa only [sheetLowerVertex_chamber, sheetPhaseUpperVertex_chamber] using
      (incoming_chamberBetween M hau hub (sheetPhaseInterval_simple M J q))
  · rintro ⟨hu, hbet⟩
    let U := incomingLiftedTubeIndex M J u
    let B := pointTubeIndex M J q
      (sheetPhaseUpperChamber M J (complementUniversalCoverProjection M J q))
      (mem_sheetPhaseUpperChamber M J _)
    have hUB := sheet_simple_difference_of_between M J U B q hu
      (mem_pointTubeIndex M J q _ _) (by simpa only [U, B, pointTubeIndex_chamber, incomingLiftedTubeIndex_chamber] using hbet)
    refine ⟨(sheet_mem_implies_interval M J q u hu).1, ?_⟩
    simpa only [IncomingVertex.le_iff, IncomingVertex.difference, sheetPhaseUpperVertex,
      U, B, incomingLiftedTubeIndex, Equiv.apply_symm_apply] using hUB.1

/-- The incoming label of the genuine sheet carrying this canonical cell. -/
def canonicalIncomingLabel (A : LiftedCanonicalIndex M J) : IncomingVertex M (⟨J⟩ : RibbonObject M) :=
  liftedTubeIndexEquivIncoming M J A.toLiftedTubeIndex

@[simp] theorem canonicalIncomingLabel_chamber (A : LiftedCanonicalIndex M J) :
    (canonicalIncomingLabel M J A).chamber = actualCanonicalTypeChamber M J A.base :=
  liftedTubeIndexEquivIncoming_chamber M J _

theorem canonicalIncomingLabel_phase_bounds (A : LiftedCanonicalIndex M J)
    (q : ComplementUniversalCover M J) (hq : q ∈ liftedCanonicalSet M J A) :
    sheetLowerVertex M J q ≤ canonicalIncomingLabel M J A ∧
      canonicalIncomingLabel M J A ≤ sheetPhaseUpperVertex M J q := by
  apply (mem_sheet_phase_interval_iff M J q _).mpr
  constructor
  · simpa only [canonicalIncomingLabel, incomingLiftedTubeSheet, incomingLiftedTubeIndex,
      Equiv.symm_apply_apply] using hq.1
  · rw [canonicalIncomingLabel_chamber]
    exact canonicalCell_chamberBetween (E := relativeSubspace J) (actualForms M J) hq.2

/-- Any phase upper bound of an incident canonical-cell label carries the
whole original lifted cell. This uses connected lift uniqueness, not merely
membership of its center. -/
theorem liftedCanonicalSet_subset_incomingSheet (A : LiftedCanonicalIndex M J)
    (q : ComplementUniversalCover M J) (hq : q ∈ liftedCanonicalSet M J A)
    (v : IncomingVertex M (⟨J⟩ : RibbonObject M))
    (hAv : canonicalIncomingLabel M J A ≤ v) (hv : v ≤ sheetPhaseUpperVertex M J q) :
    liftedCanonicalSet M J A ⊆ incomingLiftedTubeSheet M J v := by
  have hA := canonicalIncomingLabel_phase_bounds M J A q hq
  have hav := incoming_chamberBetween M hA.1 hAv
    (IncomingVertex.simple_difference_of_interval (sheetPhaseInterval_simple M J q)
      le_rfl (hA.1.trans hAv) hv)
  have hvb := incoming_chamberBetween M (hA.1.trans hAv) hv (sheetPhaseInterval_simple M J q)
  simp only [sheetLowerVertex_chamber, sheetPhaseUpperVertex_chamber,
    canonicalIncomingLabel_chamber] at hav hvb
  apply liftedCanonicalSet_subset_liftedTubeSheet M J A (incomingLiftedTubeIndex M J v)
  · rw [incomingLiftedTubeIndex_chamber]
    intro x hx
    exact canonicalCell_subset_tubeSet (E := relativeSubspace J) (actualForms M J)
      (c := canonicalCenter (E := relativeSubspace J) (actualForms M J) A.base)
      (p := actualComplementHomeomorph M J (complementUniversalCoverProjection M J q)) hq.2 v.chamber
      (by simpa only [sheetLowerChamber, actualCanonicalTypeChamber, canonicalTypeChamber] using hav)
      (by simpa only [sheetLowerChamber, sheetPhaseUpperChamber] using hvb) hx
  · exact ⟨q, hq, ((mem_sheet_phase_interval_iff M J q v).mp ⟨hA.1.trans hAv, hv⟩).1⟩


/-- Labels of a finite packet of actual lifted canonical cells. -/
def canonicalPacketLabels (F : Finset (LiftedCanonicalIndex M J)) :
    Finset (IncomingVertex M (⟨J⟩ : RibbonObject M)) := by
  classical
  exact F.image (canonicalIncomingLabel M J)

theorem canonicalPacketLabels_nonempty (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty) :
    (canonicalPacketLabels M J F).Nonempty := by
  classical
  exact hF.image _

/-- The actual ribbon-lattice join of an incident canonical-cell packet. -/
def canonicalPacketJoin (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty) :
    IncomingVertex M (⟨J⟩ : RibbonObject M) :=
  IncomingVertex.finiteJoin (canonicalPacketLabels M J F) (canonicalPacketLabels_nonempty M J F hF)

theorem canonicalPacketJoin_mono {F G : Finset (LiftedCanonicalIndex M J)}
    (hFG : F ⊆ G) (hF : F.Nonempty) (hG : G.Nonempty) :
    canonicalPacketJoin M J F hF ≤ canonicalPacketJoin M J G hG := by
  classical
  exact IncomingVertex.finiteJoin_mono (Finset.image_subset_image hFG) _ _

/-- At every common lift, the actual finite join lies in the same simple
phase interval and its original sheet carries every whole lifted cell. -/
theorem canonicalPacketJoin_carrier (F : Finset (LiftedCanonicalIndex M J)) (hF : F.Nonempty)
    (q : ComplementUniversalCover M J) (hq : ∀ A ∈ F, q ∈ liftedCanonicalSet M J A) :
    sheetLowerVertex M J q ≤ canonicalPacketJoin M J F hF ∧
      canonicalPacketJoin M J F hF ≤ sheetPhaseUpperVertex M J q ∧
      SimpleRibbon M (sheetLowerVertex M J q).source (canonicalPacketJoin M J F hF).source
        ((sheetLowerVertex M J q).difference (canonicalPacketJoin M J F hF)) ∧
      q ∈ incomingLiftedTubeSheet M J (canonicalPacketJoin M J F hF) ∧
      ∀ A ∈ F, liftedCanonicalSet M J A ⊆ incomingLiftedTubeSheet M J (canonicalPacketJoin M J F hF) := by
  classical
  have hbounds : ∀ u ∈ canonicalPacketLabels M J F,
      sheetLowerVertex M J q ≤ u ∧ u ≤ sheetPhaseUpperVertex M J q := by
    intro u hu
    obtain ⟨A, hAF, rfl⟩ := Finset.mem_image.mp hu
    exact canonicalIncomingLabel_phase_bounds M J A q (hq A hAF)
  have hj := IncomingVertex.finiteJoin_simple_interval
    (canonicalPacketLabels M J F) (canonicalPacketLabels_nonempty M J F hF)
    (sheetLowerVertex M J q) (sheetPhaseUpperVertex M J q)
    (fun u hu => (hbounds u hu).1) (fun u hu => (hbounds u hu).2) (sheetPhaseInterval_simple M J q)
  refine ⟨hj.1, hj.2.1, hj.2.2.1,
    ((mem_sheet_phase_interval_iff M J q _).mp ⟨hj.1, hj.2.1⟩).1, ?_⟩
  intro A hAF
  exact liftedCanonicalSet_subset_incomingSheet M J A q (hq A hAF) _
    (IncomingVertex.le_finiteJoin _ _ (Finset.mem_image.mpr ⟨A, hAF, rfl⟩)) hj.2.1

end ArtinNormalisers.Deligne5

