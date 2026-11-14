import ArtinAsphericity.UniversalCoverGeometry
import ArtinChambers.ActualTubes
import ArtinChambers.ForwardEquivariance

/-!
# Actual universal-cover sheets over the contractible chamber tubes

These are subsets of the original based-path universal cover, with its accepted
coinduced topology. A sheet is indexed by an actual point in the fiber over the
canonical chamber basepoint. The endpoint projection identifies each sheet
homeomorphically with its actual tube; its inverse is the chosen-basepoint
section. These open sheets cover the actual universal cover.

Supplier inspection (2026-11-14): GitHub code searches for
`existsUnique_continuousMap_lifts` in mathlib and `proj_injOn_sheet` in TauCeti
were followed by reading the pinned declarations and proofs. This file reuses
only already accepted sources: TauCeti commit
`62bbc0596dc3539d488232e4e924a338548ea0a9`, UniversalCover/Basic.lean
(`sheet`, `isOpen_sheet`, `proj_surjOn_sheet`, `proj_injOn_sheet`,
`sheet_exhaustive`, `pairwise_disjoint_sheet`), plus its accepted Path.lean
`IsSimplyConnected.isPathHomotopyTrivial`; mathlib commit
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9` supplies
`Equiv.toHomeomorphOfContinuousOpen`. No new source cohort is imported.
The alternative mathlib lifting theorem requires a simply connected, locally
path connected source and proves a unique continuous lift; it was inspected
but is unnecessary because the accepted genuine sheet construction suffices.
No contractibility of the total cover or nerve comparison is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace ArtinNormalisers.Deligne5

open Theorem18 Chamber3 Asphericity5 Sequence4 Topology

section General

variable {X : Type*} [TopologicalSpace X] (x₀ x : X)

/-- The actual endpoint fiber consists precisely of the original path classes. -/
def universalCoverFiberEquivPathClasses :
    {z : TauCeti.UniversalCover x₀ // z.proj = x} ≃ Path.Homotopic.Quotient x₀ x where
  toFun z := z.property ▸ z.val.path
  invFun q := ⟨⟨x, q⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨y, q⟩, hy⟩
    cases hy
    rfl
  right_inv _ := rfl

variable {x₀ x}

/-- The original class defining a sheet belongs to it. -/
theorem universalCover_mk_mem_sheet (U : Set X) (hx : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    (⟨x, q⟩ : TauCeti.UniversalCover x₀) ∈ TauCeti.UniversalCover.sheet U hx q := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
    simpa only [TauCeti.UniversalCover.ofBasedPath_ofPath] using
      (TauCeti.UniversalCover.mem_sheet_self hx p)

theorem universalCover_fiberPoint_mem_sheet (U : Set X) (hx : x ∈ U)
    (e : {z : TauCeti.UniversalCover x₀ // z.proj = x}) :
    e.val ∈ TauCeti.UniversalCover.sheet U hx
      (universalCoverFiberEquivPathClasses x₀ x e) := by
  rcases e with ⟨⟨y, q⟩, hy⟩
  cases hy
  exact universalCover_mk_mem_sheet U hx q

/-- Endpoint projection restricted to one actual universal-cover sheet. -/
def universalCoverSheetProjection (U : Set X) (hx : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    C(TauCeti.UniversalCover.sheet U hx q, U) where
  toFun z := ⟨z.val.proj, TauCeti.UniversalCover.sheet_subset_proj_preimage U hx q z.property⟩
  continuous_toFun :=
    ((TauCeti.UniversalCover.continuous_proj x₀).comp continuous_subtype_val).subtype_mk _

/-- Over a path connected and path-homotopy-trivial open set, the actual sheet
projection is a homeomorphism. The stronger simply connected tube hypothesis
will discharge both geometric premises in the application below. -/
def universalCoverSheetHomeomorph [LocallyPathConnectedSpace X]
    [TauCeti.SemilocallySimplyConnectedSpace X] (U : Set X) (hU : IsOpen U)
    (hconn : IsPathConnected U) (htriv : IsPathHomotopyTrivial U) (hx : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    TauCeti.UniversalCover.sheet U hx q ≃ₜ U := by
  let f := universalCoverSheetProjection U hx q
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact TauCeti.UniversalCover.proj_injOn_sheet htriv hx q a.property b.property
        (congrArg Subtype.val hab)
    · intro y
      obtain ⟨z, hz, he⟩ := TauCeti.UniversalCover.proj_surjOn_sheet hconn hx q y.property
      exact ⟨⟨z, hz⟩, Subtype.ext he⟩
  have hopen : IsOpenMap f :=
    ((TauCeti.UniversalCover.isOpenMap_proj x₀).domRestrict
      (TauCeti.UniversalCover.isOpen_sheet U hU hx q)).subtype_mk _
  exact (Equiv.ofBijective f hbij).toHomeomorphOfContinuousOpen f.continuous hopen

@[simp]
theorem universalCoverSheetHomeomorph_apply [LocallyPathConnectedSpace X]
    [TauCeti.SemilocallySimplyConnectedSpace X] (U : Set X) (hU : IsOpen U)
    (hconn : IsPathConnected U) (htriv : IsPathHomotopyTrivial U) (hx : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) (z : TauCeti.UniversalCover.sheet U hx q) :
    (universalCoverSheetHomeomorph U hU hconn htriv hx q z).val = z.val.proj := rfl

end General

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The existing canonical chamber basepoint in the original complement. -/
def tubeBasepoint (C : ActualChamber M J) : Complement M J :=
  actualChamberBasepoint M J (actualChamberPointFamily M J) C

theorem tubeBasepoint_mem (C : ActualChamber M J) :
    tubeBasepoint M J C ∈ actualTubeSet M J C :=
  actualChamberBasepoint_mem_tube M J (actualChamberPointFamily M J) C C

/-- The canonical basepoint as an actual point of its tube. -/
def tubeBasepointInTube (C : ActualChamber M J) : actualTubeSet M J C :=
  ⟨tubeBasepoint M J C, tubeBasepoint_mem M J C⟩

omit [Finite M.Group] in
theorem isSimplyConnected_actualTube (C : ActualChamber M J) :
    IsSimplyConnected (actualTubeSet M J C) := by
  change SimplyConnectedSpace ↥(actualTubeSet M J C)
  infer_instance

/-- An actual chamber together with an actual fiber point over its canonical point. -/
structure LiftedTubeIndex where
  chamber : ActualChamber M J
  fiberPoint : {z : ComplementUniversalCover M J //
    complementUniversalCoverProjection M J z = tubeBasepoint M J chamber}

/-- The original path-homotopy class carried by the fiber point. -/
def liftedTubePathClass (A : LiftedTubeIndex M J) :
    Path.Homotopic.Quotient (standardComplementPoint M J) (tubeBasepoint M J A.chamber) :=
  universalCoverFiberEquivPathClasses (standardComplementPoint M J)
    (tubeBasepoint M J A.chamber) A.fiberPoint

/-- The actual open sheet in the original universal cover. -/
def liftedTubeSheet (A : LiftedTubeIndex M J) : Set (ComplementUniversalCover M J) :=
  TauCeti.UniversalCover.sheet (actualTubeSet M J A.chamber)
    (tubeBasepoint_mem M J A.chamber) (liftedTubePathClass M J A)

theorem isOpen_liftedTubeSheet (A : LiftedTubeIndex M J) : IsOpen (liftedTubeSheet M J A) :=
  TauCeti.UniversalCover.isOpen_sheet (actualTubeSet M J A.chamber)
    (isOpen_actualTubeSet M J A.chamber) (tubeBasepoint_mem M J A.chamber)
    (liftedTubePathClass M J A)

theorem liftedTubeSheet_subset_projection_preimage (A : LiftedTubeIndex M J) :
    liftedTubeSheet M J A ⊆
      complementUniversalCoverProjection M J ⁻¹' actualTubeSet M J A.chamber :=
  TauCeti.UniversalCover.sheet_subset_proj_preimage _ _ _

theorem fiberPoint_mem_liftedTubeSheet (A : LiftedTubeIndex M J) :
    A.fiberPoint.val ∈ liftedTubeSheet M J A :=
  universalCover_fiberPoint_mem_sheet _ _ A.fiberPoint

/-- The inverse endpoint projection identifies the original tube with its actual sheet. -/
def liftedTubeHomeomorph (A : LiftedTubeIndex M J) :
    actualTubeSet M J A.chamber ≃ₜ liftedTubeSheet M J A :=
  (universalCoverSheetHomeomorph (actualTubeSet M J A.chamber)
    (isOpen_actualTubeSet M J A.chamber)
    (isSimplyConnected_actualTube M J A.chamber).isPathConnected
    (isSimplyConnected_actualTube M J A.chamber).isPathHomotopyTrivial
    (tubeBasepoint_mem M J A.chamber) (liftedTubePathClass M J A)).symm

/-- A genuine continuous section into the actual universal-cover total space. -/
def liftedTubeSection (A : LiftedTubeIndex M J) :
    C(actualTubeSet M J A.chamber, ComplementUniversalCover M J) where
  toFun y := (liftedTubeHomeomorph M J A y).val
  continuous_toFun := continuous_subtype_val.comp (liftedTubeHomeomorph M J A).continuous

theorem liftedTubeSection_projection (A : LiftedTubeIndex M J)
    (y : actualTubeSet M J A.chamber) :
    complementUniversalCoverProjection M J (liftedTubeSection M J A y) = y.val :=
  congrArg Subtype.val ((liftedTubeHomeomorph M J A).symm_apply_apply y)

theorem liftedTubeSection_basepoint (A : LiftedTubeIndex M J) :
    liftedTubeSection M J A (tubeBasepointInTube M J A.chamber) = A.fiberPoint.val := by
  have he : liftedTubeHomeomorph M J A (tubeBasepointInTube M J A.chamber) =
      ⟨A.fiberPoint.val, fiberPoint_mem_liftedTubeSheet M J A⟩ := by
    -- Use the endpoint projection, the inverse of this displayed homeomorphism.
    apply (liftedTubeHomeomorph M J A).symm.injective
    rw [(liftedTubeHomeomorph M J A).symm_apply_apply]
    apply Subtype.ext
    exact A.fiberPoint.property.symm
  exact congrArg Subtype.val he

theorem range_liftedTubeSection (A : LiftedTubeIndex M J) :
    Set.range (liftedTubeSection M J A) = liftedTubeSheet M J A := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact (liftedTubeHomeomorph M J A y).property
  · intro hz
    refine ⟨(liftedTubeHomeomorph M J A).symm ⟨z, hz⟩, ?_⟩
    exact congrArg Subtype.val ((liftedTubeHomeomorph M J A).apply_symm_apply ⟨z, hz⟩)

theorem isOpen_range_liftedTubeSection (A : LiftedTubeIndex M J) :
    IsOpen (Set.range (liftedTubeSection M J A)) :=
  range_liftedTubeSection M J A ▸ isOpen_liftedTubeSheet M J A

/-- The actual section is an open embedding in the actual universal-cover topology. -/
theorem isOpenEmbedding_liftedTubeSection (A : LiftedTubeIndex M J) :
    IsOpenEmbedding (liftedTubeSection M J A) :=
  (isOpen_liftedTubeSheet M J A).isOpenEmbedding_subtypeVal.comp
    (liftedTubeHomeomorph M J A).isOpenEmbedding

/-- The section identifies its actual tube with its literal range. -/
def liftedTubeSectionHomeomorph (A : LiftedTubeIndex M J) :
    actualTubeSet M J A.chamber ≃ₜ Set.range (liftedTubeSection M J A) :=
  (liftedTubeHomeomorph M J A).trans
    (Homeomorph.setCongr (range_liftedTubeSection M J A).symm)

/-- Distinct actual fiber points give disjoint sheets over the same actual tube. -/
theorem disjoint_liftedTubeSheet_same_chamber (C : ActualChamber M J)
    {e f : {z : ComplementUniversalCover M J //
      complementUniversalCoverProjection M J z = tubeBasepoint M J C}}
    (hef : e ≠ f) :
    Disjoint (liftedTubeSheet M J ⟨C, e⟩) (liftedTubeSheet M J ⟨C, f⟩) := by
  apply TauCeti.UniversalCover.pairwise_disjoint_sheet
    (isSimplyConnected_actualTube M J C).isPathHomotopyTrivial
    (tubeBasepoint_mem M J C)
  intro he
  exact hef ((universalCoverFiberEquivPathClasses (standardComplementPoint M J)
    (tubeBasepoint M J C)).injective he)

/-- Each actual sheet is contractible because it is homeomorphic to its actual tube. -/
instance liftedTubeSheetContractible (A : LiftedTubeIndex M J) :
    ContractibleSpace (liftedTubeSheet M J A) :=
  (liftedTubeHomeomorph M J A).symm.contractibleSpace

/-- Every point of the actual universal cover belongs to one of these actual open sheets. -/
theorem exists_mem_liftedTubeSheet (z : ComplementUniversalCover M J) :
    ∃ A : LiftedTubeIndex M J, z ∈ liftedTubeSheet M J A := by
  obtain ⟨C, hC⟩ := exists_mem_actualTubeSet M J (complementUniversalCoverProjection M J z)
  have hz := TauCeti.UniversalCover.sheet_exhaustive
    (isSimplyConnected_actualTube M J C).isPathConnected (tubeBasepoint_mem M J C) hC
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
  let A : LiftedTubeIndex M J :=
    ⟨C, (universalCoverFiberEquivPathClasses (standardComplementPoint M J)
      (tubeBasepoint M J C)).symm q⟩
  refine ⟨A, ?_⟩
  change z ∈ TauCeti.UniversalCover.sheet (actualTubeSet M J C) (tubeBasepoint_mem M J C)
    ((universalCoverFiberEquivPathClasses (standardComplementPoint M J)
      (tubeBasepoint M J C)) ((universalCoverFiberEquivPathClasses (standardComplementPoint M J)
      (tubeBasepoint M J C)).symm q))
  rw [Equiv.apply_symm_apply]
  exact hq

theorem iUnion_liftedTubeSheet :
    (⋃ A : LiftedTubeIndex M J, liftedTubeSheet M J A) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact Set.mem_iUnion.mpr (exists_mem_liftedTubeSheet M J z)

/-- The actual sheets as open subsets of the original universal cover. -/
def liftedTubeOpen (A : LiftedTubeIndex M J) :
    TopologicalSpace.Opens (ComplementUniversalCover M J) :=
  ⟨liftedTubeSheet M J A, isOpen_liftedTubeSheet M J A⟩

theorem isOpenCover_liftedTube :
    TopologicalSpace.IsOpenCover (liftedTubeOpen M J) :=
  TopologicalSpace.IsOpenCover.of_sets (isOpen_liftedTubeSheet M J) (iUnion_liftedTubeSheet M J)

end ArtinNormalisers.Deligne5
