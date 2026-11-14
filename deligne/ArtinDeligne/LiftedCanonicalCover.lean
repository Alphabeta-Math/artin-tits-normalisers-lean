import ArtinDeligne.LiftedTubes
import ArtinDeligne.CanonicalCarriers

/-!
# Actual lifted canonical cells

The realized finite canonical cells lie in specified actual chamber tubes.
Intersecting their projection preimages with the genuine tube sheets gives
open contractible cells in the original universal cover. Their charts are
restrictions of the actual tube sections, and they cover the total space.
Uniqueness of lifts on a connected base proves whole-cell containment in
another tube sheet from one common point; no covering classification or
contractibility of the total space is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace ArtinNormalisers.Deligne5

open Theorem18 Chamber3 Asphericity5 Sequence4 Topology

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- Endpoint projection followed by the section recovers every actual sheet point. -/
theorem liftedTubeSection_projection_eq (A : LiftedTubeIndex M J)
    (z : ComplementUniversalCover M J) (hz : z ∈ liftedTubeSheet M J A) :
    liftedTubeSection M J A
      ⟨complementUniversalCoverProjection M J z,
        liftedTubeSheet_subset_projection_preimage M J A hz⟩ = z :=
  congrArg Subtype.val ((liftedTubeHomeomorph M J A).apply_symm_apply ⟨z, hz⟩)

/-- The section restricted to any actual base subspace contained in its tube. -/
def restrictedTubeSection (A : LiftedTubeIndex M J) (S : Set (Complement M J))
    (hS : S ⊆ actualTubeSet M J A.chamber) : C(S, ComplementUniversalCover M J) :=
  (liftedTubeSection M J A).comp
    ⟨fun x => ⟨x.val, hS x.property⟩, continuous_subtype_val.subtype_mk _⟩

theorem restrictedTubeSection_projection (A : LiftedTubeIndex M J)
    (S : Set (Complement M J)) (hS : S ⊆ actualTubeSet M J A.chamber) (x : S) :
    complementUniversalCoverProjection M J (restrictedTubeSection M J A S hS x) = x.val :=
  liftedTubeSection_projection M J A _

/-- On a preconnected actual base subspace, sections agreeing once agree everywhere.
This uses the genuine covering-map uniqueness theorem, not path-groupoid data. -/
theorem restrictedTubeSection_eq_of_eq (A B : LiftedTubeIndex M J)
    (S : Set (Complement M J)) [PreconnectedSpace S]
    (hA : S ⊆ actualTubeSet M J A.chamber) (hB : S ⊆ actualTubeSet M J B.chamber)
    (x : S) (hx : restrictedTubeSection M J A S hA x = restrictedTubeSection M J B S hB x) :
    restrictedTubeSection M J A S hA = restrictedTubeSection M J B S hB := by
  apply ContinuousMap.coe_injective
  exact (isCoveringMap_complementUniversalCoverProjection M J).eq_of_comp_eq
    (restrictedTubeSection M J A S hA).continuous
    (restrictedTubeSection M J B S hB).continuous
    (funext fun y => (restrictedTubeSection_projection M J A S hA y).trans
      (restrictedTubeSection_projection M J B S hB y).symm) x hx

/-- The actual sheets above any specified tube exhaust its whole projection preimage. -/
theorem exists_mem_liftedTubeSheet_at_chamber (C : ActualChamber M J)
    (z : ComplementUniversalCover M J)
    (hz : complementUniversalCoverProjection M J z ∈ actualTubeSet M J C) :
    ∃ e : {w : ComplementUniversalCover M J //
      complementUniversalCoverProjection M J w = tubeBasepoint M J C},
      z ∈ liftedTubeSheet M J ⟨C, e⟩ := by
  have hs := TauCeti.UniversalCover.sheet_exhaustive
    (isSimplyConnected_actualTube M J C).isPathConnected (tubeBasepoint_mem M J C) hz
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hs
  refine ⟨(universalCoverFiberEquivPathClasses (standardComplementPoint M J)
    (tubeBasepoint M J C)).symm q, ?_⟩
  change z ∈ TauCeti.UniversalCover.sheet _ _
    ((universalCoverFiberEquivPathClasses (standardComplementPoint M J)
      (tubeBasepoint M J C)) ((universalCoverFiberEquivPathClasses (standardComplementPoint M J)
      (tubeBasepoint M J C)).symm q))
  rw [Equiv.apply_symm_apply]
  exact hq

/-- A realized canonical type and an actual fiber point over its specified tube basepoint. -/
structure LiftedCanonicalIndex where
  base : actualCanonicalType M J
  fiberPoint : {z : ComplementUniversalCover M J // complementUniversalCoverProjection M J z =
    tubeBasepoint M J (actualCanonicalTypeChamber M J base)}

abbrev LiftedCanonicalIndex.toLiftedTubeIndex (A : LiftedCanonicalIndex M J) : LiftedTubeIndex M J :=
  ⟨actualCanonicalTypeChamber M J A.base, A.fiberPoint⟩

/-- The literal lifted canonical open subset of the actual universal cover. -/
def liftedCanonicalSet (A : LiftedCanonicalIndex M J) : Set (ComplementUniversalCover M J) :=
  liftedTubeSheet M J A.toLiftedTubeIndex ∩
    complementUniversalCoverProjection M J ⁻¹' actualCanonicalTypeSet M J A.base

theorem isOpen_liftedCanonicalSet (A : LiftedCanonicalIndex M J) :
    IsOpen (liftedCanonicalSet M J A) :=
  (isOpen_liftedTubeSheet M J A.toLiftedTubeIndex).inter
    ((isOpen_actualCanonicalTypeSet M J A.base).preimage
      (continuous_complementUniversalCoverProjection M J))

/-- The genuine section restricted to the actual canonical cell is its sheet chart. -/
def liftedCanonicalHomeomorph (A : LiftedCanonicalIndex M J) :
    actualCanonicalTypeSet M J A.base ≃ₜ liftedCanonicalSet M J A where
  toFun x := ⟨restrictedTubeSection M J A.toLiftedTubeIndex _
      (actualCanonicalTypeSet_subset_actualTubeSet M J A.base) x,
    ⟨(liftedTubeHomeomorph M J A.toLiftedTubeIndex _).property,
      by
        change complementUniversalCoverProjection M J
          (restrictedTubeSection M J A.toLiftedTubeIndex _
            (actualCanonicalTypeSet_subset_actualTubeSet M J A.base) x) ∈
            actualCanonicalTypeSet M J A.base
        rw [restrictedTubeSection_projection M J A.toLiftedTubeIndex _
          (actualCanonicalTypeSet_subset_actualTubeSet M J A.base) x]
        exact x.property⟩⟩
  invFun z := ⟨complementUniversalCoverProjection M J z.val, z.property.2⟩
  left_inv x := Subtype.ext (restrictedTubeSection_projection M J A.toLiftedTubeIndex _
    (actualCanonicalTypeSet_subset_actualTubeSet M J A.base) x)
  right_inv z := Subtype.ext (liftedTubeSection_projection_eq M J A.toLiftedTubeIndex _ z.property.1)
  continuous_toFun := (restrictedTubeSection M J A.toLiftedTubeIndex _
    (actualCanonicalTypeSet_subset_actualTubeSet M J A.base)).continuous.subtype_mk _
  continuous_invFun :=
    ((continuous_complementUniversalCoverProjection M J).comp continuous_subtype_val).subtype_mk _

@[simp]
theorem liftedCanonicalHomeomorph_projection (A : LiftedCanonicalIndex M J)
    (x : actualCanonicalTypeSet M J A.base) :
    complementUniversalCoverProjection M J (liftedCanonicalHomeomorph M J A x).val = x.val :=
  restrictedTubeSection_projection M J A.toLiftedTubeIndex _
    (actualCanonicalTypeSet_subset_actualTubeSet M J A.base) x

/-- The lift of the actual selected center, with no arbitrary total-space choice. -/
def liftedCanonicalCenter (A : LiftedCanonicalIndex M J) : ComplementUniversalCover M J :=
  (liftedCanonicalHomeomorph M J A
    ⟨actualCanonicalCenter M J A.base, actualCanonicalCenter_mem M J A.base⟩).val

theorem liftedCanonicalCenter_mem (A : LiftedCanonicalIndex M J) :
    liftedCanonicalCenter M J A ∈ liftedCanonicalSet M J A :=
  (liftedCanonicalHomeomorph M J A _).property

@[simp]
theorem liftedCanonicalCenter_projection (A : LiftedCanonicalIndex M J) :
    complementUniversalCoverProjection M J (liftedCanonicalCenter M J A) =
      actualCanonicalCenter M J A.base := liftedCanonicalHomeomorph_projection M J A _

instance liftedCanonicalSetContractible (A : LiftedCanonicalIndex M J) :
    ContractibleSpace (liftedCanonicalSet M J A) := by
  let := contractibleSpace_actualCanonicalTypeSet M J A.base
  exact (liftedCanonicalHomeomorph M J A).symm.contractibleSpace

/-- A common point forces the whole connected lifted cell into a containing tube sheet. -/
theorem liftedCanonicalSet_subset_liftedTubeSheet (A : LiftedCanonicalIndex M J)
    (B : LiftedTubeIndex M J)
    (hbase : actualCanonicalTypeSet M J A.base ⊆ actualTubeSet M J B.chamber)
    (hne : (liftedCanonicalSet M J A ∩ liftedTubeSheet M J B).Nonempty) :
    liftedCanonicalSet M J A ⊆ liftedTubeSheet M J B := by
  let := contractibleSpace_actualCanonicalTypeSet M J A.base
  obtain ⟨z, hzA, hzB⟩ := hne
  let x : actualCanonicalTypeSet M J A.base := ⟨_, hzA.2⟩
  have he := restrictedTubeSection_eq_of_eq M J A.toLiftedTubeIndex B
    (actualCanonicalTypeSet M J A.base)
    (actualCanonicalTypeSet_subset_actualTubeSet M J A.base) hbase x
    ((liftedTubeSection_projection_eq M J A.toLiftedTubeIndex z hzA.1).trans
      (liftedTubeSection_projection_eq M J B z hzB).symm)
  intro w hw
  have hew := congrArg (fun f => f (⟨_, hw.2⟩ : actualCanonicalTypeSet M J A.base)) he
  have hwA := liftedTubeSection_projection_eq M J A.toLiftedTubeIndex w hw.1
  have hwB : restrictedTubeSection M J B (actualCanonicalTypeSet M J A.base) hbase
      ⟨complementUniversalCoverProjection M J w, hw.2⟩ ∈ liftedTubeSheet M J B :=
    (liftedTubeHomeomorph M J B _).property
  rw [← hew] at hwB
  change (liftedTubeSection M J A.toLiftedTubeIndex
    ⟨complementUniversalCoverProjection M J w, _⟩) ∈ liftedTubeSheet M J B at hwB
  rwa [hwA] at hwB

theorem exists_mem_liftedCanonicalSet (z : ComplementUniversalCover M J) :
    ∃ A : LiftedCanonicalIndex M J, z ∈ liftedCanonicalSet M J A := by
  have h := Set.eq_univ_iff_forall.mp (iUnion_actualCanonicalTypeSet M J)
    (complementUniversalCoverProjection M J z)
  obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp h
  obtain ⟨e, he⟩ := exists_mem_liftedTubeSheet_at_chamber M J
    (actualCanonicalTypeChamber M J σ) z
    (actualCanonicalTypeSet_subset_actualTubeSet M J σ hσ)
  exact ⟨⟨σ, e⟩, he, hσ⟩

theorem iUnion_liftedCanonicalSet :
    (⋃ A : LiftedCanonicalIndex M J, liftedCanonicalSet M J A) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact Set.mem_iUnion.mpr (exists_mem_liftedCanonicalSet M J z)

def liftedCanonicalOpen (A : LiftedCanonicalIndex M J) :
    TopologicalSpace.Opens (ComplementUniversalCover M J) :=
  ⟨liftedCanonicalSet M J A, isOpen_liftedCanonicalSet M J A⟩

theorem isOpenCover_liftedCanonical : TopologicalSpace.IsOpenCover (liftedCanonicalOpen M J) :=
  TopologicalSpace.IsOpenCover.of_sets (isOpen_liftedCanonicalSet M J)
    (iUnion_liftedCanonicalSet M J)

end ArtinNormalisers.Deligne5
