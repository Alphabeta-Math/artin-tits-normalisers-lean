import ArtinDeligne.LiftedCanonicalCover
import ArtinChambers.TubeIntersections
import ArtinChambers.IntervalForward

/-!
# Actual components of arbitrary lifted-tube intersections

A nonempty sheet family and a point of its intersection determine a real
sign piece downstairs. Covering uniqueness identifies the sheet sections
on that entire contractible piece. This gives an actual homeomorphism to
the connected component upstairs, with no contractibility assumption on
the total universal cover.
-/

set_option autoImplicit false

noncomputable section

namespace ArtinNormalisers.Deligne5

open Theorem18 Chamber3 Asphericity5 Sequence4 Topology

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

def liftedTubeIntersection (F : Set (LiftedTubeIndex M J)) :
    Set (ComplementUniversalCover M J) := ⋂ A ∈ F, liftedTubeSheet M J A

theorem mem_liftedTubeIntersection_iff (F : Set (LiftedTubeIndex M J))
    (q : ComplementUniversalCover M J) :
    q ∈ liftedTubeIntersection M J F ↔ ∀ A ∈ F, q ∈ liftedTubeSheet M J A := by
  simp only [liftedTubeIntersection, Set.mem_iInter]

def liftedTubeChambers (F : Set (LiftedTubeIndex M J)) : Set (ActualChamber M J) :=
  (fun A => A.chamber) '' F

theorem liftedTubeChambers_nonempty {F : Set (LiftedTubeIndex M J)} (hF : F.Nonempty) :
    (liftedTubeChambers M J F).Nonempty := hF.image _

def liftedTubeProjectionPoint (q : ComplementUniversalCover M J) :
    ComplexComplement (E := relativeSubspace J) (actualForms M J) :=
  actualComplementHomeomorph M J (complementUniversalCoverProjection M J q)

def liftedTubeRealSigns (q : ComplementUniversalCover M J) : RelativeRoot M J → Bool :=
  fun h => decide (0 < actualForms M J h (liftedTubeProjectionPoint M J q).val.1)

/-- The literal base sign piece in the original complement topology. -/
def liftedTubeBasePiece (F : Set (LiftedTubeIndex M J)) (q : ComplementUniversalCover M J) :
    Set (Complement M J) :=
  actualComplementHomeomorph M J ⁻¹'
    tubeIntersectionPiece (liftedTubeChambers M J F) (liftedTubeRealSigns M J q)

def liftedTubeBasePieceHomeomorph (F : Set (LiftedTubeIndex M J))
    (q : ComplementUniversalCover M J) : liftedTubeBasePiece M J F q ≃ₜ
      tubeIntersectionPiece (liftedTubeChambers M J F) (liftedTubeRealSigns M J q) :=
  (actualComplementHomeomorph M J).subtype (fun _ => Iff.rfl)

theorem projectionPoint_mem_tubeIntersection {F : Set (LiftedTubeIndex M J)}
    {q : ComplementUniversalCover M J} (hq : q ∈ liftedTubeIntersection M J F) :
    liftedTubeProjectionPoint M J q ∈ tubeIntersection (liftedTubeChambers M J F) := by
  rintro C ⟨A, hA, rfl⟩
  exact liftedTubeSheet_subset_projection_preimage M J A
    ((mem_liftedTubeIntersection_iff M J F q).mp hq A hA)

theorem projection_mem_liftedTubeBasePiece {F : Set (LiftedTubeIndex M J)}
    {q : ComplementUniversalCover M J} (hq : q ∈ liftedTubeIntersection M J F) :
    complementUniversalCoverProjection M J q ∈ liftedTubeBasePiece M J F q := by
  refine ⟨projectionPoint_mem_tubeIntersection M J hq, ?_⟩
  intro h hd
  have hn := tubeIntersection_real_ne_zero (projectionPoint_mem_tubeIntersection M J hq) hd
  change (liftedTubeProjectionPoint M J q).val.1 ∈
    signHalfSpace (actualForms M J h)
      (decide (0 < actualForms M J h (liftedTubeProjectionPoint M J q).val.1))
  by_cases hp : 0 < actualForms M J h (liftedTubeProjectionPoint M J q).val.1
  · simpa only [signHalfSpace, Set.mem_ofPred_eq, decide_eq_true hp, ↓reduceIte] using hp
  · have hm := lt_of_le_of_ne (le_of_not_gt hp) hn
    simpa only [signHalfSpace, Set.mem_ofPred_eq, decide_eq_false hp, Bool.false_eq_true, ↓reduceIte] using hm

theorem liftedTubeBasePiece_subset_tube (F : Set (LiftedTubeIndex M J))
    (q : ComplementUniversalCover M J) (A : LiftedTubeIndex M J) (hA : A ∈ F) :
    liftedTubeBasePiece M J F q ⊆ actualTubeSet M J A.chamber := by
  intro x hx
  exact hx.1 A.chamber ⟨A, hA, rfl⟩

theorem contractibleSpace_liftedTubeBasePiece {F : Set (LiftedTubeIndex M J)}
    (hF : F.Nonempty) {q : ComplementUniversalCover M J}
    (hq : q ∈ liftedTubeIntersection M J F) : ContractibleSpace (liftedTubeBasePiece M J F q) :=
  (liftedTubeBasePieceHomeomorph M J F q).contractibleSpace_iff.mpr
    (contractibleSpace_tubeIntersectionPiece (liftedTubeChambers_nonempty M J hF)
      ⟨_, projection_mem_liftedTubeBasePiece M J hq⟩)

/-- Sections over any selected member coincide on the entire actual base
piece. Agreement at the given total-space point is proved by sheet inverses. -/
theorem restrictedTubeSection_eq_on_basePiece {F : Set (LiftedTubeIndex M J)}
    (hF : F.Nonempty) {q : ComplementUniversalCover M J}
    (hq : q ∈ liftedTubeIntersection M J F) (A B : LiftedTubeIndex M J)
    (hA : A ∈ F) (hB : B ∈ F) :
    restrictedTubeSection M J A (liftedTubeBasePiece M J F q)
      (liftedTubeBasePiece_subset_tube M J F q A hA) =
    restrictedTubeSection M J B (liftedTubeBasePiece M J F q)
      (liftedTubeBasePiece_subset_tube M J F q B hB) := by
  let := contractibleSpace_liftedTubeBasePiece M J hF hq
  apply restrictedTubeSection_eq_of_eq M J A B _ _ _
    ⟨_, projection_mem_liftedTubeBasePiece M J hq⟩
  exact (liftedTubeSection_projection_eq M J A q
    ((mem_liftedTubeIntersection_iff M J F q).mp hq A hA)).trans
    (liftedTubeSection_projection_eq M J B q
      ((mem_liftedTubeIntersection_iff M J F q).mp hq B hB)).symm

/-- The selected section sends the whole base component into every sheet. -/
theorem restrictedTubeSection_basePiece_mem_intersection {F : Set (LiftedTubeIndex M J)}
    (hF : F.Nonempty) {q : ComplementUniversalCover M J}
    (hq : q ∈ liftedTubeIntersection M J F) (A : LiftedTubeIndex M J) (hA : A ∈ F)
    (x : liftedTubeBasePiece M J F q) :
    restrictedTubeSection M J A (liftedTubeBasePiece M J F q)
      (liftedTubeBasePiece_subset_tube M J F q A hA) x ∈ liftedTubeIntersection M J F := by
  apply (mem_liftedTubeIntersection_iff M J F _).mpr
  intro B hB
  rw [restrictedTubeSection_eq_on_basePiece M J hF hq A B hA hB]
  exact (liftedTubeHomeomorph M J B _).property


/-- The actual chosen section image is connected and contains the common
point, so it lies in the indicated upstairs component. -/
theorem restrictedTubeSection_basePiece_mem_component {F : Set (LiftedTubeIndex M J)}
    (hF : F.Nonempty) {q : ComplementUniversalCover M J}
    (hq : q ∈ liftedTubeIntersection M J F) (A : LiftedTubeIndex M J) (hA : A ∈ F)
    (x : liftedTubeBasePiece M J F q) :
    restrictedTubeSection M J A (liftedTubeBasePiece M J F q)
      (liftedTubeBasePiece_subset_tube M J F q A hA) x ∈
      connectedComponentIn (liftedTubeIntersection M J F) q := by
  let := contractibleSpace_liftedTubeBasePiece M J hF hq
  let f := restrictedTubeSection M J A (liftedTubeBasePiece M J F q)
    (liftedTubeBasePiece_subset_tube M J F q A hA)
  have hqrange : q ∈ Set.range f :=
    ⟨⟨_, projection_mem_liftedTubeBasePiece M J hq⟩,
      liftedTubeSection_projection_eq M J A q
        ((mem_liftedTubeIntersection_iff M J F q).mp hq A hA)⟩
  have hsub : Set.range f ⊆ liftedTubeIntersection M J F := by
    rintro y ⟨z, rfl⟩
    exact restrictedTubeSection_basePiece_mem_intersection M J hF hq A hA z
  exact (isPreconnected_range f.continuous).subset_connectedComponentIn hqrange hsub
    ⟨x, rfl⟩

/-- Projection of the actual upstairs component stays in the precise
base sign piece, by continuous images of connected components. -/
theorem component_projection_mem_basePiece {F : Set (LiftedTubeIndex M J)}
    (hF : F.Nonempty) {q : ComplementUniversalCover M J}
    (hq : q ∈ liftedTubeIntersection M J F)
    {z : ComplementUniversalCover M J}
    (hz : z ∈ connectedComponentIn (liftedTubeIntersection M J F) q) :
    complementUniversalCoverProjection M J z ∈ liftedTubeBasePiece M J F q := by
  let f : ComplementUniversalCover M J →
      ComplexComplement (E := relativeSubspace J) (actualForms M J) :=
    liftedTubeProjectionPoint M J
  have hf : Continuous f := (actualComplementHomeomorph M J).continuous.comp
    (continuous_complementUniversalCoverProjection M J)
  have hsub : f '' liftedTubeIntersection M J F ⊆
      tubeIntersection (liftedTubeChambers M J F) := by
    rintro p ⟨y, hy, rfl⟩
    exact projectionPoint_mem_tubeIntersection M J hy
  have hmem := (hf.continuousOn.image_connectedComponentIn_subset hq) ⟨z, hz, rfl⟩
  have hmem' := connectedComponentIn_mono (f q) hsub hmem
  have he := tubeIntersectionPiece_eq_connectedComponentIn
    (liftedTubeChambers_nonempty M J hF) (projection_mem_liftedTubeBasePiece M J hq)
  change f z ∈ tubeIntersectionPiece (liftedTubeChambers M J F) (liftedTubeRealSigns M J q)
  rw [he]
  exact hmem'

/-- The genuine base-piece section is a homeomorphism onto the exact
connected component of the arbitrary nonempty lifted-tube intersection. -/
def liftedTubeComponentHomeomorph (F : Set (LiftedTubeIndex M J)) (hF : F.Nonempty)
    (q : ComplementUniversalCover M J) (hq : q ∈ liftedTubeIntersection M J F) :
    liftedTubeBasePiece M J F q ≃ₜ connectedComponentIn (liftedTubeIntersection M J F) q where
  toFun x := ⟨restrictedTubeSection M J hF.choose (liftedTubeBasePiece M J F q)
      (liftedTubeBasePiece_subset_tube M J F q hF.choose hF.choose_spec) x,
    restrictedTubeSection_basePiece_mem_component M J hF hq hF.choose hF.choose_spec x⟩
  invFun z := ⟨complementUniversalCoverProjection M J z.val,
    component_projection_mem_basePiece M J hF hq z.property⟩
  left_inv x := Subtype.ext (restrictedTubeSection_projection M J hF.choose (liftedTubeBasePiece M J F q)
    (liftedTubeBasePiece_subset_tube M J F q hF.choose hF.choose_spec) x)
  right_inv z := by
    apply Subtype.ext
    apply liftedTubeSection_projection_eq M J hF.choose z.val
    exact (mem_liftedTubeIntersection_iff M J F z.val).mp
      (connectedComponentIn_subset (liftedTubeIntersection M J F) q z.property)
      hF.choose hF.choose_spec
  continuous_toFun := (restrictedTubeSection M J hF.choose (liftedTubeBasePiece M J F q)
    (liftedTubeBasePiece_subset_tube M J F q hF.choose hF.choose_spec)).continuous.subtype_mk _
  continuous_invFun :=
    ((continuous_complementUniversalCoverProjection M J).comp continuous_subtype_val).subtype_mk _


@[simp] theorem liftedTubeComponentHomeomorph_projection
    (F : Set (LiftedTubeIndex M J)) (hF : F.Nonempty)
    (q : ComplementUniversalCover M J) (hq : q ∈ liftedTubeIntersection M J F)
    (x : liftedTubeBasePiece M J F q) :
    complementUniversalCoverProjection M J
      (liftedTubeComponentHomeomorph M J F hF q hq x).val = x.val :=
  restrictedTubeSection_projection M J hF.choose (liftedTubeBasePiece M J F q)
    (liftedTubeBasePiece_subset_tube M J F q hF.choose hF.choose_spec) x

/-- A single selected sheet and the base sign piece characterize the exact
upstairs component, independently of the section choice. -/
theorem mem_liftedTubeIntersectionComponent_iff
    {F : Set (LiftedTubeIndex M J)} (hF : F.Nonempty)
    {q : ComplementUniversalCover M J} (hq : q ∈ liftedTubeIntersection M J F)
    (A : LiftedTubeIndex M J) (hA : A ∈ F) (z : ComplementUniversalCover M J) :
    z ∈ connectedComponentIn (liftedTubeIntersection M J F) q ↔
      z ∈ liftedTubeSheet M J A ∧
        complementUniversalCoverProjection M J z ∈ liftedTubeBasePiece M J F q := by
  constructor
  · intro hz
    exact ⟨(mem_liftedTubeIntersection_iff M J F z).mp
      (connectedComponentIn_subset (liftedTubeIntersection M J F) q hz) A hA,
      component_projection_mem_basePiece M J hF hq hz⟩
  · rintro ⟨hz, hp⟩
    have hmem := restrictedTubeSection_basePiece_mem_component M J hF hq A hA
      ⟨complementUniversalCoverProjection M J z, hp⟩
    change liftedTubeSection M J A ⟨complementUniversalCoverProjection M J z, _⟩ ∈ _ at hmem
    rwa [liftedTubeSection_projection_eq M J A z hz] at hmem

/-- Every realized component is contractible in its original total-space
subspace topology; the whole intersection need not be connected. -/
theorem contractibleSpace_liftedTubeIntersectionComponent
    (F : Set (LiftedTubeIndex M J)) (hF : F.Nonempty)
    (q : ComplementUniversalCover M J) (hq : q ∈ liftedTubeIntersection M J F) :
    ContractibleSpace (connectedComponentIn (liftedTubeIntersection M J F) q) := by
  let := contractibleSpace_liftedTubeBasePiece M J hF hq
  exact (liftedTubeComponentHomeomorph M J F hF q hq).symm.contractibleSpace

/-- The same actual connected component is path connected. -/
theorem isPathConnected_liftedTubeIntersectionComponent
    (F : Set (LiftedTubeIndex M J)) (hF : F.Nonempty)
    (q : ComplementUniversalCover M J) (hq : q ∈ liftedTubeIntersection M J F) :
    IsPathConnected (connectedComponentIn (liftedTubeIntersection M J F) q) := by
  let := contractibleSpace_liftedTubeIntersectionComponent M J F hF q hq
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance


section SharedUpperPaths

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} {ℓ : H → E →L[ℝ] ℝ}

/-- On a wall where upper chambers disagree, the middle chamber retains
the lower chamber's sign. The family can be arbitrary or empty. -/
theorem sharedUpper_middle_sign (A B : Chamber ℓ) (U : Set (Chamber ℓ))
    (hb : ∀ C ∈ U, ChamberBetween A B C) {h : H}
    (hd : tubeDisagreement (insert B U) h) : B.signs h = A.signs h := by
  by_contra hne
  have hall : ∀ C ∈ insert B U, C.signs h = B.signs h := by
    intro C hC
    rcases Set.mem_insert_iff.mp hC with rfl | hC
    · rfl
    · have hh := hb C hC h
      cases ha : A.signs h <;> cases hb' : B.signs h <;> cases hc : C.signs h <;>
        simp_all
  obtain ⟨C, hC, D, hD, hCD⟩ := hd
  exact hCD ((hall C hC).trans (hall D hD).symm)

/-- Both actual real chamber points belong to one sign piece of all the
upper tubes simultaneously. -/
theorem basepoints_mem_sharedUpperPiece (c : ChamberPointFamily ℓ)
    (A B : Chamber ℓ) (U : Set (Chamber ℓ)) (hb : ∀ C ∈ U, ChamberBetween A B C) :
    chamberBasepoint c A ∈ tubeIntersectionPiece (insert B U) A.signs ∧
      chamberBasepoint c B ∈ tubeIntersectionPiece (insert B U) A.signs := by
  constructor
  · exact ⟨fun C _ => chamberBasepoint_mem_tubeSet c A C, fun h _ => (c A).property h⟩
  · refine ⟨fun C _ => chamberBasepoint_mem_tubeSet c B C, fun h hd => ?_⟩
    rw [← sharedUpper_middle_sign A B U hb hd]
    exact (c B).property h

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A single genuine path represents the positive A-to-B arrow while
remaining in every specified upper tube. -/
theorem exists_positivePath_sharedUpper (c : ChamberPointFamily ℓ)
    (A B : Chamber ℓ) (U : Set (Chamber ℓ)) (hb : ∀ C ∈ U, ChamberBetween A B C) :
    ∃ γ : Path (chamberBasepoint c A) (chamberBasepoint c B),
      (∀ t, γ t ∈ tubeIntersectionPiece (insert B U) A.signs) ∧
      IntervalForward.positiveClass c A B = Path.Homotopic.Quotient.mk γ := by
  obtain ⟨hA, hB⟩ := basepoints_mem_sharedUpperPiece c A B U hb
  have hfamily : (insert B U).Nonempty := ⟨B, Set.mem_insert B U⟩
  obtain ⟨γ, hγ⟩ := (isPathConnected_tubeIntersectionPiece hfamily ⟨_, hA⟩).joinedIn _ hA _ hB
  exact ⟨γ, hγ, IntervalForward.classInTube_eq_path B _ _ γ
    (fun t => (hγ t).1 B (Set.mem_insert B U))⟩

end SharedUpperPaths

omit [Finite M.Group] in
/-- The shared-upper path in the original article complement, with its
actual canonical real basepoints and its original topology. -/
theorem exists_actualPositivePath_sharedUpper
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J))
    (A B : ActualChamber M J) (U : Set (ActualChamber M J))
    (hb : ∀ C ∈ U, ChamberBetween A B C) :
    ∃ γ : Path (actualChamberBasepoint M J c A) (actualChamberBasepoint M J c B),
      ∀ t, ∀ C ∈ insert B U, γ t ∈ actualTubeSet M J C := by
  obtain ⟨γ, hγ, _⟩ := exists_positivePath_sharedUpper c A B U hb
  refine ⟨γ.map (actualComplementHomeomorph M J).symm.continuous, ?_⟩
  intro t C hC
  change actualComplementHomeomorph M J
    ((actualComplementHomeomorph M J).symm (γ t)) ∈ tubeSet C
  rw [Homeomorph.apply_symm_apply]
  exact (hγ t).1 C hC


omit [Finite M.Group] in
/-- The same path represents the actual interval-positive image, while its
entire range remains simultaneously in the whole family of target tubes. -/
theorem exists_actualPositiveClass_sharedUpper
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J))
    (A B : ActualChamber M J) (U : Set (ActualChamber M J))
    (hb : ∀ C ∈ U, ChamberBetween A B C) :
    ∃ γ : Path (actualChamberBasepoint M J c A) (actualChamberBasepoint M J c B),
      (∀ t, ∀ C ∈ insert B U, γ t ∈ actualTubeSet M J C) ∧
      (actualIntervalForwardOfPoints M J c).map (intervalPositive A B) =
        Path.Homotopic.Quotient.mk γ := by
  obtain ⟨γ, hγ⟩ := exists_actualPositivePath_sharedUpper M J c A B U hb
  exact ⟨γ, hγ, actualIntervalForwardOfPoints_positive_eq_path M J c A B γ
    (fun t => hγ t B (Set.mem_insert B U))⟩

end ArtinNormalisers.Deligne5
