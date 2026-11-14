module

public import ArtinChambers.FaceProjection
public import ArtinChambers.TubeCover
public import ArtinChamberVendor.AlgebraicTopology.FundamentalGroupoid.Glue
public import Mathlib.CategoryTheory.NatIso

/-!
# Descent from actual complement paths to the interval groupoid

The local functors use one common chamber selector on their objects. Face
connectors supply their gauge maps. The connector cocycle and its proved
local constancy on actual overlaps establish strict agreement of these local
functors. The verified Tau Ceti gluing theorem then constructs the global
functor; its objects are copied to the explicit selector for transparent use.

The only external gluing proof used is the source-bound verified
`ArtinChamberVendor.AlgebraicTopology.FundamentalGroupoid.Glue`, originally
`TauCeti.AlgebraicTopology.FundamentalGroupoid.Glue`. No comparison
equivalence is assumed here.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open CategoryTheory

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} [Finite H] (ℓ : H → E →L[ℝ] ℝ)

/-- One cover selector, used for every local object map. -/
noncomputable def chosenCoverChamber (p : ComplexComplement ℓ) : Chamber ℓ :=
  Classical.choose (exists_mem_tubeSet ℓ p)

theorem chosenCoverChamber_mem (p : ComplexComplement ℓ) :
    p ∈ tubeSet (chosenCoverChamber ℓ p) :=
  Classical.choose_spec (exists_mem_tubeSet ℓ p)

/-- A gauge from the common selector to the indicated tube chamber. -/
noncomputable def tubeGauge (C : Chamber ℓ) (p : ComplexComplement ℓ) :
    intervalObject (chosenCoverChamber ℓ p) ⟶ intervalObject C :=
  faceIntervalConnector ℓ p.val.1 (chosenCoverChamber ℓ p) C

omit [Finite H] in
private theorem tube_signs_agree_zero {A B : Chamber ℓ} {p : ComplexComplement ℓ}
    (hA : p ∈ tubeSet A) (hB : p ∈ tubeSet B) :
    ∀ h, ℓ h p.val.1 = 0 → A.signs h = B.signs h := by
  intro h hz
  by_contra hne
  have hp : p ∈ tubeIntersection ({A, B} : Set (Chamber ℓ)) := by
    intro C hC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · exact hA
    · exact hB
  exact tubeIntersection_real_ne_zero hp ⟨A, by simp, B, by simp, hne⟩ hz

theorem faceChamber_eq_of_mem_tubes {A B : Chamber ℓ} {p : ComplexComplement ℓ}
    (hA : p ∈ tubeSet A) (hB : p ∈ tubeSet B) :
    faceChamber ℓ p.val.1 A = faceChamber ℓ p.val.1 B :=
  faceChamber_eq_of_signs_on_zero ℓ _ A B (tube_signs_agree_zero ℓ hA hB)

/-- At an actual common tube point, the face connectors satisfy the cocycle. -/
theorem faceIntervalConnector_cocycle {A B C : Chamber ℓ} {p : ComplexComplement ℓ}
    (hA : p ∈ tubeSet A) (hB : p ∈ tubeSet B) (_hC : p ∈ tubeSet C) :
    faceIntervalConnector ℓ p.val.1 A B ≫ faceIntervalConnector ℓ p.val.1 B C =
      faceIntervalConnector ℓ p.val.1 A C := by
  have hface := faceChamber_eq_of_mem_tubes ℓ hB hA
  have he := congrArg (fun F : Chamber ℓ =>
    inv (intervalPositive F B) ≫ intervalPositive F C) hface
  change faceIntervalConnector ℓ p.val.1 A B ≫
    (inv (intervalPositive (faceChamber ℓ p.val.1 B) B) ≫
      intervalPositive (faceChamber ℓ p.val.1 B) C) = _
  rw [he]
  simp [faceIntervalConnector, Category.assoc]

theorem tubeGauge_change {C D : Chamber ℓ} {p : ComplexComplement ℓ}
    (hC : p ∈ tubeSet C) (hD : p ∈ tubeSet D) :
    tubeGauge ℓ D p = tubeGauge ℓ C p ≫ faceIntervalConnector ℓ p.val.1 C D :=
  (faceIntervalConnector_cocycle ℓ (chosenCoverChamber_mem ℓ p) hC hD).symm

/-- The connector is locally constant on the entire actual two-tube
intersection; separate connected components may have different values. -/
theorem isLocallyConstant_tubeConnector (C D : Chamber ℓ) :
    IsLocallyConstant (fun p : ↥(tubeSet C ∩ tubeSet D) =>
      faceIntervalConnector ℓ p.val.val.1 C D) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro p
  let U := nonzeroSignRegion ℓ p.val.val.1
  have hreal : Continuous (fun q : ↥(tubeSet C ∩ tubeSet D) => q.val.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hU : IsOpen U := isOpen_nonzeroSignRegion ℓ _
  have hpU : p.val.val.1 ∈ U := mem_nonzeroSignRegion_self ℓ _
  apply Filter.eventually_of_mem ((hU.preimage hreal).mem_nhds hpU)
  intro q hq
  exact faceIntervalConnector_eq_of_mem_nonzeroSignRegion ℓ
    (tube_signs_agree_zero ℓ p.property.1 p.property.2) hq

theorem tubeConnector_eq_of_path (C D : Chamber ℓ)
    {p q : ↥(tubeSet C ∩ tubeSet D)} (γ : Path p q) :
    faceIntervalConnector ℓ p.val.val.1 C D = faceIntervalConnector ℓ q.val.val.1 C D := by
  have h := (isLocallyConstant_tubeConnector ℓ C D).comp_continuous γ.continuous
  have he := h.apply_eq_of_preconnectedSpace 0 1
  simpa only [Function.comp_apply, γ.source, γ.target] using he

/-- Each actual tube has a local functor with the same selector object map. -/
noncomputable def tubeLocalFunctor (C : Chamber ℓ) :
    FundamentalGroupoid (tubeSet C) ⥤ IntervalGroupoid ℓ where
  obj p := intervalObject (chosenCoverChamber ℓ p.as.val)
  map {p q} _ := tubeGauge ℓ C p.as.val ≫ inv (tubeGauge ℓ C q.as.val)
  map_id p := by simp
  map_comp f g := by simp [Category.assoc]

/-- Actual overlap paths make the two local functors strictly equal. -/
theorem tubeLocalFunctor_agree (C D : Chamber ℓ) :
    FundamentalGroupoid.map
        (ContinuousMap.inclusion (Set.inter_subset_left : tubeSet C ∩ tubeSet D ⊆ tubeSet C)) ⋙
          tubeLocalFunctor ℓ C =
      FundamentalGroupoid.map
        (ContinuousMap.inclusion (Set.inter_subset_right : tubeSet C ∩ tubeSet D ⊆ tubeSet D)) ⋙
          tubeLocalFunctor ℓ D := by
  refine Functor.hext ?_ ?_
  · intro p; rfl
  intro p q γ
  apply heq_of_eq
  change tubeGauge ℓ C p.as.val ≫ inv (tubeGauge ℓ C q.as.val) =
    tubeGauge ℓ D p.as.val ≫ inv (tubeGauge ℓ D q.as.val)
  obtain ⟨γ, _⟩ := Path.Homotopic.Quotient.mk_surjective γ
  have hconn := tubeConnector_eq_of_path ℓ C D γ
  have hp := tubeGauge_change ℓ p.as.property.1 p.as.property.2
  have hq := tubeGauge_change ℓ q.as.property.1 q.as.property.2
  simp [hp, hq, ← hconn, Category.assoc]

theorem tube_neighborhood_cover (p : ComplexComplement ℓ) :
    ∃ C : Chamber ℓ, tubeSet C ∈ nhds p := by
  obtain ⟨C, hp⟩ := exists_mem_tubeSet ℓ p
  exact ⟨C, (isOpen_tubeSet C).mem_nhds hp⟩

/-- The verified strict gluing construction on the actual tubes. -/
noncomputable def gluedTubeDescent :
    FundamentalGroupoid (ComplexComplement ℓ) ⥤ IntervalGroupoid ℓ :=
  TauCeti.FundamentalGroupoid.glue (tube_neighborhood_cover ℓ)
    (tubeLocalFunctor ℓ) (tubeLocalFunctor_agree ℓ)

theorem gluedTubeDescent_obj (p : ComplexComplement ℓ) :
    (gluedTubeDescent ℓ).obj (FundamentalGroupoid.mk p) =
      intervalObject (chosenCoverChamber ℓ p) :=
  TauCeti.FundamentalGroupoid.glue_obj_mk (tube_neighborhood_cover ℓ)
    (tubeLocalFunctor ℓ) (tubeLocalFunctor_agree ℓ)
    (chosenCoverChamber ℓ p) (chosenCoverChamber_mem ℓ p)

/-- The genuine global descent, with its common selector object map made
definitionally explicit. -/
noncomputable def descentFunctor :
    FundamentalGroupoid (ComplexComplement ℓ) ⥤ IntervalGroupoid ℓ :=
  (gluedTubeDescent ℓ).copyObj
    (fun p => intervalObject (chosenCoverChamber ℓ p.as))
    (fun p => eqToIso (gluedTubeDescent_obj ℓ p.as))

@[simp] theorem descentFunctor_obj (p : FundamentalGroupoid (ComplexComplement ℓ)) :
    (descentFunctor ℓ).obj p = intervalObject (chosenCoverChamber ℓ p.as) := rfl

theorem descentFunctor_map_eqToHom
    {p q : FundamentalGroupoid (ComplexComplement ℓ)} (γ : p ⟶ q) :
    (descentFunctor ℓ).map γ = eqToHom (gluedTubeDescent_obj ℓ p.as).symm ≫
      (gluedTubeDescent ℓ).map γ ≫ eqToHom (gluedTubeDescent_obj ℓ q.as) := rfl

theorem descentFunctor_map_heq
    {p q : FundamentalGroupoid (ComplexComplement ℓ)} (γ : p ⟶ q) :
    (descentFunctor ℓ).map γ ≍ (gluedTubeDescent ℓ).map γ :=
  (conj_eqToHom_iff_heq _ _ (gluedTubeDescent_obj ℓ p.as).symm
    (gluedTubeDescent_obj ℓ q.as).symm).1 (descentFunctor_map_eqToHom ℓ γ)

/-- The copied descent still restricts exactly to each actual local functor. -/
theorem map_subtypeVal_comp_descentFunctor (C : Chamber ℓ) :
    FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C)) ⋙ descentFunctor ℓ =
      tubeLocalFunctor ℓ C := by
  have hF := TauCeti.FundamentalGroupoid.map_subtypeVal_comp_glue (tube_neighborhood_cover ℓ)
    (tubeLocalFunctor ℓ) (tubeLocalFunctor_agree ℓ) C
  change FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C)) ⋙
    gluedTubeDescent ℓ = tubeLocalFunctor ℓ C at hF
  refine Functor.hext ?_ ?_
  · intro p; rfl
  intro p q γ
  exact (descentFunctor_map_heq ℓ
    ((FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C))).map γ)).trans
      (Functor.hcongr_hom hF γ)

/-- Explicit value on every actual path class lying in one tube. -/
theorem descentFunctor_map_local (C : Chamber ℓ)
    {p q : FundamentalGroupoid (tubeSet C)} (γ : p ⟶ q) :
    (descentFunctor ℓ).map
        ((FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C))).map γ) =
      tubeGauge ℓ C p.as.val ≫ inv (tubeGauge ℓ C q.as.val) := by
  exact eq_of_heq (Functor.hcongr_hom (map_subtypeVal_comp_descentFunctor ℓ C) γ)

end ArtinNormalisers.Chamber3
