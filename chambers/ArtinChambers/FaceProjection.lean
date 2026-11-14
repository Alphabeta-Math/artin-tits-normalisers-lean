module

public import ArtinChambers.SignCells
public import ArtinChambers.TubeIntersections
public import ArtinChambers.IntervalGroupoid
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Canonical face projections of realized chambers

The face projection at `x` keeps the signs of `x` away from its vanishing
forms and takes the remaining signs from the chosen chamber. A sufficiently
small positive perturbation toward any point of that chamber realizes this
sign pattern. Finite sign stability also proves the local interval property
used to compare actual overlap connectors.

These proofs are local authoring using mathlib's finite intersections,
continuity of real affine functions and open metric neighborhoods. No
external GitHub proof of the construction is imported.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open CategoryTheory

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} (ℓ : H → E →L[ℝ] ℝ)

private theorem mem_own_signHalfSpace (f : E →L[ℝ] ℝ) {x : E} (hx : f x ≠ 0) :
    x ∈ signHalfSpace f (decide (0 < f x)) := by
  classical
  by_cases hp : 0 < f x
  · simp [signHalfSpace, hp]
  · have hn : f x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simpa only [signHalfSpace, decide_eq_false hp, Bool.false_eq_true,
      ↓reduceIte, Set.mem_ofPred_eq] using hn

private theorem decide_sign_of_mem_signHalfSpace (f : E →L[ℝ] ℝ)
    {x : E} {s : Bool} (hx : x ∈ signHalfSpace f s) : decide (0 < f x) = s := by
  classical
  cases s
  · have hn : f x < 0 := hx
    exact decide_eq_false (not_lt_of_ge hn.le)
  · have hp : 0 < f x := hx
    exact decide_eq_true hp

/-- One positive real parameter preserves all specified nonzero signs. -/
theorem exists_pos_parameter_preserving_signs [Finite H] (a b : H → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h, a h ≠ 0 →
      (if 0 < a h then 0 < a h + ε * b h else a h + ε * b h < 0) := by
  classical
  let S : H → Set ℝ := fun h =>
    if a h = 0 then Set.univ else
      {t | if 0 < a h then 0 < a h + t * b h else a h + t * b h < 0}
  have hopen (h : H) : IsOpen (S h) := by
    have hf : Continuous (fun t : ℝ => a h + t * b h) :=
      continuous_const.add (continuous_id.mul continuous_const)
    by_cases hz : a h = 0
    · simp only [S, ite_eq_left hz]
      exact isOpen_univ
    · by_cases hp : 0 < a h
      · simpa only [S, ite_eq_right hz, ite_eq_left hp] using isOpen_lt continuous_const hf
      · simpa only [S, ite_eq_right hz, ite_eq_right hp] using isOpen_lt hf continuous_const
  have hzero (h : H) : (0 : ℝ) ∈ S h := by
    by_cases hz : a h = 0
    · simp [S, hz]
    · by_cases hp : 0 < a h
      · simp [S, hz, hp]
      · have hn : a h < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
        simpa only [S, ite_eq_right hz, ite_eq_right hp, Set.mem_ofPred_eq, zero_mul, add_zero] using hn
  have hUopen : IsOpen (⋂ h, S h) := isOpen_iInter_of_finite hopen
  have hUzero : (0 : ℝ) ∈ ⋂ h, S h := Set.mem_iInter.2 hzero
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hUopen 0 hUzero
  have heps : δ / 2 ∈ ⋂ h, S h := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < δ / 2)]
    linarith)
  refine ⟨δ / 2, by linarith, fun h hn => ?_⟩
  have hs := Set.mem_iInter.1 heps h
  simpa only [S, ite_eq_right hn, Set.mem_ofPred_eq] using hs

/-- The signs of the canonical face projection. -/
noncomputable def faceSigns (x : E) (C : Chamber ℓ) : H → Bool := by
  classical
  exact fun h => if ℓ h x = 0 then C.signs h else decide (0 < ℓ h x)

/-- A positive perturbation toward a realized chamber realizes the face signs. -/
theorem faceSigns_nonempty [Finite H] (x : E) (C : Chamber ℓ) :
    (signCell ℓ (faceSigns ℓ x C)).Nonempty := by
  classical
  obtain ⟨c, hc⟩ := C.region_nonempty
  obtain ⟨ε, hε, hsign⟩ := exists_pos_parameter_preserving_signs (H := H)
    (fun h => ℓ h x) (fun h => ℓ h c)
  refine ⟨x + ε • c, fun h => ?_⟩
  by_cases hz : ℓ h x = 0
  · have hh := hc h
    cases hs : C.signs h
    · have hn : ℓ h c < 0 := by simpa only [signHalfSpace, hs, Bool.false_eq_true,
        ↓reduceIte, Set.mem_ofPred_eq] using hh
      have hp := mul_neg_of_pos_of_neg hε hn
      simpa only [faceSigns, hz, ite_eq_left, hs, signHalfSpace, Bool.false_eq_true,
        ↓reduceIte, Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul, zero_add] using hp
    · have hn : 0 < ℓ h c := by simpa only [signHalfSpace, hs, ↓reduceIte,
        Set.mem_ofPred_eq] using hh
      have hp := mul_pos hε hn
      simpa only [faceSigns, hz, ite_eq_left, hs, signHalfSpace, ↓reduceIte,
        Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul, zero_add] using hp
  · have hh := hsign h hz
    by_cases hp : 0 < ℓ h x
    · simpa only [faceSigns, ite_eq_right hz, decide_eq_true hp, signHalfSpace, ↓reduceIte,
        Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul, ite_eq_left hp] using hh
    · simpa only [faceSigns, ite_eq_right hz, decide_eq_false hp, signHalfSpace, Bool.false_eq_true,
        ↓reduceIte, Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul, ite_eq_right hp] using hh

/-- The canonical realized chamber `x ∘ C`, specified by its signs. -/
noncomputable def faceChamber [Finite H] (x : E) (C : Chamber ℓ) : Chamber ℓ :=
  ⟨faceSigns ℓ x C, faceSigns_nonempty ℓ x C⟩

@[simp] theorem faceChamber_signs_zero [Finite H] (x : E) (C : Chamber ℓ) {h : H}
    (hh : ℓ h x = 0) : (faceChamber ℓ x C).signs h = C.signs h := by
  classical
  simp only [faceChamber, faceSigns, ite_eq_left hh]

theorem faceChamber_signs_nonzero [Finite H] (x : E) (C : Chamber ℓ) {h : H}
    (hh : ℓ h x ≠ 0) : (faceChamber ℓ x C).signs h = decide (0 < ℓ h x) := by
  classical
  simp only [faceChamber, faceSigns, ite_eq_right hh]

theorem faceChamber_eq_chamberOfRegular [Finite H] (x : E) (C : Chamber ℓ)
    (hx : x ∈ regularSet ℓ) : faceChamber ℓ x C = chamberOfRegular ℓ x hx := by
  classical
  apply Chamber.ext
  funext h
  simp only [faceChamber_signs_nonzero ℓ x C (hx h), chamberOfRegular]

theorem faceChamber_eq_of_signs_on_zero [Finite H] (x : E) (C D : Chamber ℓ)
    (hCD : ∀ h, ℓ h x = 0 → C.signs h = D.signs h) :
    faceChamber ℓ x C = faceChamber ℓ x D := by
  classical
  apply Chamber.ext
  funext h
  by_cases hz : ℓ h x = 0
  · rw [faceChamber_signs_zero ℓ x C hz, faceChamber_signs_zero ℓ x D hz, hCD h hz]
  · rw [faceChamber_signs_nonzero ℓ x C hz, faceChamber_signs_nonzero ℓ x D hz]

/-- A neighborhood preserving every sign that is already nonzero at `x`. -/
noncomputable def nonzeroSignRegion (x : E) : Set E := by
  classical
  exact {y | ∀ h, ℓ h x ≠ 0 → y ∈ signHalfSpace (ℓ h) (decide (0 < ℓ h x))}

theorem mem_nonzeroSignRegion_self (x : E) : x ∈ nonzeroSignRegion ℓ x :=
  fun h hh => mem_own_signHalfSpace (ℓ h) hh

theorem isOpen_nonzeroSignRegion [Finite H] (x : E) : IsOpen (nonzeroSignRegion ℓ x) := by
  classical
  have he : nonzeroSignRegion ℓ x =
      ⋂ h, ⋂ (_ : ℓ h x ≠ 0), signHalfSpace (ℓ h) (decide (0 < ℓ h x)) := by
    ext y
    simp only [nonzeroSignRegion, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  exact isOpen_iInter_of_finite fun h =>
    isOpen_iInter_of_finite fun _ => isOpen_signHalfSpace (ℓ h) _

/-- Near `z`, a face projection at `z` lies in each of the two sign intervals
starting at the face projection at `z'`, provided the endpoint chambers agree
on every form vanishing at `z`. -/
theorem faceChamber_between_of_mem_nonzeroSignRegion [Finite H]
    {z z' : E} {C D : Chamber ℓ}
    (hzero : ∀ h, ℓ h z = 0 → C.signs h = D.signs h)
    (hz' : z' ∈ nonzeroSignRegion ℓ z) :
    ChamberBetween (faceChamber ℓ z' C) (faceChamber ℓ z C) C ∧
      ChamberBetween (faceChamber ℓ z' C) (faceChamber ℓ z C) D := by
  have hstable (h : H) (hh : ℓ h z ≠ 0) :
      (faceChamber ℓ z' C).signs h = (faceChamber ℓ z C).signs h := by
    have hs := hz' h hh
    have hne := signHalfSpace_nonzero hs
    rw [faceChamber_signs_nonzero ℓ z' C hne, faceChamber_signs_nonzero ℓ z C hh]
    exact decide_sign_of_mem_signHalfSpace (ℓ h) hs
  have key (F : Chamber ℓ) (hF : ∀ h, ℓ h z = 0 → C.signs h = F.signs h) :
      ChamberBetween (faceChamber ℓ z' C) (faceChamber ℓ z C) F := by
    intro h hshared
    by_cases hh : ℓ h z = 0
    · calc
        (faceChamber ℓ z C).signs h = C.signs h := faceChamber_signs_zero ℓ z C hh
        _ = F.signs h := hF h hh
        _ = (faceChamber ℓ z' C).signs h := hshared.symm
    · exact (hstable h hh).symm
  exact ⟨key C (fun _ _ => rfl), key D hzero⟩

/-- The preceding interval identities hold throughout an actual open
neighborhood, not merely at a chosen nearby regular point. -/
theorem exists_open_faceChamber_intervals [Finite H] {z : E} {C D : Chamber ℓ}
    (hzero : ∀ h, ℓ h z = 0 → C.signs h = D.signs h) :
    ∃ U : Set E, IsOpen U ∧ z ∈ U ∧ ∀ z' ∈ U,
      ChamberBetween (faceChamber ℓ z' C) (faceChamber ℓ z C) C ∧
        ChamberBetween (faceChamber ℓ z' C) (faceChamber ℓ z C) D :=
  ⟨nonzeroSignRegion ℓ z, isOpen_nonzeroSignRegion ℓ z, mem_nonzeroSignRegion_self ℓ z,
    fun _ hz' => faceChamber_between_of_mem_nonzeroSignRegion ℓ hzero hz'⟩

/-- On an actual overlap, a vanishing real form cannot separate its two chambers. -/
theorem chamber_signs_agree_on_zero_of_overlap {z : E} {C D : Chamber ℓ}
    {ρ : H → Bool} (hz : z ∈ overlapRealRegion ({C, D} : Set (Chamber ℓ)) ρ) :
    ∀ h, ℓ h z = 0 → C.signs h = D.signs h := by
  intro h hh
  by_contra hne
  have hdis : tubeDisagreement ({C, D} : Set (Chamber ℓ)) h :=
    ⟨C, by simp, D, by simp, hne⟩
  exact signHalfSpace_nonzero (hz h hdis) hh

/-- A real point in an actual two-tube overlap sign piece satisfies the
vanishing-form agreement needed by the local interval theorem. -/
theorem faceChamber_intervals_of_overlap [Finite H] {z z' : E} {C D : Chamber ℓ}
    {ρ : H → Bool} (hz : z ∈ overlapRealRegion ({C, D} : Set (Chamber ℓ)) ρ)
    (hz' : z' ∈ nonzeroSignRegion ℓ z) :
    ChamberBetween (faceChamber ℓ z' C) (faceChamber ℓ z C) C ∧
      ChamberBetween (faceChamber ℓ z' C) (faceChamber ℓ z C) D := by
  exact faceChamber_between_of_mem_nonzeroSignRegion ℓ
    (chamber_signs_agree_on_zero_of_overlap ℓ hz) hz'

/-- The interval connector associated with the actual face projection. -/
noncomputable def faceIntervalConnector [Finite H] (z : E) (C D : Chamber ℓ) :
    intervalObject C ⟶ intervalObject D :=
  inv (intervalPositive (faceChamber ℓ z C) C) ≫ intervalPositive (faceChamber ℓ z C) D

/-- The local interval identities cancel their common prefix, proving actual
equality of the overlap connectors in the presented interval groupoid. -/
theorem faceIntervalConnector_eq_of_mem_nonzeroSignRegion [Finite H]
    {z z' : E} {C D : Chamber ℓ}
    (hzero : ∀ h, ℓ h z = 0 → C.signs h = D.signs h)
    (hz' : z' ∈ nonzeroSignRegion ℓ z) :
    faceIntervalConnector ℓ z' C D = faceIntervalConnector ℓ z C D := by
  obtain ⟨hC, hD⟩ := faceChamber_between_of_mem_nonzeroSignRegion ℓ hzero hz'
  have h₁ := intervalPositive_comp (faceChamber ℓ z' C) (faceChamber ℓ z C) C hC
  have h₂ := intervalPositive_comp (faceChamber ℓ z' C) (faceChamber ℓ z C) D hD
  unfold faceIntervalConnector
  simp [h₁, h₂, Category.assoc]

/-- Each actual real overlap point has an open neighborhood on which its
interval connector is constant. No adjacency or gallery topology is assumed. -/
theorem exists_open_faceIntervalConnector_constant_of_overlap [Finite H]
    {z : E} {C D : Chamber ℓ} {ρ : H → Bool}
    (hz : z ∈ overlapRealRegion ({C, D} : Set (Chamber ℓ)) ρ) :
    ∃ U : Set E, IsOpen U ∧ z ∈ U ∧ ∀ z' ∈ U,
      faceIntervalConnector ℓ z' C D = faceIntervalConnector ℓ z C D :=
  ⟨nonzeroSignRegion ℓ z, isOpen_nonzeroSignRegion ℓ z, mem_nonzeroSignRegion_self ℓ z,
    fun _ hz' => faceIntervalConnector_eq_of_mem_nonzeroSignRegion ℓ
      (chamber_signs_agree_on_zero_of_overlap ℓ hz) hz'⟩

/-- The actual face connector is locally constant on each real overlap sign
piece, as a function to the interval-groupoid hom set. -/
theorem isLocallyConstant_faceIntervalConnector_overlap [Finite H]
    (C D : Chamber ℓ) (ρ : H → Bool) :
    IsLocallyConstant (fun z : overlapRealRegion ({C, D} : Set (Chamber ℓ)) ρ =>
      faceIntervalConnector ℓ z.val C D) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro z
  obtain ⟨U, hU, hzU, hconst⟩ := exists_open_faceIntervalConnector_constant_of_overlap ℓ z.property
  exact Filter.eventually_of_mem
    ((hU.preimage continuous_subtype_val).mem_nhds hzU) (fun z' hz' => hconst z'.val hz')

end ArtinNormalisers.Chamber3
