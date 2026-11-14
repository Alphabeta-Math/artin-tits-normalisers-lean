module

public import ArtinChambers.SignCells

/-!
# Open, contractible tubes in the actual complexified complement

First move the imaginary coordinate into a chosen point of the chamber,
keeping the real coordinate fixed. Then move the real coordinate to that
point while the imaginary coordinate stays regular. Concatenating these
two homotopies contracts the actual tube to `(c,c)`.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} {ℓ : H → E →L[ℝ] ℝ}

/-- Each tube is open in the actual complement for a finite arrangement. -/
theorem isOpen_tubeSet [Finite H] (C : Chamber ℓ) : IsOpen (tubeSet C) := by
  classical
  have he : tubeSet C = ⋂ h, {p : ComplexComplement ℓ |
      ℓ h p.val.1 ≠ 0 ∨ p.val.2 ∈ signHalfSpace (ℓ h) (C.signs h)} := by
    ext p
    simp only [tubeSet, Set.mem_ofPred_eq, Set.mem_iInter]
    apply forall_congr'
    intro h
    by_cases hx : ℓ h p.val.1 = 0 <;> simp [hx]
  rw [he]
  apply isOpen_iInter_of_finite
  intro h
  have hx : Continuous (fun p : ComplexComplement ℓ => ℓ h p.val.1) :=
    (ℓ h).continuous.comp (continuous_fst.comp continuous_subtype_val)
  have hy : Continuous (fun p : ComplexComplement ℓ => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  exact (isClosed_eq hx continuous_const).isOpen_compl.union
    ((isOpen_signHalfSpace (ℓ h) (C.signs h)).preimage hy)

namespace Tubes

/-- This is a type alias for the literal tube subtype, with inherited topology. -/
abbrev Space (C : Chamber ℓ) := ↥(tubeSet C)

noncomputable def chosenPoint (C : Chamber ℓ) : E := C.region_nonempty.choose

theorem chosenPoint_mem (C : Chamber ℓ) : chosenPoint C ∈ C.region :=
  C.region_nonempty.choose_spec

/-- The tube condition itself proves avoidance of simultaneous zeros. -/
def makePoint (C : Chamber ℓ) (x y : E)
    (hy : ∀ h, ℓ h x = 0 → y ∈ signHalfSpace (ℓ h) (C.signs h)) : Space C :=
  ⟨⟨(x, y), by
    intro h hz
    exact signHalfSpace_nonzero (hy h hz.1) hz.2⟩, hy⟩

/-- An actual point of the tube, even when the arrangement has no forms. -/
noncomputable def center (C : Chamber ℓ) : Space C :=
  makePoint C (chosenPoint C) (chosenPoint C) (fun h _ => chosenPoint_mem C h)

theorem continuous_real (C : Chamber ℓ) : Continuous (fun p : Space C => p.val.val.1) :=
  continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_imag (C : Chamber ℓ) : Continuous (fun p : Space C => p.val.val.2) :=
  continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)

/-- At the end of the first stage the real coordinate is unchanged and
the imaginary coordinate is the chosen actual chamber point. -/
noncomputable def stageOneMap (C : Chamber ℓ) : C(Space C, Space C) where
  toFun p := makePoint C p.val.val.1 (chosenPoint C) (fun h _ => chosenPoint_mem C h)
  continuous_toFun := ((continuous_real C).prodMk continuous_const).subtype_mk _ |>.subtype_mk _

section Contraction

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The first stage stays in every required open halfspace whenever its
fixed real coordinate vanishes on the corresponding form. -/
noncomputable def imaginaryHomotopy (C : Chamber ℓ) :
    ContinuousMap.Homotopy (ContinuousMap.id (Space C)) (stageOneMap C) where
  toFun p := makePoint C p.2.val.val.1
    ((1 - (p.1 : ℝ)) • p.2.val.val.2 + (p.1 : ℝ) • chosenPoint C) (by
      intro h hx
      exact (convex_signHalfSpace (ℓ h) (C.signs h))
        (p.2.property h hx) (chosenPoint_mem C h)
        (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ)))
  continuous_toFun := by
    have hp : Continuous (fun p : unitInterval × Space C =>
        (p.2.val.val.1,
          (1 - (p.1 : ℝ)) • p.2.val.val.2 + (p.1 : ℝ) • chosenPoint C)) := by
      fun_prop
    exact hp.subtype_mk _ |>.subtype_mk _
  map_zero_left p := by
    apply Subtype.ext
    apply Subtype.ext
    change (p.val.val.1, (1 - (0 : ℝ)) • p.val.val.2 + (0 : ℝ) • chosenPoint C) = p.val.val
    simp
  map_one_left p := by
    apply Subtype.ext
    apply Subtype.ext
    change (p.val.val.1, (1 - (1 : ℝ)) • p.val.val.2 + (1 : ℝ) • chosenPoint C) =
      (p.val.val.1, chosenPoint C)
    simp

/-- The second stage moves the real coordinate with imaginary coordinate
fixed at a regular chamber point, so no simultaneous zero can occur. -/
noncomputable def realHomotopy (C : Chamber ℓ) :
    ContinuousMap.Homotopy (stageOneMap C) (ContinuousMap.const (Space C) (center C)) where
  toFun p := makePoint C
    ((1 - (p.1 : ℝ)) • p.2.val.val.1 + (p.1 : ℝ) • chosenPoint C)
    (chosenPoint C) (fun h _ => chosenPoint_mem C h)
  continuous_toFun := by
    have hp : Continuous (fun p : unitInterval × Space C =>
        ((1 - (p.1 : ℝ)) • p.2.val.val.1 + (p.1 : ℝ) • chosenPoint C,
          chosenPoint C)) := by
      fun_prop
    exact hp.subtype_mk _ |>.subtype_mk _
  map_zero_left p := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (0 : ℝ)) • p.val.val.1 + (0 : ℝ) • chosenPoint C, chosenPoint C) =
      (p.val.val.1, chosenPoint C)
    simp
  map_one_left p := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (1 : ℝ)) • p.val.val.1 + (1 : ℝ) • chosenPoint C, chosenPoint C) =
      (chosenPoint C, chosenPoint C)
    simp

/-- Explicit two-stage contraction of the actual tube to `(c,c)`. -/
noncomputable def contraction (C : Chamber ℓ) :
    ContinuousMap.Homotopy (ContinuousMap.id (Space C))
      (ContinuousMap.const (Space C) (center C)) :=
  (imaginaryHomotopy C).trans (realHomotopy C)

end Contraction
end Tubes

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The actual tube is contractible, with no finiteness or nonempty-rank
hypothesis needed for its explicit contraction. -/
theorem contractibleSpace_tubeSet (C : Chamber ℓ) : ContractibleSpace ↥(tubeSet C) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨Tubes.center C, ⟨Tubes.contraction C⟩⟩

instance tubeSetContractibleSpace (C : Chamber ℓ) : ContractibleSpace ↥(tubeSet C) :=
  contractibleSpace_tubeSet C

end ArtinNormalisers.Chamber3
