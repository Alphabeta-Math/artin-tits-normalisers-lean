module

public import ArtinChambers.SignCells
public import ArtinChambers.TubeCover
public import ArtinNormalisers.Theorem18.Geometry
public import ArtinLandmarks.RegularStabilizer

/-!
# The actual relative arrangement is the generic linear-form arrangement

The forms are the actual evaluations at retained roots, with no invented
ambient Coxeter system or substitute space. Repeated restricted hyperplanes
are allowed. The comparison with the existing real-pair complement is the
identity on both coordinates, as a proved homeomorphism.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open Theorem18

variable {I : Type*}

/-- Actual evaluation at a root, restricted to the specified relative flat. -/
noncomputable def relativeEvaluation (J : Set I) (r : Vector I) :
    relativeSubspace J →L[ℝ] ℝ where
  toLinearMap := (Module.Dual.eval ℝ (Vector I) r).comp (relativeSubspace J).subtype
  cont := (continuous_evaluation r).comp continuous_subtype_val

@[simp] theorem relativeEvaluation_apply (J : Set I) (r : Vector I)
    (x : relativeSubspace J) : relativeEvaluation J r x = x.val r := rfl

/-- Actual retained roots, including roots that induce the same hyperplane. -/
abbrev RelativeRoot (M : CoxeterMatrix I) (J : Set I) :=
  ↥(retainedRoots M J)

noncomputable instance relativeRootFinite (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    Finite (RelativeRoot M J) := by
  let := (retainedRoots_finite M J).fintype
  infer_instance

/-- The literal family of restricted root evaluations. -/
noncomputable def actualForms (M : CoxeterMatrix I) (J : Set I) :
    RelativeRoot M J → relativeSubspace J →L[ℝ] ℝ :=
  fun r => relativeEvaluation J r.val

@[simp] theorem actualForms_apply (M : CoxeterMatrix I) (J : Set I)
    (r : RelativeRoot M J) (x : relativeSubspace J) :
    actualForms M J r x = x.val r.val := rfl

/-- Retention is exactly what makes the restricted evaluation nonzero. -/
theorem actualForms_ne_zero (M : CoxeterMatrix I) (J : Set I)
    (r : RelativeRoot M J) : actualForms M J r ≠ 0 := by
  obtain ⟨x, hx⟩ := r.property.2
  intro hz
  apply hx
  have he := congrArg (fun f : relativeSubspace J →L[ℝ] ℝ => f x) hz
  exact he

/-- The new real regular locus is the already proved actual regularity condition. -/
theorem mem_actual_regularSet_iff (M : CoxeterMatrix I) (J : Set I)
    (x : relativeSubspace J) :
    x ∈ regularSet (actualForms M J) ↔ Landmark1.realRelativeRegular M J x := by
  constructor
  · intro h r hr
    exact h ⟨r, hr⟩
  · intro h r
    exact h r.val r.property

/-- Both complement predicates remove precisely the same actual pairs. -/
theorem mem_actual_complexComplementSet_iff (M : CoxeterMatrix I) (J : Set I)
    (p : relativeSubspace J × relativeSubspace J) :
    p ∈ complexComplementSet (actualForms M J) ↔ p ∈ complementSet M J := by
  constructor
  · intro h r hr
    exact h ⟨r, hr⟩
  · intro h r
    exact h r.val r.property

/-- Identity on coordinates identifies the two actual subspace complements. -/
noncomputable def actualComplementHomeomorph (M : CoxeterMatrix I) (J : Set I) :
    Complement M J ≃ₜ ComplexComplement (E := relativeSubspace J) (actualForms M J) where
  toFun p := ⟨p.val, (mem_actual_complexComplementSet_iff M J p.val).2 p.property⟩
  invFun p := ⟨p.val, (mem_actual_complexComplementSet_iff M J p.val).1 p.property⟩
  left_inv _p := rfl
  right_inv _p := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp] theorem actualComplementHomeomorph_val (M : CoxeterMatrix I) (J : Set I)
    (p : Complement M J) : (actualComplementHomeomorph M J p).val = p.val := rfl

/-- The actual restricted-arrangement chamber type. -/
abbrev ActualChamber (M : CoxeterMatrix I) (J : Set I) :=
  Chamber (E := relativeSubspace J) (actualForms M J)

/-- The article's actual chamber tube, expressed in the original complement. -/
noncomputable def actualTubeSet (M : CoxeterMatrix I) (J : Set I) (C : ActualChamber M J) :
    Set (Complement M J) := (actualComplementHomeomorph M J) ⁻¹' tubeSet C

theorem isOpen_actualTubeSet (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) (C : ActualChamber M J) : IsOpen (actualTubeSet M J C) :=
  (isOpen_tubeSet C).preimage (actualComplementHomeomorph M J).continuous

theorem exists_mem_actualTubeSet (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) (p : Complement M J) :
    ∃ C : ActualChamber M J, p ∈ actualTubeSet M J C := by
  change ∃ C : Chamber (E := relativeSubspace J) (actualForms M J),
    actualComplementHomeomorph M J p ∈ tubeSet C
  exact exists_mem_tubeSet (E := relativeSubspace J) (actualForms M J)
    (actualComplementHomeomorph M J p)

end ArtinNormalisers.Chamber3
