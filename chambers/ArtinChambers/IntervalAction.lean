module

public import ArtinChambers.ChamberAction
public import ArtinChambers.IntervalGroupoid
public import Mathlib.CategoryTheory.Equivalence

/-!
# The actual normalizer quotient acts on the interval groupoid

The existing quotient action permutes the actual chambers and preserves their
sign intervals. Its action on every positive ordered-pair generator therefore
extends through the proved interval presentation. The multiplication law uses
the usual left action: first act by `r`, then by `q`, to act by `q * r`.
No geometric comparison or equivariance conclusion is assumed here.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Chamber3

open CategoryTheory Theorem18

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The actual root permutation preserves the shared-sign interval condition. -/
theorem chamberBetween_transportedChamber (w : CoxeterNormalizer M J)
    {C D F : ActualChamber M J} (h : ChamberBetween C D F) :
    ChamberBetween (transportedChamber M J w C) (transportedChamber M J w D)
      (transportedChamber M J w F) := by
  intro r hr
  obtain ⟨s, rfl⟩ := (retainedRootEquiv M J w).surjective r
  rw [transportedChamber_signs, transportedChamber_signs] at hr
  rw [transportedChamber_signs, transportedChamber_signs]
  exact h s hr

/-- Preservation descends through the same actual parabolic normalizer quotient. -/
theorem chamberBetween_quotient_smul (q : Artin.coxeterNormalizerQuotient M J)
    {C D F : ActualChamber M J} (h : ChamberBetween C D F) :
    ChamberBetween (q • C) (q • D) (q • F) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    ((Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J)) q
  exact chamberBetween_transportedChamber M J w h

theorem chamberBetween_quotient_smul_iff (q : Artin.coxeterNormalizerQuotient M J)
    (C D F : ActualChamber M J) :
    ChamberBetween (q • C) (q • D) (q • F) ↔ ChamberBetween C D F := by
  constructor
  · intro h
    have hi := chamberBetween_quotient_smul M J q⁻¹ h
    simpa only [inv_smul_smul] using hi
  · exact chamberBetween_quotient_smul M J q

/-- Transport the positive generators, retaining both ordered directions. -/
noncomputable def intervalActionData (q : Artin.coxeterNormalizerQuotient M J) :
    IntervalGeneratorData (E := relativeSubspace J) (actualForms M J)
      (IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) where
  obj C := intervalObject (q • C)
  positive C D := intervalPositive (q • C) (q • D)

theorem intervalActionData_respects (q : Artin.coxeterNormalizerQuotient M J) :
    (intervalActionData M J q).RespectsIntervals :=
  ⟨fun C => intervalPositive_self (q • C),
    fun C D F h => intervalPositive_comp (q • C) (q • D) (q • F)
      (chamberBetween_quotient_smul M J q h)⟩

/-- The induced endofunctor of the genuine interval groupoid. -/
noncomputable def intervalAction (q : Artin.coxeterNormalizerQuotient M J) :
    IntervalGroupoid (E := relativeSubspace J) (actualForms M J) ⥤
      IntervalGroupoid (E := relativeSubspace J) (actualForms M J) :=
  (intervalActionData M J q).extensionFunctor (intervalActionData_respects M J q)

@[simp] theorem intervalAction_obj (q : Artin.coxeterNormalizerQuotient M J)
    (X : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) :
    (intervalAction M J q).obj X = intervalObject (q • intervalChamber X) := rfl

@[simp] theorem intervalAction_obj_chamber (q : Artin.coxeterNormalizerQuotient M J)
    (C : ActualChamber M J) :
    (intervalAction M J q).obj (intervalObject C) = intervalObject (q • C) := rfl

@[simp] theorem intervalAction_positive (q : Artin.coxeterNormalizerQuotient M J)
    (C D : ActualChamber M J) :
    (intervalAction M J q).map (intervalPositive C D) = intervalPositive (q • C) (q • D) :=
  (intervalActionData M J q).extensionFunctor_positive _ C D

/-- The identity element acts by the identity functor, on every morphism. -/
@[simp] theorem intervalAction_one :
    intervalAction M J 1 = 𝟭 (IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) := by
  symm
  apply (intervalActionData M J 1).extensionFunctor_unique
    (intervalActionData_respects M J 1)
  · funext X
    simp only [Functor.id_obj, intervalActionData, one_smul, intervalObject_intervalChamber]
  · intro C D
    change HEq (intervalPositive C D)
      (intervalPositive ((1 : Artin.coxeterNormalizerQuotient M J) • C)
        ((1 : Artin.coxeterNormalizerQuotient M J) • D))
    rw [one_smul, one_smul]

/-- Multiplication agrees with the actual left quotient action. -/
theorem intervalAction_mul (q r : Artin.coxeterNormalizerQuotient M J) :
    intervalAction M J (q * r) = intervalAction M J r ⋙ intervalAction M J q := by
  symm
  apply (intervalActionData M J (q * r)).extensionFunctor_unique
    (intervalActionData_respects M J (q * r))
  · funext X
    simp only [Functor.comp_obj, intervalAction_obj, intervalChamber_intervalObject,
      intervalActionData, mul_smul]
  · intro C D
    change HEq ((intervalAction M J q).map (intervalPositive (r • C) (r • D)))
      (intervalPositive ((q * r) • C) ((q * r) • D))
    rw [intervalAction_positive, mul_smul, mul_smul]
    rfl

@[simp] theorem intervalAction_comp_inv (q : Artin.coxeterNormalizerQuotient M J) :
    intervalAction M J q ⋙ intervalAction M J q⁻¹ =
      𝟭 (IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) := by
  rw [← intervalAction_mul, inv_mul_cancel, intervalAction_one]

@[simp] theorem intervalAction_inv_comp (q : Artin.coxeterNormalizerQuotient M J) :
    intervalAction M J q⁻¹ ⋙ intervalAction M J q =
      𝟭 (IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) := by
  rw [← intervalAction_mul, mul_inv_cancel, intervalAction_one]

/-- Every quotient element acts by an equivalence with its actual inverse element. -/
noncomputable def intervalActionEquivalence (q : Artin.coxeterNormalizerQuotient M J) :
    IntervalGroupoid (E := relativeSubspace J) (actualForms M J) ≌
      IntervalGroupoid (E := relativeSubspace J) (actualForms M J) :=
  CategoryTheory.Equivalence.mk (intervalAction M J q) (intervalAction M J q⁻¹)
    (eqToIso (intervalAction_comp_inv M J q).symm)
    (eqToIso (intervalAction_inv_comp M J q))

noncomputable instance intervalAction_isEquivalence (q : Artin.coxeterNormalizerQuotient M J) :
    (intervalAction M J q).IsEquivalence :=
  (intervalActionEquivalence M J q).isEquivalence_functor

end ArtinNormalisers.Chamber3
