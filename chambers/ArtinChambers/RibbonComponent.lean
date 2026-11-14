import ArtinChambers.RibbonCover

/-!
# The actual reduced associate component and the chamber object fibers

The target is a full subcategory of the already constructed reduced ribbon
groupoid. Its arrows retain the actual reduced-ribbon condition. The chamber
object fibers are precisely normalizer-quotient orbits, and that action is free.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Chamber3

open Theorem18 Landmark1 Ribbon2 CategoryTheory

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The associate property on objects of the actual reduced groupoid. -/
def reducedAssociateProperty : ObjectProperty (ActualReducedRibbonGroupoid M) :=
  fun X => ParabolicAssociate M X.val.indices J

/-- The actual reduced ribbon component on associates of `J`. -/
abbrev AssociateReducedRibbonObject := (reducedAssociateProperty M J).FullSubcategory

instance associateReducedRibbonGroupoid : Groupoid (AssociateReducedRibbonObject M J) :=
  inferInstanceAs (Groupoid (InducedCategory (ActualReducedRibbonGroupoid M)
    (fun X : AssociateReducedRibbonObject M J => X.obj)))

theorem intervalRibbonFunctor_obj_property
    (X : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) :
    reducedAssociateProperty M J ((intervalRibbonFunctor M J).obj X) := by
  rw [← intervalObject_intervalChamber X, intervalRibbonFunctor_obj]
  exact intervalRibbonFunctor_object_associate M J _

/-- Restriction of the actual functor through the actual reduced full component. -/
noncomputable def componentRibbonFunctor :
    IntervalGroupoid (E := relativeSubspace J) (actualForms M J) ⥤ AssociateReducedRibbonObject M J :=
  (reducedAssociateProperty M J).lift (intervalRibbonFunctor M J)
    (intervalRibbonFunctor_obj_property M J)

@[simp] theorem componentRibbonFunctor_obj_underlying (C : ActualChamber M J) :
    ((componentRibbonFunctor M J).obj (intervalObject C)).obj =
      actualRibbonObject M ⟨actualChamberIndices M J C⟩ := rfl

theorem componentRibbonFunctor_comp_inclusion :
    componentRibbonFunctor M J ⋙ (reducedAssociateProperty M J).ι = intervalRibbonFunctor M J := rfl

omit [Finite M.Group] in
private theorem associate_iff_map_conj (K : Set I) :
    ParabolicAssociate M K J ↔ ∃ w : M.Group,
      (Artin.coxeterParabolic M K).map (MulAut.conj w).toMonoidHom =
        Artin.coxeterParabolic M J := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w⁻¹, ?_⟩
    ext a
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
      hw (w * a * w⁻¹)
  · rintro ⟨w, hw⟩
    refine ⟨w⁻¹, ?_⟩
    intro a
    rw [inv_inv, ← hw, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

theorem exists_chamberIndices_iff_associate (K : Set I) :
    (∃ C : ActualChamber M J, actualChamberIndices M J C = K) ↔ ParabolicAssociate M K J :=
  (exists_actualChamberIndices_iff M J K).trans (associate_iff_map_conj M J K).symm

private theorem actualRibbonObject_of_indices (X : ActualReducedRibbonGroupoid M) :
    actualRibbonObject M ⟨X.val.indices⟩ = X := by
  apply Subtype.ext
  cases X.val
  rfl

/-- Literal object surjectivity holds onto the actual associate component. -/
theorem componentRibbonFunctor_obj_surjective :
    Function.Surjective (componentRibbonFunctor M J).obj := by
  intro X
  obtain ⟨C, hC⟩ := (exists_chamberIndices_iff_associate M J X.obj.val.indices).mpr X.property
  refine ⟨intervalObject C, ?_⟩
  apply ObjectProperty.FullSubcategory.ext
  change actualRibbonObject M ⟨actualChamberIndices M J C⟩ = X.obj
  rw [hC]
  exact actualRibbonObject_of_indices M X.obj

/-- Equality of object images is exactly equality of the proved standard-facet
indices; it does not identify all chambers. -/
theorem componentRibbonFunctor_obj_eq_iff (C D : ActualChamber M J) :
    (componentRibbonFunctor M J).obj (intervalObject C) =
        (componentRibbonFunctor M J).obj (intervalObject D) ↔
      actualChamberIndices M J C = actualChamberIndices M J D := by
  constructor
  · intro h
    exact congrArg (fun X : AssociateReducedRibbonObject M J => X.obj.val.indices) h
  · intro h
    apply ObjectProperty.FullSubcategory.ext
    change actualRibbonObject M ⟨actualChamberIndices M J C⟩ =
      actualRibbonObject M ⟨actualChamberIndices M J D⟩
    rw [h]

/-- Two raw labels with the same standard-facet index set differ by an
actual normalizer on the left. -/
theorem rawLabels_same_indices_normalizer (L K : RawFacetLabel M J)
    (hI : L.indices = K.indices) :
    ∃ w : CoxeterNormalizer M J,
      transportedChamber M J w (actualChamberOfRawLabel M J L) =
        actualChamberOfRawLabel M J K := by
  let n := K.representative * L.representative⁻¹
  have hcomp : (MulAut.conj n).toMonoidHom.comp (MulAut.conj L.representative).toMonoidHom =
      (MulAut.conj K.representative).toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change n * (L.representative * g * L.representative⁻¹) * n⁻¹ =
      K.representative * g * K.representative⁻¹
    dsimp only [n]
    group
  have hnmap : (Artin.coxeterParabolic M J).map (MulAut.conj n).toMonoidHom =
      Artin.coxeterParabolic M J := by
    calc
      _ = ((Artin.coxeterParabolic M L.indices).map
          (MulAut.conj L.representative).toMonoidHom).map (MulAut.conj n).toMonoidHom := by
        rw [L.parabolic_conjugacy]
      _ = (Artin.coxeterParabolic M L.indices).map
          (MulAut.conj K.representative).toMonoidHom := by rw [Subgroup.map_map, hcomp]
      _ = _ := by rw [hI, K.parabolic_conjugacy]
  let w : CoxeterNormalizer M J := ⟨n, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hnmap⟩
  refine ⟨w, ?_⟩
  rw [transportedChamber_rawLabel]
  apply (actualChamberOfRawLabel_eq_iff M J _ K).mpr
  refine ⟨hI, ?_⟩
  change (n * L.representative)⁻¹ * K.representative ∈ Artin.coxeterParabolic M L.indices
  have he : n * L.representative = K.representative := by dsimp only [n]; group
  rw [he, inv_mul_cancel]
  exact Subgroup.one_mem _

/-- The quotient acts transitively on each chamber-index fiber, with no
transitivity assertion across different index sets. -/
theorem chamberIndices_eq_iff_exists_smul (C D : ActualChamber M J) :
    actualChamberIndices M J C = actualChamberIndices M J D ↔
      ∃ q : Artin.coxeterNormalizerQuotient M J, q • C = D := by
  constructor
  · intro h
    obtain ⟨L, rfl⟩ := actualChamberOfRawLabel_surjective M J C
    obtain ⟨K, rfl⟩ := actualChamberOfRawLabel_surjective M J D
    rw [actualChamberIndices_rawLabel, actualChamberIndices_rawLabel] at h
    obtain ⟨w, hw⟩ := rawLabels_same_indices_normalizer M J L K h
    refine ⟨QuotientGroup.mk' ((Artin.coxeterParabolic M J).subgroupOf
      (CoxeterNormalizer M J)) w, ?_⟩
    exact hw
  · rintro ⟨q, rfl⟩
    exact (actualChamberIndices_smul M J q C).symm

theorem componentRibbonFunctor_obj_eq_iff_exists_smul (C D : ActualChamber M J) :
    (componentRibbonFunctor M J).obj (intervalObject C) =
        (componentRibbonFunctor M J).obj (intervalObject D) ↔
      ∃ q : Artin.coxeterNormalizerQuotient M J, q • C = D :=
  (componentRibbonFunctor_obj_eq_iff M J C D).trans (chamberIndices_eq_iff_exists_smul M J C D)

/-- The actual quotient action on the actual relative chamber set is free. -/
theorem quotientChamber_smul_fixed_iff (q : Artin.coxeterNormalizerQuotient M J)
    (C : ActualChamber M J) : q • C = C ↔ q = 1 := by
  constructor
  · intro h
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
      ((Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J)) q
    obtain ⟨L, rfl⟩ := actualChamberOfRawLabel_surjective M J C
    change transportedChamber M J w (actualChamberOfRawLabel M J L) =
      actualChamberOfRawLabel M J L at h
    rw [transportedChamber_rawLabel] at h
    have hc := ((actualChamberOfRawLabel_eq_iff M J L (normalizerRawLabel M J w L)).mp h.symm).2
    have hw : w.val ∈ Artin.coxeterParabolic M J := by
      rw [← L.parabolic_conjugacy]
      apply Subgroup.mem_map.mpr
      refine ⟨L.representative⁻¹ * (w.val * L.representative), hc, ?_⟩
      change L.representative * (L.representative⁻¹ * (w.val * L.representative)) *
        L.representative⁻¹ = w.val
      group
    exact (QuotientGroup.eq_one_iff w).mpr hw
  · rintro rfl
    exact one_smul _ _

instance quotientChamberIsCancelSMul :
    IsCancelSMul (Artin.coxeterNormalizerQuotient M J) (ActualChamber M J) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun q C h => (quotientChamber_smul_fixed_iff M J q C).mp h

private theorem lift_eq_of_functor_eq {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty D) {F G : C ⥤ D} (h : F = G)
    (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X)) : P.lift F hF = P.lift G hG := by
  subst G
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Strict quotient invariance survives restriction to the actual reduced component. -/
theorem componentRibbonFunctor_invariant (q : Artin.coxeterNormalizerQuotient M J) :
    intervalAction M J q ⋙ componentRibbonFunctor M J = componentRibbonFunctor M J := by
  change (reducedAssociateProperty M J).lift
      (intervalAction M J q ⋙ intervalRibbonFunctor M J)
      (fun X => intervalRibbonFunctor_obj_property M J ((intervalAction M J q).obj X)) = _
  exact lift_eq_of_functor_eq _ (intervalRibbonFunctor_invariant M J q) _ _

/-- The fiber statement on all objects of the actual interval groupoid,
in the strict form needed for the later quotient-cover comparison. -/
theorem componentRibbonFunctor_obj_eq_iff_exists_action
    (X Y : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) :
    (componentRibbonFunctor M J).obj X = (componentRibbonFunctor M J).obj Y ↔
      ∃ q : Artin.coxeterNormalizerQuotient M J, (intervalAction M J q).obj X = Y := by
  constructor
  · intro h
    have h' : (componentRibbonFunctor M J).obj (intervalObject (intervalChamber X)) =
        (componentRibbonFunctor M J).obj (intervalObject (intervalChamber Y)) := by
      simpa only [intervalObject_intervalChamber] using h
    obtain ⟨q, hq⟩ := (componentRibbonFunctor_obj_eq_iff_exists_smul M J
      (intervalChamber X) (intervalChamber Y)).mp h'
    refine ⟨q, ?_⟩
    rw [intervalAction_obj, hq, intervalObject_intervalChamber]
  · rintro ⟨q, hq⟩
    have hch : q • intervalChamber X = intervalChamber Y := by
      simpa only [intervalAction_obj, intervalChamber_intervalObject] using
        congrArg intervalChamber hq
    have h' := (componentRibbonFunctor_obj_eq_iff_exists_smul M J
      (intervalChamber X) (intervalChamber Y)).mpr ⟨q, hch⟩
    simpa only [intervalObject_intervalChamber] using h'

theorem intervalAction_obj_fixed_iff (q : Artin.coxeterNormalizerQuotient M J)
    (X : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) :
    (intervalAction M J q).obj X = X ↔ q = 1 := by
  constructor
  · intro h
    apply (quotientChamber_smul_fixed_iff M J q (intervalChamber X)).mp
    simpa only [intervalAction_obj, intervalChamber_intervalObject] using congrArg intervalChamber h
  · rintro rfl
    rw [intervalAction_one]
    rfl

end ArtinNormalisers.Chamber3
