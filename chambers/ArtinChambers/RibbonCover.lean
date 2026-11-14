import ArtinChambers.ChamberTransport
import ArtinChambers.ChamberAction
import ArtinChambers.IntervalAction
import ArtinRibbons.RibbonUniversal

set_option autoImplicit false

/-!
# The actual interval-to-ribbon functor

Objects are sent to their proved standard-facet index sets. Positive pair
generators are sent to the actual canonical positive simple lifts of the
minimal relative Coxeter elements. The interval relations follow from the
proved geometric transport and length laws and positive-lift multiplication.
-/

namespace ArtinNormalisers.Chamber3

open Theorem18 Landmark1 Ribbon2 CategoryTheory OAI.HarmonicArtin

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The actual generated ribbon arrow associated with a positive interval. -/
noncomputable def intervalRibbonPositive (C D : ActualChamber M J) :
    actualRibbonObject M ⟨actualChamberIndices M J C⟩ ⟶
      actualRibbonObject M ⟨actualChamberIndices M J D⟩ :=
  actualReducedHom M (transporterPositiveLift_generated M
    (relativeTransport_conjugacy M J C D) (relativeTransport_minimal M J C D)).toReducedArrow

@[simp] theorem intervalRibbonPositive_value (C D : ActualChamber M J) :
    (intervalRibbonPositive M J C D).val.val =
      transporterPositiveLift M (relativeTransport M J C D) := rfl

theorem intervalRibbonPositive_self (C : ActualChamber M J) :
    intervalRibbonPositive M J C C = 𝟙 (actualRibbonObject M ⟨actualChamberIndices M J C⟩) := by
  classical
  let : Finite I := finite_index M
  let := Fintype.ofFinite I
  apply Subtype.ext
  apply Subtype.ext
  change transporterPositiveLift M (relativeTransport M J C C) = 1
  rw [relativeTransport_self, transporterPositiveLift, positiveSimpleLift_one, map_one]

theorem intervalRibbonPositive_comp {C D E : ActualChamber M J}
    (hbet : ChamberBetween C D E) :
    intervalRibbonPositive M J C E =
      intervalRibbonPositive M J C D ≫ intervalRibbonPositive M J D E := by
  classical
  let : Finite I := finite_index M
  let := Fintype.ofFinite I
  apply Subtype.ext
  apply Subtype.ext
  change transporterPositiveLift M (relativeTransport M J C E) =
    transporterPositiveLift M (relativeTransport M J C D) *
      transporterPositiveLift M (relativeTransport M J D E)
  have hlen : M.toCoxeterSystem.length
      (relativeTransport M J C D * relativeTransport M J D E) =
      M.toCoxeterSystem.length (relativeTransport M J C D) +
        M.toCoxeterSystem.length (relativeTransport M J D E) := by
    rw [← relativeTransport_comp_of_between M J hbet]
    exact relativeTransport_length_of_between M J hbet
  rw [relativeTransport_comp_of_between M J hbet]
  unfold transporterPositiveLift
  rw [positiveSimpleLift_mul M _ _ hlen, map_mul]

/-- Concrete data in the pre-existing actual generated ribbon groupoid. -/
noncomputable def intervalRibbonData :
    IntervalGeneratorData (E := relativeSubspace J) (actualForms M J)
      (ActualReducedRibbonGroupoid M) where
  obj C := actualRibbonObject M ⟨actualChamberIndices M J C⟩
  positive := intervalRibbonPositive M J

theorem intervalRibbonData_respects : (intervalRibbonData M J).RespectsIntervals :=
  ⟨intervalRibbonPositive_self M J, fun _ _ _ h => intervalRibbonPositive_comp M J h⟩

/-- The actual functor, obtained from the interval presentation's proved
universal property, with no quotient imposed on the target ribbon labels. -/
noncomputable def intervalRibbonFunctor :
    IntervalGroupoid (E := relativeSubspace J) (actualForms M J) ⥤ ActualReducedRibbonGroupoid M :=
  (intervalRibbonData M J).extensionFunctor (intervalRibbonData_respects M J)

@[simp] theorem intervalRibbonFunctor_obj (C : ActualChamber M J) :
    (intervalRibbonFunctor M J).obj (intervalObject C) =
      actualRibbonObject M ⟨actualChamberIndices M J C⟩ := rfl

@[simp] theorem intervalRibbonFunctor_positive (C D : ActualChamber M J) :
    (intervalRibbonFunctor M J).map (intervalPositive C D) = intervalRibbonPositive M J C D :=
  (intervalRibbonData M J).extensionFunctor_positive (intervalRibbonData_respects M J) C D

/-- The object image lies in the actual parabolic-associate component of
`J`; no surjectivity onto unrelated components is asserted. -/
theorem intervalRibbonFunctor_object_associate (C : ActualChamber M J) :
    ParabolicAssociate M (actualChamberIndices M J C) J := by
  let L := chamberRawLabel M J C
  refine ⟨L.representative⁻¹, ?_⟩
  intro a
  change a ∈ Artin.coxeterParabolic M L.indices ↔
    (L.representative⁻¹)⁻¹ * a * L.representative⁻¹ ∈ Artin.coxeterParabolic M J
  rw [inv_inv, ← L.parabolic_conjugacy, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- Simultaneous left action on raw facet representatives by the actual
normalizer, retaining their standard-facet index sets. -/
noncomputable def normalizerRawLabel (w : CoxeterNormalizer M J) (L : RawFacetLabel M J) :
    RawFacetLabel M J where
  indices := L.indices
  representative := w.val * L.representative
  parabolic_conjugacy := by
    have he : (MulAut.conj (w.val * L.representative)).toMonoidHom =
        (MulAut.conj w.val).toMonoidHom.comp (MulAut.conj L.representative).toMonoidHom := by
      apply MonoidHom.ext
      intro g
      change (w.val * L.representative) * g * (w.val * L.representative)⁻¹ =
        w.val * (L.representative * g * L.representative⁻¹) * w.val⁻¹
      group
    rw [he, ← Subgroup.map_map, L.parabolic_conjugacy]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp w.property

theorem transportedChamber_rawLabel (w : CoxeterNormalizer M J) (L : RawFacetLabel M J) :
    transportedChamber M J w (actualChamberOfRawLabel M J L) =
      actualChamberOfRawLabel M J (normalizerRawLabel M J w L) := by
  let p := facetCanonicalPoint M L
  have hp : p ∈ (actualChamberOfRawLabel M J L).region := by
    rw [actualChamberOfRawLabel_region]
    exact facetCanonicalPoint_mem M L
  apply Chamber.eq_of_mem_region
    ((mem_transportedChamber_iff M J w _ p).mpr hp)
  rw [actualChamberOfRawLabel_region]
  apply (mem_translatedFacet_iff _ _).mpr
  refine ⟨canonicalDominant L.indices, canonicalDominant_mem_standardFacet M L.indices, ?_⟩
  change dualAction M (w.val * L.representative) (canonicalDominant L.indices) =
    dualAction M w.val (dualAction M L.representative (canonicalDominant L.indices))
  rw [map_mul, mul_apply_eq_comp]

theorem actualChamberIndices_transported (w : CoxeterNormalizer M J) (C : ActualChamber M J) :
    actualChamberIndices M J (transportedChamber M J w C) = actualChamberIndices M J C := by
  obtain ⟨L, rfl⟩ := actualChamberOfRawLabel_surjective M J C
  rw [transportedChamber_rawLabel, actualChamberIndices_rawLabel, actualChamberIndices_rawLabel]
  rfl

theorem relativeTransport_transported (w : CoxeterNormalizer M J) (C D : ActualChamber M J) :
    relativeTransport M J (transportedChamber M J w C) (transportedChamber M J w D) =
      relativeTransport M J C D := by
  obtain ⟨L, rfl⟩ := actualChamberOfRawLabel_surjective M J C
  obtain ⟨K, rfl⟩ := actualChamberOfRawLabel_surjective M J D
  rw [transportedChamber_rawLabel, transportedChamber_rawLabel,
    relativeTransport_eq_raw, relativeTransport_eq_raw]
  unfold rawRelativeTransport
  change M.toCoxeterSystem.minimalCosetRep K.indices
    ((w.val * L.representative)⁻¹ * (w.val * K.representative)) = _
  have he : (w.val * L.representative)⁻¹ * (w.val * K.representative) =
      L.representative⁻¹ * K.representative := by group
  rw [he]

theorem actualChamberIndices_smul (q : Artin.coxeterNormalizerQuotient M J)
    (C : ActualChamber M J) : actualChamberIndices M J (q • C) = actualChamberIndices M J C := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    ((Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J)) q
  exact actualChamberIndices_transported M J w C

theorem relativeTransport_smul (q : Artin.coxeterNormalizerQuotient M J)
    (C D : ActualChamber M J) : relativeTransport M J (q • C) (q • D) =
      relativeTransport M J C D := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    ((Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J)) q
  exact relativeTransport_transported M J w C D

/-- Invariance of the actual Artin labels, without identifying different
object types by an unproved equality of transported index sets. -/
theorem intervalRibbonPositive_smul_value (q : Artin.coxeterNormalizerQuotient M J)
    (C D : ActualChamber M J) :
    (intervalRibbonPositive M J (q • C) (q • D)).val.val =
      (intervalRibbonPositive M J C D).val.val := by
  simp only [intervalRibbonPositive_value, relativeTransport_smul]

private theorem actualReducedHom_heq_of_value {X Y X' Y' : RibbonObject M}
    {β γ : Artin.Group M} (hX : X = X') (hY : Y = Y')
    (hβ : ReducedArrow M X Y β) (hγ : ReducedArrow M X' Y' γ) (h : β = γ) :
    HEq (actualReducedHom M hβ) (actualReducedHom M hγ) := by
  subst X'
  subst Y'
  subst γ
  rfl

theorem intervalRibbonPositive_smul_heq (q : Artin.coxeterNormalizerQuotient M J)
    (C D : ActualChamber M J) :
    HEq (intervalRibbonPositive M J (q • C) (q • D)) (intervalRibbonPositive M J C D) := by
  unfold intervalRibbonPositive
  apply actualReducedHom_heq_of_value M
  · exact congrArg (fun K : Set I => (⟨K⟩ : RibbonObject M)) (actualChamberIndices_smul M J q C)
  · exact congrArg (fun K : Set I => (⟨K⟩ : RibbonObject M)) (actualChamberIndices_smul M J q D)
  · rw [relativeTransport_smul]

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual normalizer quotient acts trivially after the actual ribbon
functor, on every morphism of the presented interval groupoid. -/
theorem intervalRibbonFunctor_invariant (q : Artin.coxeterNormalizerQuotient M J) :
    intervalAction M J q ⋙ intervalRibbonFunctor M J = intervalRibbonFunctor M J := by
  apply (intervalRibbonData M J).extensionFunctor_unique (intervalRibbonData_respects M J)
  · funext X
    simp only [Functor.comp_obj, intervalAction_obj, intervalRibbonFunctor_obj,
      intervalRibbonData, actualChamberIndices_smul]
  · intro C D
    change HEq ((intervalRibbonFunctor M J).map
      ((intervalAction M J q).map (intervalPositive C D))) (intervalRibbonPositive M J C D)
    rw [intervalAction_positive]
    change HEq ((intervalRibbonFunctor M J).map (intervalPositive (q • C) (q • D)))
      (intervalRibbonPositive M J C D)
    rw [intervalRibbonFunctor_positive]
    exact intervalRibbonPositive_smul_heq M J q C D

end ArtinNormalisers.Chamber3
