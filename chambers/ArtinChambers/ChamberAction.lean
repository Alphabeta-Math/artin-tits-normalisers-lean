module

public import ArtinChambers.ActualArrangement
public import ArtinNormalisers.Theorem18.NormalizerAction

/-!
# The actual normalizer action on relative chambers and tubes

Root labels are transported by the primal geometric representation, and
points of the relative flat by its actual contragredient representation.
Their evaluation pairing gives covariance of geometric sign cells and tubes.
The pointwise trivial parabolic action then descends to the same normalizer
quotient that already acts on the actual complexified complement.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open Theorem18

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The actual primal action permutes the retained root labels. -/
noncomputable def retainedRootEquiv (w : CoxeterNormalizer M J) :
    RelativeRoot M J ≃ RelativeRoot M J where
  toFun r := ⟨M.toCoxeterSystem.geometricRepresentation w.val r.val,
    geometricAction_mem_retainedRoots M J w r.property⟩
  invFun r := ⟨M.toCoxeterSystem.geometricRepresentation w⁻¹.val r.val,
    geometricAction_mem_retainedRoots M J w⁻¹ r.property⟩
  left_inv r := by
    apply Subtype.ext
    simp only [Subgroup.coe_inv, ← mul_apply_eq_comp, ← map_mul,
      inv_mul_cancel, map_one, one_apply_eq_self]
  right_inv r := by
    apply Subtype.ext
    simp only [Subgroup.coe_inv, ← mul_apply_eq_comp, ← map_mul,
      mul_inv_cancel, map_one, one_apply_eq_self]

@[simp] theorem retainedRootEquiv_apply_val (w : CoxeterNormalizer M J)
    (r : RelativeRoot M J) :
    (retainedRootEquiv M J w r).val =
      M.toCoxeterSystem.geometricRepresentation w.val r.val := rfl

/-- The actual restricted contragredient action as a linear homeomorphism. -/
noncomputable def normalizerFlatEquiv (w : CoxeterNormalizer M J) :
    relativeSubspace J ≃L[ℝ] relativeSubspace J where
  toFun := normalizerRepresentation M J w
  invFun := normalizerRepresentation M J w⁻¹
  left_inv x := by
    simp only [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
      map_one, one_apply_eq_self]
  right_inv x := by
    simp only [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel,
      map_one, one_apply_eq_self]
  map_add' := (normalizerRepresentation M J w).map_add
  map_smul' := (normalizerRepresentation M J w).map_smul
  continuous_toFun := continuous_normalizerRepresentation M J w
  continuous_invFun := continuous_normalizerRepresentation M J w⁻¹

@[simp] theorem normalizerFlatEquiv_apply (w : CoxeterNormalizer M J)
    (x : relativeSubspace J) :
    normalizerFlatEquiv M J w x = normalizerRepresentation M J w x := rfl

/-- Actual restricted forms obey the primal/contragredient pairing. -/
theorem actualForms_transport (w : CoxeterNormalizer M J)
    (r : RelativeRoot M J) (x : relativeSubspace J) :
    actualForms M J (retainedRootEquiv M J w r) (normalizerFlatEquiv M J w x) =
      actualForms M J r x :=
  dualAction_pairing M w.val x.val r.val

/-- Transport the signs of a realized chamber by the actual root permutation. -/
noncomputable def transportedChamber (w : CoxeterNormalizer M J)
    (C : ActualChamber M J) : ActualChamber M J where
  signs r := C.signs ((retainedRootEquiv M J w).symm r)
  nonempty := by
    obtain ⟨x, hx⟩ := C.region_nonempty
    refine ⟨normalizerFlatEquiv M J w x, fun r => ?_⟩
    obtain ⟨s, rfl⟩ := (retainedRootEquiv M J w).surjective r
    change (if C.signs ((retainedRootEquiv M J w).symm
      (retainedRootEquiv M J w s)) then
        0 < actualForms M J (retainedRootEquiv M J w s) (normalizerFlatEquiv M J w x)
      else actualForms M J (retainedRootEquiv M J w s) (normalizerFlatEquiv M J w x) < 0)
    simpa only [Equiv.symm_apply_apply, actualForms_transport, signHalfSpace, Set.mem_ofPred_eq] using hx s

@[simp] theorem transportedChamber_signs (w : CoxeterNormalizer M J)
    (C : ActualChamber M J) (r : RelativeRoot M J) :
    (transportedChamber M J w C).signs (retainedRootEquiv M J w r) = C.signs r :=
  congrArg C.signs ((retainedRootEquiv M J w).symm_apply_apply r)

/-- Transported chamber regions are the images under the actual flat action. -/
theorem mem_transportedChamber_iff (w : CoxeterNormalizer M J)
    (C : ActualChamber M J) (x : relativeSubspace J) :
    normalizerRepresentation M J w x ∈ (transportedChamber M J w C).region ↔
      x ∈ C.region := by
  constructor
  · intro hx r
    have h := hx (retainedRootEquiv M J w r)
    change (if (transportedChamber M J w C).signs (retainedRootEquiv M J w r) then
      0 < actualForms M J (retainedRootEquiv M J w r) (normalizerFlatEquiv M J w x)
      else actualForms M J (retainedRootEquiv M J w r) (normalizerFlatEquiv M J w x) < 0) at h
    simpa only [transportedChamber_signs, actualForms_transport, signHalfSpace, Set.mem_ofPred_eq] using h
  · intro hx r
    obtain ⟨s, rfl⟩ := (retainedRootEquiv M J w).surjective r
    change (if (transportedChamber M J w C).signs (retainedRootEquiv M J w s) then
      0 < actualForms M J (retainedRootEquiv M J w s) (normalizerFlatEquiv M J w x)
      else actualForms M J (retainedRootEquiv M J w s) (normalizerFlatEquiv M J w x) < 0)
    simpa only [transportedChamber_signs, actualForms_transport, signHalfSpace, Set.mem_ofPred_eq] using hx s

/-- Exact geometric image of a realized chamber region. -/
theorem normalizer_image_chamber_region (w : CoxeterNormalizer M J)
    (C : ActualChamber M J) :
    normalizerFlatEquiv M J w '' C.region = (transportedChamber M J w C).region := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_transportedChamber_iff M J w C x).2 hx
  · intro hy
    obtain ⟨x, rfl⟩ := (normalizerFlatEquiv M J w).surjective y
    exact ⟨x, (mem_transportedChamber_iff M J w C x).1 hy, rfl⟩

@[simp] theorem transportedChamber_one (C : ActualChamber M J) :
    transportedChamber M J 1 C = C := by
  obtain ⟨x, hx⟩ := C.region_nonempty
  apply Chamber.eq_of_mem_region (x := x) _ hx
  have h := (mem_transportedChamber_iff M J 1 C x).2 hx
  simpa only [map_one, one_apply_eq_self] using h

theorem transportedChamber_mul (w z : CoxeterNormalizer M J)
    (C : ActualChamber M J) :
    transportedChamber M J (w * z) C =
      transportedChamber M J w (transportedChamber M J z C) := by
  obtain ⟨x, hx⟩ := C.region_nonempty
  apply Chamber.eq_of_mem_region ((mem_transportedChamber_iff M J (w * z) C x).2 hx)
  have h := (mem_transportedChamber_iff M J w (transportedChamber M J z C)
    (normalizerRepresentation M J z x)).2 ((mem_transportedChamber_iff M J z C x).2 hx)
  simpa only [map_mul, mul_apply_eq_comp] using h

/-- The actual normalizer acts on the actual realized chamber type. -/
noncomputable def normalizerChamberAction :
    CoxeterNormalizer M J →* Equiv.Perm (ActualChamber M J) where
  toFun w :=
    { toFun := transportedChamber M J w
      invFun := transportedChamber M J w⁻¹
      left_inv C := by
        rw [← transportedChamber_mul, inv_mul_cancel, transportedChamber_one]
      right_inv C := by
        rw [← transportedChamber_mul, mul_inv_cancel, transportedChamber_one] }
  map_one' := by
    apply Equiv.ext
    exact transportedChamber_one M J
  map_mul' w z := by
    apply Equiv.ext
    exact transportedChamber_mul M J w z

/-- Pointwise triviality on the actual flat implies triviality on its chambers. -/
theorem parabolic_le_normalizerChamberAction_ker :
    (Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J) ≤
      (normalizerChamberAction M J).ker := by
  intro w hw
  have hflat := parabolic_le_normalizerRepresentation_ker M J hw
  change normalizerRepresentation M J w = 1 at hflat
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro C
  change transportedChamber M J w C = C
  obtain ⟨x, hx⟩ := C.region_nonempty
  apply Chamber.eq_of_mem_region (x := x) _ hx
  have h := (mem_transportedChamber_iff M J w C x).2 hx
  simpa only [hflat, one_apply_eq_self] using h

/-- The actual normalizer quotient acts on the realized relative chambers. -/
noncomputable def quotientChamberAction :
    Artin.coxeterNormalizerQuotient M J →* Equiv.Perm (ActualChamber M J) :=
  QuotientGroup.lift _ (normalizerChamberAction M J)
    (parabolic_le_normalizerChamberAction_ker M J)

noncomputable instance quotientChamberMulAction :
    MulAction (Artin.coxeterNormalizerQuotient M J) (ActualChamber M J) :=
  MulAction.compHom _ (quotientChamberAction M J)

@[simp] theorem quotientChamberAction_mk (w : CoxeterNormalizer M J)
    (C : ActualChamber M J) :
    quotientChamberAction M J
      (QuotientGroup.mk' ((Artin.coxeterParabolic M J).subgroupOf
        (CoxeterNormalizer M J)) w) C = transportedChamber M J w C := rfl

@[simp] theorem quotient_chamber_smul_eq (q : Artin.coxeterNormalizerQuotient M J)
    (C : ActualChamber M J) : q • C = quotientChamberAction M J q C := rfl

/-- Region covariance under the existing actual quotient representation. -/
theorem quotient_mem_chamber_region_iff (q : Artin.coxeterNormalizerQuotient M J)
    (C : ActualChamber M J) (x : relativeSubspace J) :
    quotientRepresentation M J q x ∈ (q • C).region ↔ x ∈ C.region := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    ((Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J)) q
  exact mem_transportedChamber_iff M J w C x

/-- Covariance uses the previously defined actual complement action. -/
theorem normalizer_mem_actualTubeSet_iff (w : CoxeterNormalizer M J)
    (C : ActualChamber M J) (p : Complement M J) :
    normalizerComplementAction M J w p ∈ actualTubeSet M J (transportedChamber M J w C) ↔
      p ∈ actualTubeSet M J C := by
  change (∀ r, actualForms M J r (normalizerRepresentation M J w p.val.1) = 0 →
    normalizerRepresentation M J w p.val.2 ∈
      signHalfSpace (actualForms M J r) ((transportedChamber M J w C).signs r)) ↔
    (∀ r, actualForms M J r p.val.1 = 0 →
      p.val.2 ∈ signHalfSpace (actualForms M J r) (C.signs r))
  constructor
  · intro hp r hr
    have hz : actualForms M J (retainedRootEquiv M J w r)
        (normalizerRepresentation M J w p.val.1) = 0 := by
      rw [← normalizerFlatEquiv_apply, actualForms_transport, hr]
    have h := hp (retainedRootEquiv M J w r) hz
    simpa only [signHalfSpace, Set.mem_ofPred_eq, transportedChamber_signs,
      ← normalizerFlatEquiv_apply, actualForms_transport] using h
  · intro hp r hr
    obtain ⟨s, rfl⟩ := (retainedRootEquiv M J w).surjective r
    have hz : actualForms M J s p.val.1 = 0 := by
      rwa [← normalizerFlatEquiv_apply, actualForms_transport] at hr
    simpa only [signHalfSpace, Set.mem_ofPred_eq, transportedChamber_signs,
      ← normalizerFlatEquiv_apply, actualForms_transport] using hp s hz

/-- The chamber-indexed tube cover is equivariant for the actual quotient action. -/
theorem quotient_mem_actualTubeSet_iff (q : Artin.coxeterNormalizerQuotient M J)
    (C : ActualChamber M J) (p : Complement M J) :
    q • p ∈ actualTubeSet M J (q • C) ↔ p ∈ actualTubeSet M J C := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    ((Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J)) q
  exact normalizer_mem_actualTubeSet_iff M J w C p

/-- Exact image covariance of the actual open tube subsets. -/
theorem quotient_image_actualTubeSet (q : Artin.coxeterNormalizerQuotient M J)
    (C : ActualChamber M J) :
    (fun p : Complement M J => q • p) '' actualTubeSet M J C =
      actualTubeSet M J (q • C) := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (quotient_mem_actualTubeSet_iff M J q C x).2 hx
  · intro hp
    refine ⟨q⁻¹ • p, ?_, smul_inv_smul q p⟩
    have h := (quotient_mem_actualTubeSet_iff M J q⁻¹ (q • C) p).2 hp
    simpa only [inv_smul_smul] using h

end ArtinNormalisers.Chamber3
