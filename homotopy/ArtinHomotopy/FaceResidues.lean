import ArtinHomotopy.FacePrefixes
import ArtinHomotopy.ParabolicRootSigns
import ArtinChambers.FaceProjection
import ArtinChambers.RibbonLifting
import ArtinAsphericity.Simpliciality

/-!
# Actual face incidence and chamber residues

Incidence means literal membership in the closure of the actual chamber.
Its sign description and its interval description are proved for real linear
arrangements. The face opposition retains nonzero face signs and reverses
only signs of forms vanishing on the face.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Homotopy5

open Chamber3 Theorem18 Landmark1 Ribbon2 Asphericity5
open scoped Classical

section Arrangement

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} (ℓ : H → E →L[ℝ] ℝ)

/-- Literal geometric incidence with the actual closed chamber. -/
def ChamberIncident (z : E) (C : Chamber ℓ) : Prop := z ∈ closure C.region

/-- The signs at a face constrain only its nonvanishing forms. -/
def IncidentSigns (z : E) (C : Chamber ℓ) : Prop :=
  ∀ h, ℓ h z ≠ 0 → C.signs h = decide (0 < ℓ h z)

def chamberWeakRegion (C : Chamber ℓ) : Set E :=
  {z | ∀ h, if C.signs h then 0 ≤ ℓ h z else ℓ h z ≤ 0}

theorem incidentSigns_iff_weak (z : E) (C : Chamber ℓ) :
    IncidentSigns ℓ z C ↔ z ∈ chamberWeakRegion ℓ C := by
  classical
  constructor
  · intro h h'
    cases hs : C.signs h'
    · change ℓ h' z ≤ 0
      by_contra hn
      have hp : 0 < ℓ h' z := lt_of_not_ge hn
      have he := h h' (ne_of_gt hp)
      rw [hs, decide_eq_true hp] at he
      contradiction
    · change 0 ≤ ℓ h' z
      by_contra hn
      have hp : ℓ h' z < 0 := lt_of_not_ge hn
      have he := h h' (ne_of_lt hp)
      rw [hs, decide_eq_false (not_lt_of_ge hp.le)] at he
      contradiction
  · intro h h' hz
    have hh := h h'
    cases hs : C.signs h'
    · have hn : ℓ h' z ≤ 0 := by simpa [hs] using hh
      simp only [decide_eq_false (not_lt_of_ge hn)]
    · have hn : 0 ≤ ℓ h' z := by simpa [hs] using hh
      have hp : 0 < ℓ h' z := lt_of_le_of_ne hn (Ne.symm hz)
      simp only [decide_eq_true hp]

variable [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- The closure of any nonempty central sign cell is exactly its weak sign
cell. No simpliciality or independence of the forms is needed. -/
theorem closure_chamber_region (C : Chamber ℓ) : closure C.region = chamberWeakRegion ℓ C := by
  apply Set.Subset.antisymm
  · intro z hz h
    cases hs : C.signs h
    · change ℓ h z ≤ 0
      apply closure_minimal (t := {x | ℓ h x ≤ 0}) ?_
        (isClosed_le (ℓ h).continuous continuous_const) hz
      intro x hx
      exact (show ℓ h x < 0 from by simpa [signHalfSpace, hs] using hx h).le
    · change 0 ≤ ℓ h z
      apply closure_minimal (t := {x | 0 ≤ ℓ h x}) ?_
        (isClosed_le continuous_const (ℓ h).continuous) hz
      intro x hx
      exact (show 0 < ℓ h x from by simpa [signHalfSpace, hs] using hx h).le
  · intro z hz
    obtain ⟨c, hc⟩ := C.region_nonempty
    have hseg : openSegment ℝ c z ⊆ C.region := by
      intro y hy h
      obtain ⟨t, ht, rfl⟩ := (openSegment_eq_image_lineMap ℝ c z).le hy
      have hh := hc h
      have hzh := hz h
      cases hs : C.signs h
      · have hcn : ℓ h c < 0 := by simpa [signHalfSpace, hs] using hh
        have hzn : ℓ h z ≤ 0 := by simpa [hs] using hzh
        change ℓ h (AffineMap.lineMap c z t) < 0
        rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul]
        exact add_neg_of_neg_of_nonpos
          (mul_neg_of_pos_of_neg (sub_pos.mpr ht.2) hcn) (mul_nonpos_of_nonneg_of_nonpos ht.1.le hzn)
      · have hcp : 0 < ℓ h c := by simpa [signHalfSpace, hs] using hh
        have hzp : 0 ≤ ℓ h z := by simpa [hs] using hzh
        change 0 < ℓ h (AffineMap.lineMap c z t)
        rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul]
        exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr ht.2) hcp) (mul_nonneg ht.1.le hzp)
    exact closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ c z))

theorem chamberIncident_iff_signs (z : E) (C : Chamber ℓ) :
    ChamberIncident ℓ z C ↔ IncidentSigns ℓ z C := by
  rw [ChamberIncident, closure_chamber_region]
  exact (incidentSigns_iff_weak ℓ z C).symm

/-- Central opposition is actual negation of points and reversal of all signs. -/
noncomputable def oppositeChamber (C : Chamber ℓ) : Chamber ℓ where
  signs h := !(C.signs h)
  nonempty := by
    obtain ⟨c, hc⟩ := C.region_nonempty
    refine ⟨-c, fun h => ?_⟩
    have hh := hc h
    cases hs : C.signs h <;> simpa [signHalfSpace, hs, map_neg] using hh

omit [ContinuousAdd E] [ContinuousSMul ℝ E] in
@[simp] theorem oppositeChamber_signs (C : Chamber ℓ) (h : H) :
    (oppositeChamber ℓ C).signs h = !(C.signs h) := rfl

/-- Opposition in the residue of a face flips exactly the vanishing forms. -/
noncomputable def oppositeAtFace [Finite H] (z : E) (C : Chamber ℓ) : Chamber ℓ :=
  faceChamber ℓ z (oppositeChamber ℓ C)

omit [ContinuousAdd E] [ContinuousSMul ℝ E] in
theorem oppositeAtFace_signs_zero [Finite H] (z : E) (C : Chamber ℓ) {h : H}
    (hz : ℓ h z = 0) : (oppositeAtFace ℓ z C).signs h = !(C.signs h) :=
  faceChamber_signs_zero ℓ z (oppositeChamber ℓ C) hz

omit [ContinuousAdd E] [ContinuousSMul ℝ E] in
theorem oppositeAtFace_signs_nonzero [Finite H] (z : E) (C : Chamber ℓ) {h : H}
    (hz : ℓ h z ≠ 0) : (oppositeAtFace ℓ z C).signs h = decide (0 < ℓ h z) :=
  faceChamber_signs_nonzero ℓ z (oppositeChamber ℓ C) hz

theorem oppositeAtFace_incident [Finite H] (z : E) (C : Chamber ℓ) :
    ChamberIncident ℓ z (oppositeAtFace ℓ z C) :=
  (chamberIncident_iff_signs ℓ z _).mpr fun _ hz => oppositeAtFace_signs_nonzero ℓ z C hz

/-- The actual incident chamber set is exactly the sign interval from an
incident chamber to its opposite at the face. -/
theorem chamberIncident_iff_between_oppositeAtFace [Finite H] {z : E} {C : Chamber ℓ}
    (hC : ChamberIncident ℓ z C) (D : Chamber ℓ) :
    ChamberIncident ℓ z D ↔ ChamberBetween C D (oppositeAtFace ℓ z C) := by
  classical
  have hCs := (chamberIncident_iff_signs ℓ z C).mp hC
  rw [chamberIncident_iff_signs]
  constructor
  · intro hD h hshared
    by_cases hz : ℓ h z = 0
    · rw [oppositeAtFace_signs_zero ℓ z C hz] at hshared
      cases hs : C.signs h <;> simp [hs] at hshared
    · exact (hD h hz).trans (hCs h hz).symm
  · intro hb h hz
    have hshared : C.signs h = (oppositeAtFace ℓ z C).signs h :=
      (hCs h hz).trans (oppositeAtFace_signs_nonzero ℓ z C hz).symm
    exact (hb h hshared).trans (hCs h hz)

end Arrangement

section ActualFaces

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The actual coordinate-face point: zero on the added indices and one
on all other outside simple coordinates, then transported by the raw label. -/
noncomputable def rawFacePoint (L : RawFacetLabel M J) (T : Set I) : relativeSubspace J :=
  facetFlatEquiv L ⟨canonicalDominant (L.indices ∪ T), by
    intro i hi
    simp [canonicalDominant_apply_simpleRoot, hi]⟩

omit [Finite M.Group] in
theorem rawFacePoint_coordinates (L : RawFacetLabel M J) (T : Set I)
    (i : {i : I // i ∉ L.indices}) :
    rawFacetCoordinates L (rawFacePoint M J L T) i = if i.val ∈ T then 0 else 1 := by
  classical
  unfold rawFacetCoordinates rawFacePoint
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply,
    flatComplementCoordinates_apply,
    canonicalDominant_apply_simpleRoot]
  simp only [Set.mem_union, i.property, false_or]

theorem rawFacePoint_incident (L : RawFacetLabel M J) (T : Set I) :
    ChamberIncident (actualForms M J) (rawFacePoint M J L T) (actualChamberOfRawLabel M J L) := by
  have he : translatedFacet L = (rawFacetCoordinates L) ⁻¹'
      positiveOrthant {i : I // i ∉ L.indices} :=
    Set.ext (mem_translatedFacet_iff_coordinates_pos L)
  have hc : (rawFacetCoordinates L) ⁻¹' closure (positiveOrthant {i : I // i ∉ L.indices}) =
      closure ((rawFacetCoordinates L) ⁻¹' positiveOrthant {i : I // i ∉ L.indices}) :=
    (rawFacetCoordinates L).toHomeomorph.preimage_closure _
  rw [ChamberIncident, actualChamberOfRawLabel_region, he, ← hc, closure_positiveOrthant]
  intro i
  rw [rawFacePoint_coordinates]
  split_ifs <;> norm_num

theorem facePrefix_eq_simpleLift (X : RibbonObject M) (T : Set I) :
    facePrefix M X T = transporterPositiveLift M
      ((parabolicLongest M X.indices)⁻¹ * parabolicLongest M (X.indices ∪ T)) :=
  parabolicDelta_ratio_eq_simpleLift M X.indices (X.indices ∪ T) Set.subset_union_left

theorem facePrefix_projection (X : RibbonObject M) (T : Set I) :
    Artin.projection M (facePrefix M X T) =
      (parabolicLongest M X.indices)⁻¹ * parabolicLongest M (X.indices ∪ T) := by
  rw [facePrefix_eq_simpleLift, projection_transporterPositiveLift]

theorem facePrefix_projection_minimal (X : RibbonObject M) (T : Set I) :
    M.toCoxeterSystem.IsMinimalCosetRep (facePrefixTarget M X T).indices
      (Artin.projection M (facePrefix M X T)) := by
  apply simple_reduced_projection_minimal M (facePrefix_isRibbon M X T)
    (facePrefix_leftReduced M X T)
  rw [facePrefix_eq_simpleLift, projection_transporterPositiveLift]

private theorem canonical_eval_zero_of_supported (U : Set I) (r : Vector I)
    (hs : ∀ i, i ∉ U → r i = 0) : canonicalDominant U r = 0 := by
  classical
  have he : canonicalDominant U = Finsupp.linearCombination ℝ
      (fun i => canonicalDominant U (simpleRoot i)) :=
    (dualCoordinates (I := I)).symm_apply_apply (canonicalDominant U) |>.symm
  rw [he, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ U
  · simp [canonicalDominant_apply_simpleRoot, hi]
  · simp [hs i hi]

private theorem nonneg_support_of_canonical_eval_zero (U : Set I) {r : Vector I}
    (hr : 0 ≤ r) (hz : canonicalDominant U r = 0) : ∀ i, i ∉ U → r i = 0 := by
  classical
  have he : canonicalDominant U = Finsupp.linearCombination ℝ
      (fun i => canonicalDominant U (simpleRoot i)) :=
    (dualCoordinates (I := I)).symm_apply_apply (canonicalDominant U) |>.symm
  rw [he, Finsupp.linearCombination_apply, Finsupp.sum] at hz
  simp only [smul_eq_mul] at hz
  intro i hi
  by_cases hmem : i ∈ r.support
  · have hle := Finset.single_le_sum
      (fun j (_ : j ∈ r.support) => mul_nonneg (hr j) (canonicalDominant_isDominant U j)) hmem
    rw [hz] at hle
    have hri : r i ≤ 0 := by
      simpa [canonicalDominant_apply_simpleRoot, hi] using hle
    exact le_antisymm hri (hr i)
  · exact Finsupp.notMem_support_iff.mp hmem

omit [Finite M.Group] in
/-- A genuine root vanishes on the canonical face point exactly when its
support lies in the face's selected standard indices. -/
theorem canonicalDominant_root_zero_iff_support {U : Set I} {r : Vector I}
    (hr : r ∈ M.toCoxeterSystem.geometricRoots) :
    canonicalDominant U r = 0 ↔ ∀ i, i ∉ U → r i = 0 := by
  constructor
  · intro hz
    rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hr with hp | hn
    · exact nonneg_support_of_canonical_eval_zero U hp.le hz
    · have hs := nonneg_support_of_canonical_eval_zero U (neg_nonneg.mpr hn.le)
        (by simp only [map_neg, hz, neg_zero])
      intro i hi
      simpa only [Finsupp.neg_apply, neg_eq_zero] using hs i hi
  · exact canonical_eval_zero_of_supported U r

private theorem positive_coefficient_outside {U : Set I} {r : Vector I}
    (hp : 0 < r) (hz : canonicalDominant U r ≠ 0) : ∃ i, i ∉ U ∧ 0 < r i := by
  classical
  by_contra hn
  apply hz
  apply canonical_eval_zero_of_supported U r
  intro i hi
  exact le_antisymm (le_of_not_gt (fun hp' => hn ⟨i, hi, hp'⟩)) (hp.le i)

private theorem parabolicLongest_inv (U : Set I) :
    (parabolicLongest M U)⁻¹ = parabolicLongest M U := by
  apply mul_left_cancel (a := parabolicLongest M U)
  rw [mul_inv_cancel, parabolicLongest_mul_self]

/-- The inverse face-prefix projection reverses every positive source root
vanishing on the face, provided it does not vanish on the source flat. -/
theorem facePrefix_inverse_negative_of_zero (X : RibbonObject M) (T : Set I)
    {r : Vector I} (hr : r ∈ M.toCoxeterSystem.geometricRoots) (hp : 0 < r)
    (hsource : canonicalDominant X.indices r ≠ 0)
    (hz : canonicalDominant (X.indices ∪ T) r = 0) :
    M.toCoxeterSystem.geometricRepresentation (Artin.projection M (facePrefix M X T))⁻¹ r < 0 := by
  let U := X.indices ∪ T
  let v := M.toCoxeterSystem.geometricRepresentation (parabolicLongest M X.indices) r
  have hvroot : v ∈ M.toCoxeterSystem.geometricRoots :=
    (M.toCoxeterSystem.geometricRepresentation_apply_mem_geometricRoots_iff _).mpr hr
  obtain ⟨i, hi, hri⟩ := positive_coefficient_outside hp hsource
  have hvpos : 0 < v := by
    rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hvroot with hv | hv
    · exact hv
    · have he := geometricRepresentation_apply_outside_parabolic M X.indices
        (parabolicLongest_mem_parabolic M X.indices) r hi
      have hnonpos := hv.le i
      change M.toCoxeterSystem.geometricRepresentation (parabolicLongest M X.indices) r i ≤ 0
        at hnonpos
      rw [he] at hnonpos
      exact False.elim (hri.not_ge hnonpos)
  have hrU := (canonicalDominant_root_zero_iff_support M hr).mp hz
  have hwXU : parabolicLongest M X.indices ∈ Artin.coxeterParabolic M U :=
    Subgroup.closure_mono (Set.image_mono Set.subset_union_left)
      (parabolicLongest_mem_parabolic M X.indices)
  have hvU : ∀ j, j ∉ U → v j = 0 := by
    intro j hj
    rw [show v j = r j from geometricRepresentation_apply_outside_parabolic M U hwXU r hj]
    exact hrU j hj
  have hneg := parabolicLongest_positive_supported_negative M U hvroot hvpos hvU
  rw [facePrefix_projection, mul_inv_rev, inv_inv, parabolicLongest_inv,
    map_mul, mul_apply_eq_comp]
  exact hneg

/-- A nonvanishing positive root keeps its sign: the inverse face-prefix
projection cannot change its positive coefficient outside the face indices. -/
theorem facePrefix_inverse_positive_of_nonzero (X : RibbonObject M) (T : Set I)
    {r : Vector I} (hr : r ∈ M.toCoxeterSystem.geometricRoots) (hp : 0 < r)
    (hz : canonicalDominant (X.indices ∪ T) r ≠ 0) :
    0 < M.toCoxeterSystem.geometricRepresentation (Artin.projection M (facePrefix M X T))⁻¹ r := by
  let U := X.indices ∪ T
  obtain ⟨i, hi, hri⟩ := positive_coefficient_outside hp hz
  have hwXU : parabolicLongest M X.indices ∈ Artin.coxeterParabolic M U :=
    Subgroup.closure_mono (Set.image_mono Set.subset_union_left)
      (parabolicLongest_mem_parabolic M X.indices)
  have hdU : (Artin.projection M (facePrefix M X T))⁻¹ ∈ Artin.coxeterParabolic M U := by
    rw [facePrefix_projection]
    exact (Artin.coxeterParabolic M U).inv_mem
      ((Artin.coxeterParabolic M U).mul_mem ((Artin.coxeterParabolic M U).inv_mem hwXU)
        (parabolicLongest_mem_parabolic M U))
  have hroot := (M.toCoxeterSystem.geometricRepresentation_apply_mem_geometricRoots_iff
    (Artin.projection M (facePrefix M X T))⁻¹).mpr hr
  rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hroot with h | h
  · exact h
  · have hnonpos := h.le i
    rw [geometricRepresentation_apply_outside_parabolic M U hdU r hi] at hnonpos
    exact False.elim (hri.not_ge hnonpos)

/-- The actual endpoint label obtained by multiplying a raw facet label by
the actual Coxeter projection of its face-prefix ribbon. -/
noncomputable def facePrefixLabel (L : RawFacetLabel M J) (T : Set I) : RawFacetLabel M J :=
  rightTransportRawLabel M J L (facePrefixTarget M ⟨L.indices⟩ T).indices
    (Artin.projection M (facePrefix M ⟨L.indices⟩ T))
    (isRibbon_projection_transporter M (facePrefix_isRibbon M ⟨L.indices⟩ T))

theorem rawRelativeTransport_facePrefixLabel (L : RawFacetLabel M J) (T : Set I) :
    rawRelativeTransport M L (facePrefixLabel M J L T) =
      Artin.projection M (facePrefix M ⟨L.indices⟩ T) := by
  unfold rawRelativeTransport
  change M.toCoxeterSystem.minimalCosetRep (facePrefixTarget M ⟨L.indices⟩ T).indices
    (L.representative⁻¹ * (L.representative * Artin.projection M (facePrefix M ⟨L.indices⟩ T))) = _
  rw [inv_mul_cancel_left]
  exact (facePrefix_projection_minimal M ⟨L.indices⟩ T).minimalCosetRep_eq _

noncomputable def facePrefixFiberTarget (X : RibbonObject M) (T : Set I)
    (C : ChamberFiber M J X) : ChamberFiber M J (facePrefixTarget M X T) :=
  fiberTarget M J (X := X) (Y := facePrefixTarget M X T)
    (Artin.projection M (facePrefix M X T))
    (isRibbon_projection_transporter M (facePrefix_isRibbon M X T)) C

theorem fiberTarget_facePrefixLabel (L : RawFacetLabel M J) (T : Set I) :
    (facePrefixFiberTarget M J ⟨L.indices⟩ T
      (⟨actualChamberOfRawLabel M J L, actualChamberIndices_rawLabel M J L⟩ :
        ChamberFiber M J ⟨L.indices⟩)).val = actualChamberOfRawLabel M J (facePrefixLabel M J L T) := by
  have hchosen := chamberRawLabel_chamber M J (actualChamberOfRawLabel M J L)
  exact rightTransportRawLabel_independent M J hchosen _ _ _ _

omit [Finite M.Group] in
theorem rawFacePoint_pairing (L : RawFacetLabel M J) (T : Set I) (r : Vector I) :
    (rawFacePoint M J L T).val
      (M.toCoxeterSystem.geometricRepresentation L.representative r) =
        canonicalDominant (L.indices ∪ T) r :=
  dualAction_pairing M L.representative (canonicalDominant (L.indices ∪ T)) r

omit [Finite M.Group] in
private theorem rawRelativeTransport_self (L : RawFacetLabel M J) :
    rawRelativeTransport M L L = 1 := by
  unfold rawRelativeTransport
  rw [inv_mul_cancel]
  exact (M.toCoxeterSystem.isMinimalCosetRep_one _).minimalCosetRep_eq _

/-- The actual face-prefix endpoint is exactly opposition in the actual
geometric residue. Nonzero face signs are fixed and zero face signs reversed. -/
theorem facePrefixLabel_eq_oppositeAtFace (L : RawFacetLabel M J) (T : Set I) :
    actualChamberOfRawLabel M J (facePrefixLabel M J L T) =
      oppositeAtFace (actualForms M J) (rawFacePoint M J L T) (actualChamberOfRawLabel M J L) := by
  apply Chamber.ext
  funext R
  let r := M.toCoxeterSystem.geometricRepresentation L.representative⁻¹ R.val
  have hRroot : R.val ∈ M.toCoxeterSystem.geometricRoots := by
    obtain ⟨w, i, he⟩ := R.property.1
    exact M.toCoxeterSystem.mem_geometricRoots.mpr ⟨w, i, he⟩
  have hr : r ∈ M.toCoxeterSystem.geometricRoots :=
    (M.toCoxeterSystem.geometricRepresentation_apply_mem_geometricRoots_iff L.representative⁻¹).mpr hRroot
  have heR : M.toCoxeterSystem.geometricRepresentation L.representative r = R.val := by
    dsimp only [r]
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  have hface : actualForms M J R (rawFacePoint M J L T) = canonicalDominant (L.indices ∪ T) r := by
    calc
      _ = (rawFacePoint M J L T).val
          (M.toCoxeterSystem.geometricRepresentation L.representative r) :=
        congrArg (rawFacePoint M J L T).val heR.symm
      _ = _ := rawFacePoint_pairing M J L T r
  have hbase : actualForms M J R (facetCanonicalPoint M L) = canonicalDominant L.indices r := by
    calc
      _ = (facetCanonicalPoint M L).val
          (M.toCoxeterSystem.geometricRepresentation L.representative r) :=
        congrArg (facetCanonicalPoint M L).val heR.symm
      _ = _ := facetCanonicalPoint_pairing M L r
  have hCpoint : facetCanonicalPoint M L ∈ (actualChamberOfRawLabel M J L).region := by
    rw [actualChamberOfRawLabel_region]
    exact facetCanonicalPoint_mem M L
  have hsource : canonicalDominant L.indices r ≠ 0 := by
    rw [← hbase]
    exact (actualChamberOfRawLabel M J L).region_subset_regularSet hCpoint R
  have hC : (actualChamberOfRawLabel M J L).signs R = true ↔ 0 < r := by
    simpa only [rawRelativeTransport_self, inv_one, map_one, one_apply_eq_self] using rawFacet_sign_iff M J L L R
  have hD := rawFacet_sign_iff M J L (facePrefixLabel M J L T) R
  rw [rawRelativeTransport_facePrefixLabel] at hD
  have hsourceNeg : canonicalDominant L.indices (-r) ≠ 0 := by simpa only [map_neg, neg_ne_zero] using hsource
  have hnegroot : -r ∈ M.toCoxeterSystem.geometricRoots := M.toCoxeterSystem.neg_mem_geometricRoots_iff.mpr hr
  by_cases hz : actualForms M J R (rawFacePoint M J L T) = 0
  · rw [oppositeAtFace_signs_zero _ _ _ hz]
    have hzr : canonicalDominant (L.indices ∪ T) r = 0 := hface.symm.trans hz
    rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hr with hp | hn
    · have hc := hC.mpr hp
      have hneg := facePrefix_inverse_negative_of_zero M ⟨L.indices⟩ T hr hp hsource hzr
      have hd : (actualChamberOfRawLabel M J (facePrefixLabel M J L T)).signs R = false := by
        cases hs : (actualChamberOfRawLabel M J (facePrefixLabel M J L T)).signs R
        · rfl
        · exact False.elim (lt_asymm (hD.mp hs) hneg)
      rw [hc, hd]
      rfl
    · have hc : (actualChamberOfRawLabel M J L).signs R = false := by
        cases hs : (actualChamberOfRawLabel M J L).signs R
        · rfl
        · exact False.elim (lt_asymm (hC.mp hs) hn)
      have hneg := facePrefix_inverse_negative_of_zero M ⟨L.indices⟩ T hnegroot
        (neg_pos.mpr hn) hsourceNeg (by simp only [map_neg, hzr, neg_zero])
      have hpos : 0 < M.toCoxeterSystem.geometricRepresentation
          (Artin.projection M (facePrefix M ⟨L.indices⟩ T))⁻¹ r := by
        simpa only [map_neg, neg_lt_zero] using hneg
      rw [hD.mpr hpos, hc]
      rfl
  · rw [oppositeAtFace_signs_nonzero _ _ _ hz]
    have hsC := (chamberIncident_iff_signs _ _ _).mp (rawFacePoint_incident M J L T) R hz
    rw [← hsC]
    have hzr : canonicalDominant (L.indices ∪ T) r ≠ 0 := fun h => hz (hface.trans h)
    rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hr with hp | hn
    · have hpos := facePrefix_inverse_positive_of_nonzero M ⟨L.indices⟩ T hr hp hzr
      rw [hD.mpr hpos, hC.mpr hp]
    · have hc : (actualChamberOfRawLabel M J L).signs R = false := by
        cases hs : (actualChamberOfRawLabel M J L).signs R
        · rfl
        · exact False.elim (lt_asymm (hC.mp hs) hn)
      have hpos := facePrefix_inverse_positive_of_nonzero M ⟨L.indices⟩ T hnegroot
        (neg_pos.mpr hn) (by simpa only [map_neg, neg_ne_zero] using hzr)
      have hneg : M.toCoxeterSystem.geometricRepresentation
          (Artin.projection M (facePrefix M ⟨L.indices⟩ T))⁻¹ r < 0 := by
        simpa only [map_neg, neg_pos] using hpos
      have hd : (actualChamberOfRawLabel M J (facePrefixLabel M J L T)).signs R = false := by
        cases hs : (actualChamberOfRawLabel M J (facePrefixLabel M J L T)).signs R
        · rfl
        · exact False.elim (lt_asymm (hD.mp hs) hneg)
      rw [hc, hd]

theorem fiberTarget_facePrefix_oppositeAtFace (L : RawFacetLabel M J) (T : Set I) :
    (facePrefixFiberTarget M J ⟨L.indices⟩ T
      (⟨actualChamberOfRawLabel M J L, actualChamberIndices_rawLabel M J L⟩ :
        ChamberFiber M J ⟨L.indices⟩)).val =
      oppositeAtFace (actualForms M J) (rawFacePoint M J L T) (actualChamberOfRawLabel M J L) := by
  rw [fiberTarget_facePrefixLabel, facePrefixLabel_eq_oppositeAtFace]

/-- Actual residue incidence is precisely the chamber interval ending at
the actual face-prefix endpoint. -/
theorem rawFacePoint_incident_iff_between_facePrefix (L : RawFacetLabel M J) (T : Set I)
    (D : ActualChamber M J) :
    ChamberIncident (actualForms M J) (rawFacePoint M J L T) D ↔
      ChamberBetween (actualChamberOfRawLabel M J L) D
        (actualChamberOfRawLabel M J (facePrefixLabel M J L T)) := by
  rw [facePrefixLabel_eq_oppositeAtFace]
  exact chamberIncident_iff_between_oppositeAtFace _ (rawFacePoint_incident M J L T) D

theorem ribbonPrefix_simpleLift_iff (u v : M.Group) :
    RibbonPrefix M (transporterPositiveLift M u) (transporterPositiveLift M v) ↔
      M.toCoxeterSystem.length v = M.toCoxeterSystem.length u +
        M.toCoxeterSystem.length (u⁻¹ * v) := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  exact (positivePrefix_iff_parentQuotient M _ _).symm.trans
    (OAI.HarmonicArtin.positivePrefix_simple_iff M u v)

theorem facePrefix_eq_simpleLift_projection (X : RibbonObject M) (T : Set I) :
    facePrefix M X T = transporterPositiveLift M (Artin.projection M (facePrefix M X T)) := by
  rw [facePrefix_projection]
  exact facePrefix_eq_simpleLift M X T

/-- Residue incidence is equivalent to actual positive left divisibility
of the face prefix by the chamber's canonical simple ribbon. -/
theorem rawFacePoint_incident_iff_ribbonPrefix (L : RawFacetLabel M J) (T : Set I)
    (D : ActualChamber M J) :
    ChamberIncident (actualForms M J) (rawFacePoint M J L T) D ↔
      RibbonPrefix M (transporterPositiveLift M
        (relativeTransport M J (actualChamberOfRawLabel M J L) D)) (facePrefix M ⟨L.indices⟩ T) := by
  rw [rawFacePoint_incident_iff_between_facePrefix, chamberBetween_iff_relativeTransport_length,
    relativeTransport_eq_raw M J L (facePrefixLabel M J L T), rawRelativeTransport_facePrefixLabel]
  have hη := facePrefix_eq_simpleLift_projection M (⟨L.indices⟩ : RibbonObject M) T
  simpa only [← hη] using
    (ribbonPrefix_simpleLift_iff M
      (relativeTransport M J (actualChamberOfRawLabel M J L) D)
      (Artin.projection M (facePrefix M ⟨L.indices⟩ T))).symm

/-- Actual geometric face residues, defined by actual closure incidence. -/
def FaceResidue (L : RawFacetLabel M J) (T : Set I) :=
  {D : ActualChamber M J // ChamberIncident (actualForms M J) (rawFacePoint M J L T) D}

/-- Actual simple positive generated ribbon divisors of the actual face
prefix, defined algebraically without mentioning chambers or incidence. -/
def SimpleFaceDivisor (X : RibbonObject M) (T : Set I) :=
  {p : Artin.Group M // ∃ Y : RibbonObject M,
    PositiveReducedArrow M X Y p ∧
    p = transporterPositiveLift M (Artin.projection M p) ∧
    RibbonPrefix M p (facePrefix M X T)}

noncomputable def residueToFaceDivisor (L : RawFacetLabel M J) (T : Set I)
    (D : FaceResidue M J L T) : SimpleFaceDivisor M ⟨L.indices⟩ T := by
  let d := relativeTransport M J (actualChamberOfRawLabel M J L) D.val
  refine ⟨transporterPositiveLift M d, ⟨⟨actualChamberIndices M J D.val⟩, ?_, ?_, ?_⟩⟩
  · simpa only [actualChamberIndices_rawLabel] using transporterPositiveLift_generated M
      (relativeTransport_conjugacy M J (actualChamberOfRawLabel M J L) D.val)
      (relativeTransport_minimal M J (actualChamberOfRawLabel M J L) D.val)
  · rw [projection_transporterPositiveLift]
  · exact (rawFacePoint_incident_iff_ribbonPrefix M J L T D.val).mp D.property

private theorem relativeTransport_injective (C : ActualChamber M J) :
    Function.Injective (relativeTransport M J C) := by
  intro D E h
  apply Chamber.ext
  funext R
  have hd := rawFacet_sign_iff M J (chamberRawLabel M J C) (chamberRawLabel M J D) R
  have he := rawFacet_sign_iff M J (chamberRawLabel M J C) (chamberRawLabel M J E) R
  rw [chamberRawLabel_chamber] at hd he
  change (D.signs R = true ↔ 0 < M.toCoxeterSystem.geometricRepresentation
    (relativeTransport M J C D)⁻¹
      (M.toCoxeterSystem.geometricRepresentation (chamberRawLabel M J C).representative⁻¹ R.val)) at hd
  change (E.signs R = true ↔ 0 < M.toCoxeterSystem.geometricRepresentation
    (relativeTransport M J C E)⁻¹
      (M.toCoxeterSystem.geometricRepresentation (chamberRawLabel M J C).representative⁻¹ R.val)) at he
  rw [h] at hd
  have hb := hd.trans he.symm
  cases hD : D.signs R <;> cases hE : E.signs R <;> try rfl
  all_goals simp [hD, hE] at hb

theorem residueToFaceDivisor_injective (L : RawFacetLabel M J) (T : Set I) :
    Function.Injective (residueToFaceDivisor M J L T) := by
  intro D E h
  have hv := congrArg Subtype.val h
  change transporterPositiveLift M (relativeTransport M J (actualChamberOfRawLabel M J L) D.val) =
    transporterPositiveLift M (relativeTransport M J (actualChamberOfRawLabel M J L) E.val) at hv
  have hd := congrArg (Artin.projection M) hv
  simp only [projection_transporterPositiveLift] at hd
  apply Subtype.ext
  exact relativeTransport_injective M J (actualChamberOfRawLabel M J L) hd

theorem residueToFaceDivisor_surjective (L : RawFacetLabel M J) (T : Set I) :
    Function.Surjective (residueToFaceDivisor M J L T) := by
  rintro ⟨p, ⟨Y, hp, hs, hpref⟩⟩
  let C : ChamberFiber M J (⟨L.indices⟩ : RibbonObject M) :=
    ⟨actualChamberOfRawLabel M J L, actualChamberIndices_rawLabel M J L⟩
  let D : ChamberFiber M J Y := fiberTarget M J (X := ⟨L.indices⟩) (Y := Y)
    (Artin.projection M p) (isRibbon_projection_transporter M hp.isRibbon) C
  have hmin := simple_reduced_projection_minimal M hp.isRibbon hp.leftReduced hs
  have hrel : relativeTransport M J C.val D.val = Artin.projection M p :=
    relativeTransport_fiberTarget M J _ _ hmin C
  have hvalue : transporterPositiveLift M
      (relativeTransport M J (actualChamberOfRawLabel M J L) D.val) = p := by
    rw [show relativeTransport M J (actualChamberOfRawLabel M J L) D.val =
      Artin.projection M p from hrel]
    exact hs.symm
  have hinc : ChamberIncident (actualForms M J) (rawFacePoint M J L T) D.val := by
    apply (rawFacePoint_incident_iff_ribbonPrefix M J L T D.val).mpr
    rw [hvalue]
    exact hpref
  refine ⟨⟨D.val, hinc⟩, ?_⟩
  apply Subtype.ext
  exact hvalue

/-- The actual residue chambers are in bijection with the actual simple
positive generated ribbon divisors of the actual face fundamental prefix. -/
noncomputable def faceResidueEquivSimpleFaceDivisor (L : RawFacetLabel M J) (T : Set I) :
    FaceResidue M J L T ≃ SimpleFaceDivisor M ⟨L.indices⟩ T :=
  Equiv.ofBijective (residueToFaceDivisor M J L T)
    ⟨residueToFaceDivisor_injective M J L T, residueToFaceDivisor_surjective M J L T⟩

end ActualFaces

end ArtinNormalisers.Homotopy5
