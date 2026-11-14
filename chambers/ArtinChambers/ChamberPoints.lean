module

public import ArtinChambers.ChamberLabels
public import ArtinChambers.ChamberAction
public import ArtinChambers.IntervalForward

/-!
# Canonical equivariant points of actual relative chambers

For a raw facet label `(w,K)`, take the actual point
`w · canonicalDominant K`. Its right-parabolic ambiguity fixes the point,
so it descends to the algebraic facet-label quotient and then to actual
chambers. Left multiplication of raw labels proves covariance under the
actual normalizer and its quotient. No equivariance property is assumed
of an arbitrary chamber-point choice.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

namespace ArtinNormalisers.Chamber3

open Theorem18 Landmark1

variable {I : Type*} {M : CoxeterMatrix I} {J : Set I}

/-- The canonical point of an actual transported standard facet. -/
noncomputable def rawCanonicalFacetPoint (L : RawFacetLabel M J) : relativeSubspace J :=
  facetFlatEquiv L ⟨canonicalDominant L.indices, canonicalDominant_mem_relativeSubspace L.indices⟩

@[simp]
theorem rawCanonicalFacetPoint_val (L : RawFacetLabel M J) :
    (rawCanonicalFacetPoint L).val = dualAction M L.representative (canonicalDominant L.indices) := rfl

theorem rawCanonicalFacetPoint_mem (L : RawFacetLabel M J) :
    rawCanonicalFacetPoint L ∈ translatedFacet L :=
  ⟨_, canonicalDominant_mem_standardFacet M L.indices, rfl⟩

/-- The actual right source parabolic fixes the canonical dominant point. -/
theorem rawCanonicalFacetPoint_eq_of_related (L K : RawFacetLabel M J)
    (h : (rawFacetSetoid M J).r L K) : rawCanonicalFacetPoint L = rawCanonicalFacetPoint K := by
  obtain ⟨hIK, hc⟩ := h
  apply Subtype.ext
  change dualAction M L.representative (canonicalDominant L.indices) =
    dualAction M K.representative (canonicalDominant K.indices)
  rw [← hIK]
  have hfix := (canonicalDominant_fixed_iff M L.indices
    (L.representative⁻¹ * K.representative)).mpr hc
  calc
    dualAction M L.representative (canonicalDominant L.indices) =
      dualAction M L.representative
        (dualAction M (L.representative⁻¹ * K.representative) (canonicalDominant L.indices)) := by
          rw [hfix]
    _ = dualAction M K.representative (canonicalDominant L.indices) := by
      rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]

/-- The canonical point descends through the actual right-coset relation. -/
noncomputable def facetLabelCanonicalPoint : FacetLabel M J → relativeSubspace J :=
  Quotient.lift rawCanonicalFacetPoint rawCanonicalFacetPoint_eq_of_related

@[simp]
theorem facetLabelCanonicalPoint_mk (L : RawFacetLabel M J) :
    facetLabelCanonicalPoint (Quotient.mk (rawFacetSetoid M J) L) = rawCanonicalFacetPoint L := rfl

theorem facetLabelCanonicalPoint_mem (L : FacetLabel M J) :
    facetLabelCanonicalPoint L ∈ facetRegion L := by
  refine Quotient.inductionOn L ?_
  exact rawCanonicalFacetPoint_mem

variable (M) [Finite M.Group] (J)

/-- The actual real point of a chamber, obtained through its unique
algebraic facet label, not by choosing an arbitrary point of its region. -/
noncomputable def actualChamberPoint (C : ActualChamber M J) : relativeSubspace J :=
  facetLabelCanonicalPoint ((facetLabelEquivActualChamber M J).symm C)

theorem actualChamberPoint_mem (C : ActualChamber M J) :
    actualChamberPoint M J C ∈ C.region := by
  let L := (facetLabelEquivActualChamber M J).symm C
  have hC : actualChamberOfFacetLabel M J L = C :=
    (facetLabelEquivActualChamber M J).apply_symm_apply C
  change facetLabelCanonicalPoint L ∈ C.region
  rw [← hC, actualChamberOfFacetLabel_region]
  exact facetLabelCanonicalPoint_mem L

theorem actualChamberPoint_rawLabel (L : RawFacetLabel M J) :
    actualChamberPoint M J (actualChamberOfRawLabel M J L) = rawCanonicalFacetPoint L := by
  change facetLabelCanonicalPoint ((facetLabelEquivActualChamber M J).symm
    (facetLabelEquivActualChamber M J (Quotient.mk _ L))) = rawCanonicalFacetPoint L
  rw [Equiv.symm_apply_apply, facetLabelCanonicalPoint_mk]

omit [Finite M.Group] in
/-- Left normalizer multiplication preserves the actual parabolic-conjugacy
condition while retaining the source index set. -/
noncomputable def normalizerRawFacetLabel (n : CoxeterNormalizer M J) (L : RawFacetLabel M J) :
    RawFacetLabel M J where
  indices := L.indices
  representative := n.val * L.representative
  parabolic_conjugacy := by
    have he : (MulAut.conj (n.val * L.representative)).toMonoidHom =
        (MulAut.conj n.val).toMonoidHom.comp (MulAut.conj L.representative).toMonoidHom := by
      apply MonoidHom.ext
      intro g
      change (n.val * L.representative) * g * (n.val * L.representative)⁻¹ =
        n.val * (L.representative * g * L.representative⁻¹) * n.val⁻¹
      group
    rw [he, ← Subgroup.map_map, L.parabolic_conjugacy]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp n.property

omit [Finite M.Group] in
theorem normalizerRawFacetLabel_point (n : CoxeterNormalizer M J) (L : RawFacetLabel M J) :
    rawCanonicalFacetPoint (normalizerRawFacetLabel M J n L) =
      normalizerRepresentation M J n (rawCanonicalFacetPoint L) := by
  apply Subtype.ext
  change dualAction M (n.val * L.representative) (canonicalDominant L.indices) =
    dualAction M n.val (dualAction M L.representative (canonicalDominant L.indices))
  rw [map_mul, mul_apply_eq_comp]

omit [Finite M.Group] in
theorem normalizerRawFacetLabel_region (n : CoxeterNormalizer M J) (L : RawFacetLabel M J) :
    translatedFacet (normalizerRawFacetLabel M J n L) =
      normalizerFlatEquiv M J n '' translatedFacet L := by
  ext p
  constructor
  · intro hp
    obtain ⟨φ, hφ, he⟩ := (mem_translatedFacet_iff _ p).mp hp
    let x : relativeSubspace J := facetFlatEquiv L ⟨φ, hφ.1⟩
    refine ⟨x, ⟨⟨φ, hφ.1⟩, hφ, rfl⟩, ?_⟩
    apply Subtype.ext
    change dualAction M n.val (dualAction M L.representative φ) = p.val
    rw [← mul_apply_eq_comp, ← map_mul]
    exact he
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨φ, hφ, he⟩ := (mem_translatedFacet_iff L p).mp hp
    apply (mem_translatedFacet_iff _ _).mpr
    refine ⟨φ, hφ, ?_⟩
    change dualAction M (n.val * L.representative) φ = dualAction M n.val p.val
    rw [map_mul, mul_apply_eq_comp, he]

theorem actualChamberOfRawLabel_normalizer (n : CoxeterNormalizer M J) (L : RawFacetLabel M J) :
    actualChamberOfRawLabel M J (normalizerRawFacetLabel M J n L) =
      transportedChamber M J n (actualChamberOfRawLabel M J L) := by
  have hreg : (actualChamberOfRawLabel M J (normalizerRawFacetLabel M J n L)).region =
      (transportedChamber M J n (actualChamberOfRawLabel M J L)).region := by
    rw [actualChamberOfRawLabel_region, normalizerRawFacetLabel_region,
      ← normalizer_image_chamber_region, actualChamberOfRawLabel_region]
  obtain ⟨p, hp⟩ := (actualChamberOfRawLabel M J (normalizerRawFacetLabel M J n L)).region_nonempty
  exact Chamber.eq_of_mem_region hp (hreg ▸ hp)

/-- Strict covariance follows from the raw-label multiplication formula. -/
theorem actualChamberPoint_normalizer (n : CoxeterNormalizer M J) (C : ActualChamber M J) :
    actualChamberPoint M J (transportedChamber M J n C) =
      normalizerRepresentation M J n (actualChamberPoint M J C) := by
  obtain ⟨L, rfl⟩ := actualChamberOfRawLabel_surjective M J C
  rw [← actualChamberOfRawLabel_normalizer, actualChamberPoint_rawLabel, actualChamberPoint_rawLabel]
  exact normalizerRawFacetLabel_point M J n L

/-- The same actual normalizer quotient acts on both chambers and flat points. -/
theorem actualChamberPoint_equivariant (q : Artin.coxeterNormalizerQuotient M J)
    (C : ActualChamber M J) : actualChamberPoint M J (q • C) =
      quotientRepresentation M J q (actualChamberPoint M J C) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective
    ((Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J)) q
  change actualChamberPoint M J (transportedChamber M J n C) =
    normalizerRepresentation M J n (actualChamberPoint M J C)
  exact actualChamberPoint_normalizer M J n C

/-- Canonical actual points in every actual chamber, for use by the genuine
interval-to-complement functor. Membership is proved, not assumed. -/
noncomputable def actualChamberPointFamily :
    ChamberPointFamily (E := relativeSubspace J) (H := RelativeRoot M J) (actualForms M J) :=
  fun C => ⟨actualChamberPoint M J C, actualChamberPoint_mem M J C⟩

theorem actualChamberPointFamily_equivariant (q : Artin.coxeterNormalizerQuotient M J)
    (C : ActualChamber M J) : (actualChamberPointFamily M J (q • C)).val =
      quotientRepresentation M J q (actualChamberPointFamily M J C).val :=
  actualChamberPoint_equivariant M J q C

end ArtinNormalisers.Chamber3
