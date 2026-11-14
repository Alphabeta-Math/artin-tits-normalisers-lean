import ArtinChambers.ChamberTransport
import ArtinChambers.WeakInversions

/-!
# Geometric chamber intervals and ambient Coxeter weak prefixes

The converse interval criterion reads actual root signs at transported
canonical facet points. It preserves repeated restricted root hyperplanes
and uses no identification of Coxeter length with restricted edge counts.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Chamber3

open Theorem18 Landmark1

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

private theorem eval_nonneg {φ : Dual I} (hφ : IsDominant φ) {r : Vector I}
    (hr : 0 ≤ r) : 0 ≤ φ r := by
  have h := evaluation_nonpos_of_nonpos hφ (neg_nonpos.mpr hr)
  simpa only [map_neg, neg_nonpos] using h

omit [Finite M.Group] in
private theorem root_eval_pos_iff {φ : Dual I} (hφ : IsDominant φ)
    {r : Vector I} (hr : r ∈ M.toCoxeterSystem.geometricRoots) (hz : φ r ≠ 0) :
    0 < φ r ↔ 0 < r := by
  rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hr with hp | hn
  · exact iff_of_true (lt_of_le_of_ne (eval_nonneg hφ hp.le) (Ne.symm hz)) hp
  · exact iff_of_false (not_lt.mpr (evaluation_nonpos_of_nonpos hφ hn.le)) (not_lt_of_ge hn.le)

omit [Finite M.Group] in
private theorem rawRelativeTransport_self (L : RawFacetLabel M J) :
    rawRelativeTransport M L L = 1 := by
  unfold rawRelativeTransport
  rw [inv_mul_cancel]
  exact (M.toCoxeterSystem.isMinimalCosetRep_one _).minimalCosetRep_eq _

/-- Actual signs at a transported facet agree with the signs of the actual
inverse-transformed roots at the standard facet. -/
theorem rawFacet_sign_iff (L K : RawFacetLabel M J) (R : RelativeRoot M J) :
    (actualChamberOfRawLabel M J K).signs R = true ↔
      0 < M.toCoxeterSystem.geometricRepresentation (rawRelativeTransport M L K)⁻¹
        (M.toCoxeterSystem.geometricRepresentation L.representative⁻¹ R.val) := by
  let r := M.toCoxeterSystem.geometricRepresentation L.representative⁻¹ R.val
  have hrootR : R.val ∈ M.toCoxeterSystem.geometricRoots := by
    obtain ⟨w, i, he⟩ := R.property.1
    exact M.toCoxeterSystem.mem_geometricRoots.mpr ⟨w, i, he⟩
  have hr := (M.toCoxeterSystem.geometricRepresentation_apply_mem_geometricRoots_iff
    L.representative⁻¹).mpr hrootR
  have hs := (M.toCoxeterSystem.geometricRepresentation_apply_mem_geometricRoots_iff
    (rawRelativeTransport M L K)⁻¹).mpr hr
  have heR : M.toCoxeterSystem.geometricRepresentation L.representative r = R.val := by
    dsimp only [r]
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  have hD : facetCanonicalPoint M (relativeTargetLabel M L K) ∈
      (actualChamberOfRawLabel M J K).region := by
    rw [actualChamberOfRawLabel_region, ← relativeTargetLabel_region M L K]
    exact facetCanonicalPoint_mem M _
  have heval : actualForms M J R (facetCanonicalPoint M (relativeTargetLabel M L K)) =
      canonicalDominant K.indices
        (M.toCoxeterSystem.geometricRepresentation (rawRelativeTransport M L K)⁻¹ r) := by
    calc
      _ = (facetCanonicalPoint M (relativeTargetLabel M L K)).val
          (M.toCoxeterSystem.geometricRepresentation L.representative r) :=
        congrArg (facetCanonicalPoint M (relativeTargetLabel M L K)).val heR.symm
      _ = _ := relativeTargetLabel_pairing M L K r
  have hz := (actualChamberOfRawLabel M J K).region_subset_regularSet hD R
  rw [heval] at hz
  rw [Chamber.signs_eq_true_iff hD R, heval]
  exact root_eval_pos_iff M (canonicalDominant_isDominant K.indices) hs hz

/-- The reverse geometric bridge: an ambient weak prefix between the
canonical relative elements forces actual sign betweenness of the chambers. -/
theorem chamberBetween_rawLabels_of_length (L K T : RawFacetLabel M J)
    (hlen : M.toCoxeterSystem.length (rawRelativeTransport M L T) =
      M.toCoxeterSystem.length (rawRelativeTransport M L K) +
        M.toCoxeterSystem.length
          ((rawRelativeTransport M L K)⁻¹ * rawRelativeTransport M L T)) :
    ChamberBetween (actualChamberOfRawLabel M J L) (actualChamberOfRawLabel M J K)
      (actualChamberOfRawLabel M J T) := by
  have hsub := rootInversions_subset_of_length_eq_add M
    (rawRelativeTransport M L K) (rawRelativeTransport M L T) hlen
  intro R hshared
  let r := M.toCoxeterSystem.geometricRepresentation L.representative⁻¹ R.val
  have hrootR : R.val ∈ M.toCoxeterSystem.geometricRoots := by
    obtain ⟨w, i, he⟩ := R.property.1
    exact M.toCoxeterSystem.mem_geometricRoots.mpr ⟨w, i, he⟩
  have hr : r ∈ M.toCoxeterSystem.geometricRoots :=
    (M.toCoxeterSystem.geometricRepresentation_apply_mem_geometricRoots_iff
      L.representative⁻¹).mpr hrootR
  have hbase : (actualChamberOfRawLabel M J L).signs R = true ↔ 0 < r := by
    simpa only [rawRelativeTransport_self, inv_one, map_one, one_apply_eq_self] using
      rawFacet_sign_iff M J L L R
  have hmid := rawFacet_sign_iff M J L K R
  have hend := rawFacet_sign_iff M J L T R
  rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hr with hp | hn
  · have hC := hbase.mpr hp
    have hE : (actualChamberOfRawLabel M J T).signs R = true := hshared.symm.trans hC
    have hEpos := hend.mp hE
    have hDpos : 0 < M.toCoxeterSystem.geometricRepresentation (rawRelativeTransport M L K)⁻¹ r := by
      have hDroot := (M.toCoxeterSystem.geometricRepresentation_apply_mem_geometricRoots_iff
        (rawRelativeTransport M L K)⁻¹).mpr hr
      rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hDroot with hdp | hdn
      · exact hdp
      · exact False.elim (lt_asymm hEpos (hsub r hr hp hdn))
    exact (hmid.mpr hDpos).trans hC.symm
  · have hC : (actualChamberOfRawLabel M J L).signs R = false := by
      cases hc : (actualChamberOfRawLabel M J L).signs R
      · rfl
      · exact False.elim (lt_asymm (hbase.mp hc) hn)
    have hE : (actualChamberOfRawLabel M J T).signs R = false := hshared.symm.trans hC
    have hD : (actualChamberOfRawLabel M J K).signs R = false := by
      cases hd : (actualChamberOfRawLabel M J K).signs R
      · rfl
      · have hdp := hmid.mp hd
        have hnr : -r ∈ M.toCoxeterSystem.geometricRoots :=
          M.toCoxeterSystem.neg_mem_geometricRoots_iff.mpr hr
        have hnd : M.toCoxeterSystem.geometricRepresentation (rawRelativeTransport M L K)⁻¹
            (-r) < 0 := by simpa only [map_neg, neg_lt_zero] using hdp
        have hnf := hsub (-r) hnr (neg_pos.mpr hn) hnd
        have hfp : 0 < M.toCoxeterSystem.geometricRepresentation
            (rawRelativeTransport M L T)⁻¹ r := by
          simpa only [map_neg, neg_lt_zero] using hnf
        have hetrue := hend.mpr hfp
        rw [hE] at hetrue
        contradiction
    exact hD.trans hC.symm

theorem chamberBetween_iff_relativeTransport_length (C D E : ActualChamber M J) :
    ChamberBetween C D E ↔
      M.toCoxeterSystem.length (relativeTransport M J C E) =
        M.toCoxeterSystem.length (relativeTransport M J C D) +
          M.toCoxeterSystem.length
            ((relativeTransport M J C D)⁻¹ * relativeTransport M J C E) := by
  constructor
  · intro h
    exact rawRelativeTransport_length_of_between M J
      (chamberRawLabel M J C) (chamberRawLabel M J D) (chamberRawLabel M J E)
      (by simpa only [chamberRawLabel_chamber] using h)
  · intro h
    have hh := chamberBetween_rawLabels_of_length M J
      (chamberRawLabel M J C) (chamberRawLabel M J D) (chamberRawLabel M J E) h
    simpa only [chamberRawLabel_chamber] using hh

end ArtinNormalisers.Chamber3
