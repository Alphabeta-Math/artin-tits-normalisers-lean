import ArtinChambers.ChamberLabels
import ArtinChambers.IntervalGroupoid
import ArtinChambers.InversionLength
import ArtinChambers.PositiveTransport
import ArtinNormalisers.Artin.NormalizerLift

/-!
# Canonical relative Coxeter transport of actual arrangement chambers

The transport is the minimal representative of the actual parabolic coset
between two facet labels. Right parabolic ambiguity of both labels is
removed by the canonical minimal-coset projection.
-/

namespace ArtinNormalisers.Chamber3

open Theorem18 Landmark1

variable {I : Type*} (M : CoxeterMatrix I) {J : Set I}

private theorem eval_nonneg_of_nonneg {φ : Dual I} (hφ : IsDominant φ)
    {r : Vector I} (hr : 0 ≤ r) : 0 ≤ φ r := by
  have h := evaluation_nonpos_of_nonpos hφ (neg_nonpos.mpr hr)
  simpa only [map_neg, neg_nonpos] using h

private theorem canonical_eval_zero_support (K : Set I) {r : Vector I}
    (hr : 0 ≤ r) (hz : canonicalDominant K r = 0) :
    ∀ i ∉ K, r i = 0 := by
  classical
  have he : canonicalDominant K = Finsupp.linearCombination ℝ
      (fun i => canonicalDominant K (simpleRoot i)) :=
    (dualCoordinates (I := I)).symm_apply_apply (canonicalDominant K) |>.symm
  rw [he, Finsupp.linearCombination_apply, Finsupp.sum] at hz
  simp only [smul_eq_mul] at hz
  intro i hi
  by_cases hmem : i ∈ r.support
  · have hle := Finset.single_le_sum
      (fun j (_ : j ∈ r.support) => mul_nonneg (hr j) (canonicalDominant_isDominant K j)) hmem
    rw [hz] at hle
    have hri : r i ≤ 0 := by
      simpa only [canonicalDominant_apply_simpleRoot, ite_eq_right hi, smul_eq_mul, mul_one]
        using hle
    exact le_antisymm hri (hr i)
  · exact Finsupp.notMem_support_iff.mp hmem

private theorem representation_nonneg_of_supported (w : M.Group) (K : Set I)
    (hw : ∀ i ∈ K, 0 ≤ M.toCoxeterSystem.geometricRepresentation w (simpleRoot i))
    {r : Vector I} (hr : 0 ≤ r) (hs : ∀ i ∉ K, r i = 0) :
    0 ≤ M.toCoxeterSystem.geometricRepresentation w r := by
  classical
  have he : (∑ i ∈ r.support, r i • simpleRoot i) = r := by
    simpa only [simpleRoot, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum]
      using r.sum_single
  rw [← he, map_sum]
  apply Finset.sum_nonneg
  intro i hi
  rw [map_smul]
  have hiK : i ∈ K := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hi) (hs i hn)
  exact smul_nonneg (hr i) (hw i hiK)

/-- A positive inversion root of a representative left-minimal at `K`
cannot vanish on the whole actual relative flat. -/
theorem inversionRoot_retained {K : Set I} {d : M.Group}
    (hmin : M.toCoxeterSystem.IsMinimalCosetRep K d⁻¹)
    {r : Vector I} (hr : r ∈ M.toCoxeterSystem.geometricRoots) (hp : 0 < r)
    (hn : M.toCoxeterSystem.geometricRepresentation d⁻¹ r < 0) :
    r ∈ retainedRoots M K := by
  have hroot : r ∈ roots M := by
    obtain ⟨w, i, he⟩ := M.toCoxeterSystem.mem_geometricRoots.mp hr
    exact ⟨w, i, he⟩
  refine ⟨hroot, ⟨canonicalDominant K, canonicalDominant_mem_relativeSubspace K⟩, ?_⟩
  intro hz
  have hs := canonical_eval_zero_support K hp.le hz
  have hgens : ∀ i ∈ K,
      0 ≤ M.toCoxeterSystem.geometricRepresentation d⁻¹ (simpleRoot i) := by
    intro i hi
    exact ((M.toCoxeterSystem.geometricRepresentation_single_pos_iff d⁻¹ i).mpr
      (M.toCoxeterSystem.isMinimalCosetRep_iff.mp hmin i hi)).le
  exact (representation_nonneg_of_supported M d⁻¹ K hgens hp.le hs).not_gt hn

/-- Relative raw transport conjugates the target source parabolic onto the
starting source parabolic. -/
noncomputable def relativeRawLabel (L K : RawFacetLabel M J) : RawFacetLabel M L.indices where
  indices := K.indices
  representative := L.representative⁻¹ * K.representative
  parabolic_conjugacy := by
    have he : (MulAut.conj (L.representative⁻¹ * K.representative)).toMonoidHom =
        (MulAut.conj L.representative⁻¹).toMonoidHom.comp
          (MulAut.conj K.representative).toMonoidHom := by
      apply MonoidHom.ext
      intro g
      change (L.representative⁻¹ * K.representative) * g *
          (L.representative⁻¹ * K.representative)⁻¹ =
        L.representative⁻¹ * (K.representative * g * K.representative⁻¹) *
          (L.representative⁻¹)⁻¹
      group
    rw [he, ← Subgroup.map_map, K.parabolic_conjugacy]
    exact conjugacy_symm M L.parabolic_conjugacy

/-- The canonical right-parabolic-minimal relative element of raw labels. -/
noncomputable def rawRelativeTransport (L K : RawFacetLabel M J) : M.Group :=
  M.toCoxeterSystem.minimalCosetRep K.indices (L.representative⁻¹ * K.representative)

theorem rawRelativeTransport_minimal (L K : RawFacetLabel M J) :
    M.toCoxeterSystem.IsMinimalCosetRep K.indices (rawRelativeTransport M L K) :=
  M.toCoxeterSystem.isMinimalCosetRep_minimalCosetRep K.indices _

theorem rawRelativeTransport_coset (L K : RawFacetLabel M J) :
    (L.representative⁻¹ * K.representative)⁻¹ * rawRelativeTransport M L K ∈
      Artin.coxeterParabolic M K.indices := by
  rw [Artin.coxeterParabolic_eq]
  exact M.toCoxeterSystem.inv_mul_minimalCosetRep_mem K.indices _

theorem rawRelativeTransport_conjugacy (L K : RawFacetLabel M J) :
    (Artin.coxeterParabolic M K.indices).map
      (MulAut.conj (rawRelativeTransport M L K)).toMonoidHom =
        Artin.coxeterParabolic M L.indices := by
  simp only [Artin.coxeterParabolic_eq]
  apply minimalCosetRep_transports_parabolic M.toCoxeterSystem
  simpa only [Artin.coxeterParabolic_eq, relativeRawLabel] using
    (relativeRawLabel M L K).parabolic_conjugacy

theorem rawRelativeTransport_inv_minimal (L K : RawFacetLabel M J) :
    M.toCoxeterSystem.IsMinimalCosetRep L.indices (rawRelativeTransport M L K)⁻¹ := by
  apply minimal_inv_of_parabolic_transporter M.toCoxeterSystem
    (by simpa only [Artin.coxeterParabolic_eq] using rawRelativeTransport_conjugacy M L K)
    (rawRelativeTransport_minimal M L K)

/-- Replace the target label by the canonical relative representative,
without changing its actual endpoint chamber. -/
noncomputable def relativeTargetLabel (L K : RawFacetLabel M J) : RawFacetLabel M J where
  indices := K.indices
  representative := L.representative * rawRelativeTransport M L K
  parabolic_conjugacy := by
    have he : (MulAut.conj (L.representative * rawRelativeTransport M L K)).toMonoidHom =
        (MulAut.conj L.representative).toMonoidHom.comp
          (MulAut.conj (rawRelativeTransport M L K)).toMonoidHom := by
      apply MonoidHom.ext
      intro g
      change (L.representative * rawRelativeTransport M L K) * g *
        (L.representative * rawRelativeTransport M L K)⁻¹ =
        L.representative * (rawRelativeTransport M L K * g *
          (rawRelativeTransport M L K)⁻¹) * L.representative⁻¹
      group
    rw [he, ← Subgroup.map_map, rawRelativeTransport_conjugacy, L.parabolic_conjugacy]

theorem relativeTargetLabel_region (L K : RawFacetLabel M J) :
    translatedFacet (relativeTargetLabel M L K) = translatedFacet K := by
  symm
  apply translatedFacet_eq_of_indices_coset K (relativeTargetLabel M L K) rfl
  have hc := rawRelativeTransport_coset M L K
  convert hc using 1; simp only [relativeTargetLabel]; group

/-- Changing either facet representative by its right source parabolic does
not change canonical relative transport. -/
theorem rawRelativeTransport_eq_of_regions
    {L L' K K' : RawFacetLabel M J}
    (hL : translatedFacet L = translatedFacet L')
    (hK : translatedFacet K = translatedFacet K') :
    rawRelativeTransport M L K = rawRelativeTransport M L' K' := by
  obtain ⟨hLI, ha⟩ := (translatedFacet_eq_iff L L').mp hL
  obtain ⟨hKI, hb⟩ := (translatedFacet_eq_iff K K').mp hK
  unfold rawRelativeTransport
  rw [← hKI]
  apply M.toCoxeterSystem.minimalCosetRep_eq_minimalCosetRep_iff.mpr
  rw [← Artin.coxeterParabolic_eq]
  have hconj := (relativeRawLabel M L K).parabolic_conjugacy
  change (Artin.coxeterParabolic M K.indices).map
    (MulAut.conj (L.representative⁻¹ * K.representative)).toMonoidHom =
      Artin.coxeterParabolic M L.indices at hconj
  have ha' : (L.representative⁻¹ * L'.representative)⁻¹ ∈
      (Artin.coxeterParabolic M K.indices).map
        (MulAut.conj (L.representative⁻¹ * K.representative)).toMonoidHom := by
    rw [hconj]
    exact (Artin.coxeterParabolic M L.indices).inv_mem ha
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at ha'
  have hp := (Artin.coxeterParabolic M K.indices).mul_mem ha' hb
  convert hp using 1; group

/-- The canonical dominant point transported into a raw label's actual facet. -/
noncomputable def facetCanonicalPoint (L : RawFacetLabel M J) : relativeSubspace J :=
  facetFlatEquiv L ⟨canonicalDominant L.indices, canonicalDominant_mem_relativeSubspace L.indices⟩

theorem facetCanonicalPoint_mem (L : RawFacetLabel M J) :
    facetCanonicalPoint M L ∈ translatedFacet L :=
  (mem_translatedFacet_iff L _).mpr
    ⟨canonicalDominant L.indices, canonicalDominant_mem_standardFacet M L.indices, rfl⟩

theorem facetCanonicalPoint_pairing (L : RawFacetLabel M J) (r : Vector I) :
    (facetCanonicalPoint M L).val
        (M.toCoxeterSystem.geometricRepresentation L.representative r) =
      canonicalDominant L.indices r :=
  dualAction_pairing M L.representative (canonicalDominant L.indices) r

theorem relativeTargetLabel_pairing (L K : RawFacetLabel M J) (r : Vector I) :
    (facetCanonicalPoint M (relativeTargetLabel M L K)).val
        (M.toCoxeterSystem.geometricRepresentation L.representative r) =
      canonicalDominant K.indices
        (M.toCoxeterSystem.geometricRepresentation (rawRelativeTransport M L K)⁻¹ r) := by
  change dualAction M (L.representative * rawRelativeTransport M L K)
      (canonicalDominant K.indices)
      (M.toCoxeterSystem.geometricRepresentation L.representative r) = _
  rw [map_mul, mul_apply_eq_comp, dualAction_pairing]
  rfl

theorem facetTransport_retained (L : RawFacetLabel M J) {r : Vector I}
    (hr : r ∈ retainedRoots M L.indices) :
    M.toCoxeterSystem.geometricRepresentation L.representative r ∈ retainedRoots M J := by
  obtain ⟨hroot, φ, hφ⟩ := hr
  refine ⟨geometricAction_mem_roots M L.representative hroot, facetFlatEquiv L φ, ?_⟩
  change dualAction M L.representative φ.val
    (M.toCoxeterSystem.geometricRepresentation L.representative r) ≠ 0
  rw [dualAction_pairing]
  exact hφ

private theorem canonical_eval_pos_of_retained {K : Set I} {r : Vector I}
    (hr : r ∈ retainedRoots M K) (hp : 0 < r) : 0 < canonicalDominant K r := by
  have hreg : realRelativeRegular M K
      ⟨canonicalDominant K, canonicalDominant_mem_relativeSubspace K⟩ :=
    realRelativeRegular_of_stabilizer M K _ (canonicalDominant_fixed_iff M K)
  exact lt_of_le_of_ne (eval_nonneg_of_nonneg (canonicalDominant_isDominant K) hp.le)
    (Ne.symm (hreg r hr))

variable [Finite M.Group] (J)

/-- A raw facet label for an actual chamber, selected from the proved
classification theorem. -/
noncomputable def chamberRawLabel (C : ActualChamber M J) : RawFacetLabel M J :=
  Classical.choose (actualChamberOfRawLabel_surjective M J C)

theorem chamberRawLabel_chamber (C : ActualChamber M J) :
    actualChamberOfRawLabel M J (chamberRawLabel M J C) = C :=
  Classical.choose_spec (actualChamberOfRawLabel_surjective M J C)

theorem chamberRawLabel_region (C : ActualChamber M J) :
    translatedFacet (chamberRawLabel M J C) = C.region := by
  rw [← actualChamberOfRawLabel_region, chamberRawLabel_chamber]

@[simp] theorem chamberRawLabel_indices (C : ActualChamber M J) :
    (chamberRawLabel M J C).indices = actualChamberIndices M J C := rfl

/-- Canonical relative transport between actual chambers, independent of
all raw facet representatives. -/
noncomputable def relativeTransport (C D : ActualChamber M J) : M.Group :=
  rawRelativeTransport M (chamberRawLabel M J C) (chamberRawLabel M J D)

theorem relativeTransport_eq_raw (L K : RawFacetLabel M J) :
    relativeTransport M J (actualChamberOfRawLabel M J L) (actualChamberOfRawLabel M J K) =
      rawRelativeTransport M L K := by
  apply rawRelativeTransport_eq_of_regions M
  · rw [chamberRawLabel_region, actualChamberOfRawLabel_region]
  · rw [chamberRawLabel_region, actualChamberOfRawLabel_region]

theorem relativeTransport_minimal (C D : ActualChamber M J) :
    M.toCoxeterSystem.IsMinimalCosetRep (actualChamberIndices M J D)
      (relativeTransport M J C D) :=
  rawRelativeTransport_minimal M _ _

theorem relativeTransport_conjugacy (C D : ActualChamber M J) :
    (Artin.coxeterParabolic M (actualChamberIndices M J D)).map
      (MulAut.conj (relativeTransport M J C D)).toMonoidHom =
        Artin.coxeterParabolic M (actualChamberIndices M J C) :=
  rawRelativeTransport_conjugacy M _ _

theorem relativeTransport_inverse_minimal (C D : ActualChamber M J) :
    M.toCoxeterSystem.IsMinimalCosetRep (actualChamberIndices M J C)
      (relativeTransport M J C D)⁻¹ :=
  rawRelativeTransport_inv_minimal M _ _

/-- The raw target of the actual elementary ribbon label, retaining its
proved index endpoint and using its actual Coxeter projection. -/
noncomputable def elementaryTargetLabel (L : RawFacetLabel M J) (a : I) :
    RawFacetLabel M J where
  indices := Ribbon2.parabolicTwistImage M (insert a L.indices) L.indices
  representative := L.representative * Artin.projection M (Ribbon2.elementaryMu M L.indices a)
  parabolic_conjugacy := by
    have hμ := isRibbon_projection_transporter M (Ribbon2.elementaryMu_isRibbon M L.indices a)
    have he : (MulAut.conj (L.representative *
        Artin.projection M (Ribbon2.elementaryMu M L.indices a))).toMonoidHom =
        (MulAut.conj L.representative).toMonoidHom.comp
          (MulAut.conj (Artin.projection M (Ribbon2.elementaryMu M L.indices a))).toMonoidHom := by
      apply MonoidHom.ext
      intro g
      change (L.representative * Artin.projection M (Ribbon2.elementaryMu M L.indices a)) * g *
          (L.representative * Artin.projection M (Ribbon2.elementaryMu M L.indices a))⁻¹ =
        L.representative * (Artin.projection M (Ribbon2.elementaryMu M L.indices a) * g *
          (Artin.projection M (Ribbon2.elementaryMu M L.indices a))⁻¹) * L.representative⁻¹
      group
    rw [he, ← Subgroup.map_map, hμ, L.parabolic_conjugacy]

/-- On an actual elementary ribbon step, canonical geometric relative
transport is exactly the Coxeter projection of that elementary label. -/
theorem relativeTransport_elementary (L : RawFacetLabel M J) (a : I) :
    relativeTransport M J (actualChamberOfRawLabel M J L)
      (actualChamberOfRawLabel M J (elementaryTargetLabel M J L a)) =
        Artin.projection M (Ribbon2.elementaryMu M L.indices a) := by
  rw [relativeTransport_eq_raw]
  unfold rawRelativeTransport
  change M.toCoxeterSystem.minimalCosetRep
      (Ribbon2.parabolicTwistImage M (insert a L.indices) L.indices)
      (L.representative⁻¹ *
        (L.representative * Artin.projection M (Ribbon2.elementaryMu M L.indices a))) = _
  rw [inv_mul_cancel_left]
  exact (elementaryMu_projection_minimal M L.indices a).minimalCosetRep_eq _

@[simp] theorem relativeTransport_self (C : ActualChamber M J) :
    relativeTransport M J C C = 1 := by
  unfold relativeTransport rawRelativeTransport
  rw [inv_mul_cancel]
  exact (M.toCoxeterSystem.isMinimalCosetRep_one _).minimalCosetRep_eq _

/-- Actual chamber betweenness gives ambient root-inversion inclusion, hence
Coxeter length additivity. Restricted hyperplanes need not be distinct root
labels, and no count of restricted gallery edges enters this argument. -/
theorem rawRelativeTransport_length_of_between (L K T : RawFacetLabel M J)
    (hbet : ChamberBetween (actualChamberOfRawLabel M J L)
      (actualChamberOfRawLabel M J K) (actualChamberOfRawLabel M J T)) :
    M.toCoxeterSystem.length (rawRelativeTransport M L T) =
      M.toCoxeterSystem.length (rawRelativeTransport M L K) +
        M.toCoxeterSystem.length
          ((rawRelativeTransport M L K)⁻¹ * rawRelativeTransport M L T) := by
  apply length_eq_add_of_rootInversions_subset
  intro r hr hp hn
  have hrI := inversionRoot_retained M (rawRelativeTransport_inv_minimal M L K) hr hp hn
  let R : RelativeRoot M J :=
    ⟨M.toCoxeterSystem.geometricRepresentation L.representative r,
      facetTransport_retained M L hrI⟩
  have hC : facetCanonicalPoint M L ∈ (actualChamberOfRawLabel M J L).region := by
    rw [actualChamberOfRawLabel_region]
    exact facetCanonicalPoint_mem M L
  have hD : facetCanonicalPoint M (relativeTargetLabel M L K) ∈
      (actualChamberOfRawLabel M J K).region := by
    rw [actualChamberOfRawLabel_region, ← relativeTargetLabel_region M L K]
    exact facetCanonicalPoint_mem M _
  have hE : facetCanonicalPoint M (relativeTargetLabel M L T) ∈
      (actualChamberOfRawLabel M J T).region := by
    rw [actualChamberOfRawLabel_region, ← relativeTargetLabel_region M L T]
    exact facetCanonicalPoint_mem M _
  have hposC : 0 < actualForms M J R (facetCanonicalPoint M L) := by
    change 0 < (facetCanonicalPoint M L).val
      (M.toCoxeterSystem.geometricRepresentation L.representative r)
    rw [facetCanonicalPoint_pairing]
    exact canonical_eval_pos_of_retained M hrI hp
  have hnonposD : actualForms M J R
      (facetCanonicalPoint M (relativeTargetLabel M L K)) ≤ 0 := by
    change (facetCanonicalPoint M (relativeTargetLabel M L K)).val
      (M.toCoxeterSystem.geometricRepresentation L.representative r) ≤ 0
    rw [relativeTargetLabel_pairing]
    exact evaluation_nonpos_of_nonpos (canonicalDominant_isDominant K.indices) hn.le
  have hnegD : actualForms M J R
      (facetCanonicalPoint M (relativeTargetLabel M L K)) < 0 :=
    lt_of_le_of_ne hnonposD
      ((actualChamberOfRawLabel M J K).region_subset_regularSet hD R)
  have hsC : (actualChamberOfRawLabel M J L).signs R = true :=
    (Chamber.signs_eq_true_iff hC R).mpr hposC
  have hsD : (actualChamberOfRawLabel M J K).signs R = false := by
    cases hs : (actualChamberOfRawLabel M J K).signs R
    · rfl
    · exact False.elim (lt_asymm ((Chamber.signs_eq_true_iff hD R).mp hs) hnegD)
  have hsE : (actualChamberOfRawLabel M J T).signs R = false := by
    cases hs : (actualChamberOfRawLabel M J T).signs R
    · rfl
    · have hh := hbet R (hsC.trans hs.symm)
      rw [hsD, hsC] at hh
      contradiction
  have hnegE : actualForms M J R
      (facetCanonicalPoint M (relativeTargetLabel M L T)) < 0 := by
    have hh := hE R
    change (if (actualChamberOfRawLabel M J T).signs R then
      0 < actualForms M J R (facetCanonicalPoint M (relativeTargetLabel M L T)) else
      actualForms M J R (facetCanonicalPoint M (relativeTargetLabel M L T)) < 0) at hh
    simpa only [hsE, Bool.false_eq_true, ite_false] using hh
  change (facetCanonicalPoint M (relativeTargetLabel M L T)).val
    (M.toCoxeterSystem.geometricRepresentation L.representative r) < 0 at hnegE
  rw [relativeTargetLabel_pairing] at hnegE
  have hroot := (M.toCoxeterSystem.geometricRepresentation_apply_mem_geometricRoots_iff
    (rawRelativeTransport M L T)⁻¹).mpr hr
  rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hroot with hpos | hneg
  · exact False.elim ((eval_nonneg_of_nonneg (canonicalDominant_isDominant T.indices)
      hpos.le).not_gt hnegE)
  · exact hneg

omit [Finite M.Group] in
private theorem minimal_suffix_of_length_add {K : Set I} {d f : M.Group}
    (hmin : M.toCoxeterSystem.IsMinimalCosetRep K f)
    (hlen : M.toCoxeterSystem.length f = M.toCoxeterSystem.length d +
      M.toCoxeterSystem.length (d⁻¹ * f)) :
    M.toCoxeterSystem.IsMinimalCosetRep K (d⁻¹ * f) := by
  refine M.toCoxeterSystem.isMinimalCosetRep_iff.mpr ?_
  intro i hi hd
  have hlong := M.toCoxeterSystem.not_isRightDescent_iff.mp
    (M.toCoxeterSystem.isMinimalCosetRep_iff.mp hmin i hi)
  have hshort := M.toCoxeterSystem.isRightDescent_iff.mp hd
  simp only [CoxeterMatrix.toCoxeterSystem_simple] at hlong hshort
  have hbound := M.toCoxeterSystem.length_mul_le d ((d⁻¹ * f) * M.simple i)
  have he : d * ((d⁻¹ * f) * M.simple i) = f * M.simple i := by group
  rw [he] at hbound
  omega

/-- Composition through a chamber between the endpoints is actual
multiplication of the canonical minimal relative Coxeter elements. -/
theorem rawRelativeTransport_comp_of_between (L K T : RawFacetLabel M J)
    (hbet : ChamberBetween (actualChamberOfRawLabel M J L)
      (actualChamberOfRawLabel M J K) (actualChamberOfRawLabel M J T)) :
    rawRelativeTransport M L T = rawRelativeTransport M L K * rawRelativeTransport M K T := by
  have hlen := rawRelativeTransport_length_of_between M J L K T hbet
  have hmin := minimal_suffix_of_length_add M (rawRelativeTransport_minimal M L T) hlen
  have he : rawRelativeTransport M K T =
      (rawRelativeTransport M L K)⁻¹ * rawRelativeTransport M L T := by
    calc
      rawRelativeTransport M K T = rawRelativeTransport M
          (relativeTargetLabel M L K) (relativeTargetLabel M L T) :=
        rawRelativeTransport_eq_of_regions M (relativeTargetLabel_region M L K).symm
          (relativeTargetLabel_region M L T).symm
      _ = (rawRelativeTransport M L K)⁻¹ * rawRelativeTransport M L T := by
        unfold rawRelativeTransport
        change M.toCoxeterSystem.minimalCosetRep T.indices
          ((L.representative * rawRelativeTransport M L K)⁻¹ *
            (L.representative * rawRelativeTransport M L T)) = _
        have hc : (L.representative * rawRelativeTransport M L K)⁻¹ *
            (L.representative * rawRelativeTransport M L T) =
            (rawRelativeTransport M L K)⁻¹ * rawRelativeTransport M L T := by group
        rw [hc]
        exact hmin.minimalCosetRep_eq _
  rw [he]
  group

theorem relativeTransport_comp_of_between {C D E : ActualChamber M J}
    (hbet : ChamberBetween C D E) :
    relativeTransport M J C E = relativeTransport M J C D * relativeTransport M J D E := by
  apply rawRelativeTransport_comp_of_between M J
  simpa only [chamberRawLabel_chamber] using hbet

theorem relativeTransport_length_of_between {C D E : ActualChamber M J}
    (hbet : ChamberBetween C D E) :
    M.toCoxeterSystem.length (relativeTransport M J C E) =
      M.toCoxeterSystem.length (relativeTransport M J C D) +
        M.toCoxeterSystem.length (relativeTransport M J D E) := by
  have hlen := rawRelativeTransport_length_of_between M J (chamberRawLabel M J C)
    (chamberRawLabel M J D) (chamberRawLabel M J E)
    (by simpa only [chamberRawLabel_chamber] using hbet)
  change M.toCoxeterSystem.length (relativeTransport M J C E) =
    M.toCoxeterSystem.length (relativeTransport M J C D) +
      M.toCoxeterSystem.length ((relativeTransport M J C D)⁻¹ * relativeTransport M J C E)
    at hlen
  have hc : (relativeTransport M J C D)⁻¹ * relativeTransport M J C E =
      relativeTransport M J D E := by
    rw [relativeTransport_comp_of_between M J hbet, inv_mul_cancel_left]
  rw [hc] at hlen
  exact hlen

end ArtinNormalisers.Chamber3
