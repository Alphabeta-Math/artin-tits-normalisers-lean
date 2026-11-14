module

public import ArtinChambers.ActualArrangement
public import ArtinChambers.Dominant
public import ArtinChambers.FacetTransport
public import ArtinChambers.RegularCriterion

/-!
# Actual chambers and transported standard-facet labels

Every regular relative point can be made dominant. Its full point stabilizer
then supplies the actual parabolic-conjugacy condition on its facet label.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open Theorem18 Landmark1

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- A regular point belongs to a transported standard facet whose actual
standard parabolic is conjugated onto the parabolic of the ambient flat. -/
theorem exists_standardFacet_transport (φ : relativeSubspace J)
    (hφ : realRelativeRegular M J φ) :
    ∃ (K : Set I) (w : M.Group),
      (Artin.coxeterParabolic M K).map (MulAut.conj w).toMonoidHom =
        Artin.coxeterParabolic M J ∧
      φ.val ∈ dualAction M w '' standardFacet M K := by
  obtain ⟨u, hu⟩ := exists_dominant_dualAction M φ.val
  let ψ := dualAction M u φ.val
  let K := zeroIndices ψ
  have hψ : ψ ∈ standardFacet M K := mem_standardFacet_zeroIndices hu
  refine ⟨K, u⁻¹, ?_, ψ, hψ, ?_⟩
  · ext g
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    rw [← dominant_fixed_iff M hu, ← realRelativeRegular_fixed_iff M J φ hφ g]
    constructor
    · intro h
      have hc := congrArg (fun f : Dual I => dualAction M u⁻¹ f) h
      simp only [← mul_apply_eq_comp, ← map_mul] at hc
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel,
        mul_one,
        map_one, one_apply_eq_self] using hc
    · intro h
      have hc := congrArg (fun f : Dual I => dualAction M u f) h
      simp only [← mul_apply_eq_comp, ← map_mul]
      simpa only [← mul_apply_eq_comp, ← map_mul, mul_assoc, inv_mul_cancel,
        mul_one] using hc
  · dsimp only [ψ]
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

/-- An open connected partition of a subset is precisely its connected-component
partition. Different labels may represent the same part. -/
theorem connectedComponentIn_eq_of_open_partition
    {E : Type*} [TopologicalSpace E] {L : Type*} (R : L → Set E) (U : Set E)
    (hopen : ∀ l, IsOpen (R l)) (hconn : ∀ l, IsPreconnected (R l))
    (hsub : ∀ l, R l ⊆ U) (hcover : ∀ x ∈ U, ∃ l, x ∈ R l)
    (hmeet : ∀ l k, (R l ∩ R k).Nonempty → R l = R k)
    (l : L) {x : E} (hx : x ∈ R l) : connectedComponentIn U x = R l := by
  classical
  apply Set.Subset.antisymm
  · let V : Set E := ⋃ k : {k : L // R k ≠ R l}, R k.val
    have hopenV : IsOpen V := isOpen_iUnion fun k => hopen k.val
    have hdisj : Disjoint (R l) V := by
      apply Set.disjoint_left.mpr
      intro y hyl hyV
      obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp hyV
      exact k.property (hmeet k.val l ⟨y, hyk, hyl⟩)
    have hcover' : connectedComponentIn U x ⊆ R l ∪ V := by
      intro y hy
      obtain ⟨k, hyk⟩ := hcover y (connectedComponentIn_subset U x hy)
      by_cases he : R k = R l
      · exact Or.inl (he ▸ hyk)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k, he⟩, hyk⟩)
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
      (hopen l) hopenV hdisj hcover'
      ⟨x, mem_connectedComponentIn (hsub l hx), hx⟩
  · exact (hconn l).subset_connectedComponentIn hx (hsub l)

theorem exists_mem_translatedFacet (φ : relativeSubspace J)
    (hφ : φ ∈ regularSet (actualForms M J)) :
    ∃ L : RawFacetLabel M J, φ ∈ translatedFacet L := by
  obtain ⟨K, w, hw, ψ, hψ, he⟩ := exists_standardFacet_transport M J φ
    ((mem_actual_regularSet_iff M J φ).mp hφ)
  exact ⟨⟨K, w, hw⟩, (mem_translatedFacet_iff _ φ).mpr ⟨ψ, hψ, he⟩⟩

/-- Actual transported facets are the connected components of the actual
regular locus, rather than merely subsets of components. -/
theorem translatedFacet_eq_connectedComponentIn (L : RawFacetLabel M J)
    {φ : relativeSubspace J} (hφ : φ ∈ translatedFacet L) :
    translatedFacet L = connectedComponentIn (regularSet (actualForms M J)) φ := by
  let : Finite I := finite_index M
  exact (connectedComponentIn_eq_of_open_partition translatedFacet
    (regularSet (actualForms M J)) isOpen_translatedFacet
    (fun K => (convex_translatedFacet K).isPreconnected)
    translatedFacet_subset_regularSet (exists_mem_translatedFacet M J)
    translatedFacet_eq_of_intersection L hφ).symm

/-- A concrete point of a raw label's actual facet. -/
noncomputable def rawFacetPoint (L : RawFacetLabel M J) : relativeSubspace J :=
  Classical.choose (translatedFacet_nonempty L)

omit [Finite M.Group] in
theorem rawFacetPoint_mem (L : RawFacetLabel M J) :
    rawFacetPoint M J L ∈ translatedFacet L :=
  Classical.choose_spec (translatedFacet_nonempty L)

/-- The actual sign chamber represented by a raw algebraic facet label. -/
noncomputable def actualChamberOfRawLabel (L : RawFacetLabel M J) : ActualChamber M J :=
  chamberOfRegular (actualForms M J) (rawFacetPoint M J L)
    (translatedFacet_subset_regularSet L (rawFacetPoint_mem M J L))

theorem actualChamberOfRawLabel_region (L : RawFacetLabel M J) :
    (actualChamberOfRawLabel M J L).region = translatedFacet L := by
  unfold actualChamberOfRawLabel
  rw [Chamber.region_eq_connectedComponentIn _
    (mem_chamberOfRegular_region (actualForms M J) (rawFacetPoint M J L)
      (translatedFacet_subset_regularSet L (rawFacetPoint_mem M J L)))]
  exact (translatedFacet_eq_connectedComponentIn M J L (rawFacetPoint_mem M J L)).symm

theorem actualChamberOfRawLabel_eq_iff (L K : RawFacetLabel M J) :
    actualChamberOfRawLabel M J L = actualChamberOfRawLabel M J K ↔
      L.indices = K.indices ∧ L.representative⁻¹ * K.representative ∈
        Artin.coxeterParabolic M L.indices := by
  rw [← translatedFacet_eq_iff L K]
  constructor
  · intro h
    simpa only [actualChamberOfRawLabel_region] using congrArg Chamber.region h
  · intro h
    apply Chamber.eq_of_mem_region (x := rawFacetPoint M J L)
    · rw [actualChamberOfRawLabel_region]
      exact rawFacetPoint_mem M J L
    · rw [actualChamberOfRawLabel_region, ← h]
      exact rawFacetPoint_mem M J L

theorem actualChamberOfRawLabel_surjective :
    Function.Surjective (actualChamberOfRawLabel M J) := by
  intro C
  obtain ⟨φ, hφ⟩ := C.region_nonempty
  obtain ⟨L, hL⟩ := exists_mem_translatedFacet M J φ (C.region_subset_regularSet hφ)
  refine ⟨L, Chamber.eq_of_mem_region ?_ hφ⟩
  rw [actualChamberOfRawLabel_region]
  exact hL

/-- The actual chamber map descends through exactly the right parabolic-coset
ambiguity already proved for raw facet labels. -/
noncomputable def actualChamberOfFacetLabel : FacetLabel M J → ActualChamber M J :=
  Quotient.lift (actualChamberOfRawLabel M J)
    (fun L K h => (actualChamberOfRawLabel_eq_iff M J L K).mpr h)

theorem actualChamberOfFacetLabel_bijective :
    Function.Bijective (actualChamberOfFacetLabel M J) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h L =>
      induction b using Quotient.inductionOn with
      | h K =>
        intro h
        exact Quotient.sound ((actualChamberOfRawLabel_eq_iff M J L K).mp h)
  · intro C
    obtain ⟨L, hL⟩ := actualChamberOfRawLabel_surjective M J C
    exact ⟨Quotient.mk _ L, hL⟩

/-- Classification by actual transported facets, with the source index set
retained and representatives quotiented by their right source parabolic. -/
noncomputable def facetLabelEquivActualChamber : FacetLabel M J ≃ ActualChamber M J :=
  Equiv.ofBijective (actualChamberOfFacetLabel M J) (actualChamberOfFacetLabel_bijective M J)

theorem actualChamberOfFacetLabel_region (L : FacetLabel M J) :
    (actualChamberOfFacetLabel M J L).region = facetRegion L := by
  induction L using Quotient.inductionOn with
  | h L => exact actualChamberOfRawLabel_region M J L

/-- The unique standard-facet index set associated with an actual chamber. -/
noncomputable def actualChamberIndices (C : ActualChamber M J) : Set I :=
  (Classical.choose (actualChamberOfRawLabel_surjective M J C)).indices

theorem actualChamberIndices_rawLabel (L : RawFacetLabel M J) :
    actualChamberIndices M J (actualChamberOfRawLabel M J L) = L.indices := by
  exact ((actualChamberOfRawLabel_eq_iff M J _ L).mp
    (Classical.choose_spec
      (actualChamberOfRawLabel_surjective M J (actualChamberOfRawLabel M J L)))).1

/-- Precisely the standard parabolics conjugate to the fixed parabolic occur
as chamber index sets. No transitivity of the normalizer quotient is assumed. -/
theorem exists_actualChamberIndices_iff (K : Set I) :
    (∃ C : ActualChamber M J, actualChamberIndices M J C = K) ↔
      ∃ w : M.Group, (Artin.coxeterParabolic M K).map
        (MulAut.conj w).toMonoidHom = Artin.coxeterParabolic M J := by
  constructor
  · rintro ⟨C, hC⟩
    let L := Classical.choose (actualChamberOfRawLabel_surjective M J C)
    refine ⟨L.representative, ?_⟩
    have hLK : L.indices = K := hC
    rw [← hLK]
    exact L.parabolic_conjugacy
  · rintro ⟨w, hw⟩
    let L : RawFacetLabel M J := ⟨K, w, hw⟩
    exact ⟨actualChamberOfRawLabel M J L, actualChamberIndices_rawLabel M J L⟩

end ArtinNormalisers.Chamber3
