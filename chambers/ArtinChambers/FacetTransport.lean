module

public import ArtinChambers.Dominant
public import ArtinChambers.RegularCriterion
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Actual transported standard facets

A raw label records an actual Coxeter element conjugating one standard
parabolic onto the fixed target parabolic. The contragredient action gives
a continuous linear equivalence of the actual relative flats. Its image of
the standard facet is the transported facet, with no connected-component
or chamber property imposed by definition.
-/

set_option autoImplicit false

@[expose] public section

namespace ArtinNormalisers.Chamber3

open Theorem18 Landmark1

variable {I : Type*}

/-- A raw facet label uses equality of actual conjugated parabolic groups. -/
structure RawFacetLabel (M : CoxeterMatrix I) (J : Set I) where
  indices : Set I
  representative : M.Group
  parabolic_conjugacy :
    (Artin.coxeterParabolic M indices).map
      (MulAut.conj representative).toMonoidHom = Artin.coxeterParabolic M J

theorem conjugacy_dualAction_mem_flat (M : CoxeterMatrix I) {K J : Set I} {w : M.Group}
    (hw : (Artin.coxeterParabolic M K).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M J) {φ : Dual I} (hφ : φ ∈ relativeSubspace K) :
    dualAction M w φ ∈ relativeSubspace J := by
  apply (mem_relativeSubspace_iff_fixed M J _).mpr
  intro g hg
  rw [← hw] at hg
  obtain ⟨h, hh, he⟩ := Subgroup.mem_map.mp hg
  have hfix := (mem_relativeSubspace_iff_fixed M K φ).mp hφ h hh
  change w * h * w⁻¹ = g at he
  rw [← he]
  calc
    dualAction M (w * h * w⁻¹) (dualAction M w φ) =
        dualAction M w (dualAction M h φ) := by
      simp only [← mul_apply_eq_comp, ← map_mul]
      congr 2
      group
    _ = dualAction M w φ := by rw [hfix]

theorem conjugacy_symm (M : CoxeterMatrix I) {K J : Set I} {w : M.Group}
    (hw : (Artin.coxeterParabolic M K).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M J) :
    (Artin.coxeterParabolic M J).map (MulAut.conj w⁻¹).toMonoidHom =
      Artin.coxeterParabolic M K := by
  rw [← hw, Subgroup.map_map]
  have he : (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom =
      MonoidHom.id M.Group := by
    apply MonoidHom.ext
    intro g
    change w⁻¹ * (w * g * w⁻¹) * (w⁻¹)⁻¹ = g
    simp [mul_assoc]
  rw [he, Subgroup.map_id]

/-- Actual action transport of the relative flats. -/
noncomputable def facetFlatEquiv {M : CoxeterMatrix I} {J : Set I} (L : RawFacetLabel M J) :
    relativeSubspace L.indices ≃L[ℝ] relativeSubspace J where
  toLinearEquiv :=
    { toFun := fun φ => ⟨dualAction M L.representative φ.val,
        conjugacy_dualAction_mem_flat M L.parabolic_conjugacy φ.property⟩
      invFun := fun φ => ⟨dualAction M L.representative⁻¹ φ.val,
        conjugacy_dualAction_mem_flat M (conjugacy_symm M L.parabolic_conjugacy) φ.property⟩
      left_inv := by
        intro φ
        apply Subtype.ext
        change dualAction M L.representative⁻¹ (dualAction M L.representative φ.val) = φ.val
        rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
      right_inv := by
        intro φ
        apply Subtype.ext
        change dualAction M L.representative (dualAction M L.representative⁻¹ φ.val) = φ.val
        rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
      map_add' := fun φ ψ => Subtype.ext (map_add (dualAction M L.representative) φ.val ψ.val)
      map_smul' := fun c φ => Subtype.ext (map_smul (dualAction M L.representative) c φ.val) }
  continuous_toFun :=
    ((continuous_dualAction M L.representative).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_dualAction M L.representative⁻¹).comp continuous_subtype_val).subtype_mk _

@[simp]
theorem facetFlatEquiv_apply_val {M : CoxeterMatrix I} {J : Set I} (L : RawFacetLabel M J)
    (φ : relativeSubspace L.indices) :
    (facetFlatEquiv L φ).val = dualAction M L.representative φ.val := rfl

/-- The actual image of the standard facet inside the target relative flat. -/
noncomputable def translatedFacet {M : CoxeterMatrix I} {J : Set I} (L : RawFacetLabel M J) :
    Set (relativeSubspace J) :=
  facetFlatEquiv L '' ((Subtype.val : relativeSubspace L.indices → Dual I) ⁻¹'
    standardFacet M L.indices)

theorem mem_translatedFacet_iff {M : CoxeterMatrix I} {J : Set I} (L : RawFacetLabel M J)
    (p : relativeSubspace J) :
    p ∈ translatedFacet L ↔ ∃ φ ∈ standardFacet M L.indices,
      dualAction M L.representative φ = p.val := by
  constructor
  · rintro ⟨φ, hφ, he⟩
    exact ⟨φ.val, hφ, congrArg Subtype.val he⟩
  · rintro ⟨φ, hφ, he⟩
    exact ⟨⟨φ, hφ.1⟩, hφ, Subtype.ext he⟩

theorem realRelativeRegular_of_mem_translatedFacet {M : CoxeterMatrix I} {J : Set I}
    (L : RawFacetLabel M J) {p : relativeSubspace J} (hp : p ∈ translatedFacet L) :
    realRelativeRegular M J p := by
  obtain ⟨φ, hφ, he⟩ := (mem_translatedFacet_iff L p).mp hp
  exact realRelativeRegular_of_translated_standardFacet M J p hφ L.representative
    L.parabolic_conjugacy he.symm

theorem translatedFacet_subset_regularSet {M : CoxeterMatrix I} {J : Set I}
    (L : RawFacetLabel M J) : translatedFacet L ⊆ regularSet (actualForms M J) := by
  intro p hp
  exact (mem_actual_regularSet_iff M J p).mpr (realRelativeRegular_of_mem_translatedFacet L hp)

theorem translatedFacet_nonempty {M : CoxeterMatrix I} {J : Set I} (L : RawFacetLabel M J) :
    (translatedFacet L).Nonempty := by
  refine ⟨facetFlatEquiv L ⟨canonicalDominant L.indices,
    canonicalDominant_mem_relativeSubspace L.indices⟩, ?_⟩
  exact ⟨_, canonicalDominant_mem_standardFacet M L.indices, rfl⟩

theorem convex_translatedFacet {M : CoxeterMatrix I} {J : Set I} (L : RawFacetLabel M J) :
    Convex ℝ (translatedFacet L) :=
  ((convex_standardFacet M L.indices).linear_preimage (relativeSubspace L.indices).subtype).linear_image
    (facetFlatEquiv L).toLinearMap

theorem isOpen_translatedFacet {M : CoxeterMatrix I} [Finite I] {J : Set I}
    (L : RawFacetLabel M J) : IsOpen (translatedFacet L) :=
  (facetFlatEquiv L).toHomeomorph.isOpenMap _ (isOpen_standardFacet_in_flat M L.indices)

/-- An intersection of actual translated facets forces equality of their
standard facet indices and equality of representatives modulo the right
standard parabolic. No finiteness assumption is used. -/
theorem translatedFacet_intersection_indices_coset {M : CoxeterMatrix I} {J : Set I}
    (L K : RawFacetLabel M J) (h : (translatedFacet L ∩ translatedFacet K).Nonempty) :
    L.indices = K.indices ∧ L.representative⁻¹ * K.representative ∈
      Artin.coxeterParabolic M L.indices := by
  obtain ⟨p, hpL, hpK⟩ := h
  obtain ⟨φ, hφ, hwφ⟩ := (mem_translatedFacet_iff L p).mp hpL
  obtain ⟨ψ, hψ, hvψ⟩ := (mem_translatedFacet_iff K p).mp hpK
  have htrans : dualAction M (L.representative⁻¹ * K.representative) ψ = φ := by
    rw [map_mul, mul_apply_eq_comp, hvψ, ← hwφ]
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  have hdom : IsDominant (dualAction M (L.representative⁻¹ * K.representative) ψ) :=
    htrans.symm ▸ standardFacet_isDominant M hφ
  have hfix := dominant_translate_eq M (standardFacet_isDominant M hψ)
    (L.representative⁻¹ * K.representative) hdom
  have hφψ : φ = ψ := htrans.symm.trans hfix
  have hIK : L.indices = K.indices :=
    standardFacet_indices_unique M hφ (hφψ.symm ▸ hψ)
  refine ⟨hIK, ?_⟩
  have hmem := dominant_translate_mem_parabolic M (standardFacet_isDominant M hψ)
    (L.representative⁻¹ * K.representative) hdom
  rw [zeroIndices_of_mem_standardFacet M hψ, ← hIK] at hmem
  exact hmem

/-- Representatives differing by the right source parabolic act identically
on its entire relative flat, hence have exactly the same actual facet image. -/
theorem translatedFacet_eq_of_indices_coset {M : CoxeterMatrix I} {J : Set I}
    (L K : RawFacetLabel M J) (hIK : L.indices = K.indices)
    (hc : L.representative⁻¹ * K.representative ∈ Artin.coxeterParabolic M L.indices) :
    translatedFacet L = translatedFacet K := by
  have hact {φ : Dual I} (hφ : φ ∈ relativeSubspace L.indices) :
      dualAction M K.representative φ = dualAction M L.representative φ := by
    have hfix := (mem_relativeSubspace_iff_fixed M L.indices φ).mp hφ _ hc
    calc
      dualAction M K.representative φ =
        dualAction M (L.representative * (L.representative⁻¹ * K.representative)) φ := by
          rw [mul_inv_cancel_left]
      _ = dualAction M L.representative
          (dualAction M (L.representative⁻¹ * K.representative) φ) := by
        rw [map_mul, mul_apply_eq_comp]
      _ = dualAction M L.representative φ := by rw [hfix]
  ext p
  rw [mem_translatedFacet_iff, mem_translatedFacet_iff]
  constructor
  · rintro ⟨φ, hφ, he⟩
    refine ⟨φ, hIK ▸ hφ, ?_⟩
    exact (hact hφ.1).trans he
  · rintro ⟨φ, hφ, he⟩
    have hφ' : φ ∈ standardFacet M L.indices := hIK.symm ▸ hφ
    exact ⟨φ, hφ', (hact hφ'.1).symm.trans he⟩

theorem translatedFacet_eq_of_intersection {M : CoxeterMatrix I} {J : Set I}
    (L K : RawFacetLabel M J) (h : (translatedFacet L ∩ translatedFacet K).Nonempty) :
    translatedFacet L = translatedFacet K := by
  obtain ⟨hIK, hc⟩ := translatedFacet_intersection_indices_coset L K h
  exact translatedFacet_eq_of_indices_coset L K hIK hc

theorem translatedFacet_intersection_iff {M : CoxeterMatrix I} {J : Set I}
    (L K : RawFacetLabel M J) :
    (translatedFacet L ∩ translatedFacet K).Nonempty ↔
      L.indices = K.indices ∧ L.representative⁻¹ * K.representative ∈
        Artin.coxeterParabolic M L.indices := by
  refine ⟨translatedFacet_intersection_indices_coset L K, ?_⟩
  rintro ⟨hIK, hc⟩
  have he := translatedFacet_eq_of_indices_coset L K hIK hc
  obtain ⟨p, hp⟩ := translatedFacet_nonempty L
  exact ⟨p, hp, he ▸ hp⟩

theorem translatedFacet_eq_iff {M : CoxeterMatrix I} {J : Set I}
    (L K : RawFacetLabel M J) : translatedFacet L = translatedFacet K ↔
      L.indices = K.indices ∧ L.representative⁻¹ * K.representative ∈
        Artin.coxeterParabolic M L.indices := by
  constructor
  · intro he
    obtain ⟨p, hp⟩ := translatedFacet_nonempty L
    exact translatedFacet_intersection_indices_coset L K ⟨p, hp, he ▸ hp⟩
  · rintro ⟨hIK, hc⟩
    exact translatedFacet_eq_of_indices_coset L K hIK hc

/-- Raw labels are quotiented by actual equality of right parabolic cosets,
with the source index set retained. No minimal representative is chosen. -/
def rawFacetSetoid (M : CoxeterMatrix I) (J : Set I) : Setoid (RawFacetLabel M J) where
  r L K := L.indices = K.indices ∧ L.representative⁻¹ * K.representative ∈
    Artin.coxeterParabolic M L.indices
  iseqv :=
    ⟨fun L => (translatedFacet_eq_iff L L).mp rfl,
      fun {L K} h => (translatedFacet_eq_iff K L).mp ((translatedFacet_eq_iff L K).mpr h).symm,
      fun {L K T} h₁ h₂ => (translatedFacet_eq_iff L T).mp
        (((translatedFacet_eq_iff L K).mpr h₁).trans ((translatedFacet_eq_iff K T).mpr h₂))⟩

/-- Facet labels modulo their actual right standard-parabolic ambiguity. -/
def FacetLabel (M : CoxeterMatrix I) (J : Set I) := Quotient (rawFacetSetoid M J)

/-- The actual region is well defined on the algebraic label quotient. -/
noncomputable def facetRegion {M : CoxeterMatrix I} {J : Set I} :
    FacetLabel M J → Set (relativeSubspace J) :=
  Quotient.lift translatedFacet (fun _ _ h => (translatedFacet_eq_iff _ _).mpr h)

@[simp]
theorem facetRegion_mk {M : CoxeterMatrix I} {J : Set I} (L : RawFacetLabel M J) :
    facetRegion (Quotient.mk (rawFacetSetoid M J) L) = translatedFacet L := rfl

theorem facetRegion_injective {M : CoxeterMatrix I} {J : Set I} :
    Function.Injective (facetRegion (M := M) (J := J)) := by
  refine Quotient.ind₂ ?_
  intro L K h
  exact Quotient.sound ((translatedFacet_eq_iff L K).mp h)

theorem facetRegion_nonempty {M : CoxeterMatrix I} {J : Set I} (L : FacetLabel M J) :
    (facetRegion L).Nonempty := by
  refine Quotient.inductionOn L ?_
  exact translatedFacet_nonempty

theorem facetRegion_subset_regularSet {M : CoxeterMatrix I} {J : Set I}
    (L : FacetLabel M J) : facetRegion L ⊆ regularSet (actualForms M J) := by
  refine Quotient.inductionOn L ?_
  exact translatedFacet_subset_regularSet

end ArtinNormalisers.Chamber3
