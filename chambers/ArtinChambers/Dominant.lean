module

public import ArtinLandmarks.Dominant
public import Mathlib.Analysis.Convex.Basic

/-!
# Uniqueness in the actual closed dominant dual chamber

If a dominant dual point has a dominant Coxeter translate, the two points
are equal. A left descent forces the corresponding coordinate of the
translated point to vanish; its simple reflection therefore fixes that
point, reducing the Coxeter length. This uses the actual contragredient
action and the already verified root-sign theorem, with no finite-type or
finite-rank hypothesis.
-/

set_option autoImplicit false

@[expose] public section

namespace ArtinNormalisers.Chamber3

open Theorem18 Landmark1

variable {I : Type*}

/-- The actual closed dominant dual chamber meets each Coxeter orbit in at
most one point, for an arbitrary Coxeter matrix and arbitrary index universe. -/
theorem dominant_translate_eq (M : CoxeterMatrix I) {φ : Dual I}
    (hφ : IsDominant φ) (w : M.Group) (hw : IsDominant (dualAction M w φ)) :
    dualAction M w φ = φ := by
  have core : ∀ n (u : M.Group), M.toCoxeterSystem.length u = n →
      IsDominant (dualAction M u φ) → dualAction M u φ = φ := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro u hn hu
      by_cases hu1 : u = 1
      · subst u
        simp
      obtain ⟨i, hi⟩ := M.toCoxeterSystem.exists_leftDescent_of_ne_one hu1
      have hneg : M.toCoxeterSystem.geometricRepresentation u⁻¹ (simpleRoot i) < 0 :=
        (M.toCoxeterSystem.geometricRepresentation_single_neg_iff u⁻¹ i).2
          (M.toCoxeterSystem.isRightDescent_inv_iff.mpr hi)
      have hnonpos := evaluation_nonpos_of_nonpos hφ hneg.le
      have hzero : dualAction M u φ (simpleRoot i) = 0 :=
        le_antisymm hnonpos (hu i)
      have hsimple : dualAction M (M.simple i) (dualAction M u φ) = dualAction M u φ :=
        (dualAction_simple_fixed_iff M i (dualAction M u φ)).2 hzero
      have hshort : dualAction M (M.simple i * u) φ = dualAction M u φ := by
        rw [map_mul, mul_apply_eq_comp, hsimple]
      have hlt : M.toCoxeterSystem.length (M.simple i * u) < n := by
        have hlen := M.toCoxeterSystem.isLeftDescent_iff.mp hi
        change M.toCoxeterSystem.length (M.simple i * u) + 1 =
          M.toCoxeterSystem.length u at hlen
        omega
      have hshortDom : IsDominant (dualAction M (M.simple i * u) φ) := hshort.symm ▸ hu
      exact hshort.symm.trans (ih _ hlt (M.simple i * u) rfl hshortDom)
  exact core _ w rfl hw

/-- Dominant-to-dominant transport lies in the actual standard parabolic
on the vanishing simple coordinates of the starting point. -/
theorem dominant_translate_mem_parabolic (M : CoxeterMatrix I) {φ : Dual I}
    (hφ : IsDominant φ) (w : M.Group) (hw : IsDominant (dualAction M w φ)) :
    w ∈ Artin.coxeterParabolic M (zeroIndices φ) :=
  (dominant_fixed_iff M hφ w).mp (dominant_translate_eq M hφ w hw)

/-- The actual standard facet: simple coordinates vanish on `J` and are
strictly positive off `J`, in the existing dual-space topology. -/
def standardFacet (_M : CoxeterMatrix I) (J : Set I) : Set (Dual I) :=
  {φ | φ ∈ relativeSubspace J ∧ ∀ i ∉ J, 0 < φ (simpleRoot i)}

theorem standardFacet_isDominant (M : CoxeterMatrix I) {J : Set I} {φ : Dual I}
    (hφ : φ ∈ standardFacet M J) : IsDominant φ := by
  intro i
  by_cases hi : i ∈ J
  · exact le_of_eq (hφ.1 i hi).symm
  · exact (hφ.2 i hi).le

theorem zeroIndices_of_mem_standardFacet (M : CoxeterMatrix I) {J : Set I} {φ : Dual I}
    (hφ : φ ∈ standardFacet M J) : zeroIndices φ = J := by
  ext i
  constructor
  · intro hi
    by_contra hiJ
    exact (ne_of_gt (hφ.2 i hiJ)) hi
  · exact hφ.1 i

theorem standardFacet_indices_unique (M : CoxeterMatrix I) {J K : Set I} {φ : Dual I}
    (hJ : φ ∈ standardFacet M J) (hK : φ ∈ standardFacet M K) : J = K :=
  (zeroIndices_of_mem_standardFacet M hJ).symm.trans (zeroIndices_of_mem_standardFacet M hK)

theorem canonicalDominant_mem_standardFacet (M : CoxeterMatrix I) (J : Set I) :
    canonicalDominant J ∈ standardFacet M J := by
  classical
  refine ⟨canonicalDominant_mem_relativeSubspace J, ?_⟩
  intro i hi
  simp [hi]

theorem standardFacet_nonempty (M : CoxeterMatrix I) (J : Set I) :
    (standardFacet M J).Nonempty :=
  ⟨canonicalDominant J, canonicalDominant_mem_standardFacet M J⟩

theorem mem_standardFacet_zeroIndices {M : CoxeterMatrix I} {φ : Dual I}
    (hφ : IsDominant φ) : φ ∈ standardFacet M (zeroIndices φ) := by
  refine ⟨fun _ hi => hi, ?_⟩
  intro i hi
  exact lt_of_le_of_ne (hφ i) (Ne.symm hi)

theorem standardFacet_translate_indices_eq (M : CoxeterMatrix I) {J K : Set I}
    {φ : Dual I} (hφ : φ ∈ standardFacet M J) (w : M.Group)
    (hwφ : dualAction M w φ ∈ standardFacet M K) : J = K := by
  have he := dominant_translate_eq M (standardFacet_isDominant M hφ) w
    (standardFacet_isDominant M hwφ)
  exact standardFacet_indices_unique M hφ (he ▸ hwφ)

theorem standardFacet_translate_mem_parabolic (M : CoxeterMatrix I) {J K : Set I}
    {φ : Dual I} (hφ : φ ∈ standardFacet M J) (w : M.Group)
    (hwφ : dualAction M w φ ∈ standardFacet M K) :
    w ∈ Artin.coxeterParabolic M J := by
  have hw := dominant_translate_mem_parabolic M (standardFacet_isDominant M hφ) w
    (standardFacet_isDominant M hwφ)
  rwa [zeroIndices_of_mem_standardFacet M hφ] at hw

theorem convex_standardFacet (M : CoxeterMatrix I) (J : Set I) :
    Convex ℝ (standardFacet M J) := by
  intro φ hφ ψ hψ a b ha hb hab
  refine ⟨(relativeSubspace J).add_mem ((relativeSubspace J).smul_mem a hφ.1)
    ((relativeSubspace J).smul_mem b hψ.1), ?_⟩
  intro i hi
  change 0 < a * φ (simpleRoot i) + b * ψ (simpleRoot i)
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    simpa [hb1] using hψ.2 i hi
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (hφ.2 i hi))
      (mul_nonneg hb (hψ.2 i hi).le)

/-- In finite rank, a standard facet is open inside its actual relative
flat; openness in the whole ambient dual space is not asserted. -/
theorem isOpen_standardFacet_in_flat [Finite I] (M : CoxeterMatrix I) (J : Set I) :
    IsOpen ((Subtype.val : relativeSubspace J → Dual I) ⁻¹' standardFacet M J) := by
  have he : (Subtype.val : relativeSubspace J → Dual I) ⁻¹' standardFacet M J =
      ⋂ i : {i : I // i ∉ J}, {φ : relativeSubspace J | 0 < φ.val (simpleRoot i)} := by
    ext φ
    simp only [Set.mem_preimage, standardFacet, Set.mem_ofPred_eq, φ.property, true_and,
      Set.mem_iInter]
    exact ⟨fun h i => h i i.property, fun h i hi => h ⟨i, hi⟩⟩
  rw [he]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
    ((continuous_evaluation (simpleRoot (i : I))).comp continuous_subtype_val)

end ArtinNormalisers.Chamber3
