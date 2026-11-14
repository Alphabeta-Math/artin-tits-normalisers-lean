module

public import ArtinChambers.ActualArrangement
public import ArtinChambers.Dominant

/-!
# Actual relative regularity and the full Coxeter stabilizer

A conjugated simple reflection fixes a dual point exactly when evaluation at
its actual root vanishes. A retained root has a nonzero evaluation somewhere
on the relative flat, so its reflection cannot belong to the flat's
pointwise parabolic stabilizer. This proves the converse to Landmark 1.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open Theorem18 Landmark1

variable {I : Type*}

/-- Stabilizers of actual dual points transform by actual group conjugation. -/
theorem dualAction_stabilizer_conjugate (M : CoxeterMatrix I) (w : M.Group)
    (φ : Dual I) (g : M.Group) :
    dualAction M g (dualAction M w φ) = dualAction M w φ ↔
      dualAction M (w⁻¹ * g * w) φ = φ := by
  constructor
  · intro h
    have hh := congrArg (dualAction M w⁻¹) h
    simpa only [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
      map_one, one_apply_eq_self, mul_assoc] using hh
  · intro h
    apply (Representation.apply_bijective (dualAction M) w⁻¹).injective
    simpa only [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
      map_one, one_apply_eq_self, mul_assoc] using h

/-- The actual reflection through an actual root has precisely its dual
evaluation hyperplane as its fixed locus. -/
theorem conjugate_simple_fixed_iff (M : CoxeterMatrix I) (a : M.Group) (i : I)
    (φ : Dual I) :
    dualAction M (a * M.simple i * a⁻¹) φ = φ ↔ φ (root M a i) = 0 := by
  have hc := (dualAction_stabilizer_conjugate M a⁻¹ φ (M.simple i)).symm
  simp only [inv_inv] at hc
  simpa only [dualAction_apply, inv_inv, root] using
    hc.trans (dualAction_simple_fixed_iff M i (dualAction M a⁻¹ φ))

/-- Retention rules out membership of the root's reflection in the standard
parabolic: that subgroup fixes every actual point of the relative flat. -/
theorem conjugate_simple_not_mem_parabolic_of_retained (M : CoxeterMatrix I)
    (J : Set I) (a : M.Group) (i : I) (hr : root M a i ∈ retainedRoots M J) :
    a * M.simple i * a⁻¹ ∉ Artin.coxeterParabolic M J := by
  obtain ⟨_, ψ, hψ⟩ := hr
  intro ht
  have hfix := (mem_relativeSubspace_iff_fixed M J ψ.val).mp ψ.property _ ht
  exact hψ ((conjugate_simple_fixed_iff M a i ψ.val).mp hfix)

/-- A relative point with exactly the actual standard parabolic stabilizer
avoids every retained root hyperplane. No finite-type assumption is needed
for this direction. -/
theorem realRelativeRegular_of_stabilizer (M : CoxeterMatrix I) (J : Set I)
    (φ : relativeSubspace J)
    (hstab : ∀ w : M.Group, dualAction M w φ.val = φ.val ↔
      w ∈ Artin.coxeterParabolic M J) : realRelativeRegular M J φ := by
  intro r hr hz
  obtain ⟨hr, ψ, hψ⟩ := hr
  obtain ⟨a, i, rfl⟩ := hr
  have hret : root M a i ∈ retainedRoots M J := ⟨⟨a, i, rfl⟩, ψ, hψ⟩
  have hfix := (conjugate_simple_fixed_iff M a i φ.val).mpr hz
  exact conjugate_simple_not_mem_parabolic_of_retained M J a i hret
    ((hstab _).mp hfix)

/-- In finite Coxeter type, regularity of the actual relative arrangement is
equivalent to the full point-stabilizer statement. -/
theorem realRelativeRegular_iff_stabilizer (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) (φ : relativeSubspace J) :
    realRelativeRegular M J φ ↔ ∀ w : M.Group,
      dualAction M w φ.val = φ.val ↔ w ∈ Artin.coxeterParabolic M J := by
  constructor
  · intro h w
    exact realRelativeRegular_fixed_iff M J φ h w
  · exact realRelativeRegular_of_stabilizer M J φ

theorem mem_actual_regularSet_iff_stabilizer (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) (φ : relativeSubspace J) :
    φ ∈ regularSet (actualForms M J) ↔ ∀ w : M.Group,
      dualAction M w φ.val = φ.val ↔ w ∈ Artin.coxeterParabolic M J :=
  (mem_actual_regularSet_iff M J φ).trans (realRelativeRegular_iff_stabilizer M J φ)

/-- Conjugating an actual standard parabolic transports the full stabilizer
of every point in its standard facet, not merely the stabilizer of a chosen
canonical point. -/
theorem standardFacet_translate_stabilizer (M : CoxeterMatrix I) {K J : Set I}
    {φ : Dual I} (hφ : φ ∈ standardFacet M K) (w : M.Group)
    (hconj : (Artin.coxeterParabolic M K).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M J) (g : M.Group) :
    dualAction M g (dualAction M w φ) = dualAction M w φ ↔
      g ∈ Artin.coxeterParabolic M J := by
  calc
    dualAction M g (dualAction M w φ) = dualAction M w φ ↔
        dualAction M (w⁻¹ * g * w) φ = φ := dualAction_stabilizer_conjugate M w φ g
    _ ↔ w⁻¹ * g * w ∈ Artin.coxeterParabolic M K := by
      simpa only [zeroIndices_of_mem_standardFacet M hφ] using
        dominant_fixed_iff M (standardFacet_isDominant M hφ) (w⁻¹ * g * w)
    _ ↔ g ∈ Artin.coxeterParabolic M J := by
      rw [← hconj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem standardFacet_translate_mem_flat (M : CoxeterMatrix I) {K J : Set I}
    {φ : Dual I} (hφ : φ ∈ standardFacet M K) (w : M.Group)
    (hconj : (Artin.coxeterParabolic M K).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M J) : dualAction M w φ ∈ relativeSubspace J := by
  apply (mem_relativeSubspace_iff_fixed M J _).mpr
  intro g hg
  exact (standardFacet_translate_stabilizer M hφ w hconj g).mpr hg

/-- Any concrete representation of the transported point in the actual flat
is regular. The explicit value equality makes this independent of a chosen
proof used to construct that subtype. -/
theorem realRelativeRegular_of_translated_standardFacet (M : CoxeterMatrix I) (J : Set I)
    (ψ : relativeSubspace J) {K : Set I} {φ : Dual I}
    (hφ : φ ∈ standardFacet M K) (w : M.Group)
    (hconj : (Artin.coxeterParabolic M K).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M J) (he : ψ.val = dualAction M w φ) :
    realRelativeRegular M J ψ := by
  apply realRelativeRegular_of_stabilizer M J ψ
  intro g
  rw [he]
  exact standardFacet_translate_stabilizer M hφ w hconj g

theorem mem_actual_regularSet_of_translated_standardFacet (M : CoxeterMatrix I) (J : Set I)
    (ψ : relativeSubspace J) {K : Set I} {φ : Dual I}
    (hφ : φ ∈ standardFacet M K) (w : M.Group)
    (hconj : (Artin.coxeterParabolic M K).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M J) (he : ψ.val = dualAction M w φ) :
    ψ ∈ regularSet (actualForms M J) :=
  (mem_actual_regularSet_iff M J ψ).mpr
    (realRelativeRegular_of_translated_standardFacet M J ψ hφ w hconj he)

end ArtinNormalisers.Chamber3
