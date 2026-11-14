module

public import ArtinLandmarkVendor.Geometric.Sign

/-!
# Inclusion of actual root inversions implies Coxeter length additivity

The inversions use the standard geometric representation and its actual
positive roots. A left descent is common to both elements; removing it
transports the remaining inversions by the same simple reflection. Induction
on Coxeter length gives the prefix length identity, without any finiteness
or ambient/restricted length identification.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

variable {I W : Type*} [Group W] {M : CoxeterMatrix I}

/-- Inversion inclusion for the actual geometric roots implies that `d` is
an initial factor of `f` with additive Coxeter lengths. -/
theorem length_eq_add_of_rootInversions_subset_system (cs : CoxeterSystem M W)
    (d f : W)
    (hsub : ∀ r ∈ cs.geometricRoots, 0 < r →
      cs.geometricRepresentation d⁻¹ r < 0 → cs.geometricRepresentation f⁻¹ r < 0) :
    cs.length f = cs.length d + cs.length (d⁻¹ * f) := by
  induction hn : cs.length d using Nat.strong_induction_on generalizing d f with
  | ind n ih =>
    by_cases hd : d = 1
    · subst d
      have hn0 : n = 0 := by simpa using hn.symm
      simp [hn0]
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hd
    have hdi : cs.geometricRepresentation d⁻¹ (Finsupp.single i 1) < 0 :=
      (cs.geometricRepresentation_single_neg_iff d⁻¹ i).2
        (cs.isRightDescent_inv_iff.2 hi)
    have hα : (0 : I →₀ ℝ) < Finsupp.single i 1 :=
      lt_of_le_of_ne (Finsupp.single_nonneg.mpr zero_le_one)
        (Finsupp.single_ne_zero.mpr one_ne_zero).symm
    have hfi : cs.IsLeftDescent f i :=
      cs.isRightDescent_inv_iff.1 ((cs.geometricRepresentation_single_neg_iff f⁻¹ i).1
        (hsub _ (cs.single_mem_geometricRoots i) hα hdi))
    have hnew : ∀ r ∈ cs.geometricRoots, 0 < r →
        cs.geometricRepresentation (cs.simple i * d)⁻¹ r < 0 →
        cs.geometricRepresentation (cs.simple i * f)⁻¹ r < 0 := by
      intro r hr hpos hneg
      have hne : r ≠ Finsupp.single i 1 := by
        intro heq
        subst r
        have he : cs.geometricRepresentation (cs.simple i * d)⁻¹ (Finsupp.single i 1) =
            -cs.geometricRepresentation d⁻¹ (Finsupp.single i 1) := by
          rw [mul_inv_rev, cs.inv_simple, map_mul, mul_apply_eq_comp,
            cs.geometricRepresentation_simple, M.geometricReflection_apply_single_self, map_neg]
        rw [he] at hneg
        exact (neg_pos.mpr hdi).not_gt hneg
      have hr' : M.geometricReflection i r ∈ cs.geometricRoots :=
        (cs.geometricReflection_apply_mem_geometricRoots_iff i).2 hr
      have hp' : 0 < M.geometricReflection i r :=
        cs.geometricReflection_pos_of_mem_geometricRoots hr hpos hne
      have hd' : cs.geometricRepresentation d⁻¹ (M.geometricReflection i r) < 0 := by
        simpa only [mul_inv_rev, cs.inv_simple, map_mul, mul_apply_eq_comp,
          cs.geometricRepresentation_simple] using hneg
      have hf' := hsub _ hr' hp' hd'
      simpa only [mul_inv_rev, cs.inv_simple, map_mul, mul_apply_eq_comp,
        cs.geometricRepresentation_simple] using hf'
    have hld : cs.length (cs.simple i * d) + 1 = cs.length d :=
      cs.isLeftDescent_iff.1 hi
    have hlf : cs.length (cs.simple i * f) + 1 = cs.length f :=
      cs.isLeftDescent_iff.1 hfi
    have hind := ih (cs.length (cs.simple i * d)) (by omega)
      (cs.simple i * d) (cs.simple i * f) hnew rfl
    have hcancel : (cs.simple i * d)⁻¹ * (cs.simple i * f) = d⁻¹ * f := by
      rw [mul_inv_rev, cs.inv_simple, mul_assoc, cs.simple_mul_simple_cancel_left]
    rw [hcancel] at hind
    omega

/-- The same root-inversion criterion for the presentation-defined Coxeter group. -/
theorem length_eq_add_of_rootInversions_subset (M : CoxeterMatrix I) (d f : M.Group)
    (hsub : ∀ r ∈ M.toCoxeterSystem.geometricRoots, 0 < r →
      M.toCoxeterSystem.geometricRepresentation d⁻¹ r < 0 →
      M.toCoxeterSystem.geometricRepresentation f⁻¹ r < 0) :
    M.toCoxeterSystem.length f = M.toCoxeterSystem.length d +
      M.toCoxeterSystem.length (d⁻¹ * f) :=
  length_eq_add_of_rootInversions_subset_system M.toCoxeterSystem d f hsub

end ArtinNormalisers.Chamber3
