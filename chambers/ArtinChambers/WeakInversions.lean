module

public import ArtinChambers.InversionLength

/-!
# Coxeter weak prefixes and the actual geometric root inversions

Length additivity forces a common left descent. Removing it preserves
length additivity, and its simple reflection transports all positive roots
except its own simple root. Induction gives the converse of InversionLength,
for arbitrary Coxeter systems with no finiteness assumption.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

variable {I W : Type*} [Group W] {M : CoxeterMatrix I}

/-- An additive initial factor has a subset of the inverse root inversions. -/
theorem rootInversions_subset_of_length_eq_add_system (cs : CoxeterSystem M W)
    (d f : W) (hadd : cs.length f = cs.length d + cs.length (d⁻¹ * f)) :
    ∀ r ∈ cs.geometricRoots, 0 < r →
      cs.geometricRepresentation d⁻¹ r < 0 → cs.geometricRepresentation f⁻¹ r < 0 := by
  induction hn : cs.length d using Nat.strong_induction_on generalizing d f with
  | ind n ih =>
    by_cases hd : d = 1
    · subst d
      intro r _ hpos hneg
      simp only [inv_one, map_one, one_apply_eq_self] at hneg
      exact False.elim (lt_asymm hpos hneg)
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hd
    have hld : cs.length (cs.simple i * d) + 1 = cs.length d :=
      cs.isLeftDescent_iff.1 hi
    have hprod : (cs.simple i * d) * (d⁻¹ * f) = cs.simple i * f := by
      simp only [mul_assoc, mul_inv_cancel_left]
    have hbound := cs.length_mul_le (cs.simple i * d) (d⁻¹ * f)
    rw [hprod] at hbound
    have hfi : cs.IsLeftDescent f i := by
      change cs.length (cs.simple i * f) < cs.length f
      omega
    have hlf : cs.length (cs.simple i * f) + 1 = cs.length f :=
      cs.isLeftDescent_iff.1 hfi
    have hcancel : (cs.simple i * d)⁻¹ * (cs.simple i * f) = d⁻¹ * f := by
      rw [mul_inv_rev, cs.inv_simple, mul_assoc, cs.simple_mul_simple_cancel_left]
    have hadd' : cs.length (cs.simple i * f) = cs.length (cs.simple i * d) +
        cs.length ((cs.simple i * d)⁻¹ * (cs.simple i * f)) := by
      rw [hcancel]
      omega
    have hind := ih (cs.length (cs.simple i * d)) (by omega)
      (cs.simple i * d) (cs.simple i * f) hadd' rfl
    intro r hr hpos hneg
    by_cases heq : r = Finsupp.single i 1
    · subst r
      exact (cs.geometricRepresentation_single_neg_iff f⁻¹ i).2
        (cs.isRightDescent_inv_iff.2 hfi)
    have hreflect (g : W) (v : I →₀ ℝ) :
        cs.geometricRepresentation (cs.simple i * g)⁻¹ (M.geometricReflection i v) =
          cs.geometricRepresentation g⁻¹ v := by
      rw [mul_inv_rev, cs.inv_simple, map_mul, mul_apply_eq_comp,
        cs.geometricRepresentation_simple]
      have hreflection := LinearMap.congr_fun (M.geometricReflection_mul_self i) v
      change M.geometricReflection i (M.geometricReflection i v) = v at hreflection
      rw [hreflection]
    have hr' : M.geometricReflection i r ∈ cs.geometricRoots :=
      (cs.geometricReflection_apply_mem_geometricRoots_iff i).2 hr
    have hp' : 0 < M.geometricReflection i r :=
      cs.geometricReflection_pos_of_mem_geometricRoots hr hpos heq
    have hn' : cs.geometricRepresentation (cs.simple i * d)⁻¹
        (M.geometricReflection i r) < 0 := by
      rwa [hreflect]
    have hf := hind _ hr' hp' hn'
    rwa [hreflect] at hf

/-- Root inversion inclusion is equivalent to the additive weak-prefix identity. -/
theorem length_eq_add_iff_rootInversions_subset_system (cs : CoxeterSystem M W)
    (d f : W) :
    cs.length f = cs.length d + cs.length (d⁻¹ * f) ↔
      ∀ r ∈ cs.geometricRoots, 0 < r →
        cs.geometricRepresentation d⁻¹ r < 0 → cs.geometricRepresentation f⁻¹ r < 0 :=
  ⟨rootInversions_subset_of_length_eq_add_system cs d f,
    length_eq_add_of_rootInversions_subset_system cs d f⟩

/-- Converse for the actual presentation-defined Coxeter group. -/
theorem rootInversions_subset_of_length_eq_add (M : CoxeterMatrix I) (d f : M.Group)
    (hadd : M.toCoxeterSystem.length f = M.toCoxeterSystem.length d +
      M.toCoxeterSystem.length (d⁻¹ * f)) :
    ∀ r ∈ M.toCoxeterSystem.geometricRoots, 0 < r →
      M.toCoxeterSystem.geometricRepresentation d⁻¹ r < 0 →
      M.toCoxeterSystem.geometricRepresentation f⁻¹ r < 0 :=
  rootInversions_subset_of_length_eq_add_system M.toCoxeterSystem d f hadd

/-- The inversion criterion for weak prefixes in the actual Coxeter group. -/
theorem length_eq_add_iff_rootInversions_subset (M : CoxeterMatrix I) (d f : M.Group) :
    M.toCoxeterSystem.length f = M.toCoxeterSystem.length d +
      M.toCoxeterSystem.length (d⁻¹ * f) ↔
    ∀ r ∈ M.toCoxeterSystem.geometricRoots, 0 < r →
      M.toCoxeterSystem.geometricRepresentation d⁻¹ r < 0 →
      M.toCoxeterSystem.geometricRepresentation f⁻¹ r < 0 :=
  length_eq_add_iff_rootInversions_subset_system M.toCoxeterSystem d f

end ArtinNormalisers.Chamber3
