import ArtinRibbons.Fundamental
import ArtinLandmarks.Dominant

/-!
# Actual parabolic coefficient invariance and longest-element root signs

A simple reflection changes only its own coefficient. A word in the actual
standard parabolic therefore fixes every coefficient outside its index set.
For a finite Coxeter group the actual longest parabolic element has every
simple index of that parabolic as a right descent. Its simple-root images
are negative; positive linear combinations supported there are nonpositive,
and genuine roots remain nonzero. No restricted-root classification or
additional Coxeter matrix is assumed.

All proof suppliers are the already accepted TauCeti geometric reflection,
parabolic word and root-sign APIs, the local accepted Ribbon2 longest-element
construction, and ordinary pinned mathlib linear/order APIs.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Homotopy5

open Theorem18 Ribbon2

variable {I : Type*} (M : CoxeterMatrix I)

/-- Every actual standard-parabolic element fixes all coefficients outside
its generating index set, for arbitrary finitely supported vectors. -/
theorem geometricRepresentation_apply_outside_parabolic (U : Set I)
    {w : M.Group} (hw : w ∈ Artin.coxeterParabolic M U)
    (r : Vector I) {i : I} (hi : i ∉ U) :
    M.toCoxeterSystem.geometricRepresentation w r i = r i := by
  let cs := M.toCoxeterSystem
  obtain ⟨word, hword, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hw
  have key : ∀ word : List I, (∀ j ∈ word, j ∈ U) → ∀ v : Vector I,
      cs.geometricRepresentation (cs.wordProd word) v i = v i := by
    intro word
    induction word with
    | nil => intro _ v; simp
    | cons j word ih =>
      intro hjword v
      have hij : i ≠ j := fun he => hi (he ▸ hjword j List.mem_cons_self)
      rw [cs.wordProd_cons, map_mul, mul_apply_eq_comp,
        cs.geometricRepresentation_simple,
        M.geometricReflection_apply_apply_of_ne hij]
      exact ih (fun k hk => hjword k (List.mem_cons_of_mem j hk)) v
  exact key word hword r

variable [Finite M.Group]

/-- The actual longest element of a standard parabolic makes every
positive root supported on that parabolic negative. -/
theorem parabolicLongest_positive_supported_negative (U : Set I)
    {r : Vector I} (hrroot : r ∈ M.toCoxeterSystem.geometricRoots)
    (hrpos : 0 < r) (hsupp : ∀ i, i ∉ U → r i = 0) :
    M.toCoxeterSystem.geometricRepresentation (parabolicLongest M U) r < 0 := by
  classical
  let cs := M.toCoxeterSystem
  let longest := parabolicLongest M U
  have simple_negative (i : I) (hi : i ∈ U) :
      cs.geometricRepresentation longest (Finsupp.single i 1) < 0 := by
    apply (cs.geometricRepresentation_single_neg_iff longest i).2
    by_contra hdesc
    have hlen := cs.not_isRightDescent_iff.mp hdesc
    have hmem : longest * cs.simple i ∈ Artin.coxeterParabolic M U :=
      (Artin.coxeterParabolic M U).mul_mem (parabolicLongest_mem_parabolic M U)
        (Subgroup.subset_closure ⟨i, hi, rfl⟩)
    have hmax := parabolicLongest_max M U hmem
    dsimp only [cs, longest] at hlen hmax
    omega
  have expand : r.sum (fun i a => a • Finsupp.single i (1 : ℝ)) = r := by
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using r.sum_single
  have nonpositive : cs.geometricRepresentation longest r ≤ 0 := by
    rw [← expand]
    simp only [Finsupp.sum, map_sum, map_smul]
    apply Finset.sum_nonpos
    intro i hi
    have hiU : i ∈ U := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hi) (hsupp i hn)
    exact smul_nonpos_of_nonneg_of_nonpos (hrpos.le i) (simple_negative i hiU).le
  apply lt_of_le_of_ne nonpositive
  exact (map_ne_zero_iff _ (cs.geometricRepresentation.apply_bijective longest).injective).2
    (cs.ne_zero_of_mem_geometricRoots hrroot)

end ArtinNormalisers.Homotopy5
