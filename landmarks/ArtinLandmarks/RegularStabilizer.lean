module

public import ArtinLandmarks.Dominant
public import Mathlib.Data.Finset.Max

/-!
# Regular relative points have exactly the parabolic stabilizer

In finite Coxeter type every actual dual orbit meets the closed dominant
chamber: maximize evaluation on the sum of the positive roots. A simple
reflection permutes all positive roots except its own, so a negative simple
coordinate contradicts maximality. Dominant stabilizer generation then
identifies the full Coxeter stabilizer at a real relative regular point.
-/

@[expose] public section

namespace ArtinNormalisers.Landmark1

open ArtinNormalisers.Theorem18

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The actual positive roots in the standard geometric representation. -/
def positiveRoots : Set (Vector I) := {r | r ∈ roots M ∧ 0 < r}

theorem positiveRoots_finite [Finite M.Group] : (positiveRoots M).Finite :=
  (roots_finite M).subset (fun _ h => h.1)

/-- The sum contains each root vector once, independently of orbit indexing. -/
noncomputable def positiveRootSum [Finite M.Group] : Vector I :=
  ∑ r ∈ (positiveRoots_finite M).toFinset, r

private theorem roots_eq_geometricRoots : roots M = M.toCoxeterSystem.geometricRoots := by
  ext r
  rw [M.toCoxeterSystem.mem_geometricRoots]
  rfl

/-- Reflecting the positive-root sum subtracts twice the simple root. -/
theorem geometricReflection_positiveRootSum [Finite M.Group] (i : I) :
    M.geometricReflection i (positiveRootSum M) = positiveRootSum M - (2 : ℝ) • simpleRoot i := by
  classical
  let S := (positiveRoots_finite M).toFinset
  let a := simpleRoot i
  have hmem (r : Vector I) : r ∈ S ↔ r ∈ roots M ∧ 0 < r := by
    simp only [S, Set.Finite.mem_toFinset, positiveRoots, Set.mem_ofPred_eq]
  have ha : a ∈ S := by
    apply (hmem a).2
    refine ⟨⟨1, i, root_one M i⟩, ?_⟩
    exact lt_of_le_of_ne (Finsupp.single_nonneg.mpr zero_le_one)
      (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  have hbij := M.toCoxeterSystem.bijOn_geometricReflection_geometricRoots i
  have herase (r : Vector I) : r ∈ S.erase a ↔
      r ∈ M.toCoxeterSystem.geometricRoots ∧ 0 < r ∧ r ≠ Finsupp.single i 1 := by
    rw [Finset.mem_erase, hmem, roots_eq_geometricRoots]
    change (r ≠ Finsupp.single i 1 ∧ r ∈ M.toCoxeterSystem.geometricRoots ∧ 0 < r) ↔ _
    tauto
  have hsum : (∑ r ∈ S.erase a, M.geometricReflection i r) = ∑ r ∈ S.erase a, r := by
    apply Finset.sum_bij (fun r _ => M.geometricReflection i r)
    · intro r hr
      exact (herase _).2 (hbij.mapsTo ((herase r).1 hr))
    · intro r hr s hs hrs
      exact hbij.injOn ((herase r).1 hr) ((herase s).1 hs) hrs
    · intro r hr
      obtain ⟨s, hs, hsr⟩ := hbij.surjOn ((herase r).1 hr)
      exact ⟨s, (herase s).2 hs, hsr⟩
    · intro r hr
      rfl
  have hdecomp : positiveRootSum M = a + ∑ r ∈ S.erase a, r := by
    exact (Finset.add_sum_erase S (fun r => r) ha).symm
  have harefl : M.geometricReflection i a = -a :=
    M.geometricReflection_apply_single_self i
  rw [hdecomp, map_add, map_sum, hsum, harefl]
  change -a + ∑ r ∈ S.erase a, r = (a + ∑ r ∈ S.erase a, r) - (2 : ℝ) • a
  module

/-- A finite actual dual orbit has a representative in the closed dominant chamber. -/
theorem exists_dominant_dualAction [Finite M.Group] (φ : Dual I) :
    ∃ u : M.Group, IsDominant (dualAction M u φ) := by
  classical
  let := Fintype.ofFinite M.Group
  obtain ⟨u, _, hu⟩ := Finset.exists_max_image Finset.univ
    (fun w : M.Group => dualAction M w φ (positiveRootSum M)) Finset.univ_nonempty
  refine ⟨u, fun i => ?_⟩
  have hle := hu (M.simple i * u) (Finset.mem_univ _)
  have hsimple : M.toCoxeterSystem.simple i = M.simple i := by
    rw [CoxeterMatrix.toCoxeterSystem_simple]
  have heval : dualAction M (M.simple i * u) φ (positiveRootSum M) =
      dualAction M u φ (positiveRootSum M) - 2 * dualAction M u φ (simpleRoot i) := by
    rw [map_mul, mul_apply_eq_comp, dualAction_apply, ← hsimple,
      M.toCoxeterSystem.inv_simple, M.toCoxeterSystem.geometricRepresentation_simple,
      geometricReflection_positiveRootSum, map_sub, map_smul, smul_eq_mul]
  rw [heval] at hle
  linarith

/-- A real relative regular point avoids every retained restricted root hyperplane. -/
def realRelativeRegular (φ : relativeSubspace J) : Prop :=
  ∀ r ∈ retainedRoots M J, φ.val r ≠ 0

private def flatPointwiseStabilizer : Subgroup M.Group where
  carrier := {w | ∀ φ : relativeSubspace J, dualAction M w φ.val = φ.val}
  one_mem' := by intro φ; simp
  mul_mem' := by
    intro u v hu hv φ
    rw [map_mul, mul_apply_eq_comp, hv φ, hu φ]
  inv_mem' := by
    intro u hu φ
    have h := congrArg (fun f => dualAction M u⁻¹ f) (hu φ)
    simpa only [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
      map_one, one_apply_eq_self] using h.symm

/-- The full Coxeter stabilizer of a real regular relative point is the
actual generated parabolic, without assuming that an element normalizes it. -/
theorem realRelativeRegular_fixed_iff [Finite M.Group]
    (φ : relativeSubspace J) (hφ : realRelativeRegular M J φ) (g : M.Group) :
    dualAction M g φ.val = φ.val ↔ g ∈ Artin.coxeterParabolic M J := by
  constructor
  · intro hg
    obtain ⟨u, hu⟩ := exists_dominant_dualAction M φ.val
    let ψ := dualAction M u φ.val
    have hconj : dualAction M (u * g * u⁻¹) ψ = ψ := by
      dsimp only [ψ]
      rw [← mul_apply_eq_comp, ← map_mul]
      have heq : u * g * u⁻¹ * u = u * g := by group
      rw [heq, map_mul, mul_apply_eq_comp, hg]
    have hpar := (dominant_fixed_iff M hu (u * g * u⁻¹)).1 hconj
    have hle : Artin.coxeterParabolic M (zeroIndices ψ) ≤
        (flatPointwiseStabilizer M J).comap (MulAut.conj u⁻¹).toMonoidHom := by
      change Subgroup.closure (M.simple '' zeroIndices ψ) ≤ _
      apply (Subgroup.closure_le _).2
      rintro _ ⟨i, hi, rfl⟩
      have hβroot : root M u⁻¹ i ∈ roots M := ⟨u⁻¹, i, rfl⟩
      have hβzero : φ.val (root M u⁻¹ i) = 0 := hi
      have hβann : ∀ f : relativeSubspace J, f.val (root M u⁻¹ i) = 0 := by
        intro f
        by_contra hf
        exact (hφ _ ⟨hβroot, f, hf⟩) hβzero
      intro f
      have hsf : dualAction M (M.simple i) (dualAction M u f.val) =
          dualAction M u f.val := by
        apply (dualAction_simple_fixed_iff M i _).2
        exact hβann f
      have h := congrArg (fun a => dualAction M u⁻¹ a) hsf
      change dualAction M (u⁻¹ * M.simple i * (u⁻¹)⁻¹) f.val = f.val
      simpa only [inv_inv, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, mul_assoc,
        map_one, one_apply_eq_self] using h
    have hgflat := hle hpar
    have heq : u⁻¹ * (u * g * u⁻¹) * (u⁻¹)⁻¹ = g := by group
    change ∀ f : relativeSubspace J,
      dualAction M (u⁻¹ * (u * g * u⁻¹) * (u⁻¹)⁻¹) f.val = f.val at hgflat
    rw [heq] at hgflat
    exact (pointwise_flat_fixed_iff M J g).1 hgflat
  · intro hg
    exact (mem_relativeSubspace_iff_fixed M J φ.val).1 φ.property g hg

end ArtinNormalisers.Landmark1
