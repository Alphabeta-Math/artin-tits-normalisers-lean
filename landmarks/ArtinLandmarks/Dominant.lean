module

public import ArtinNormalisers.Theorem18.NormalizerAction
public import ArtinLandmarkVendor.Geometric.Sign

/-!
# Dominant dual points and pointwise relative-flat stabilizers

The standard closed dual chamber has nonnegative simple-root evaluations.
Its point stabilizers are exactly the parabolics on the vanishing evaluations.
The argument uses finite-support evaluation and Coxeter length induction,
without a finite-rank or finite-group assumption.
-/

@[expose] public section

namespace ArtinNormalisers.Landmark1

open Theorem18
open scoped Classical

variable {I : Type*}

/-- Membership in the standard closed dual chamber. -/
def IsDominant (φ : Dual I) : Prop := ∀ i, 0 ≤ φ (simpleRoot i)

/-- The simple walls containing a dual point. -/
def zeroIndices (φ : Dual I) : Set I := {i | φ (simpleRoot i) = 0}

/-- A dominant functional is nonpositive on coordinatewise nonpositive
vectors. Only the finite support of the input vector is summed. -/
theorem evaluation_nonpos_of_nonpos {φ : Dual I} (hφ : IsDominant φ)
    {v : Vector I} (hv : v ≤ 0) : φ v ≤ 0 := by
  classical
  have he : φ = Finsupp.linearCombination ℝ (fun i => φ (simpleRoot i)) :=
    (dualCoordinates (I := I)).symm_apply_apply φ |>.symm
  rw [he, Finsupp.linearCombination_apply]
  exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hv i) (hφ i)

/-- The stabilizer of a dominant dual point is its actual generated standard
parabolic. No stabilizer or freeness theorem is assumed. -/
theorem dominant_fixed_iff (M : CoxeterMatrix I) {φ : Dual I} (hφ : IsDominant φ)
    (w : M.Group) :
    dualAction M w φ = φ ↔ w ∈ Artin.coxeterParabolic M (zeroIndices φ) := by
  constructor
  · intro hw
    have key : ∀ n (u : M.Group), M.toCoxeterSystem.length u = n →
        dualAction M u φ = φ → u ∈ Artin.coxeterParabolic M (zeroIndices φ) := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro u hn hu
        by_cases hu1 : u = 1
        · subst u
          exact Subgroup.one_mem _
        obtain ⟨i, hi⟩ := M.toCoxeterSystem.exists_leftDescent_of_ne_one hu1
        have hneg :
            M.toCoxeterSystem.geometricRepresentation u⁻¹ (simpleRoot i) < 0 :=
          (M.toCoxeterSystem.geometricRepresentation_single_neg_iff u⁻¹ i).2
            (M.toCoxeterSystem.isRightDescent_inv_iff.mpr hi)
        have hnonpos := evaluation_nonpos_of_nonpos hφ hneg.le
        have heval :
            φ (M.toCoxeterSystem.geometricRepresentation u⁻¹ (simpleRoot i)) =
              φ (simpleRoot i) :=
          congrArg (fun ψ : Dual I => ψ (simpleRoot i)) hu
        have hzero : φ (simpleRoot i) = 0 :=
          le_antisymm (heval ▸ hnonpos) (hφ i)
        have hsimple := (dualAction_simple_fixed_iff M i φ).2 hzero
        have hshortFixed : dualAction M (M.simple i * u) φ = φ := by
          rw [map_mul, mul_apply_eq_comp, hu, hsimple]
        have hshortLt : M.toCoxeterSystem.length (M.simple i * u) < n := by
          have hlen := M.toCoxeterSystem.isLeftDescent_iff.mp hi
          change M.toCoxeterSystem.length (M.simple i * u) + 1 =
            M.toCoxeterSystem.length u at hlen
          omega
        have hshort := ih (M.toCoxeterSystem.length (M.simple i * u))
          hshortLt (M.simple i * u) rfl hshortFixed
        have hsimpleMem : M.simple i ∈ Artin.coxeterParabolic M (zeroIndices φ) :=
          Subgroup.subset_closure ⟨i, hzero, rfl⟩
        have hcancel : M.simple i * (M.simple i * u) = u :=
          M.toCoxeterSystem.simple_mul_simple_cancel_left i
        exact hcancel ▸ Subgroup.mul_mem _ hsimpleMem hshort
    exact key _ w rfl hw
  · intro hw
    exact (mem_relativeSubspace_iff_fixed M (zeroIndices φ) φ).1
      (fun _ hi => hi) w hw

/-- A canonical dominant point of the relative flat: zero on selected simple
roots and one on every other simple root. -/
noncomputable def canonicalDominant (J : Set I) : Dual I := by
  classical
  exact (dualCoordinates (I := I)).symm (fun i => if i ∈ J then 0 else 1)

@[simp]
theorem canonicalDominant_apply_simpleRoot (J : Set I) (i : I) :
    canonicalDominant J (simpleRoot i) = if i ∈ J then 0 else 1 := by
  classical
  change dualCoordinates (canonicalDominant J) i = _
  simp [canonicalDominant]

theorem canonicalDominant_isDominant (J : Set I) : IsDominant (canonicalDominant J) := by
  classical
  intro i
  rw [canonicalDominant_apply_simpleRoot]
  split <;> norm_num

@[simp]
theorem zeroIndices_canonicalDominant (J : Set I) : zeroIndices (canonicalDominant J) = J := by
  classical
  ext i
  simp [zeroIndices]

theorem canonicalDominant_mem_relativeSubspace (J : Set I) :
    canonicalDominant J ∈ relativeSubspace J := by
  classical
  intro i hi
  simp [hi]

theorem canonicalDominant_fixed_iff (M : CoxeterMatrix I) (J : Set I) (w : M.Group) :
    dualAction M w (canonicalDominant J) = canonicalDominant J ↔
      w ∈ Artin.coxeterParabolic M J := by
  simpa only [zeroIndices_canonicalDominant] using
    dominant_fixed_iff M (canonicalDominant_isDominant J) w

/-- The pointwise stabilizer of the actual relative dual flat is exactly the
actual standard parabolic. This is valid in arbitrary Coxeter type. -/
theorem pointwise_flat_fixed_iff (M : CoxeterMatrix I) (J : Set I) (w : M.Group) :
    (∀ φ : relativeSubspace J, dualAction M w φ.val = φ.val) ↔
      w ∈ Artin.coxeterParabolic M J := by
  constructor
  · intro hw
    exact (canonicalDominant_fixed_iff M J w).1
      (hw ⟨canonicalDominant J, canonicalDominant_mem_relativeSubspace J⟩)
  · intro hw φ
    exact (mem_relativeSubspace_iff_fixed M J φ.val).1 φ.property w hw

end ArtinNormalisers.Landmark1
