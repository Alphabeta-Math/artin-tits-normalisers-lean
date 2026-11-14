module

public import ArtinAsphericity.Simpliciality
public import ArtinAsphericity.ConvexCover
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite central proper hyperplanes and the actual simpliciality hypotheses

The arrangement is the original family of distinct restricted root kernels.
Every member is closed, passes through zero and has codimension one. Its
actual chambers are strict finite-basis positive cones. These are geometric
inputs to Deligne's theorem; no asphericity theorem is assumed or concluded.
-/

@[expose] public section

namespace ArtinNormalisers.Asphericity5

open Theorem18 Chamber3

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The actual distinct restricted hyperplanes form a finite set. -/
theorem restrictedArrangement_finite [Finite M.Group] :
    (restrictedArrangement M J).Finite :=
  (retainedRoots_finite M J).image (restrictedHyperplane J)

/-- Every actual retained hyperplane is closed in the actual relative flat. -/
theorem restrictedArrangement_isClosed {H : Submodule ℝ (relativeSubspace J)}
    (hH : H ∈ restrictedArrangement M J) : IsClosed (H : Set (relativeSubspace J)) := by
  obtain ⟨r, _, rfl⟩ := hH
  exact (relativeEvaluation J r).isClosed_ker

/-- Centrality is literal containment of the origin by each linear kernel. -/
theorem restrictedArrangement_zero_mem {H : Submodule ℝ (relativeSubspace J)}
    (_hH : H ∈ restrictedArrangement M J) : (0 : relativeSubspace J) ∈ H := H.zero_mem

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Retaining only nonzero forms makes every retained kernel a genuine
codimension-one hyperplane, including in all degenerate parabolic cases. -/
theorem restrictedHyperplane_finrank_add_one [Finite M.Group] (r : RelativeRoot M J) :
    Module.finrank ℝ (restrictedHyperplane J r.val) + 1 =
      Module.finrank ℝ (relativeSubspace J) := by
  let : Finite I := finite_index M
  let : FiniteDimensional ℝ (relativeSubspace J) := finiteDimensional_relativeSubspace J
  have hf : (actualForms M J r).toLinearMap ≠ 0 := by
    intro hz
    apply actualForms_ne_zero M J r
    ext x
    exact congrArg (fun f : relativeSubspace J →ₗ[ℝ] ℝ => f x) hz
  exact Module.Dual.finrank_ker_add_one_of_ne_zero
    (K := ℝ) (V₁ := relativeSubspace J) (f := (actualForms M J r).toLinearMap) hf

/-- The complete actual finite/central/proper/closed/codimension-one and
strict-basis chamber hypotheses, independently of the desired conclusion. -/
theorem actual_arrangement_simplicial_hypotheses [Finite M.Group] :
    (restrictedArrangement M J).Finite ∧
      (∀ H ∈ restrictedArrangement M J,
        H ≠ ⊤ ∧ IsClosed (H : Set (relativeSubspace J)) ∧
        (0 : relativeSubspace J) ∈ H ∧
        Module.finrank ℝ H + 1 = Module.finrank ℝ (relativeSubspace J)) ∧
      (∀ C : ActualChamber M J,
        ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ (relativeSubspace J)),
          C.region = {x | ∀ i, 0 < b.repr x i} ∧
          closure C.region = (PointedCone.hull ℝ (Set.range b) : Set (relativeSubspace J)) ∧
          (PointedCone.hull ℝ (Set.range b)).IsSimplicial) := by
  refine ⟨restrictedArrangement_finite M J, ?_, actualChamber_basis_and_closure M J⟩
  intro H hH
  refine ⟨restrictedArrangement_proper M J hH,
    restrictedArrangement_isClosed M J hH,
    restrictedArrangement_zero_mem M J hH, ?_⟩
  obtain ⟨r, hr, rfl⟩ := hH
  exact restrictedHyperplane_finrank_add_one M J ⟨r, hr⟩

end ArtinNormalisers.Asphericity5
