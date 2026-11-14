module

public import ArtinDeligne.ContractibleExtension

/-! Actual parameterized simplex extensions into contractible spaces.
The parameter is arbitrary; none of the conclusions is a field of the data. -/
@[expose] public section
set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open scoped unitInterval
open Convexity Topology

universe u v

/-- Arbitrary continuous boundary data over any parameter space extends into a
contractible target. Source and target universes are independent. -/
theorem exists_parameterized_simplex_extension
    {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
    [ContractibleSpace Z] (n : ℕ)
    (h : C(X × StdSimplex.boundary n, Z)) :
    ∃ F : C(X × StdSimplex ℝ (Fin (n + 1)), Z),
      ∀ x (b : StdSimplex.boundary n), F (x, b.val) = h (x, b) := by
  obtain ⟨z, ⟨L⟩⟩ := id_nullhomotopic Z
  let H : C((X × StdSimplex.boundary n) × I, Z) :=
    ⟨fun p ↦ L.symm (p.2, h p.1), by fun_prop⟩
  obtain ⟨K, _, hK⟩ := StdSimplex.simplexBoundary_homotopy_extension n
    (ContinuousMap.const _ z) H (fun x b ↦ L.symm.apply_zero (h (x, b)))
  refine ⟨⟨fun p ↦ K (p, 1), by fun_prop⟩, fun x b ↦ ?_⟩
  exact (hK x b 1).trans (L.symm.apply_one (h (x, b)))

/-- The whole parameterized side homotopy extends while retaining both complete
endpoint maps. This statement permits an arbitrary parameter topology. -/
theorem exists_parameterized_simplex_homotopy_extension_same_universe
    {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]
    [ContractibleSpace Z] (n : ℕ)
    (f₀ f₁ : C(X × StdSimplex ℝ (Fin (n + 1)), Z))
    (H : C(I × (X × StdSimplex.boundary n), Z))
    (h₀ : ∀ x b, H (0, (x, b)) = f₀ (x, b.val))
    (h₁ : ∀ x b, H (1, (x, b)) = f₁ (x, b.val)) :
    ∃ K : ContinuousMap.Homotopy f₀ f₁,
      ∀ t x (b : StdSimplex.boundary n), K (t, (x, b.val)) = H (t, (x, b)) := by
  obtain ⟨K, hK⟩ := exists_homotopy_extension_of_hep (Z := TopCat.of Z)
    (TopCat.parameterizedSimplexBoundaryInclusion (TopCat.of X) n)
    (TopCat.homotopyExtensionProperty_simplexBoundary (TopCat.of X) n)
    f₀ f₁ H (fun a ↦ h₀ a.1 a.2) (fun a ↦ h₁ a.1 a.2)
  exact ⟨K, fun t x b ↦ hK t (x, b)⟩


/-- Universe-independent parameterized endpoint-relative extension. The lifts
only reconcile the categorical universe and are removed from the conclusion. -/
theorem exists_parameterized_simplex_homotopy_extension
    {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
    [ContractibleSpace Z] (n : ℕ)
    (f₀ f₁ : C(X × StdSimplex ℝ (Fin (n + 1)), Z))
    (H : C(I × (X × StdSimplex.boundary n), Z))
    (h₀ : ∀ x b, H (0, (x, b)) = f₀ (x, b.val))
    (h₁ : ∀ x b, H (1, (x, b)) = f₁ (x, b.val)) :
    ∃ K : ContinuousMap.Homotopy f₀ f₁,
      ∀ t x (b : StdSimplex.boundary n), K (t, (x, b.val)) = H (t, (x, b)) := by
  let _ : ContractibleSpace (ULift.{u} Z) :=
    (Homeomorph.ulift : ULift.{u} Z ≃ₜ Z).contractibleSpace
  let g₀ : C(ULift.{v} X × StdSimplex ℝ (Fin (n + 1)), ULift.{u} Z) :=
    ⟨fun p ↦ ULift.up (f₀ (p.1.down, p.2)), by fun_prop⟩
  let g₁ : C(ULift.{v} X × StdSimplex ℝ (Fin (n + 1)), ULift.{u} Z) :=
    ⟨fun p ↦ ULift.up (f₁ (p.1.down, p.2)), by fun_prop⟩
  let B : C(I × (ULift.{v} X × StdSimplex.boundary n), ULift.{u} Z) :=
    ⟨fun p ↦ ULift.up (H (p.1, (p.2.1.down, p.2.2))), by fun_prop⟩
  obtain ⟨K, hK⟩ := exists_parameterized_simplex_homotopy_extension_same_universe n
    g₀ g₁ B (fun x b ↦ congrArg ULift.up (h₀ x.down b))
    (fun x b ↦ congrArg ULift.up (h₁ x.down b))
  let L : ContinuousMap.Homotopy f₀ f₁ :=
    ⟨⟨fun p ↦ (K (p.1, (ULift.up p.2.1, p.2.2))).down, by fun_prop⟩,
      fun x ↦ congrArg ULift.down (K.apply_zero (ULift.up x.1, x.2)),
      fun x ↦ congrArg ULift.down (K.apply_one (ULift.up x.1, x.2))⟩
  exact ⟨L, fun t x b ↦ congrArg ULift.down (hK t (ULift.up x) b)⟩


end ArtinNormalisers.Deligne5
