module

public import ArtinDeligneVendor.Topology.HELP.CylinderBoundary
public import ArtinDeligneVendor.Topology.Realization.SimplexBoundaryHEP
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Extensions into a contractible space

The contraction of the target and the actual homotopy extension property give
extensions of arbitrary continuous maps. Gluing the side and both caps in the
provider's topological pushout gives a homotopy with its entire prescribed side.

Proof ingredients: mathlib's `id_nullhomotopic` and homotopy reversal; the Colib
HEP, cylinder-boundary pushout, and simplex-boundary HEP at snapshot
`bac5cab53eb6526e366e861d289253ec81aa89f0`, relocated without changing these
mathematical objects. No extension or filler is assumed for the target.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped unitInterval

namespace ArtinNormalisers.Deligne5

universe u

/-- A contractible target extends every map across a map having HEP. -/
theorem exists_extension_of_hep
    {A B Z : TopCat.{u}} [ContractibleSpace Z]
    (i : A ⟶ B) (hi : TopCat.HomotopyExtensionProperty i) (h : C(A, Z)) :
    ∃ F : C(B, Z), ∀ a, F (i a) = h a := by
  obtain ⟨z, ⟨L⟩⟩ := id_nullhomotopic Z
  let H : C(I × A, Z) :=
    ⟨fun p ↦ L.symm (p.1, h p.2), by fun_prop⟩
  obtain ⟨K, _, hK⟩ := TopCat.homotopyExtensionProperty_continuous hi Z
    (ContinuousMap.const B z) H (fun a ↦ L.symm.apply_zero (h a))
  refine ⟨⟨fun b ↦ K (1, b), by fun_prop⟩, fun a ↦ ?_⟩
  exact (hK 1 a).trans (L.symm.apply_one (h a))

/-- Side data with both endpoint maps glued on the actual cylinder-boundary
pushout. The domain is not replaced by an assumed boundary filler. -/
def cylinderBoundaryData
    {A B Z : TopCat.{u}} (i : A ⟶ B) (f₀ f₁ : C(B, Z))
    (H : C(I × A, Z))
    (h₀ : ∀ a, H (0, a) = f₀ (i a))
    (h₁ : ∀ a, H (1, a) = f₁ (i a)) : TopCat.CylinderBoundary i ⟶ Z :=
  pushout.desc
    (TopCat.ofHom ⟨fun p ↦ H (p.2, p.1), by fun_prop⟩)
    (TopCat.ofHom ⟨Sum.elim f₀ f₁, f₀.continuous.sumElim f₁.continuous⟩)
    (by
      ext a
      cases a with
      | inl a => exact h₀ a
      | inr a => exact h₁ a)

@[simp] theorem cylinderBoundaryData_side
    {A B Z : TopCat.{u}} (i : A ⟶ B) (f₀ f₁ : C(B, Z))
    (H : C(I × A, Z)) (h₀ : ∀ a, H (0, a) = f₀ (i a))
    (h₁ : ∀ a, H (1, a) = f₁ (i a)) (a : A) (t : I) :
    cylinderBoundaryData i f₀ f₁ H h₀ h₁
      (TopCat.CylinderBoundary.cylinderBoundarySide i (a, t)) = H (t, a) :=
  by
    have he : TopCat.CylinderBoundary.cylinderBoundarySide i ≫
        cylinderBoundaryData i f₀ f₁ H h₀ h₁ =
        TopCat.ofHom ⟨fun p : A × I ↦ H (p.2, p.1), by fun_prop⟩ :=
      pushout.inl_desc _ _ _
    simpa only [CategoryTheory.comp_apply, TopCat.ofHom, ConcreteCategory.hom_ofHom, ContinuousMap.coe_mk,
      Sum.elim_inl, Sum.elim_inr, TopCat.CylinderBoundary.cylinderBoundarySideMap,
      TopCat.CylinderBoundary.cylinderBoundaryEnds] using ConcreteCategory.congr_hom he (a, t)

@[simp] theorem cylinderBoundaryData_cap_zero
    {A B Z : TopCat.{u}} (i : A ⟶ B) (f₀ f₁ : C(B, Z))
    (H : C(I × A, Z)) (h₀ : ∀ a, H (0, a) = f₀ (i a))
    (h₁ : ∀ a, H (1, a) = f₁ (i a)) (b : B) :
    cylinderBoundaryData i f₀ f₁ H h₀ h₁
      (TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inl b)) = f₀ b :=
  by
    have he : TopCat.CylinderBoundary.cylinderBoundaryCaps i ≫
        cylinderBoundaryData i f₀ f₁ H h₀ h₁ =
        TopCat.ofHom ⟨Sum.elim f₀ f₁, f₀.continuous.sumElim f₁.continuous⟩ :=
      pushout.inr_desc _ _ _
    simpa only [CategoryTheory.comp_apply, TopCat.ofHom, ConcreteCategory.hom_ofHom, ContinuousMap.coe_mk,
      Sum.elim_inl, Sum.elim_inr, TopCat.CylinderBoundary.cylinderBoundarySideMap,
      TopCat.CylinderBoundary.cylinderBoundaryEnds] using
      ConcreteCategory.congr_hom he (Sum.inl b)

@[simp] theorem cylinderBoundaryData_cap_one
    {A B Z : TopCat.{u}} (i : A ⟶ B) (f₀ f₁ : C(B, Z))
    (H : C(I × A, Z)) (h₀ : ∀ a, H (0, a) = f₀ (i a))
    (h₁ : ∀ a, H (1, a) = f₁ (i a)) (b : B) :
    cylinderBoundaryData i f₀ f₁ H h₀ h₁
      (TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inr b)) = f₁ b :=
  by
    have he : TopCat.CylinderBoundary.cylinderBoundaryCaps i ≫
        cylinderBoundaryData i f₀ f₁ H h₀ h₁ =
        TopCat.ofHom ⟨Sum.elim f₀ f₁, f₀.continuous.sumElim f₁.continuous⟩ :=
      pushout.inr_desc _ _ _
    simpa only [CategoryTheory.comp_apply, TopCat.ofHom, ConcreteCategory.hom_ofHom, ContinuousMap.coe_mk,
      Sum.elim_inl, Sum.elim_inr, TopCat.CylinderBoundary.cylinderBoundarySideMap,
      TopCat.CylinderBoundary.cylinderBoundaryEnds] using
      ConcreteCategory.congr_hom he (Sum.inr b)

/-- Every prescribed boundary homotopy between two maps into a contractible
space extends, retaining both complete endpoint maps and the exact side data. -/
theorem exists_homotopy_extension_of_hep
    {A B Z : TopCat.{u}} [ContractibleSpace Z]
    (i : A ⟶ B) (hi : TopCat.HomotopyExtensionProperty i)
    (f₀ f₁ : C(B, Z)) (H : C(I × A, Z))
    (h₀ : ∀ a, H (0, a) = f₀ (i a))
    (h₁ : ∀ a, H (1, a) = f₁ (i a)) :
    ∃ K : ContinuousMap.Homotopy f₀ f₁, ∀ t a, K (t, i a) = H (t, a) := by
  let h := cylinderBoundaryData i f₀ f₁ H h₀ h₁
  obtain ⟨F, hF⟩ := exists_extension_of_hep
    (TopCat.CylinderBoundary.cylinderBoundaryMap i)
    (TopCat.CylinderBoundary.homotopyExtensionProperty_cylinderBoundaryMap i hi) h.hom
  have hside (a : A) (t : I) : F (i a, t) = H (t, a) := by
    have he := hF (TopCat.CylinderBoundary.cylinderBoundarySide i (a, t))
    have hm : TopCat.CylinderBoundary.cylinderBoundaryMap i
        (TopCat.CylinderBoundary.cylinderBoundarySide i (a, t)) = (i a, t) := by
      simpa only [CategoryTheory.comp_apply, TopCat.ofHom, ConcreteCategory.hom_ofHom, ContinuousMap.coe_mk,
      Sum.elim_inl, Sum.elim_inr, TopCat.CylinderBoundary.cylinderBoundarySideMap,
      TopCat.CylinderBoundary.cylinderBoundaryEnds] using ConcreteCategory.congr_hom
        (TopCat.CylinderBoundary.cylinderBoundarySide_map i) (a, t)
    rw [hm] at he
    exact he.trans (cylinderBoundaryData_side i f₀ f₁ H h₀ h₁ a t)
  have hzero (b : B) : F (b, 0) = f₀ b := by
    have he := hF (TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inl b))
    have hm : TopCat.CylinderBoundary.cylinderBoundaryMap i
        (TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inl b)) = (b, 0) := by
      simpa only [CategoryTheory.comp_apply, TopCat.ofHom, ConcreteCategory.hom_ofHom, ContinuousMap.coe_mk,
      Sum.elim_inl, Sum.elim_inr, TopCat.CylinderBoundary.cylinderBoundarySideMap,
      TopCat.CylinderBoundary.cylinderBoundaryEnds] using ConcreteCategory.congr_hom
        (TopCat.CylinderBoundary.cylinderBoundaryCaps_map i) (Sum.inl b)
    rw [hm] at he
    exact he.trans (cylinderBoundaryData_cap_zero i f₀ f₁ H h₀ h₁ b)
  have hone (b : B) : F (b, 1) = f₁ b := by
    have he := hF (TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inr b))
    have hm : TopCat.CylinderBoundary.cylinderBoundaryMap i
        (TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inr b)) = (b, 1) := by
      simpa only [CategoryTheory.comp_apply, TopCat.ofHom, ConcreteCategory.hom_ofHom, ContinuousMap.coe_mk,
      Sum.elim_inl, Sum.elim_inr, TopCat.CylinderBoundary.cylinderBoundarySideMap,
      TopCat.CylinderBoundary.cylinderBoundaryEnds] using ConcreteCategory.congr_hom
        (TopCat.CylinderBoundary.cylinderBoundaryCaps_map i) (Sum.inr b)
    rw [hm] at he
    exact he.trans (cylinderBoundaryData_cap_one i f₀ f₁ H h₀ h₁ b)
  exact ⟨⟨⟨fun p ↦ F (p.2, p.1), by fun_prop⟩, hzero, hone⟩,
    fun t a ↦ hside a t⟩

/-- Two prescribed maps of the literal geometric simplex extend any homotopy
on its literal boundary, with equality on the whole side. This also includes
the empty boundary of the zero-dimensional simplex. -/
theorem exists_simplex_boundary_homotopy_extension
    {Z : Type u} [TopologicalSpace Z] [ContractibleSpace Z] (n : ℕ)
    (f₀ f₁ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), Z))
    (H : C(I × Convexity.StdSimplex.boundary n, Z))
    (h₀ : ∀ a, H (0, a) = f₀ a.1)
    (h₁ : ∀ a, H (1, a) = f₁ a.1) :
    ∃ K : ContinuousMap.Homotopy f₀ f₁,
      ∀ t (a : Convexity.StdSimplex.boundary n), K (t, a.1) = H (t, a) := by
  let X : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let g₀ : C(X × Convexity.StdSimplex ℝ (Fin (n + 1)), Z) :=
    ⟨fun p ↦ f₀ p.2, by fun_prop⟩
  let g₁ : C(X × Convexity.StdSimplex ℝ (Fin (n + 1)), Z) :=
    ⟨fun p ↦ f₁ p.2, by fun_prop⟩
  let G : C(I × (X × Convexity.StdSimplex.boundary n), Z) :=
    ⟨fun p ↦ H (p.1, p.2.2), by fun_prop⟩
  obtain ⟨L, hL⟩ := exists_homotopy_extension_of_hep (Z := TopCat.of Z)
    (TopCat.parameterizedSimplexBoundaryInclusion X n)
    (TopCat.homotopyExtensionProperty_simplexBoundary X n)
    g₀ g₁ G (fun a ↦ h₀ a.2) (fun a ↦ h₁ a.2)
  refine ⟨⟨⟨fun p ↦ L (p.1, (PUnit.unit, p.2)), by fun_prop⟩,
    fun a ↦ L.apply_zero (PUnit.unit, a),
    fun a ↦ L.apply_one (PUnit.unit, a)⟩, ?_⟩
  intro t a
  exact hL t (PUnit.unit, a)

end ArtinNormalisers.Deligne5
