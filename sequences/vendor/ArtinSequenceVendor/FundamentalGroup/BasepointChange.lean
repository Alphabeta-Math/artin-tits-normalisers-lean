/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Two exact TauCeti basepoint-change declarations

Extracted on 2026-11-14 from TauCeti at 62bbc0596dc3539d488232e4e924a338548ea0a9.
This file changes only the module wrapper/imports and omits unrelated declarations.
Both selected declaration blocks are retained byte for byte; the complete original,
line locators, hashes and assembly recipe are preserved beside this source.
-/

public section

namespace FundamentalGroup

open CategoryTheory in
/-- Basepoint change along `γ` is represented by conjugation with `γ` in the path quotient: a loop
`g` at `x₀` goes to the class of `γ⁻¹ ⬝ g ⬝ γ`. This is the forward counterpart of
`FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply`. -/
@[simp]
lemma fundamentalGroupMulEquivOfPath_apply
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) (g : FundamentalGroup X x₀) :
    fundamentalGroupMulEquivOfPath γ g =
      .of (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ).symm
        (Path.Homotopic.Quotient.trans g.asHom (Path.Homotopic.Quotient.mk γ))) := by
  let γq : Path.Homotopic.Quotient x₀ x₁ := Path.Homotopic.Quotient.mk γ
  let α : FundamentalGroupoid.mk x₀ ≅ FundamentalGroupoid.mk x₁ :=
    (Groupoid.isoEquivHom _ _).symm γq
  -- Mathlib defines the transport as `α.conj`; the groupoid arrow and path quotient are
  -- definitionally the same type (`FundamentalGroupoid.Hom` is a path quotient).
  change α.conj g = .of (γq.symm.trans (g.asHom.trans γq))
  ext
  rw [CategoryTheory.Iso.conj_apply_asHom]
  rfl

open CategoryTheory in
/-- **Induced maps commute with basepoint change.** Changing basepoint along `γ` and then applying
`f` is applying `f` and then changing basepoint along the image path `γ.map f.continuous`. -/
lemma map_fundamentalGroupMulEquivOfPath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ x₁ : X} (f : C(X, Y)) (γ : Path x₀ x₁) (g : FundamentalGroup X x₀) :
    map f x₁ (fundamentalGroupMulEquivOfPath γ g) =
      fundamentalGroupMulEquivOfPath (γ.map f.continuous) (map f x₀ g) := by
  -- `FundamentalGroupoid.map f` sends the class of `γ` to the class of `γ.map f.continuous` by
  -- definition, so the image of the basepoint-change isomorphism is the one along the image path.
  have hα : (FundamentalGroupoid.map f).mapIso ((Groupoid.isoEquivHom _ _).symm ⟦γ⟧) =
      (Groupoid.isoEquivHom _ _).symm ⟦γ.map f.continuous⟧ := Iso.ext rfl
  ext
  refine (Functor.map_conj (FundamentalGroupoid.map f) _ g).trans ?_
  rw [hα]
  -- Mathlib defines basepoint change as `Iso.conj` and `FundamentalGroup.map` as
  -- `Functor.mapEnd`, so the two sides now agree by unfolding these definitions.
  rfl

end FundamentalGroup
