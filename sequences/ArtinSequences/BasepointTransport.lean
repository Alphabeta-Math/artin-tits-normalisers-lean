module

public import ArtinSequenceVendor.FundamentalGroup.BasepointChange
public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Basepoint transport in the actual quotient-cover exact sequence

The path downstairs is always the projection of the chosen path upstairs.
The covering-induced fundamental-group square commutes by the selected
TauCeti naturality proof. Raw endpoint monodromy in the same opposite group
is unchanged because lifting the projected path carries the chosen fiber
point to the endpoint of the original path, equivariantly for the given
group action. No independent base path or conjugation in the acting group
is introduced.
-/

@[expose] public section

namespace ArtinNormalisers.Sequence4

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} {e₀ e₁ : E}

/-- The actual covering-induced maps commute with transport along a total-space
path and its projected path. -/
theorem coveringMap_basepointTransport (hp : IsCoveringMap p) (θ : Path e₀ e₁)
    (α : FundamentalGroup E e₀) :
    FundamentalGroup.map ⟨p, hp.continuous⟩ e₁
        (FundamentalGroup.fundamentalGroupMulEquivOfPath θ α) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (θ.map hp.continuous)
        (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀ α) :=
  FundamentalGroup.map_fundamentalGroupMulEquivOfPath ⟨p, hp.continuous⟩ θ α

/-- The same actual square with the equality-based spelling of the maps. -/
theorem coveringMapOfEq_basepointTransport (hp : IsCoveringMap p) (θ : Path e₀ e₁)
    (α : FundamentalGroup E e₀) :
    FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ rfl
        (FundamentalGroup.fundamentalGroupMulEquivOfPath θ α) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (θ.map hp.continuous)
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ rfl α) := by
  simpa only [FundamentalGroup.mapOfEq_rfl] using coveringMap_basepointTransport hp θ α

/-- The covering-map naturality square as equality of actual homomorphisms. -/
theorem coveringMap_basepointTransport_comp (hp : IsCoveringMap p) (θ : Path e₀ e₁) :
    (FundamentalGroup.map ⟨p, hp.continuous⟩ e₁).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath θ).toMonoidHom =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (θ.map hp.continuous)).toMonoidHom.comp
        (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀) := by
  apply MonoidHom.ext
  intro α
  exact coveringMap_basepointTransport hp θ α

variable {Q : Type*} [Group Q] [MulAction Q E]

/-- Raw endpoint labels in the same `Qᵐᵒᵖ` are preserved by transport along
an actual total-space path and precisely its projected base path. -/
theorem rawMonodromy_basepointTransport (hp : IsQuotientCoveringMap p Q)
    (θ : Path e₀ e₁) (α : FundamentalGroup X (p e₀)) :
    hp.fundamentalGroupToMulOpposite ⟨e₁, rfl⟩
        (FundamentalGroup.fundamentalGroupMulEquivOfPath (θ.map hp.continuous) α) =
      hp.fundamentalGroupToMulOpposite ⟨e₀, rfl⟩ α := by
  let σ : Path.Homotopic.Quotient (p e₀) (p e₁) := .mk (θ.map hp.continuous)
  let g : Q := (hp.fundamentalGroupToMulOpposite ⟨e₀, rfl⟩ α).unop
  have hσ : hp.isCoveringMap.monodromy σ ⟨e₀, rfl⟩ = ⟨e₁, rfl⟩ :=
    hp.isCoveringMap.monodromy_map (.mk θ)
  have hσinv : hp.isCoveringMap.monodromy σ.symm ⟨e₁, rfl⟩ = ⟨e₀, rfl⟩ :=
    hp.isCoveringMap.monodromy_map (.mk θ.symm)
  have hloop : hp.isCoveringMap.monodromy α.asHom ⟨e₀, rfl⟩ =
      hp.toPermFiber (p e₀) g ⟨e₀, rfl⟩ := by
    apply Subtype.ext
    rw [hp.toPermFiber_apply_apply_coe]
    exact (hp.unop_fundamentalGroupToMulOpposite_smul (e := ⟨e₀, rfl⟩) (γ := α)).symm
  apply hp.fundamentalGroupToMulOpposite_apply_eq_iff.mpr
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_apply]
  change g • e₁ =
    (hp.isCoveringMap.monodromy (σ.symm.trans (α.asHom.trans σ)) ⟨e₁, rfl⟩).val
  rw [hp.isCoveringMap.monodromy_trans_apply, hσinv,
    hp.isCoveringMap.monodromy_trans_apply, hloop, hp.monodromy_toPermFiber, hσ,
    hp.toPermFiber_apply_apply_coe]

/-- Equality of the actual homomorphisms, rather than only their values. -/
theorem rawMonodromy_basepointTransport_comp (hp : IsQuotientCoveringMap p Q)
    (θ : Path e₀ e₁) :
    (hp.fundamentalGroupToMulOpposite ⟨e₁, rfl⟩).comp
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (θ.map hp.continuous)).toMonoidHom =
      hp.fundamentalGroupToMulOpposite ⟨e₀, rfl⟩ := by
  ext α
  exact rawMonodromy_basepointTransport hp θ α

end ArtinNormalisers.Sequence4
