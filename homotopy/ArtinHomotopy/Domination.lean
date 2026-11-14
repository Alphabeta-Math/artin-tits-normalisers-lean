module

public import ArtinAsphericityVendor.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic

/-!
# Domination and the actual higher homotopy groups

If genuine continuous maps `f : X → Y` and `g : Y → X` have a genuine free
homotopy from `g ∘ f` to `id`, the map induced by `f` on every finite-dimensional
cube homotopy group is injective. Higher homotopy vanishing therefore transfers
from `Y` to `X`. The homotopy need not fix the chosen basepoint.

The proof uses the accepted TauCeti theorem
`HomotopyGroup.map_comp_map_bijective_of_homotopy_id`, whose round-trip formula
already accounts for the basepoint's trace through the homotopy. No homotopy
equivalence of `X` and `Y` is assumed, and no arrangement-specific domination
or asphericity is asserted here.
-/

@[expose] public section

namespace ArtinNormalisers.Homotopy5

open scoped Topology

universe u v w

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A genuine homotopy retraction makes the actual cube-homotopy map injective.
The supplier handles the free homotopy's moving basepoint explicitly. -/
theorem homotopyGroupMap_injective_of_domination (f : C(X, Y)) (g : C(Y, X))
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (N : Type w) [Finite N] (x : X) :
    Function.Injective (HomotopyGroup.map (N := N) f (rfl : f x = f x)) :=
  (HomotopyGroup.map_comp_map_bijective_of_homotopy_id (N := N) H x).injective.of_comp

/-- Vanishing transfers along domination in every finite dimension, for the
actual generalized-loop quotient and at the actual image basepoint `f x`. -/
theorem homotopyGroup_subsingleton_of_domination (f : C(X, Y)) (g : C(Y, X))
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (N : Type w) [Finite N] (x : X)
    [Subsingleton (HomotopyGroup N Y (f x))] : Subsingleton (HomotopyGroup N X x) :=
  (homotopyGroupMap_injective_of_domination f g H N x).subsingleton

/-- The higher-dimensional specialization used by `TauCeti.IsAspherical`. -/
theorem homotopyGroupPi_subsingleton_of_domination (f : C(X, Y)) (g : C(Y, X))
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (x : X) (n : ℕ)
    [Subsingleton (π_ (n + 2) Y (f x))] : Subsingleton (π_ (n + 2) X x) :=
  homotopyGroup_subsingleton_of_domination f g H (Fin (n + 2)) x

/-- Higher-homotopy vanishing in a dominating space implies asphericity of a
path-connected dominated space. The continuous maps and homotopy are inputs,
not consequences assumed for a particular geometric model. -/
theorem isAspherical_of_domination (f : C(X, Y)) (g : C(Y, X))
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) [PathConnectedSpace X] (x : X)
    (hπ : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y (f x))) : TauCeti.IsAspherical X x := by
  refine TauCeti.IsAspherical.mk inferInstance fun n => ?_
  let : Subsingleton (π_ (n + 2) Y (f x)) := hπ n
  exact homotopyGroupPi_subsingleton_of_domination f g H x n

/-- Asphericity transfers from an actual dominating space; path-connectedness
of the dominated space is supplied separately. -/
theorem isAspherical_of_dominated_by_aspherical (f : C(X, Y)) (g : C(Y, X))
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) [PathConnectedSpace X] (x : X)
    (hY : TauCeti.IsAspherical Y (f x)) : TauCeti.IsAspherical X x :=
  isAspherical_of_domination f g H x hY.subsingleton_homotopyGroup

end ArtinNormalisers.Homotopy5
