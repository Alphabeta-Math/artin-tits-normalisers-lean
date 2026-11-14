module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import ArtinAsphericityVendor.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Compactness.Compact

/-!
# Higher homotopy of directed unions of contractible open subspaces

These are criteria for genuine homotopy groups, defined by generalized loops
on finite-dimensional cubes modulo homotopy relative to the boundary. Compact
cube images together with the basepoint lie in one member of a directed open
cover. A loop therefore factors through that actual contractible subspace.

No geometric filtration of an arrangement complement or its universal cover is
constructed here. Applying this criterion requires proving such cover data.
-/

@[expose] public section

namespace ArtinNormalisers.Asphericity5

open scoped unitInterval Topology Topology.Homotopy

universe u v w

variable {X : Type u} [TopologicalSpace X]

/-- The native interface to TauCeti's proved contractible-space theorem,
`HomotopyGroup.subsingleton_of_contractibleSpace`, in every finite dimension.
Its original proof uses actual homotopy equivalence and basepoint transport. -/
theorem homotopyGroup_subsingleton_of_contractible (N : Type v) [Finite N]
    [ContractibleSpace X] (x : X) : Subsingleton (HomotopyGroup N X x) :=
  HomotopyGroup.subsingleton_of_contractibleSpace

variable {ι : Type w} (U : ι → Set X)
  (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
  (hdir : Directed (· ⊆ ·) U) (hcontract : ∀ i, ContractibleSpace (U i))

include U hopen hcover hdir hcontract

/-- Every actual generalized loop is homotopic relative to its boundary to
the constant loop: its compact image and basepoint lie in one cover member. -/
theorem genLoop_class_eq_const_of_directed_open_contractible_cover
    (N : Type v) [Finite N] (x : X) (f : GenLoop N X x) :
    (⟦f⟧ : HomotopyGroup N X x) = ⟦GenLoop.const⟧ := by
  classical
  let : Fintype N := Fintype.ofFinite N
  have hxcover : x ∈ ⋃ i, U i := by rw [hcover]; trivial
  obtain ⟨i₀, _⟩ := Set.mem_iUnion.mp hxcover
  let : Nonempty ι := ⟨i₀⟩
  have hk : IsCompact ({x} ∪ Set.range f) :=
    isCompact_singleton.union (isCompact_range f.val.continuous)
  obtain ⟨i, hi⟩ := hk.elim_directed_cover U hopen
    (by rw [hcover]; exact Set.subset_univ _) hdir
  have hx : x ∈ U i := hi (Or.inl (Set.mem_singleton x))
  have hf (z : I^N) : f z ∈ U i := hi (Or.inr ⟨z, rfl⟩)
  let xi : U i := ⟨x, hx⟩
  let fi : GenLoop N (U i) xi :=
    ⟨⟨fun z => ⟨f z, hf z⟩, f.val.continuous.subtype_mk _⟩,
      fun z hz => Subtype.ext (GenLoop.boundary f z hz)⟩
  let : ContractibleSpace (U i) := hcontract i
  have hzero : (⟦fi⟧ : HomotopyGroup N (U i) xi) = ⟦GenLoop.const⟧ :=
    (homotopyGroup_subsingleton_of_contractible N xi).elim _ _
  let inclusion : C(U i, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hfi : GenLoop.map inclusion rfl fi = f := by
    apply GenLoop.ext
    intro z
    rw [GenLoop.map_apply]
    change (fi z).val = f z
    exact congrArg Subtype.val (@GenLoop.mk_apply N (U i) _ xi _ _ z)
  have hm := congrArg (HomotopyGroup.map (N := N) inclusion rfl) hzero
  rw [HomotopyGroup.map_mk, HomotopyGroup.map_mk, hfi, GenLoop.map_const] at hm
  exact hm

/-- A directed open cover by actual contractible subspaces kills every
finite-dimensional homotopy group, including dimensions zero and one. -/
theorem homotopyGroup_subsingleton_of_directed_open_contractible_cover
    (N : Type v) [Finite N] (x : X) : Subsingleton (HomotopyGroup N X x) := by
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂ a b fun f g => ?_
  exact (genLoop_class_eq_const_of_directed_open_contractible_cover
    U hopen hcover hdir hcontract N x f).trans
      (genLoop_class_eq_const_of_directed_open_contractible_cover
        U hopen hcover hdir hcontract N x g).symm

/-- The higher-dimensional form used by the actual asphericity predicate. -/
theorem homotopyGroupPi_subsingleton_of_directed_open_contractible_cover
    (x : X) (n : ℕ) : Subsingleton (π_ (n + 2) X x) :=
  homotopyGroup_subsingleton_of_directed_open_contractible_cover
    U hopen hcover hdir hcontract (Fin (n + 2)) x

/-- Conditional recognition of asphericity from genuine geometric cover data.
This does not assert that any particular arrangement has such a filtration. -/
theorem isAspherical_of_directed_open_contractible_cover [PathConnectedSpace X]
    (x : X) : TauCeti.IsAspherical X x :=
  TauCeti.IsAspherical.mk inferInstance
    (homotopyGroupPi_subsingleton_of_directed_open_contractible_cover
      U hopen hcover hdir hcontract x)

end ArtinNormalisers.Asphericity5
