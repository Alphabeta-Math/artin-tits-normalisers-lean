module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# The fundamental-group exact sequence of a quotient covering

This is a generic covering-space supplier. Its inputs are topological spaces
`E` and `X`, a group `G` acting on `E`, and an actual quotient covering map
`p : E → X`. A chosen point `e` of the fiber over `x` determines both
basepoints and the endpoint-monodromy map. Path connectedness of `E` is used
only for terminal surjectivity; no simple connectedness is assumed.

The terminal group is explicitly `Gᵐᵒᵖ`. Mathlib multiplies fundamental-group
elements in the endomorphism convention, so this is the endpoint label for
the given left action, without inversion of that label.

This file does not construct the Coxeter arrangement, its normalizer action,
or a comparison with Artin normalizer groups, and does not assert Theorem 1.8
or asphericity of an arrangement complement.
-/

set_option autoImplicit false

@[expose] public section

namespace ArtinNormalisers.Theorem18

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- A covering map induces an injective map on the actual homotopy classes
of based loops. This is the fundamental-group form of mathlib's injectivity
on all hom-sets of the fundamental groupoid. -/
theorem covering_fundamentalGroup_map_injective (hp : IsCoveringMap p) (e : E) :
    Function.Injective (FundamentalGroup.map ⟨p, hp.continuous⟩ e) := by
  intro a b hab
  apply CategoryTheory.End.ext
  apply hp.injective_path_homotopic_map e e
  simpa only [FundamentalGroup.map_apply_asHom] using
    congrArg CategoryTheory.End.asHom hab

/-- The same injection after transporting the target basepoint along a
specified equality. No connectedness hypothesis is needed. -/
theorem covering_fundamentalGroup_mapOfEq_injective (hp : IsCoveringMap p)
    {e : E} {x : X} (he : p e = x) :
    Function.Injective (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he) :=
  (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk he)).conj.injective.comp
    (covering_fundamentalGroup_map_injective hp e)

variable {G : Type*} [Group G] [MulAction G E]
    (hp : IsQuotientCoveringMap p G) {x : X} (e : p ⁻¹' {x})

/-- The image of the covering-induced fundamental-group map is the kernel
of endpoint monodromy to the opposite group. This needs no connectedness
assumption on the total space. -/
theorem quotientCovering_fundamentalGroup_range_eq_ker :
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range =
      (hp.fundamentalGroupToMulOpposite e : FundamentalGroup X x →* Gᵐᵒᵖ).ker := by
  rw [hp.ker_fundamentalGroupToMulOpposite e, hp.ker_monodromyPerm e]

/-- The short exact sequence of a quotient covering with path-connected
total space:
`1 → π₁(E,e) → π₁(X,x) → Gᵐᵒᵖ → 1`.
The first arrow is induced by the given covering and the second is its
actual endpoint-monodromy homomorphism. -/
theorem quotientCovering_fundamentalGroup_shortExact [PathConnectedSpace E] :
    Function.Injective (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2) ∧
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range =
        (hp.fundamentalGroupToMulOpposite e : FundamentalGroup X x →* Gᵐᵒᵖ).ker ∧
      Function.Surjective
        (hp.fundamentalGroupToMulOpposite e : FundamentalGroup X x →* Gᵐᵒᵖ) :=
  ⟨covering_fundamentalGroup_mapOfEq_injective hp.isCoveringMap e.2,
    quotientCovering_fundamentalGroup_range_eq_ker hp e,
    hp.fundamentalGroupToMulOpposite_surjective e⟩

end ArtinNormalisers.Theorem18
