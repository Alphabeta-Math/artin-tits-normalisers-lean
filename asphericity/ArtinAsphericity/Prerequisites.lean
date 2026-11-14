import ArtinAsphericity.FiniteArrangement
import ArtinAsphericity.DirectedCover
import ArtinAsphericity.UniversalCoverGeometry

/-!
# Actual geometric and local-topological prerequisites for asphericity

This packages an actual simply connected covering and an actual finite good
cover. The independent finite/central/basis-simplicial statement is
`actual_arrangement_simplicial_hypotheses` in `FiniteArrangement`.

These results do not give a contraction of the universal cover, a nerve
homotopy comparison, or vanishing of its higher homotopy groups. Neither
landmark 5 nor full Theorem 1.8 is asserted here.
-/

namespace ArtinNormalisers.Asphericity5

open Theorem18 Chamber3

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The actual cover and finite convex-cover data, with every hypothesis
proved for the original spaces. Intersections are required to be nonempty
and to involve a nonempty family; the empty-family case would be the whole
complement and is not declared contractible. -/
theorem actual_universal_cover_and_good_cover :
    IsCoveringMap (complementUniversalCoverProjection M J) ∧
      Function.Surjective (complementUniversalCoverProjection M J) ∧
      PathConnectedSpace (ComplementUniversalCover M J) ∧
      SimplyConnectedSpace (ComplementUniversalCover M J) ∧
      Finite (RelativeRoot M J → Fin 4) ∧
      (∀ σ : RelativeRoot M J → Fin 4, IsOpen (actualConvexCoverSet M J σ)) ∧
      ((⋃ σ : RelativeRoot M J → Fin 4, actualConvexCoverSet M J σ) = Set.univ) ∧
      (∀ s : Finset (RelativeRoot M J → Fin 4), s.Nonempty →
        (⋂ σ ∈ s, actualConvexCoverSet M J σ).Nonempty →
        ContractibleSpace (⋂ σ ∈ s, actualConvexCoverSet M J σ)) :=
  ⟨isCoveringMap_complementUniversalCoverProjection M J,
    complementUniversalCoverProjection_surjective M J,
    inferInstance, inferInstance,
    finite_actualConvexCoverIndex M J,
    isOpen_actualConvexCoverSet M J,
    iUnion_actualConvexCoverSet M J,
    fun s hs hne => contractibleSpace_finset_actualConvexCoverSet M J s hs hne⟩

end ArtinNormalisers.Asphericity5
