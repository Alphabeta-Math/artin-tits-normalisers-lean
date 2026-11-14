import ArtinChambers.ActualComparison
import ArtinChambers.RibbonDeckLabels

/-!
# Landmark 3: the actual equivariant geometric comparison

For a finite Coxeter group, the interval groupoid on the actual restricted
real chambers is equivalent to the fundamental groupoid of the original
relative complement. The actual reduced ribbon groupoid, restricted to the
J-associate component, is equivalent to the fundamental groupoid of the
original normalizer orbit space. The actual covering square commutes strictly,
with the same quotient-group action and the same signed Coxeter endpoint labels.

The interval presentation uses positive arrows for all ordered chamber pairs
and sign-between relations. No identification with the paper's literal
adjacent-gallery presentation is asserted. Based exact-sequence comparisons
and asphericity remain landmarks 4 and 5; this is not full Theorem 1.8.
-/

namespace ArtinNormalisers.Chamber3

open CategoryTheory CategoryTheory.Limits Theorem18

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The concrete geometric, ribbon and quotient comparisons, with their actual
covering functors and strict equivariance. All hypotheses beyond finite Coxeter
type are proved in the suppliers; no comparison assumption is supplied here. -/
theorem landmark_3 :
    (actualIntervalForward M J).IsEquivalence ∧
    IsCoveringFunctor (componentRibbonFunctor M J) ∧
    IsCoveringFunctor (orbitFundamentalGroupoidFunctor M J) ∧
    (∀ q : Artin.coxeterNormalizerQuotient M J,
      (actualIntervalGroupoidAction M J).functor q ⋙ actualIntervalForward M J =
        actualIntervalForward M J ⋙ (actualFundamentalGroupoidAction M J).functor q) ∧
    Nonempty (AssociateReducedRibbonObject M J ≌
      FundamentalGroupoid (OrbitSpace M J)) ∧
    (componentRibbonFunctor M J ⋙ (actualRibbonOrbitEquivalence M J).functor =
      actualIntervalForward M J ⋙ orbitFundamentalGroupoidFunctor M J) ∧
    Nonempty (IsColimit (actualRibbonOrbitData M J).orbitCocone) ∧
    Nonempty (IsColimit (actualSpaceOrbitData M J).orbitCocone) :=
  ⟨actualIntervalForward_isEquivalence M J,
    componentRibbonFunctor_isCovering M J,
    isCoveringFunctor_orbitFundamentalGroupoidFunctor M J,
    actualComparison_equivariant M J,
    ⟨actualRibbonOrbitEquivalence M J⟩,
    actualComparison_square M J,
    ⟨actualRibbonOrbitIsColimit M J⟩,
    ⟨actualSpaceOrbitIsColimit M J⟩⟩

end ArtinNormalisers.Chamber3
