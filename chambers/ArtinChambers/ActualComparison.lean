import ArtinChambers.RibbonLiftUniqueness
import ArtinChambers.CoverComparison
import ArtinChambers.OrbitColimit
import ArtinChambers.OrbitGroupoid

/-!
# The actual equivariant orbit/ribbon comparison

Every covering, invariance, object-surjectivity and orbit-fiber condition in
the generic descent theorem is instantiated by its proved concrete theorem.
The reduced ribbon target is its actual J-associate full component. The
upstairs space and the downstairs orbit space retain their original topology.
-/

namespace ArtinNormalisers.Chamber3

open CategoryTheory CategoryTheory.Limits Theorem18

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The actual normalizer-quotient action on the geometric interval groupoid. -/
noncomputable def actualIntervalGroupoidAction :
    StrictGroupoidAction (Artin.coxeterNormalizerQuotient M J)
      (IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) where
  functor := intervalAction M J
  map_one := intervalAction_one M J
  map_mul := intervalAction_mul M J

/-- The same quotient group acts by the actual continuous maps on path classes. -/
noncomputable def actualFundamentalGroupoidAction :
    StrictGroupoidAction (Artin.coxeterNormalizerQuotient M J)
      (FundamentalGroupoid (Complement M J)) where
  functor := actualSpaceAction M J
  map_one := actualSpaceAction_one M J
  map_mul := actualSpaceAction_mul M J

variable [Finite M.Group]

/-- All orbit-cover hypotheses are proved for the actual reduced ribbon functor. -/
theorem actualRibbonOrbitData : CoverOrbitData (actualIntervalGroupoidAction M J)
    (componentRibbonFunctor M J) where
  covering := componentRibbonFunctor_isCovering M J
  obj_surjective := componentRibbonFunctor_obj_surjective M J
  invariant := componentRibbonFunctor_invariant M J
  fiber_transitive X Y h :=
    (componentRibbonFunctor_obj_eq_iff_exists_action M J X Y).mp h

/-- All orbit-cover hypotheses are proved for the actual topological orbit functor. -/
theorem actualSpaceOrbitData : CoverOrbitData (actualFundamentalGroupoidAction M J)
    (orbitFundamentalGroupoidFunctor M J) where
  covering := isCoveringFunctor_orbitFundamentalGroupoidFunctor M J
  obj_surjective := orbitFundamentalGroupoidFunctor_obj_surjective M J
  invariant := actualSpaceAction_comp_orbit M J
  fiber_transitive X Y h := (orbitFundamentalGroupoidFunctor_obj_eq_iff M J X Y).mp h

/-- The concrete upstairs equivalence is strictly equivariant for the same
actual quotient group and the already proved actual actions. -/
theorem actualComparison_equivariant (q : Artin.coxeterNormalizerQuotient M J) :
    (actualIntervalGroupoidAction M J).functor q ⋙
        (actualIntervalComplementEquivalence M J).functor =
      (actualIntervalComplementEquivalence M J).functor ⋙
        (actualFundamentalGroupoidAction M J).functor q :=
  actualIntervalForward_equivariant M J q

/-- The actual reduced ribbon component is equivalent to the fundamental
 groupoid of the original normalizer orbit space. -/
noncomputable def actualRibbonOrbitEquivalence :
    AssociateReducedRibbonObject M J ≌ FundamentalGroupoid (OrbitSpace M J) :=
  comparisonEquivalence (actualRibbonOrbitData M J) (actualSpaceOrbitData M J)
    (actualIntervalComplementEquivalence M J) (actualComparison_equivariant M J)
    (actualIntervalForward_obj_injective M J)

/-- The actual square commutes as equality of functors, not only as an
unrelated pair of groupoid equivalences. -/
theorem actualComparison_square :
    componentRibbonFunctor M J ⋙ (actualRibbonOrbitEquivalence M J).functor =
      actualIntervalForward M J ⋙ orbitFundamentalGroupoidFunctor M J :=
  comparisonEquivalence_square (actualRibbonOrbitData M J) (actualSpaceOrbitData M J)
    (actualIntervalComplementEquivalence M J) (actualComparison_equivariant M J)
    (actualIntervalForward_obj_injective M J)

/-- The actual reduced ribbon groupoid represents the genuine action colimit;
its independent Artin definition is not replaced by a quotient definition. -/
noncomputable def actualRibbonOrbitIsColimit :
    IsColimit (actualRibbonOrbitData M J).orbitCocone :=
  (actualRibbonOrbitData M J).orbitIsColimit

/-- The actual topological orbit functor likewise represents the action colimit. -/
noncomputable def actualSpaceOrbitIsColimit :
    IsColimit (actualSpaceOrbitData M J).orbitCocone :=
  (actualSpaceOrbitData M J).orbitIsColimit

end ArtinNormalisers.Chamber3
