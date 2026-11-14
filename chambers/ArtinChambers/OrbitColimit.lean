module

public import ArtinChambers.CoverQuotient
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.SingleObj

/-!
# Genuine orbit colimits of covering groupoids

The action diagram and its cocone are defined from the actual functors.
The colimit property follows from the proved covering descent theorem;
it is not an input field or a definition of the target groupoid.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open CategoryTheory CategoryTheory.Limits

universe u

variable {Q C D : Type u} [Group Q] [Groupoid.{u} C] [Groupoid.{u} D]

/-- The genuine diagram of a strict action, including every group element. -/
def StrictGroupoidAction.diagram (A : StrictGroupoidAction Q C) : SingleObj Q ⥤ Grpd.{u, u} where
  obj _ := Grpd.of C
  map q := A.functor q
  map_id _ := A.map_one
  map_comp q r := A.map_mul r q

namespace CoverOrbitData

variable {A : StrictGroupoidAction Q C} {F : C ⥤ D} (S : CoverOrbitData A F)

/-- The actual invariant functor is a cocone on the full action diagram. -/
def orbitCocone : Cocone A.diagram where
  pt := Grpd.of D
  ι :=
    { app _ := F
      naturality _ _ q := by
        change A.functor q ⋙ F = F ⋙ 𝟭 D
        simpa only [Functor.comp_id] using S.invariant q }

theorem orbitCocone_invariant (c : Cocone A.diagram) (q : Q) :
    A.functor q ⋙ c.ι.app (SingleObj.star Q) = c.ι.app (SingleObj.star Q) := by
  have h := c.w (j := SingleObj.star Q) (j' := SingleObj.star Q) q
  change A.functor q ⋙ c.ι.app (SingleObj.star Q) = c.ι.app (SingleObj.star Q) at h
  exact h

/-- The actual target groupoid is the orbit colimit, because actual unique
outgoing lifts and orbit fibers give strict existence and uniqueness of descent. -/
noncomputable def orbitIsColimit : IsColimit S.orbitCocone where
  desc c := Classical.choose (coveringFunctor_descent_existsUnique A F S.covering
    S.obj_surjective S.invariant S.fiber_transitive
    (c.ι.app (SingleObj.star Q)) (orbitCocone_invariant c))
  fac c j := by
    cases j
    exact (Classical.choose_spec (coveringFunctor_descent_existsUnique A F S.covering
      S.obj_surjective S.invariant S.fiber_transitive
      (c.ι.app (SingleObj.star Q)) (orbitCocone_invariant c))).1
  uniq c m hm := by
    apply (Classical.choose_spec (coveringFunctor_descent_existsUnique A F S.covering
      S.obj_surjective S.invariant S.fiber_transitive
      (c.ι.app (SingleObj.star Q)) (orbitCocone_invariant c))).2 m
    exact hm (SingleObj.star Q)

end CoverOrbitData

end ArtinNormalisers.Chamber3
