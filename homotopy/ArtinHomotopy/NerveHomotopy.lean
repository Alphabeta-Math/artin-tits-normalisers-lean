module

public import ArtinHomotopy.Domination
public import ArtinHomotopy.NerveComparison
public import ArtinNormalisers.Theorem18.ArrangementTopology

/-!
# Actual higher-homotopy injection into the constructed cover nerve

The maps and homotopy are the actual constructions on the original
complement. This proves an injection in every finite dimension, not an
equivalence or vanishing of the target groups. The final conditional reduction
records precisely the higher-topological obligation still to be discharged.
-/

@[expose] public section

namespace ArtinNormalisers.Homotopy5

open Theorem18
open SSet CategoryTheory
open scoped Topology Topology.Homotopy Simplicial

universe v

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The actual classifier induces an injection on genuine cube homotopy groups.
The explicit return homotopy handles the moving basepoint. -/
theorem actualNerveForward_homotopyGroupMap_injective (N : Type v) [Finite N]
    (x : Complement M J) :
    Function.Injective (HomotopyGroup.map (N := N) (actualNerveForward M J)
      (rfl : actualNerveForward M J x = actualNerveForward M J x)) :=
  homotopyGroupMap_injective_of_domination (actualNerveForward M J)
    (actualNerveReturn M J) (actualNerveDominationHomotopy M J) N x

/-- A conditional reduction through this particular constructed nerve. No
vanishing premise in this theorem has yet been proved for that nerve. -/
theorem complement_isAspherical_of_actualNerve_higher_vanishing
    (x : Complement M J)
    (hπ : ∀ n : ℕ,
      Subsingleton (π_ (n + 2) |actualMetricNerve M J| (actualNerveForward M J x))) :
    TauCeti.IsAspherical (Complement M J) x :=
  isAspherical_of_domination (actualNerveForward M J) (actualNerveReturn M J)
    (actualNerveDominationHomotopy M J) x hπ

end ArtinNormalisers.Homotopy5
