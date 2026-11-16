import Mathlib
import ArtinDeligne


noncomputable def RelativeCone : (∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S), let Θ := ArtinNormalisers.Theorem18.relativeSubspace J; let V := ArtinNormalisers.Theorem18.Vector S; Set Θ × Set Θ × Set V × Set V × Set V × Set (Submodule Real Θ)) :=
(fun {S} _ M J =>
  let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
  let V := ArtinNormalisers.Theorem18.Vector S
  letI : TopologicalSpace Θ :=
    TopologicalSpace.induced
      (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
      (inferInstance : TopologicalSpace (S → Real))
  let titsCone : Set (ArtinNormalisers.Theorem18.Dual S) :=
    { f | ∃ (w : CoxeterMatrix.Group M) (g : ArtinNormalisers.Theorem18.Dual S),
        ArtinNormalisers.Landmark1.IsDominant g ∧
        ArtinNormalisers.Theorem18.dualAction M w g = f }
  let cone : Set Θ := { f | f.val ∈ titsCone }
  let relativeRoots : Set V := ArtinNormalisers.Theorem18.retainedRoots M J
  let positiveRelativeRoots : Set V := { r | r ∈ relativeRoots ∧ 0 < r }
  let negativeRelativeRoots : Set V := { r | r ∈ relativeRoots ∧ r < 0 }
  let arrangement : Set (Submodule Real Θ) :=
    Set.image (ArtinNormalisers.Theorem18.restrictedHyperplane J) positiveRelativeRoots
  (cone, interior cone, relativeRoots, positiveRelativeRoots, negativeRelativeRoots, arrangement))
