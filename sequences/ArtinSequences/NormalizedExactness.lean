import ArtinSequences.EndpointMonodromy
import ArtinNormalisers.Artin.ExactSequence

/-!
# The actual geometric exact row in the explicit source convention

Postcomposing raw endpoint monodromy with the inverse-opposite equivalence
preserves its kernel and surjectivity. The first arrow remains the original
continuous orbit projection on fundamental groups.
-/

namespace ArtinNormalisers.Sequence4

open Theorem18

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The exact row uses the original actual covering map and the explicit
normalized endpoint homomorphism to the same Coxeter normalizer quotient. -/
theorem normalizedOrbitFundamentalGroup_shortExact (x : Complement M J) :
    Function.Injective (Landmark1.orbitFundamentalGroupMap M J x) ∧
      (Landmark1.orbitFundamentalGroupMap M J x).range =
        (normalizedOrbitMonodromy M J x).ker ∧
      Function.Surjective (normalizedOrbitMonodromy M J x) := by
  obtain ⟨hinj, hrange, hsurj⟩ := Landmark1.orbitFundamentalGroup_shortExact M J x
  refine ⟨hinj, hrange.trans (normalizedOrbitMonodromy_ker M J x).symm, ?_⟩
  intro q
  obtain ⟨α, hα⟩ := hsurj ((oppositeInverseEquiv _).symm q)
  refine ⟨α, ?_⟩
  change oppositeInverseEquiv _ (Landmark1.orbitMonodromy M J x α) = q
  rw [hα, MulEquiv.apply_symm_apply]

end ArtinNormalisers.Sequence4
