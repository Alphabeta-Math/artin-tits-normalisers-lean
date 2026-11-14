import ArtinSequences.PositiveConventions

/-!
# Theorem 6.7: the actual isomorphism of short exact sequences

Both vertical multiplicative equivalences, both actual exact rows, and both
commuting squares are proved at every actual basepoint. The rightmost vertical
map is identity on the same Coxeter normalizer quotient. Raw monodromy and its
explicit inverse-opposite normalization have already been distinguished.

This proves landmark 4. It asserts no asphericity or K(π,1) conclusion; full
Theorem 1.8 retains the separate landmark 5 obligation.
-/

namespace ArtinNormalisers.Sequence4

open Theorem18

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- **Theorem 6.7**, in the explicitly normalized mathlib fundamental-group
convention, for the original groups, original spaces and original induced maps. -/
theorem theorem_6_7 (x : Complement M J) :
    Nonempty (Artin.pureNormalizerImage M J ≃* FundamentalGroup (Complement M J) x) ∧
    Nonempty (Artin.normalizerQuotient M J ≃*
      FundamentalGroup (OrbitSpace M J) (orbitProjection M J x)) ∧
    (Function.Injective (Artin.pureNormalizerInclusion M J) ∧
      (Artin.pureNormalizerInclusion M J).range = (Artin.normalizerQuotientMap M J).ker ∧
      Function.Surjective (Artin.normalizerQuotientMap M J)) ∧
    (Function.Injective (Landmark1.orbitFundamentalGroupMap M J x) ∧
      (Landmark1.orbitFundamentalGroupMap M J x).range = (normalizedOrbitMonodromy M J x).ker ∧
      Function.Surjective (normalizedOrbitMonodromy M J x)) ∧
    ((Landmark1.orbitFundamentalGroupMap M J x).comp
        (pureFundamentalGroupEquiv M J x).toMonoidHom =
      (normalizerFundamentalGroupEquiv M J x).toMonoidHom.comp
        (Artin.pureNormalizerInclusion M J)) ∧
    ((normalizedOrbitMonodromy M J x).comp
        (normalizerFundamentalGroupEquiv M J x).toMonoidHom =
      Artin.normalizerQuotientMap M J) :=
  ⟨⟨pureFundamentalGroupEquiv M J x⟩,
    ⟨normalizerFundamentalGroupEquiv M J x⟩,
    Artin.lemma_2_8 M J,
    normalizedOrbitFundamentalGroup_shortExact M J x,
    pureFundamentalGroupEquiv_inclusion M J x,
    normalizerFundamentalGroupEquiv_monodromy M J x⟩

/-- Landmark 4 is precisely the full actual-map statement above, at every
basepoint; no asphericity is included in its scope. -/
theorem landmark_4 (x : Complement M J) :
    Nonempty (Artin.pureNormalizerImage M J ≃* FundamentalGroup (Complement M J) x) ∧
    Nonempty (Artin.normalizerQuotient M J ≃*
      FundamentalGroup (OrbitSpace M J) (orbitProjection M J x)) ∧
    (Function.Injective (Artin.pureNormalizerInclusion M J) ∧
      (Artin.pureNormalizerInclusion M J).range = (Artin.normalizerQuotientMap M J).ker ∧
      Function.Surjective (Artin.normalizerQuotientMap M J)) ∧
    (Function.Injective (Landmark1.orbitFundamentalGroupMap M J x) ∧
      (Landmark1.orbitFundamentalGroupMap M J x).range = (normalizedOrbitMonodromy M J x).ker ∧
      Function.Surjective (normalizedOrbitMonodromy M J x)) ∧
    ((Landmark1.orbitFundamentalGroupMap M J x).comp
        (pureFundamentalGroupEquiv M J x).toMonoidHom =
      (normalizerFundamentalGroupEquiv M J x).toMonoidHom.comp
        (Artin.pureNormalizerInclusion M J)) ∧
    ((normalizedOrbitMonodromy M J x).comp
        (normalizerFundamentalGroupEquiv M J x).toMonoidHom =
      Artin.normalizerQuotientMap M J) :=
  theorem_6_7 M J x

/-- The same actual diagram in positive path-traversal order, implemented by
the opposite of mathlib's fundamental group. The positive endpoint map sends
the literal lifted path to its original quotient label. -/
theorem theorem_6_7_positive (x : Complement M J) :
    Nonempty (Artin.pureNormalizerImage M J ≃* (FundamentalGroup (Complement M J) x)ᵐᵒᵖ) ∧
    Nonempty (Artin.normalizerQuotient M J ≃*
      (FundamentalGroup (OrbitSpace M J) (orbitProjection M J x))ᵐᵒᵖ) ∧
    (Function.Injective (Artin.pureNormalizerInclusion M J) ∧
      (Artin.pureNormalizerInclusion M J).range = (Artin.normalizerQuotientMap M J).ker ∧
      Function.Surjective (Artin.normalizerQuotientMap M J)) ∧
    (Function.Injective (positiveOrbitFundamentalGroupMap M J x) ∧
      (positiveOrbitFundamentalGroupMap M J x).range = (positiveOrbitMonodromy M J x).ker ∧
      Function.Surjective (positiveOrbitMonodromy M J x)) ∧
    ((positiveOrbitFundamentalGroupMap M J x).comp (positivePureEquiv M J x).toMonoidHom =
      (positiveNormalizerEquiv M J x).toMonoidHom.comp (Artin.pureNormalizerInclusion M J)) ∧
    ((positiveOrbitMonodromy M J x).comp (positiveNormalizerEquiv M J x).toMonoidHom =
      Artin.normalizerQuotientMap M J) :=
  ⟨⟨positivePureEquiv M J x⟩, ⟨positiveNormalizerEquiv M J x⟩,
    Artin.lemma_2_8 M J, positiveOrbitFundamentalGroup_shortExact M J x,
    positivePureEquiv_inclusion M J x, positiveNormalizerEquiv_monodromy M J x⟩

end ArtinNormalisers.Sequence4
