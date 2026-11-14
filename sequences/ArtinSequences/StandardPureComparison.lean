import ArtinSequences.StandardMonodromy
import ArtinSequences.NormalizedExactness
import ArtinSequences.KernelComparison

/-!
# The actual pure normalizer comparison at the standard point

The compatible middle equivalence identifies the actual algebraic kernel with
the actual geometric kernel. The original injective covering map realizes the
latter as its range. This constructs the pure equivalence and proves its
inclusion square, without assuming a pure fundamental-group comparison.
-/

namespace ArtinNormalisers.Sequence4

open Theorem18

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The pure normalizer image is compared to the actual total-space
fundamental group by the proved kernel and range identifications. -/
noncomputable def standardPureEquiv :
    Artin.pureNormalizerImage M J ≃*
      FundamentalGroup (Complement M J) (standardComplementPoint M J) :=
  subgroupKernelComparison (standardNormalizerEquiv M J)
    (Artin.normalizerQuotientMap M J)
    (normalizedOrbitMonodromy M J (standardComplementPoint M J))
    (standardNormalizerEquiv_monodromy M J)
    (Landmark1.orbitFundamentalGroupMap M J (standardComplementPoint M J))
    (normalizedOrbitFundamentalGroup_shortExact M J (standardComplementPoint M J)).1
    (normalizedOrbitFundamentalGroup_shortExact M J (standardComplementPoint M J)).2.1
    (Artin.pureNormalizerImage M J) (Artin.normalizerQuotientMap_kernel M J).symm

/-- The first square uses the actual subgroup inclusion and actual covering map. -/
theorem standardPureEquiv_inclusion :
    (Landmark1.orbitFundamentalGroupMap M J (standardComplementPoint M J)).comp
        (standardPureEquiv M J).toMonoidHom =
      (standardNormalizerEquiv M J).toMonoidHom.comp (Artin.pureNormalizerInclusion M J) :=
  subgroupKernelComparison_square (standardNormalizerEquiv M J)
    (Artin.normalizerQuotientMap M J)
    (normalizedOrbitMonodromy M J (standardComplementPoint M J))
    (standardNormalizerEquiv_monodromy M J)
    (Landmark1.orbitFundamentalGroupMap M J (standardComplementPoint M J))
    (normalizedOrbitFundamentalGroup_shortExact M J (standardComplementPoint M J)).1
    (normalizedOrbitFundamentalGroup_shortExact M J (standardComplementPoint M J)).2.1
    (Artin.pureNormalizerImage M J) (Artin.normalizerQuotientMap_kernel M J).symm

theorem standardPureEquiv_apply (a : Artin.pureNormalizerImage M J) :
    Landmark1.orbitFundamentalGroupMap M J (standardComplementPoint M J)
        (standardPureEquiv M J a) =
      standardNormalizerEquiv M J (Artin.pureNormalizerInclusion M J a) :=
  DFunLike.congr_fun (standardPureEquiv_inclusion M J) a

/-- The actual inclusion square uniquely specifies the first vertical map. -/
theorem standardPureEquiv_unique
    (F : Artin.pureNormalizerImage M J ≃*
      FundamentalGroup (Complement M J) (standardComplementPoint M J))
    (hF : (Landmark1.orbitFundamentalGroupMap M J (standardComplementPoint M J)).comp
        F.toMonoidHom =
      (standardNormalizerEquiv M J).toMonoidHom.comp (Artin.pureNormalizerInclusion M J)) :
    F = standardPureEquiv M J := by
  apply MulEquiv.ext
  intro a
  apply (normalizedOrbitFundamentalGroup_shortExact M J (standardComplementPoint M J)).1
  exact (DFunLike.congr_fun hF a).trans (standardPureEquiv_apply M J a).symm

end ArtinNormalisers.Sequence4
