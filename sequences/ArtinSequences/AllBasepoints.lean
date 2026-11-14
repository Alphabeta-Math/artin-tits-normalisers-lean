import ArtinSequences.StandardPureComparison
import ArtinSequences.BasepointTransport

/-!
# Compatible comparisons at every actual complement basepoint

Both vertical isomorphisms are transported along a single actual total-space
path and its actual projection. The monodromy label is preserved in the same
quotient group. Every helper hypothesis below is instantiated by the already
proved actual covering and the actual path-connected complement.
-/

namespace ArtinNormalisers.Sequence4

open Theorem18

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- A chosen actual path, with no connectivity assumption beyond the proved
finite-type instance on the original complement. -/
noncomputable def standardBasepointPath (x : Complement M J) :
    Path (standardComplementPoint M J) x :=
  PathConnectedSpace.somePath _ _

/-- The downstairs path is exactly the projection of the upstairs path. -/
noncomputable def projectedBasepointPath {x : Complement M J}
    (θ : Path (standardComplementPoint M J) x) :
    Path (orbitProjection M J (standardComplementPoint M J)) (orbitProjection M J x) :=
  θ.map (continuous_orbitProjection M J)

/-- Raw monodromy in the same opposite quotient is invariant under these
paired paths. In particular, no conjugation automorphism of the quotient occurs. -/
theorem orbitMonodromy_basepointTransport {x : Complement M J}
    (θ : Path (standardComplementPoint M J) x)
    (α : FundamentalGroup (OrbitSpace M J) (orbitProjection M J (standardComplementPoint M J))) :
    Landmark1.orbitMonodromy M J x
        (FundamentalGroup.fundamentalGroupMulEquivOfPath (projectedBasepointPath M J θ) α) =
      Landmark1.orbitMonodromy M J (standardComplementPoint M J) α :=
  rawMonodromy_basepointTransport (Landmark1.isQuotientCoveringMap_orbitProjection M J) θ α

theorem normalizedOrbitMonodromy_basepointTransport {x : Complement M J}
    (θ : Path (standardComplementPoint M J) x)
    (α : FundamentalGroup (OrbitSpace M J) (orbitProjection M J (standardComplementPoint M J))) :
    normalizedOrbitMonodromy M J x
        (FundamentalGroup.fundamentalGroupMulEquivOfPath (projectedBasepointPath M J θ) α) =
      normalizedOrbitMonodromy M J (standardComplementPoint M J) α :=
  congrArg (oppositeInverseEquiv _) (orbitMonodromy_basepointTransport M J θ α)

/-- The middle comparison transported along the actual projected path. -/
noncomputable def normalizerComparisonAlong {x : Complement M J}
    (θ : Path (standardComplementPoint M J) x) :
    Artin.normalizerQuotient M J ≃*
      FundamentalGroup (OrbitSpace M J) (orbitProjection M J x) :=
  (standardNormalizerEquiv M J).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath (projectedBasepointPath M J θ))

/-- The first comparison uses the same actual upstairs path. -/
noncomputable def pureComparisonAlong {x : Complement M J}
    (θ : Path (standardComplementPoint M J) x) :
    Artin.pureNormalizerImage M J ≃* FundamentalGroup (Complement M J) x :=
  (standardPureEquiv M J).trans (FundamentalGroup.fundamentalGroupMulEquivOfPath θ)

/-- The first square commutes for every actual choice of the paired paths. -/
theorem pureComparisonAlong_inclusion {x : Complement M J}
    (θ : Path (standardComplementPoint M J) x) :
    (Landmark1.orbitFundamentalGroupMap M J x).comp (pureComparisonAlong M J θ).toMonoidHom =
      (normalizerComparisonAlong M J θ).toMonoidHom.comp (Artin.pureNormalizerInclusion M J) := by
  apply MonoidHom.ext
  intro a
  change Landmark1.orbitFundamentalGroupMap M J x
      (FundamentalGroup.fundamentalGroupMulEquivOfPath θ (standardPureEquiv M J a)) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath (projectedBasepointPath M J θ)
      (standardNormalizerEquiv M J (Artin.pureNormalizerInclusion M J a))
  have h := coveringMapOfEq_basepointTransport
    (Landmark1.isCoveringMap_orbitProjection M J) θ (standardPureEquiv M J a)
  change Landmark1.orbitFundamentalGroupMap M J x
      (FundamentalGroup.fundamentalGroupMulEquivOfPath θ (standardPureEquiv M J a)) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath (projectedBasepointPath M J θ)
      (Landmark1.orbitFundamentalGroupMap M J (standardComplementPoint M J)
        (standardPureEquiv M J a)) at h
  exact h.trans (congrArg
    (FundamentalGroup.fundamentalGroupMulEquivOfPath (projectedBasepointPath M J θ))
    (standardPureEquiv_apply M J a))

/-- The right square has identity on the same actual Coxeter quotient, for
every choice of an upstairs path and its actual projected path. -/
theorem normalizerComparisonAlong_monodromy {x : Complement M J}
    (θ : Path (standardComplementPoint M J) x) :
    (normalizedOrbitMonodromy M J x).comp (normalizerComparisonAlong M J θ).toMonoidHom =
      Artin.normalizerQuotientMap M J := by
  apply MonoidHom.ext
  intro a
  change normalizedOrbitMonodromy M J x
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (projectedBasepointPath M J θ)
        (standardNormalizerEquiv M J a)) = Artin.normalizerQuotientMap M J a
  rw [normalizedOrbitMonodromy_basepointTransport]
  exact DFunLike.congr_fun (standardNormalizerEquiv_monodromy M J) a

/-- The actual first fundamental-group isomorphism at any actual basepoint. -/
noncomputable def pureFundamentalGroupEquiv (x : Complement M J) :
    Artin.pureNormalizerImage M J ≃* FundamentalGroup (Complement M J) x :=
  pureComparisonAlong M J (standardBasepointPath M J x)

/-- The actual middle fundamental-group isomorphism at any actual basepoint. -/
noncomputable def normalizerFundamentalGroupEquiv (x : Complement M J) :
    Artin.normalizerQuotient M J ≃*
      FundamentalGroup (OrbitSpace M J) (orbitProjection M J x) :=
  normalizerComparisonAlong M J (standardBasepointPath M J x)

theorem pureFundamentalGroupEquiv_inclusion (x : Complement M J) :
    (Landmark1.orbitFundamentalGroupMap M J x).comp (pureFundamentalGroupEquiv M J x).toMonoidHom =
      (normalizerFundamentalGroupEquiv M J x).toMonoidHom.comp
        (Artin.pureNormalizerInclusion M J) :=
  pureComparisonAlong_inclusion M J (standardBasepointPath M J x)

theorem normalizerFundamentalGroupEquiv_monodromy (x : Complement M J) :
    (normalizedOrbitMonodromy M J x).comp (normalizerFundamentalGroupEquiv M J x).toMonoidHom =
      Artin.normalizerQuotientMap M J :=
  normalizerComparisonAlong_monodromy M J (standardBasepointPath M J x)

/-- The raw, unnormalized endpoint formula displays the inverse label
required by mathlib's fundamental-group multiplication convention. -/
theorem normalizerFundamentalGroupEquiv_rawMonodromy (x : Complement M J)
    (a : Artin.normalizerQuotient M J) :
    Landmark1.orbitMonodromy M J x (normalizerFundamentalGroupEquiv M J x a) =
      MulOpposite.op ((Artin.normalizerQuotientMap M J a)⁻¹) := by
  apply MulOpposite.unop_injective
  have h := DFunLike.congr_fun (normalizerFundamentalGroupEquiv_monodromy M J x) a
  change (Landmark1.orbitMonodromy M J x (normalizerFundamentalGroupEquiv M J x a)).unop⁻¹ =
    Artin.normalizerQuotientMap M J a at h
  simpa only [inv_inv, MulOpposite.unop_op] using congrArg Inv.inv h

end ArtinNormalisers.Sequence4
