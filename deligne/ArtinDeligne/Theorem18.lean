import ArtinDeligne.UniversalCoverComparison
import ArtinSequences.Landmark4
import ArtinAsphericity.UniversalCoverGeometry

/-!
# Full Theorem 1.8 for the original actual spaces and normalizer groups

Source: arXiv:2509.21915v3, Theorem 1.8 (PDF p.3), Theorem 6.7 and
Remark 6.12 (pp.26–27), and Corollary 6.14 with its proof (p.27).
The unconditional actual universal-cover theorem supplies higher asphericity;
actual surjective covering projections transfer it to the original complement
and its original normalizer orbit space. The group witnesses are exactly the
inverses of the frozen M4 comparisons, in their original orientations.

Both complete short exact diagrams, their same actual Coxeter quotient,
normalized/raw conventions and the positive ribbon path formula are retained.
The Artin groups are the existing standard-presentation groups; no new group
is defined as a fundamental group. The literal TauCeti K(G,1) predicate is
asserted, with no added CW-model or universal-bundle classification claim.
All indices, subsets and basepoints are arbitrary; only the actual Coxeter
group is assumed finite, including rank zero and full/empty subsets.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open Theorem18 Asphericity5 Sequence4 Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- Literal normalized M4 diagram, including both actual exact rows and both
commuting squares with identity on the same actual Coxeter quotient. -/
def normalizedNormalizerDiagram (x : Complement M J) : Prop :=
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
      Artin.normalizerQuotientMap M J)

/-- Literal positive-traversal M4 diagram on opposite fundamental groups,
retaining exactly the same actual quotient and original induced maps. -/
def positiveNormalizerDiagram (x : Complement M J) : Prop :=
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
      Artin.normalizerQuotientMap M J)

/-- Both actual diagrams, the raw inverse endpoint convention, and the
original positive labelled path formula from Remark 6.12. -/
def actualNormalizerDiagrams (x : Complement M J) : Prop :=
  normalizedNormalizerDiagram M J x ∧ positiveNormalizerDiagram M J x ∧
    (∀ a : Artin.normalizerQuotient M J,
      Landmark1.orbitMonodromy M J x (normalizerFundamentalGroupEquiv M J x a) =
        MulOpposite.op ((Artin.normalizerQuotientMap M J a)⁻¹)) ∧
    (∀ r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M),
      (positiveNormalizerEquiv M J x (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩ r)).unop =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          (projectedBasepointPath M J (standardBasepointPath M J x))
          (standardRibbonVertexEquiv M J (componentEndOfLoop M J r)))

/-- The full geometric/algebraic compatibility package is the frozen M4
result, with none of its maps, exactness clauses or conventions discarded. -/
theorem actualNormalizerDiagrams_proved (x : Complement M J) :
    actualNormalizerDiagrams M J x :=
  ⟨Sequence4.theorem_6_7 M J x, Sequence4.theorem_6_7_positive M J x,
    normalizerFundamentalGroupEquiv_rawMonodromy M J x,
    positiveNormalizerEquiv_label M J x⟩

/-- Actual complement asphericity at every point, transferred through its
proved surjective genuine universal-cover endpoint projection. -/
theorem actualComplement_isAspherical (x : Complement M J) :
    TauCeti.IsAspherical (Complement M J) x := by
  obtain ⟨q, hq⟩ := complementUniversalCoverProjection_surjective M J x
  exact (isCoveringMap_complementUniversalCoverProjection M J).isAspherical
    (complementUniversalCoverProjection_surjective M J) hq
    (actualUniversalCover_isAspherical M J q)

/-- Actual orbit-space asphericity at every orbit point, using the original
normalizer quotient covering and its proved surjectivity. -/
theorem actualOrbit_isAspherical (y : OrbitSpace M J) :
    TauCeti.IsAspherical (OrbitSpace M J) y := by
  let cover := Landmark1.isQuotientCoveringMap_orbitProjection M J
  obtain ⟨x, rfl⟩ := cover.surjective y
  exact cover.isCoveringMap.isAspherical cover.surjective rfl
    (actualComplement_isAspherical M J x)

/-- The original complement is K(P,1) for the actual pure normalizer image.
The exhibited group witness is precisely the inverse frozen M4 equivalence. -/
theorem actualComplement_isKpi1 (x : Complement M J) :
    TauCeti.IsEilenbergMacLaneSpaceOne (Artin.pureNormalizerImage M J)
      (Complement M J) x :=
  ⟨actualComplement_isAspherical M J x, ⟨(pureFundamentalGroupEquiv M J x).symm⟩⟩

/-- The quotient at an actual projected basepoint is K(N,1), with exactly
the inverse M4 normalizer comparison as fundamental-group witness. -/
theorem actualOrbit_isKpi1_at_projection (x : Complement M J) :
    TauCeti.IsEilenbergMacLaneSpaceOne (Artin.normalizerQuotient M J)
      (OrbitSpace M J) (orbitProjection M J x) :=
  ⟨actualOrbit_isAspherical M J (orbitProjection M J x),
    ⟨(normalizerFundamentalGroupEquiv M J x).symm⟩⟩

/-- Corollary 6.14 at every actual orbit basepoint, using an actual preimage;
there is no new fiber-nonemptiness or simple-connectedness hypothesis. -/
theorem corollary_6_14 (y : OrbitSpace M J) :
    TauCeti.IsEilenbergMacLaneSpaceOne (Artin.normalizerQuotient M J)
      (OrbitSpace M J) y := by
  obtain ⟨x, rfl⟩ := (Landmark1.isQuotientCoveringMap_orbitProjection M J).surjective y
  exact actualOrbit_isKpi1_at_projection M J x

/-- **Theorem 1.8**: both full actual-map exact-sequence diagrams, including
raw/normalized and positive traversal conventions, and both original-space
K(G,1) conclusions at every actual complement basepoint. -/
theorem theorem_1_8 (x : Complement M J) :
    actualNormalizerDiagrams M J x ∧
      TauCeti.IsEilenbergMacLaneSpaceOne (Artin.pureNormalizerImage M J)
        (Complement M J) x ∧
      TauCeti.IsEilenbergMacLaneSpaceOne (Artin.normalizerQuotient M J)
        (OrbitSpace M J) (orbitProjection M J x) :=
  ⟨actualNormalizerDiagrams_proved M J x,
    actualComplement_isKpi1 M J x, actualOrbit_isKpi1_at_projection M J x⟩

/-- The full bundle also exposes the quotient conclusion at all orbit points,
not merely at a separately selected standard point. -/
theorem theorem_1_8_all_basepoints :
    (∀ x : Complement M J, actualNormalizerDiagrams M J x ∧
      TauCeti.IsEilenbergMacLaneSpaceOne (Artin.pureNormalizerImage M J)
        (Complement M J) x ∧
      TauCeti.IsEilenbergMacLaneSpaceOne (Artin.normalizerQuotient M J)
        (OrbitSpace M J) (orbitProjection M J x)) ∧
    (∀ y : OrbitSpace M J, TauCeti.IsEilenbergMacLaneSpaceOne
      (Artin.normalizerQuotient M J) (OrbitSpace M J) y) :=
  ⟨theorem_1_8 M J, corollary_6_14 M J⟩

end ArtinNormalisers.Deligne5
