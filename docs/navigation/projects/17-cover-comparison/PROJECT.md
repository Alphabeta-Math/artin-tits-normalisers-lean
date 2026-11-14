# Comparison with the actual universal cover

Actual forward/return maps have a constructed return-forward homotopy to identity.

Kind: **Prerequisite**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

No standalone article or Alphabeta statement is assigned to this local formalization result. It supports [Theorem 1.8, p. 3](https://arxiv.org/pdf/2509.21915v3#page=3) and the finite-arrangement argument in the [proof of Corollary 6.14, p. 27](https://arxiv.org/pdf/2509.21915v3#page=27). These are related target passages, not asserted original counterparts.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Deligne5.actualGarsideForward` | [`deligne/ArtinDeligne/UniversalCoverComparison.lean:27`](../../../../deligne/ArtinDeligne/UniversalCoverComparison.lean#L27) | [`deligne/ArtinDeligne/UniversalCoverComparison.lean:27–30`](../../../../deligne/ArtinDeligne/UniversalCoverComparison.lean#L27) |
| `ArtinNormalisers.Deligne5.actualGarsideReturn` | [`deligne/ArtinDeligne/GarsideTubeCarriers.lean:282`](../../../../deligne/ArtinDeligne/GarsideTubeCarriers.lean#L282) | [`deligne/ArtinDeligne/GarsideTubeCarriers.lean:282–288`](../../../../deligne/ArtinDeligne/GarsideTubeCarriers.lean#L282) |
| `ArtinNormalisers.Deligne5.actualUniversalCoverComparisonHomotopy` | [`deligne/ArtinDeligne/UniversalCoverComparison.lean:32`](../../../../deligne/ArtinDeligne/UniversalCoverComparison.lean#L32) | [`deligne/ArtinDeligne/UniversalCoverComparison.lean:32–50`](../../../../deligne/ArtinDeligne/UniversalCoverComparison.lean#L32) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Deligne5.actualGarsideForward</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] →
      (J : Set.{u_1} I) →
        ContinuousMap.{u_1, u_1} (ArtinNormalisers.Asphericity5.ComplementUniversalCover.{u_1} M J)
          (ArtinNormalisers.Deligne5.GarsideWeights.{u_1} M
            (ArtinNormalisers.Ribbon2.RibbonObject.mk.{u_1} J))
```

Source definition/construction:

```lean
/-- The continuous forward map on the original universal cover. -/
def actualGarsideForward :
    C(ComplementUniversalCover M J, GarsideWeights M (⟨J⟩ : RibbonObject M)) :=
  (canonicalGarsideMap M J).comp (universalCoverWeightsClassifier M J)
```

</details>

<details><summary>ArtinNormalisers.Deligne5.actualGarsideReturn</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] →
      (J : Set.{u_1} I) →
        ContinuousMap.{u_1, u_1}
          (ArtinNormalisers.Deligne5.GarsideWeights.{u_1} M
            (ArtinNormalisers.Ribbon2.RibbonObject.mk.{u_1} J))
          (ArtinNormalisers.Asphericity5.ComplementUniversalCover.{u_1} M J)
```

Source definition/construction:

```lean
/-- The actual continuous Garside return into the original universal cover. -/
def actualGarsideReturn :
    C(GarsideWeights M (⟨J⟩ : RibbonObject M), ComplementUniversalCover M J) :=
  (garsideTubeReturnFamily M J).descend
    (garsideSupportPredicate M (⟨J⟩ : RibbonObject M))
    (garsideSupportPredicate_hereditary M (⟨J⟩ : RibbonObject M))
    (fun _ hc hs => ⟨hc, hs⟩)
```

</details>

<details><summary>ArtinNormalisers.Deligne5.actualUniversalCoverComparisonHomotopy</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] →
      (J : Set.{u_1} I) →
        ContinuousMap.Homotopy.{u_1, u_1}
          (ContinuousMap.comp.{u_1, u_1, u_1}
            (ArtinNormalisers.Deligne5.actualGarsideReturn.{u_1} M J)
            (ArtinNormalisers.Deligne5.actualGarsideForward.{u_1} M J))
          (ContinuousMap.id.{u_1}
            (ArtinNormalisers.Asphericity5.ComplementUniversalCover.{u_1} M J))
```

Source definition/construction:

```lean
/-- The actual return and forward composite is homotopic to the identity.
The finite carrier homotopies are constructed, rather than assumed. -/
def actualUniversalCoverComparisonHomotopy :
    ((actualGarsideReturn M J).comp (actualGarsideForward M J)).Homotopy
      (ContinuousMap.id (ComplementUniversalCover M J)) := by
  exact numerableCarrierHomotopy (liftedCanonicalSet M J)
    (isOpen_liftedCanonicalSet M J) (actualLiftedCanonicalPartition M J)
    (actualLiftedCanonicalPartition_subordinate M J)
    (canonicalPacketCarrier M J)
    (fun F hF hface => contractibleSpace_canonicalPacketCarrier M J F hF
      (by obtain ⟨q, hq⟩ := hface
          exact ⟨q, (mem_canonicalPacketOverlapSet_iff M J F q).mpr hq⟩))
    (fun {_ _} hFG hF hface =>
      canonicalPacketCarrier_mono M J hFG hF (hF.mono hFG)
        (by obtain ⟨q, hq⟩ := hface
            exact ⟨q, (mem_canonicalPacketOverlapSet_iff M J _ q).mpr hq⟩))
    (fun F hF _ q hq => mem_canonicalPacketCarrier_of_common M J F hF q hq)
    ((actualGarsideReturn M J).comp (canonicalGarsideMap M J))
    (fun F hF hface w hw => canonicalGarsideMap_return_carried M J w F hF hface hw)
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [Ribbon lcms, gcds and simple prefixes](../11-ribbon-lattice/PROJECT.md)
- [Canonical packet carriers](../15-packet-carriers/PROJECT.md)
- [The coherent carrier homotopy](../16-carrier-homotopy/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`deligne/ArtinDeligne/GarsideTubeCarriers.lean`](../../../../deligne/ArtinDeligne/GarsideTubeCarriers.lean)
- [`deligne/ArtinDeligne/UniversalCoverComparison.lean`](../../../../deligne/ArtinDeligne/UniversalCoverComparison.lean)
- [`deligne/evidence/theorem18-local-final/coverage.json`](../../../../deligne/evidence/theorem18-local-final/coverage.json)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log`](../../../../deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log)
- [`deligne/evidence/theorem18-local-final/logs/replay-013-ArtinDeligne.GarsideTubeCarriers.log`](../../../../deligne/evidence/theorem18-local-final/logs/replay-013-ArtinDeligne.GarsideTubeCarriers.log)
- [`deligne/evidence/theorem18-local-final/logs/replay-035-ArtinDeligne.UniversalCoverComparison.log`](../../../../deligne/evidence/theorem18-local-final/logs/replay-035-ArtinDeligne.UniversalCoverComparison.log)
- [`deligne/evidence/theorem18-local-final/verification.json`](../../../../deligne/evidence/theorem18-local-final/verification.json)
- [`deligne/reviews/theorem18-a.json`](../../../../deligne/reviews/theorem18-a.json)
- [`deligne/reviews/theorem18-a.md`](../../../../deligne/reviews/theorem18-a.md)
- [`deligne/reviews/theorem18-b.json`](../../../../deligne/reviews/theorem18-b.json)
- [`deligne/reviews/theorem18-b.md`](../../../../deligne/reviews/theorem18-b.md)
- [`deligne/source-inventory.json`](../../../../deligne/source-inventory.json)
- [`docs/navigation/data/source-inventory.json`](../../data/source-inventory.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/coverage.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/coverage.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/review-a.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/review-a.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/review-b.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/review-b.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/run.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/verification.json)

[Successful final CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363). [Source-correspondence review A](../../reviews/source-correspondence-a.md) and [review B](../../reviews/source-correspondence-b.md).
