# Canonical packet carriers

Literal components of actual sheet intersections are contractible and monotone.

Kind: **Definition and prerequisite**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

No standalone article or Alphabeta statement is assigned to this local formalization result. It supports [Theorem 1.8, p. 3](https://arxiv.org/pdf/2509.21915v3#page=3) and the finite-arrangement argument in the [proof of Corollary 6.14, p. 27](https://arxiv.org/pdf/2509.21915v3#page=27). These are related target passages, not asserted original counterparts.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Deligne5.canonicalPacketCarrier` | [`deligne/ArtinDeligne/CanonicalPacketCarriers.lean:118`](../../../../deligne/ArtinDeligne/CanonicalPacketCarriers.lean#L118) | [`deligne/ArtinDeligne/CanonicalPacketCarriers.lean:118–124`](../../../../deligne/ArtinDeligne/CanonicalPacketCarriers.lean#L118) |
| `ArtinNormalisers.Deligne5.contractibleSpace_canonicalPacketCarrier` | [`deligne/ArtinDeligne/CanonicalPacketCarriers.lean:152`](../../../../deligne/ArtinDeligne/CanonicalPacketCarriers.lean#L152) | [`deligne/ArtinDeligne/CanonicalPacketCarriers.lean:152–162`](../../../../deligne/ArtinDeligne/CanonicalPacketCarriers.lean#L152) |
| `ArtinNormalisers.Deligne5.canonicalPacketCarrier_mono` | [`deligne/ArtinDeligne/CanonicalPacketCarriers.lean:231`](../../../../deligne/ArtinDeligne/CanonicalPacketCarriers.lean#L231) | [`deligne/ArtinDeligne/CanonicalPacketCarriers.lean:231–238`](../../../../deligne/ArtinDeligne/CanonicalPacketCarriers.lean#L231) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Deligne5.canonicalPacketCarrier</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] →
      (J : Set.{u_1} I) →
        Finset.{u_1} (ArtinNormalisers.Deligne5.LiftedCanonicalIndex.{u_1} M J) →
          Set.{u_1} (ArtinNormalisers.Asphericity5.ComplementUniversalCover.{u_1} M J)
```

Source definition/construction:

```lean
/-- The literal actual connected component. Empty packets are assigned the empty set;
no contractibility assertion is made for that default. -/
def canonicalPacketCarrier (F : Finset (LiftedCanonicalIndex M J)) :
    Set (ComplementUniversalCover M J) :=
  if hF : F.Nonempty then
    connectedComponentIn (canonicalPacketUpperIntersection M J F) (canonicalPacketCenter M J F hF)
  else ∅
```

</details>

<details><summary>ArtinNormalisers.Deligne5.contractibleSpace_canonicalPacketCarrier</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (J : Set.{u_1} I) (F : Finset.{u_1} (ArtinNormalisers.Deligne5.LiftedCanonicalIndex.{u_1} M J)),
  Finset.Nonempty.{u_1} F →
    Set.Nonempty.{u_1} (ArtinNormalisers.Deligne5.canonicalPacketOverlapSet.{u_1} M J F) →
      ContractibleSpace.{u_1} ↑(ArtinNormalisers.Deligne5.canonicalPacketCarrier.{u_1} M J F)
```

</details>

<details><summary>ArtinNormalisers.Deligne5.canonicalPacketCarrier_mono</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (J : Set.{u_1} I) {F G : Finset.{u_1} (ArtinNormalisers.Deligne5.LiftedCanonicalIndex.{u_1} M J)},
  F ⊆ G →
    Finset.Nonempty.{u_1} F →
      Finset.Nonempty.{u_1} G →
        Set.Nonempty.{u_1} (ArtinNormalisers.Deligne5.canonicalPacketOverlapSet.{u_1} M J G) →
          ArtinNormalisers.Deligne5.canonicalPacketCarrier.{u_1} M J F ⊆
            ArtinNormalisers.Deligne5.canonicalPacketCarrier.{u_1} M J G
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [Chamber/groupoid comparison](../07-chamber-comparison/PROJECT.md)
- [The actual universal cover](../10-universal-cover/PROJECT.md)
- [The Garside weight model](../12-garside-model/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`deligne/ArtinDeligne/CanonicalPacketCarriers.lean`](../../../../deligne/ArtinDeligne/CanonicalPacketCarriers.lean)
- [`deligne/evidence/theorem18-local-final/coverage.json`](../../../../deligne/evidence/theorem18-local-final/coverage.json)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log`](../../../../deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log)
- [`deligne/evidence/theorem18-local-final/logs/replay-006-ArtinDeligne.CanonicalPacketCarriers.log`](../../../../deligne/evidence/theorem18-local-final/logs/replay-006-ArtinDeligne.CanonicalPacketCarriers.log)
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
