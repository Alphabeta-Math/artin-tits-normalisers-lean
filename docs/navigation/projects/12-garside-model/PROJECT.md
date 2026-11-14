# The Garside weight model

The incoming-ribbon order and its genuine small-chain weight space.

Kind: **Definitions**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

No standalone article or Alphabeta statement is assigned to this local formalization result. It supports [Theorem 1.8, p. 3](https://arxiv.org/pdf/2509.21915v3#page=3) and the finite-arrangement argument in the [proof of Corollary 6.14, p. 27](https://arxiv.org/pdf/2509.21915v3#page=27). These are related target passages, not asserted original counterparts.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Homotopy5.SimpleRibbon` | [`homotopy/ArtinHomotopy/RibbonGcd.lean:105`](../../../../homotopy/ArtinHomotopy/RibbonGcd.lean#L105) | [`homotopy/ArtinHomotopy/RibbonGcd.lean:105–108`](../../../../homotopy/ArtinHomotopy/RibbonGcd.lean#L105) |
| `ArtinNormalisers.Deligne5.IncomingVertex` | [`deligne/ArtinDeligne/IncomingOrder.lean:27`](../../../../deligne/ArtinDeligne/IncomingOrder.lean#L27) | [`deligne/ArtinDeligne/IncomingOrder.lean:27–31`](../../../../deligne/ArtinDeligne/IncomingOrder.lean#L27) |
| `ArtinNormalisers.Deligne5.GarsideWeights` | [`deligne/ArtinDeligne/GarsideWeights.lean:55`](../../../../deligne/ArtinDeligne/GarsideWeights.lean#L55) | [`deligne/ArtinDeligne/GarsideWeights.lean:55–56`](../../../../deligne/ArtinDeligne/GarsideWeights.lean#L55) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Homotopy5.SimpleRibbon</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    [Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] →
      ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M →
        ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M → ArtinNormalisers.Artin.Group.{u_1} M → Prop
```

Source definition/construction:

```lean
/-- A simple ribbon is an actual positive generated arrow which positively
divides the actual source half-turn. This definition contains no maximality. -/
def SimpleRibbon (X Y : RibbonObject M) (s : Artin.Group M) : Prop :=
  PositiveReducedArrow M X Y s ∧ RibbonPrefix M s (cofinalDelta M X.indices)
```

</details>

<details><summary>ArtinNormalisers.Deligne5.IncomingVertex</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    [Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] →
      ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M → Type u_1
```

Source definition/construction:

```lean
/-- Signed incoming vertices in the actual generated ribbon groupoid. -/
structure IncomingVertex (B0 : RibbonObject M) where
  source : RibbonObject M
  value : Artin.Group M
  reduced : ReducedArrow M source B0 value
```

</details>

<details><summary>ArtinNormalisers.Deligne5.GarsideWeights</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    [Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] →
      ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M → Type u_1
```

Source definition/construction:

```lean
/-- The hereditary simple-chain subspace of the genuine incoming realization. -/
abbrev GarsideWeights := ↥(garsideWeightsSet M B0)
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [Reduced ribbons](../05-ribbons/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`deligne/ArtinDeligne/GarsideWeights.lean`](../../../../deligne/ArtinDeligne/GarsideWeights.lean)
- [`deligne/ArtinDeligne/IncomingOrder.lean`](../../../../deligne/ArtinDeligne/IncomingOrder.lean)
- [`deligne/evidence/theorem18-local-final/coverage.json`](../../../../deligne/evidence/theorem18-local-final/coverage.json)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log`](../../../../deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log)
- [`deligne/evidence/theorem18-local-final/logs/replay-014-ArtinDeligne.GarsideWeights.log`](../../../../deligne/evidence/theorem18-local-final/logs/replay-014-ArtinDeligne.GarsideWeights.log)
- [`deligne/evidence/theorem18-local-final/logs/replay-019-ArtinDeligne.IncomingOrder.log`](../../../../deligne/evidence/theorem18-local-final/logs/replay-019-ArtinDeligne.IncomingOrder.log)
- [`deligne/evidence/theorem18-local-final/verification.json`](../../../../deligne/evidence/theorem18-local-final/verification.json)
- [`deligne/reviews/theorem18-a.json`](../../../../deligne/reviews/theorem18-a.json)
- [`deligne/reviews/theorem18-a.md`](../../../../deligne/reviews/theorem18-a.md)
- [`deligne/reviews/theorem18-b.json`](../../../../deligne/reviews/theorem18-b.json)
- [`deligne/reviews/theorem18-b.md`](../../../../deligne/reviews/theorem18-b.md)
- [`deligne/source-inventory.json`](../../../../deligne/source-inventory.json)
- [`docs/navigation/data/source-inventory.json`](../../data/source-inventory.json)
- [`docs/theorem18/landmarks/github-evidence/run-43590812660/homotopy-prerequisites-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43590812660/homotopy-prerequisites-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43590812660/run.json`](../../../theorem18/landmarks/github-evidence/run-43590812660/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43590812660/source-inventory.json`](../../../theorem18/landmarks/github-evidence/run-43590812660/source-inventory.json)
- [`docs/theorem18/landmarks/github-evidence/run-43590812660/verification.json`](../../../theorem18/landmarks/github-evidence/run-43590812660/verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/coverage.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/coverage.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/review-a.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/review-a.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/review-b.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/review-b.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/run.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/verification.json)
- [`homotopy/ArtinHomotopy/RibbonGcd.lean`](../../../../homotopy/ArtinHomotopy/RibbonGcd.lean)
- [`homotopy/reviews/homotopy-prerequisites-a.json`](../../../../homotopy/reviews/homotopy-prerequisites-a.json)
- [`homotopy/reviews/homotopy-prerequisites-a.md`](../../../../homotopy/reviews/homotopy-prerequisites-a.md)
- [`homotopy/reviews/homotopy-prerequisites-b.json`](../../../../homotopy/reviews/homotopy-prerequisites-b.json)
- [`homotopy/reviews/homotopy-prerequisites-b.md`](../../../../homotopy/reviews/homotopy-prerequisites-b.md)

[Successful final CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363). [Source-correspondence review A](../../reviews/source-correspondence-a.md) and [review B](../../reviews/source-correspondence-b.md).
