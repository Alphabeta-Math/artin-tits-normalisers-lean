# Higher homotopy vanishing of the model

All finite based cube homotopy groups of the actual Garside model vanish.

Kind: **Prerequisite**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

No standalone article or Alphabeta statement is assigned to this local formalization result. It supports [Theorem 1.8, p. 3](https://arxiv.org/pdf/2509.21915v3#page=3) and the finite-arrangement argument in the [proof of Corollary 6.14, p. 27](https://arxiv.org/pdf/2509.21915v3#page=27). These are related target passages, not asserted original counterparts.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Deligne5.garside_homotopyGroup_subsingleton` | [`deligne/ArtinDeligne/GlobalNullity.lean:67`](../../../../deligne/ArtinDeligne/GlobalNullity.lean#L67) | [`deligne/ArtinDeligne/GlobalNullity.lean:67–73`](../../../../deligne/ArtinDeligne/GlobalNullity.lean#L67) |
| `ArtinNormalisers.Deligne5.garside_isAspherical` | [`deligne/ArtinDeligne/GlobalNullity.lean:92`](../../../../deligne/ArtinDeligne/GlobalNullity.lean#L92) | [`deligne/ArtinDeligne/GlobalNullity.lean:92–98`](../../../../deligne/ArtinDeligne/GlobalNullity.lean#L92) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Deligne5.garside_homotopyGroup_subsingleton</summary>

```lean
∀ {S : Type u_1} (M : CoxeterMatrix.{u_1} S) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (B0 : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M) (N : Type u_2) [Finite.{u_2 + 1} N]
  (x : ArtinNormalisers.Deligne5.GarsideWeights.{u_1} M B0),
  Subsingleton.{max (u_1 + 1) (u_2 + 1)}
    (HomotopyGroup.{u_2, u_1} N (ArtinNormalisers.Deligne5.GarsideWeights.{u_1} M B0) x)
```

</details>

<details><summary>ArtinNormalisers.Deligne5.garside_isAspherical</summary>

```lean
∀ {S : Type u_1} (M : CoxeterMatrix.{u_1} S) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (B0 : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M)
  (x : ArtinNormalisers.Deligne5.GarsideWeights.{u_1} M B0),
  TauCeti.IsAspherical.{u_1} (ArtinNormalisers.Deligne5.GarsideWeights.{u_1} M B0) x
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [Finite contractible carriers](../13-finite-carriers/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`deligne/ArtinDeligne/GlobalNullity.lean`](../../../../deligne/ArtinDeligne/GlobalNullity.lean)
- [`deligne/evidence/theorem18-local-final/coverage.json`](../../../../deligne/evidence/theorem18-local-final/coverage.json)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log`](../../../../deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log)
- [`deligne/evidence/theorem18-local-final/logs/replay-015-ArtinDeligne.GlobalNullity.log`](../../../../deligne/evidence/theorem18-local-final/logs/replay-015-ArtinDeligne.GlobalNullity.log)
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
