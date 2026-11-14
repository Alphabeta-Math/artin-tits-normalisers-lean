# The actual universal cover

The original path-class universal cover, its covering projection and surjectivity.

Kind: **Definition and prerequisite**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

No standalone article or Alphabeta statement is assigned to this local formalization result. It supports [Theorem 1.8, p. 3](https://arxiv.org/pdf/2509.21915v3#page=3) and the finite-arrangement argument in the [proof of Corollary 6.14, p. 27](https://arxiv.org/pdf/2509.21915v3#page=27). These are related target passages, not asserted original counterparts.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Asphericity5.ComplementUniversalCover` | [`asphericity/ArtinAsphericity/UniversalCoverGeometry.lean:45`](../../../../asphericity/ArtinAsphericity/UniversalCoverGeometry.lean#L45) | [`asphericity/ArtinAsphericity/UniversalCoverGeometry.lean:45–47`](../../../../asphericity/ArtinAsphericity/UniversalCoverGeometry.lean#L45) |
| `ArtinNormalisers.Asphericity5.isCoveringMap_complementUniversalCoverProjection` | [`asphericity/ArtinAsphericity/UniversalCoverGeometry.lean:57`](../../../../asphericity/ArtinAsphericity/UniversalCoverGeometry.lean#L57) | [`asphericity/ArtinAsphericity/UniversalCoverGeometry.lean:57–59`](../../../../asphericity/ArtinAsphericity/UniversalCoverGeometry.lean#L57) |
| `ArtinNormalisers.Asphericity5.complementUniversalCoverProjection_surjective` | [`asphericity/ArtinAsphericity/UniversalCoverGeometry.lean:61`](../../../../asphericity/ArtinAsphericity/UniversalCoverGeometry.lean#L61) | [`asphericity/ArtinAsphericity/UniversalCoverGeometry.lean:61–66`](../../../../asphericity/ArtinAsphericity/UniversalCoverGeometry.lean#L61) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Asphericity5.ComplementUniversalCover</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    [Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] → Set.{u_1} I → Type u_1
```

Source definition/construction:

```lean
/-- The genuine based-path universal cover of the original complement,
at exactly the already constructed standard geometric point. -/
abbrev ComplementUniversalCover := TauCeti.UniversalCover (standardComplementPoint M J)
```

</details>

<details><summary>ArtinNormalisers.Asphericity5.isCoveringMap_complementUniversalCoverProjection</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (J : Set.{u_1} I),
  IsCoveringMap.{u_1, u_1}
    (ArtinNormalisers.Asphericity5.complementUniversalCoverProjection.{u_1} M J)
```

</details>

<details><summary>ArtinNormalisers.Asphericity5.complementUniversalCoverProjection_surjective</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (J : Set.{u_1} I),
  Function.Surjective.{u_1 + 1, u_1 + 1}
    (ArtinNormalisers.Asphericity5.complementUniversalCoverProjection.{u_1} M J)
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [Relative complement and orbit space](../02-complement/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`asphericity/ArtinAsphericity/UniversalCoverGeometry.lean`](../../../../asphericity/ArtinAsphericity/UniversalCoverGeometry.lean)
- [`asphericity/reviews/asphericity-prerequisites-a.json`](../../../../asphericity/reviews/asphericity-prerequisites-a.json)
- [`asphericity/reviews/asphericity-prerequisites-a.md`](../../../../asphericity/reviews/asphericity-prerequisites-a.md)
- [`asphericity/reviews/asphericity-prerequisites-b.json`](../../../../asphericity/reviews/asphericity-prerequisites-b.json)
- [`asphericity/reviews/asphericity-prerequisites-b.md`](../../../../asphericity/reviews/asphericity-prerequisites-b.md)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/verification.json`](../../../../deligne/evidence/theorem18-local-final/verification.json)
- [`docs/navigation/data/source-inventory.json`](../../data/source-inventory.json)
- [`docs/theorem18/landmarks/github-evidence/run-43579352641/asphericity-prerequisites-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43579352641/asphericity-prerequisites-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43579352641/run.json`](../../../theorem18/landmarks/github-evidence/run-43579352641/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43579352641/source-inventory.json`](../../../theorem18/landmarks/github-evidence/run-43579352641/source-inventory.json)
- [`docs/theorem18/landmarks/github-evidence/run-43579352641/verification.json`](../../../theorem18/landmarks/github-evidence/run-43579352641/verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/run.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/verification.json)

[Successful final CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363). [Source-correspondence review A](../../reviews/source-correspondence-a.md) and [review B](../../reviews/source-correspondence-b.md).
