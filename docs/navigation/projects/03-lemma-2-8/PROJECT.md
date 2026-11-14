# Lemma 2.8: algebraic exact sequence

The full algebraic normalizer short exact sequence.

Kind: **Main result**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

### Source correspondence for `ArtinNormalisers.Artin.lemma_2_8`

Relation: **exact**.

**Article:** [Lemma 2.8, printed page 6](https://arxiv.org/pdf/2509.21915v3#page=6).

Normalized mathematical transcription:

The map $\pi:A\to W$ induces a map $\bar\pi:N(A,J)\to N(W,J)$ giving the short exact sequence $1\to N(P,J)\to N(A,J)\xrightarrow{\bar\pi}N(W,J)\to1$.

<details><summary>Original article statement extraction</summary>

```text
Lemma 2.8. The map π : A →W induces a map π : N(A, J) →N(W, J) giving the short exact
sequence
                         1 →N(P, J) →N(A, J) π−→N(W, J) →1.                         (2.9)
```

</details>

Scope of this source link: **exact**.

- The printed original Lemma2.8 has no spherical hypothesis; the current Alphabeta item explicitly assumes finite rank, whereas Lean permits arbitrary I.
- Original author statement and generated proof are attribution, not external Lean proof suppliers.

**Alphabeta Math:** [Normaliser quotient exact sequence](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-normaliser-exact-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a finite-rank Coxeter system, $A$ its Artin–Tits group, $\pi:A\to W$ the standard projection and $P=\ker\pi$. For a subset $J\subseteq S$, let $W_J$ and $A_J$ be the standard parabolic subgroups. Write $N(W,J)=\operatorname{Norm}_W(W_J)/W_J$, $N(A,J)=\operatorname{Norm}_A(A_J)/A_J$, and let $N(P,J)$ be the image of $P\cap\operatorname{Norm}_A(A_J)$ in $N(A,J)$. Then $\pi$ induces $\overline\pi:N(A,J)\to N(W,J)$ and the sequence $1\to N(P,J)\to N(A,J)\xrightarrow{\overline\pi}N(W,J)\to1$ is exact. Here exactness means that the inclusion $N(P,J)\hookrightarrow N(A,J)$ is injective, its image equals $\ker\overline\pi$, and $\overline\pi$ is surjective.
```

Scope of this source link: **specialization**.

- The printed original Lemma2.8 has no spherical hypothesis; the current Alphabeta item explicitly assumes finite rank, whereas Lean permits arbitrary I.
- Original author statement and generated proof are attribution, not external Lean proof suppliers.
- Direction: the finite-rank Alphabeta assertion is a restriction of this stronger arbitrary-index Lean theorem. Lean specializes to the Alphabeta hypotheses; the unrestricted article Lemma2.8 matches Lean without that additional rank restriction.

- Same actual short exact sequence; Lean is more general in rank (arbitrary I) and has no spherical premise or assumed normalizer-surjectivity premise.
- Direction: the finite-rank Alphabeta assertion is a restriction of this stronger arbitrary-index Lean theorem. Lean specializes to the Alphabeta hypotheses; the unrestricted article Lemma2.8 matches Lean without that additional rank restriction.

- The printed original Lemma2.8 has no spherical hypothesis; the current Alphabeta item explicitly assumes finite rank, whereas Lean permits arbitrary I.
- Original author statement and generated proof are attribution, not external Lean proof suppliers.
- Lean uses the standard braid-presentation Artin group. The general all-types comparison with the topological Artin definition in article §2.2 is not separately formalized here. The actual finite-Coxeter relative-space fundamental-group and exact-diagram identifications proved in milestone4 are retained; this caveat does not deny those comparisons.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Artin.lemma_2_8` | [`ArtinNormalisers/Artin/ExactSequence.lean:130`](../../../../ArtinNormalisers/Artin/ExactSequence.lean#L130) | [`ArtinNormalisers/Artin/ExactSequence.lean:130–141`](../../../../ArtinNormalisers/Artin/ExactSequence.lean#L130) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Artin.lemma_2_8</summary>

```lean
∀ {I : Type u_3} (M : CoxeterMatrix.{u_3} I) (J : Set.{u_3} I),
  Function.Injective.{u_3 + 1, u_3 + 1}
      ⇑(ArtinNormalisers.Artin.pureNormalizerInclusion.{u_3} M J) ∧
    Eq.{u_3 + 1}
        (MonoidHom.range.{u_3, u_3} (ArtinNormalisers.Artin.pureNormalizerInclusion.{u_3} M J))
        (MonoidHom.ker.{u_3, u_3} (ArtinNormalisers.Artin.normalizerQuotientMap.{u_3} M J)) ∧
      Function.Surjective.{u_3 + 1, u_3 + 1}
        ⇑(ArtinNormalisers.Artin.normalizerQuotientMap.{u_3} M J)
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [Groups and normalizer quotients](../01-groups/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`ArtinNormalisers/Artin/ExactSequence.lean`](../../../../ArtinNormalisers/Artin/ExactSequence.lean)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/verification.json`](../../../../deligne/evidence/theorem18-local-final/verification.json)
- [`docs/full/github-evidence/run-43486289665/build.log`](../../../full/github-evidence/run-43486289665/build.log)
- [`docs/full/github-evidence/run-43486289665/github-run.json`](../../../full/github-evidence/run-43486289665/github-run.json)
- [`docs/full/github-evidence/run-43486289665/project-axioms.log`](../../../full/github-evidence/run-43486289665/project-axioms.log)
- [`docs/full/github-evidence/run-43486289665/replay-ArtinNormalisers-Artin-ExactSequence.log`](../../../full/github-evidence/run-43486289665/replay-ArtinNormalisers-Artin-ExactSequence.log)
- [`docs/full/github-evidence/run-43486289665/verification.json`](../../../full/github-evidence/run-43486289665/verification.json)
- [`docs/full/reviews/reviewer-a.json`](../../../full/reviews/reviewer-a.json)
- [`docs/full/reviews/reviewer-b.json`](../../../full/reviews/reviewer-b.json)
- [`docs/full/source-inventory.json`](../../../full/source-inventory.json)
- [`docs/navigation/data/source-inventory.json`](../../data/source-inventory.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/run.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/verification.json)

[Successful final CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363). [Source-correspondence review A](../../reviews/source-correspondence-a.md) and [review B](../../reviews/source-correspondence-b.md).
