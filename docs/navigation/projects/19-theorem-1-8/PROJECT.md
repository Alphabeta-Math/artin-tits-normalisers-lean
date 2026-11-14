# Theorem 1.8

Both complete exact diagrams and both original-space K(G,1) conclusions, with all basepoints.

Kind: **Main theorem**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

### Source correspondence for `ArtinNormalisers.Deligne5.theorem_1_8`

Relation: **exact**.

**Article:** [Theorem 1.8, printed page 3](https://arxiv.org/pdf/2509.21915v3#page=3).

Normalized mathematical transcription:

Assume that $W$ is a finite Coxeter group, and let $x\in\mathcal X_J^{\mathbb C}$. The short exact sequences (1.5) and (1.6) are isomorphic. In particular, $N(A,J)\cong\pi_1(\mathcal X_J^{\mathbb C}/N(W,J),x)$ and $N(P,J)\cong\pi_1(\mathcal X_J^{\mathbb C},x)$. Moreover, $\mathcal X_J^{\mathbb C}/N(W,J)$ (resp. $\mathcal X_J^{\mathbb C}$) is a $K(\pi,1)$ space for $N(A,J)$ (resp. for $N(P,J)$).

<details><summary>Original article statement extraction</summary>

```text
Theorem 1.8. Assume that W is a finite Coxeter group, and let x ∈XJ . The short exact sequences
(1.5) and (1.6) are isomorphic. In particular, we have the following isomorphisms:

                                         C
                         N(A, J) ∼= π1(X J /N(W, J), x),
                                         C
                          N(P, J) ∼= π1(X J , x).
           C                C
Moreover, XJ /N(W, J) (resp. XJ ) is a K(π, 1) space for N(A, J) (resp. for N(P, J)).
                                                                                C
```

</details>

Scope of this source link: **exact**.

- The separate original Remark6.15 finite CW-model statement is not a Lean endpoint and must not be added to this theorem.
- Generated item explicitly assumes Choice; Lean may use the standard Classical.choice axiom and retains source-bound axiom audit evidence.
- This attribution inventory makes no independent CI acceptance/status assertion; root updates documentation after verified archive.

**Article:** [Theorem 6.7 / Equation (6.8), printed page 26](https://arxiv.org/pdf/2509.21915v3#page=26).

Normalized mathematical transcription:

For a spherical Coxeter diagram $\Gamma$, its groups $W,A$, $J\subseteq\Gamma_0$, and $x\in\mathcal X_J^{\mathbb C}$, there is an isomorphism of short exact sequences with top row $1\to N(P,J)\to N(A,J)\to N(W,J)\to1$, bottom row $1\to\pi_1(\mathcal X_J^{\mathbb C},x)\to\pi_1(\mathcal X_J^{\mathbb C}/N(W,J),x)\to N(W,J)\to1$, and identity right-hand vertical map. The rows are induced respectively by the canonical $\pi:A\to W$ and the actual normal covering (6.8).

<details><summary>Original article statement extraction</summary>

```text
Theorem 6.7. Let Γ be a spherical Coxeter diagram with associated Coxeter group W and associ-
                                                                   C
ated Artin–Tits group A. Let also J be a subset of the vertex set Γ0. Fix x ∈XJ and denote also
                C
by x its image in XJ /N(W, J).
  We have an isomorphism of short exact sequences

            1       N(P, J)           N(A, J)         N(W, J)       1

                    ≃               ≃                                                     ,         (6.8)

                       C             C
            1      π1(X J , x)      π1(X J /N(W, J), x)     N(W, J)       1

where the first short exact sequence is induced by the canonical quotient π : A →W (see Lemma
                                               C     C
2.8) and the second is induced by the normal covering XJ →X J /N(W, J).
                                  C                           C
```

</details>

Scope of this source link: **exact**.

- The separate original Remark6.15 finite CW-model statement is not a Lean endpoint and must not be added to this theorem.
- Generated item explicitly assumes Choice; Lean may use the standard Classical.choice axiom and retains source-bound axiom audit evidence.
- This attribution inventory makes no independent CI acceptance/status assertion; root updates documentation after verified archive.

**Article:** [Corollary 6.14, printed page 27](https://arxiv.org/pdf/2509.21915v3#page=27).

Normalized mathematical transcription:

The space $\mathcal X_J^{\mathbb C}/N(W,J)$ is a $K(\pi,1)$ for $N(A,J)$.

<details><summary>Original article statement extraction</summary>

```text
Corollary 6.14. The space X J /N(W, J) is a K(π, 1) for N(A, J).

                 C
```

</details>

Scope of this source link: **exact**.

- The separate original Remark6.15 finite CW-model statement is not a Lean endpoint and must not be added to this theorem.
- Generated item explicitly assumes Choice; Lean may use the standard Classical.choice axiom and retains source-bound axiom audit evidence.
- This attribution inventory makes no independent CI acceptance/status assertion; root updates documentation after verified archive.

**Alphabeta Math:** [Main spherical theorem combining exact sequences and asphericity](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-main-kpi-summary-artin-tits-normalisers).

Original statement Markdown:

```text
Assume the Axiom of Choice. Let $(W,S)$ be a finite-rank spherical Coxeter system, meaning that $S$ is finite and $W$ is finite, and let $J\subseteq S$. Let $A$ be the associated Artin–Tits group, $\pi:A\to W$ its standard projection, and $P=\ker\pi$. For $G=W,A$, let $G_J$ be the subgroup generated by the standard generators indexed by $J$, and define $N(G,J)=\operatorname{Norm}_G(G_J)/G_J$, where $\operatorname{Norm}_G(G_J)=\{g\in G:gG_Jg^{-1}=G_J\}$. Let $N(P,J)$ be the image of $P\cap\operatorname{Norm}_A(A_J)$ in $N(A,J)$.

Let $\Theta_J$ be the subspace of the real dual reflection representation on which the simple roots indexed by $J$ vanish, and let $\mathcal H^J$ consist of the distinct hyperplanes obtained by restricting to $\Theta_J$ those root hyperplanes that do not contain it. In spherical type, the relative complexified complement is $X=\mathcal X_J^{\mathbb C}=(\Theta_J\otimes_{\mathbb R}\mathbb C)\setminus\bigcup_{H\in\mathcal H^J}(H\otimes_{\mathbb R}\mathbb C)$, with its subspace topology. The action of $N(W,J)$ on $X$ is the complex-linear extension of $(nW_J)\cdot f=nf$, where $(nf)(v)=f(n^{-1}v)$ for $f\in\Theta_J$, $v$ in the real root space and $n\in\operatorname{Norm}_W(W_J)$. It is independent of the representative and preserves $X$. For $x\in X$, let $\bar x$ be its image in $X/N(W,J)$ under this action.

The algebraic exact sequence $1\to N(P,J)\to N(A,J)\to N(W,J)\to1$ is isomorphic to the covering exact sequence $1\to\pi_1(X,x)\to\pi_1(X/N(W,J),\bar x)\to N(W,J)\to1$, with the identity on $N(W,J)$. In particular, $N(P,J)\cong\pi_1(X,x)$ and $N(A,J)\cong\pi_1(X/N(W,J),\bar x)$. Moreover, $X$ is a $K(N(P,J),1)$ and $X/N(W,J)$ is a $K(N(A,J),1)$: here $K(G,1)$ means a path-connected space whose fundamental group is isomorphic to $G$ and whose homotopy groups in all degrees at least two vanish. Fundamental groups use first-path-first multiplication.
```

Scope of this source link: **exact**.

- The separate original Remark6.15 finite CW-model statement is not a Lean endpoint and must not be added to this theorem.
- Generated item explicitly assumes Choice; Lean may use the standard Classical.choice axiom and retains source-bound axiom audit evidence.
- This attribution inventory makes no independent CI acceptance/status assertion; root updates documentation after verified archive.

- Full actual normalized/positive diagram bundle and both actual-space K(G,1) predicates; all subsets/basepoints/universes, finite actual W only.

- The separate original Remark6.15 finite CW-model statement is not a Lean endpoint and must not be added to this theorem.
- Generated item explicitly assumes Choice; Lean may use the standard Classical.choice axiom and retains source-bound axiom audit evidence.
- This attribution inventory makes no independent CI acceptance/status assertion; root updates documentation after verified archive.
- Lean uses the standard braid-presentation Artin group. The general all-types comparison with the topological Artin definition in article §2.2 is not separately formalized here. The actual finite-Coxeter relative-space fundamental-group and exact-diagram identifications proved in milestone4 are retained; this caveat does not deny those comparisons.

### Source correspondence for `ArtinNormalisers.Deligne5.theorem_1_8_all_basepoints`

Relation: **exact**.

- Full actual normalized/positive diagram bundle and both actual-space K(G,1) predicates; all subsets/basepoints/universes, finite actual W only.

- The separate original Remark6.15 finite CW-model statement is not a Lean endpoint and must not be added to this theorem.
- Generated item explicitly assumes Choice; Lean may use the standard Classical.choice axiom and retains source-bound axiom audit evidence.
- This attribution inventory makes no independent CI acceptance/status assertion; root updates documentation after verified archive.
- Lean uses the standard braid-presentation Artin group. The general all-types comparison with the topological Artin definition in article §2.2 is not separately formalized here. The actual finite-Coxeter relative-space fundamental-group and exact-diagram identifications proved in milestone4 are retained; this caveat does not deny those comparisons.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Deligne5.actualNormalizerDiagrams` | [`deligne/ArtinDeligne/Theorem18.lean:69`](../../../../deligne/ArtinDeligne/Theorem18.lean#L69) | [`deligne/ArtinDeligne/Theorem18.lean:69–80`](../../../../deligne/ArtinDeligne/Theorem18.lean#L69) |
| `ArtinNormalisers.Deligne5.theorem_1_8` | [`deligne/ArtinDeligne/Theorem18.lean:131`](../../../../deligne/ArtinDeligne/Theorem18.lean#L131) | [`deligne/ArtinDeligne/Theorem18.lean:131–141`](../../../../deligne/ArtinDeligne/Theorem18.lean#L131) |
| `ArtinNormalisers.Deligne5.theorem_1_8_all_basepoints` | [`deligne/ArtinDeligne/Theorem18.lean:143`](../../../../deligne/ArtinDeligne/Theorem18.lean#L143) | [`deligne/ArtinDeligne/Theorem18.lean:143–153`](../../../../deligne/ArtinDeligne/Theorem18.lean#L143) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Deligne5.actualNormalizerDiagrams</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    [Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] →
      (J : Set.{u_1} I) → ArtinNormalisers.Theorem18.Complement.{u_1} M J → Prop
```

Source definition/construction:

```lean
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
```

</details>

<details><summary>ArtinNormalisers.Deligne5.theorem_1_8</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (J : Set.{u_1} I) (x : ArtinNormalisers.Theorem18.Complement.{u_1} M J),
  ArtinNormalisers.Deligne5.actualNormalizerDiagrams.{u_1} M J x ∧
    TauCeti.IsEilenbergMacLaneSpaceOne.{u_1, u_1}
        (↥(ArtinNormalisers.Artin.pureNormalizerImage.{u_1} M J))
        (ArtinNormalisers.Theorem18.Complement.{u_1} M J) x ∧
      TauCeti.IsEilenbergMacLaneSpaceOne.{u_1, u_1}
        (ArtinNormalisers.Artin.normalizerQuotient.{u_1} M J)
        (ArtinNormalisers.Theorem18.OrbitSpace.{u_1} M J)
        (ArtinNormalisers.Theorem18.orbitProjection.{u_1} M J x)
```

</details>

<details><summary>ArtinNormalisers.Deligne5.theorem_1_8_all_basepoints</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (J : Set.{u_1} I),
  (∀ (x : ArtinNormalisers.Theorem18.Complement.{u_1} M J),
      ArtinNormalisers.Deligne5.actualNormalizerDiagrams.{u_1} M J x ∧
        TauCeti.IsEilenbergMacLaneSpaceOne.{u_1, u_1}
            (↥(ArtinNormalisers.Artin.pureNormalizerImage.{u_1} M J))
            (ArtinNormalisers.Theorem18.Complement.{u_1} M J) x ∧
          TauCeti.IsEilenbergMacLaneSpaceOne.{u_1, u_1}
            (ArtinNormalisers.Artin.normalizerQuotient.{u_1} M J)
            (ArtinNormalisers.Theorem18.OrbitSpace.{u_1} M J)
            (ArtinNormalisers.Theorem18.orbitProjection.{u_1} M J x)) ∧
    ∀ (y : ArtinNormalisers.Theorem18.OrbitSpace.{u_1} M J),
      TauCeti.IsEilenbergMacLaneSpaceOne.{u_1, u_1}
        (ArtinNormalisers.Artin.normalizerQuotient.{u_1} M J)
        (ArtinNormalisers.Theorem18.OrbitSpace.{u_1} M J) y
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [Compatible exact diagrams](../08-exact-diagrams/PROJECT.md)
- [Corollary 6.14](../20-corollary-6-14/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`deligne/ArtinDeligne/Theorem18.lean`](../../../../deligne/ArtinDeligne/Theorem18.lean)
- [`deligne/evidence/theorem18-local-final/coverage.json`](../../../../deligne/evidence/theorem18-local-final/coverage.json)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log`](../../../../deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log)
- [`deligne/evidence/theorem18-local-final/logs/replay-034-ArtinDeligne.Theorem18.log`](../../../../deligne/evidence/theorem18-local-final/logs/replay-034-ArtinDeligne.Theorem18.log)
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
