# Chamber/groupoid comparison

Actual interval/complement and ribbon/orbit groupoid equivalences.

Kind: **Prerequisite**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

### Source correspondence for `ArtinNormalisers.Chamber3.actualRibbonOrbitEquivalence`

Relation: **alternative-model**.

**Article:** [Lemma 6.2, printed page 23](https://arxiv.org/pdf/2509.21915v3#page=23).

<details><summary>Original article statement extraction</summary>

```text
Lemma 6.2. The functor G : D →R is a groupoid covering.

--- PDF PAGE 24 ---
24          OWEN GARNIER, EDMUND HENG, ANTHONY LICATA, AND ODED YACOBI
```

</details>

Scope of this source link: **alternative-model**.

- The Lean interval groupoid has positive arrows for all chamber pairs and sign-between relations. It is not asserted to be the paper literal adjacent-gallery presentation.
- Original Proposition6.3 states an isomorphism of its orbit groupoid with R; Lean supplies equivalences/actual orbit colimit for its alternative model. Preserve this distinction.

**Article:** [Proposition 6.3, printed page 24](https://arxiv.org/pdf/2509.21915v3#page=24).

Normalized mathematical transcription:

The functor $\mathcal G$ factors through $\mathcal Q$, resulting in $\mathcal G^\prime:\mathcal D/N(W,J)\to\mathcal R$. Moreover, $\mathcal G^\prime$ is an isomorphism of groupoids.

<details><summary>Original article statement extraction</summary>

```text
Proposition 6.3. The functor G factors through Q, resulting in a functor
                                       G′ : D/N(W, J) →R.
Moreover, G′ is an isomorphism of groupoids.
```

</details>

Scope of this source link: **alternative-model**.

- The Lean interval groupoid has positive arrows for all chamber pairs and sign-between relations. It is not asserted to be the paper literal adjacent-gallery presentation.
- Original Proposition6.3 states an isomorphism of its orbit groupoid with R; Lean supplies equivalences/actual orbit colimit for its alternative model. Preserve this distinction.

**Article:** [Lemma 6.6, printed page 25](https://arxiv.org/pdf/2509.21915v3#page=25).

Normalized mathematical transcription:

There is an $N(W,J)$-equivariant equivalence $p:\mathcal D\to\pi_1(\mathcal X_J^{\mathbb C})$ inducing a commutative square with $\mathcal Q:\mathcal D\to\mathcal D/N(W,J)$ on the left, the actual-cover-induced functor on the right, and an equivalence $\bar p:\mathcal D/N(W,J)\to\pi_1(\mathcal X_J^{\mathbb C}/N(W,J))$ along the bottom.

<details><summary>Original article statement extraction</summary>

```text
Lemma 6.6 (An N(W, J)-equivariant equivalence). There is an N(W, J)-equivariant equivalence
           C
p : D →π1(X J ), which induces the following commutative square

                                                   p           C
                    D              π1(X J )

                        Q

                                              C
                     D/N(W, J)                                          π1(X J /N(W, J))                                                   p

                                                C     C
where the right vertical map is induced by the covering XJ →XJ /N(W, J), and the functor p is
an equivalence of groupoids.

                                                                        C
```

</details>

Scope of this source link: **alternative-model**.

- The Lean interval groupoid has positive arrows for all chamber pairs and sign-between relations. It is not asserted to be the paper literal adjacent-gallery presentation.
- Original Proposition6.3 states an isomorphism of its orbit groupoid with R; Lean supplies equivalences/actual orbit colimit for its alternative model. Preserve this distinction.

**Alphabeta Math:** [Deligne-to-ribbon functor is a covering](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-deligne-ribbon-cover-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a finite-rank spherical Coxeter system, so $W$ is finite, and fix $J\subseteq S$. Let $\mathcal D^+(J)$ be the positive category of the relative chamber arrangement and $\mathcal D(J)$ its groupoid completion. Let $\mathcal R(J)$ be the reduced ribbon groupoid and $\mathcal G:\mathcal D(J)\to\mathcal R(J)$ the functor sending a chamber label $(x,I)$ to $I$ and a simple crossing with index $a\notin I$ to the elementary ribbon $\mu_{a,I}$.

The functor $\mathcal G$ is a groupoid covering: for every chamber $C$ and every arrow of $\mathcal R(J)$ with source $\mathcal G(C)$, there is exactly one arrow of $\mathcal D(J)$ with source $C$ and that image. Each elementary ribbon lifts from $(x,I)$ to the corresponding simple wall crossing. The two sides of each defining ribbon-lcm relation lift from a fixed source chamber to equal morphisms of $\mathcal D^+(J)$.
```

Scope of this source link: **alternative-model**.

- The Lean interval groupoid has positive arrows for all chamber pairs and sign-between relations. It is not asserted to be the paper literal adjacent-gallery presentation.
- Original Proposition6.3 states an isomorphism of its orbit groupoid with R; Lean supplies equivalences/actual orbit colimit for its alternative model. Preserve this distinction.

**Alphabeta Math:** [Reduced ribbon groupoid is the Deligne orbit quotient](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-deligne-ribbon-quotient-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a finite-rank spherical Coxeter system, meaning that $W$ is finite, and fix $J\subseteq S$. Write $W_I$ for the subgroup generated by $I\subseteq S$, and let $N=N(W,J)=\operatorname{Norm}_W(W_J)/W_J$. Let $\mathcal D$ be the relative arrangement groupoid, whose objects are chamber labels $(x,I)$, and let $\mathcal R$ be the reduced ribbon groupoid. Its objects are the associates of $J$: the subsets $I\subseteq S$ for which $W_I$ is conjugate to $W_J$. The functor $\mathcal G:\mathcal D\to\mathcal R$ sends $(x,I)$ to $I$ and a simple wall crossing of index $a$ to the elementary ribbon $\mu_{a,I}$. Let $\mathcal Q:\mathcal D\to\mathcal D/N$ send objects and arrows to their orbits under the normaliser action.

The functor $\mathcal G$ factors as $\mathcal G=\mathcal G'\circ\mathcal Q$, where $\mathcal G':\mathcal D/N\to\mathcal R$ is an isomorphism of groupoids. On objects it identifies the $N$-orbits of chambers with the associates of $J$ by $[(x,I)]\mapsto I$.
```

Scope of this source link: **alternative-model**.

- The Lean interval groupoid has positive arrows for all chamber pairs and sign-between relations. It is not asserted to be the paper literal adjacent-gallery presentation.
- Original Proposition6.3 states an isomorphism of its orbit groupoid with R; Lean supplies equivalences/actual orbit colimit for its alternative model. Preserve this distinction.

**Alphabeta Math:** [Equivariant equivalence with fundamental groupoids](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-equivariant-topological-equivalence-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a Coxeter system with finite $W$, and let $J\subseteq S$. Put $G=N(W,J)=\operatorname{Norm}_W(W_J)/W_J$, where $W_J$ is generated by $J$. Let $X=\mathcal X_J^{\mathbb C}$ be the relative complexified arrangement complement and let $\mathcal D=\mathcal D(J)$ be the groupoid completion of the positive relative chamber category. Thus its objects are chambers and its generating arrows are directed crossings of adjacent chambers, subject to equality of positive geodesic galleries with the same endpoints and formal inversion of arrows.

The space $X$ is nonempty, path-connected and locally path-connected.

There is a $G$-equivariant equivalence $p:\mathcal D\to\Pi_1(X)$, where $\Pi_1(X)$ has points of $X$ as objects and endpoint-fixed path-homotopy classes as arrows. Equivariance means $p(gC)=g p(C)$ on objects and $p(g\alpha)=g p(\alpha)$ on arrows. With $Q:\mathcal D\to\mathcal D/G$ the orbit functor and $q:X\to X/G$ the topological orbit map, $p$ induces an equivalence $\bar p:\mathcal D/G\to\Pi_1(X/G)$ satisfying $\bar p\,Q=q_*p$. The map $q$ is a normal covering. An equivalence means a functor equipped with a quasi-inverse and natural isomorphisms to the two identity functors; the Axiom of Choice is used below to choose connecting paths for all objects.
```

Scope of this source link: **alternative-model**.

- The Lean interval groupoid has positive arrows for all chamber pairs and sign-between relations. It is not asserted to be the paper literal adjacent-gallery presentation.
- Original Proposition6.3 states an isomorphism of its orbit groupoid with R; Lean supplies equivalences/actual orbit colimit for its alternative model. Preserve this distinction.

- Equivariant actual-complement and orbit groupoid comparison via the proved interval presentation.

- The Lean interval groupoid has positive arrows for all chamber pairs and sign-between relations. It is not asserted to be the paper literal adjacent-gallery presentation.
- Original Proposition6.3 states an isomorphism of its orbit groupoid with R; Lean supplies equivalences/actual orbit colimit for its alternative model. Preserve this distinction.
- Lean uses the standard braid-presentation Artin group. The general all-types comparison with the topological Artin definition in article §2.2 is not separately formalized here. The actual finite-Coxeter relative-space fundamental-group and exact-diagram identifications proved in milestone4 are retained; this caveat does not deny those comparisons.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Chamber3.actualIntervalComplementEquivalence` | [`chambers/ArtinChambers/ForwardEquivariance.lean:230`](../../../../chambers/ArtinChambers/ForwardEquivariance.lean#L230) | [`chambers/ArtinChambers/ForwardEquivariance.lean:230–234`](../../../../chambers/ArtinChambers/ForwardEquivariance.lean#L230) |
| `ArtinNormalisers.Chamber3.actualRibbonOrbitEquivalence` | [`chambers/ArtinChambers/ActualComparison.lean:65`](../../../../chambers/ArtinChambers/ActualComparison.lean#L65) | [`chambers/ArtinChambers/ActualComparison.lean:65–71`](../../../../chambers/ArtinChambers/ActualComparison.lean#L65) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Chamber3.actualIntervalComplementEquivalence</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    (J : Set.{u_1} I) →
      [Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] →
        CategoryTheory.Equivalence.{u_1, u_1, u_1, u_1}
          (ArtinNormalisers.Chamber3.IntervalGroupoid.{u_1, u_1}
            (ArtinNormalisers.Chamber3.actualForms.{u_1} M J))
          (FundamentalGroupoid.{u_1} (ArtinNormalisers.Theorem18.Complement.{u_1} M J))
```

Source definition/construction:

```lean
/-- The canonical forward functor is the forward half of the actual-space equivalence. -/
noncomputable def actualIntervalComplementEquivalence :
    IntervalGroupoid (E := relativeSubspace J) (actualForms M J) ≌
      FundamentalGroupoid (Complement M J) :=
  actualIntervalComplementEquivalenceOfPoints M J (actualChamberPointFamily M J)
```

</details>

<details><summary>ArtinNormalisers.Chamber3.actualRibbonOrbitEquivalence</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    (J : Set.{u_1} I) →
      [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)] →
        CategoryTheory.Equivalence.{u_1, u_1, u_1, u_1}
          (ArtinNormalisers.Chamber3.AssociateReducedRibbonObject.{u_1} M J)
          (FundamentalGroupoid.{u_1} (ArtinNormalisers.Theorem18.OrbitSpace.{u_1} M J))
```

Source definition/construction:

```lean
/-- The actual reduced ribbon component is equivalent to the fundamental
 groupoid of the original normalizer orbit space. -/
noncomputable def actualRibbonOrbitEquivalence :
    AssociateReducedRibbonObject M J ≌ FundamentalGroupoid (OrbitSpace M J) :=
  comparisonEquivalence (actualRibbonOrbitData M J) (actualSpaceOrbitData M J)
    (actualIntervalComplementEquivalence M J) (actualComparison_equivariant M J)
    (actualIntervalForward_obj_injective M J)
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [Normalizer orbit covering](../04-orbit-cover/PROJECT.md)
- [Reduced ribbons](../05-ribbons/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`chambers/ArtinChambers/ActualComparison.lean`](../../../../chambers/ArtinChambers/ActualComparison.lean)
- [`chambers/ArtinChambers/ForwardEquivariance.lean`](../../../../chambers/ArtinChambers/ForwardEquivariance.lean)
- [`chambers/reviews/landmark3-a.json`](../../../../chambers/reviews/landmark3-a.json)
- [`chambers/reviews/landmark3-a.md`](../../../../chambers/reviews/landmark3-a.md)
- [`chambers/reviews/landmark3-b.json`](../../../../chambers/reviews/landmark3-b.json)
- [`chambers/reviews/landmark3-b.md`](../../../../chambers/reviews/landmark3-b.md)
- [`chambers/source-inventory.json`](../../../../chambers/source-inventory.json)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/verification.json`](../../../../deligne/evidence/theorem18-local-final/verification.json)
- [`docs/navigation/data/source-inventory.json`](../../data/source-inventory.json)
- [`docs/theorem18/landmarks/github-evidence/run-43568861942/landmark3-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43568861942/landmark3-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43568861942/run.json`](../../../theorem18/landmarks/github-evidence/run-43568861942/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43568861942/verification.json`](../../../theorem18/landmarks/github-evidence/run-43568861942/verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/run.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/verification.json)

[Successful final CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363). [Source-correspondence review A](../../reviews/source-correspondence-a.md) and [review B](../../reviews/source-correspondence-b.md).
