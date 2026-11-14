# Normalizer orbit covering

The original orbit projection is a genuine quotient covering.

Kind: **Prerequisite**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

### Source correspondence for `ArtinNormalisers.Landmark1.isQuotientCoveringMap_orbitProjection`

Relation: **specialization**.

**Article:** [Equation (3.28) and preceding paragraph, printed page 13](https://arxiv.org/pdf/2509.21915v3#page=13).

Normalized mathematical transcription:

The $N(W,J)$-action on $\mathcal X_J^{\mathbb C}$ is free and properly discontinuous. The quotient $\mathcal X_J^{\mathbb C}\to\mathcal X_J^{\mathbb C}/N(W,J)$ is a normal covering inducing $1\to\pi_1(\mathcal X_J^{\mathbb C},x)\to\pi_1(\mathcal X_J^{\mathbb C}/N(W,J),x)\to N(W,J)\to1$ (3.28).

<details><summary>Original article statement extraction</summary>

```text
Since N(W, J) acts on Cone(J), and hence on Cone(J)◦, we have a well-defined action of N(W, J)
    C
on XJ . Since the action of N(W, J) on chambers is free by Lemma 3.24(3), the action of N(W, J) on
  C                                                                C     C
X J  is both free and properly discontinuous. Thus the associated quotient map XJ →XJ /N(W, J)
is a normal (i.e. Galois) covering of topological spaces, which induces the following short exact
                                           C
sequence, generalising the one in (2.4) (where x ∈XJ ):
                          C          C
                   1 →π1(X J , x) →π1(X J /N(W, J), x) →N(W, J) →1.                (3.28)
```

</details>

Scope of this source link: **specialization**.

- Raw mathlib endpoint monodromy has codomain Q^op. First-path-first original/generated convention is handled explicitly by landmark4.
- Do not attribute the original general infinite-W relative-cone covering to this finite-W module.

**Article:** [Lemma 3.23, printed page 12](https://arxiv.org/pdf/2509.21915v3#page=12).

<details><summary>Original article statement extraction</summary>

```text
Lemma 3.23. The action of NormW (WJ) ⊆W on Θ preserves ΘJ. The kernel of the action
of NormW (WJ) on ΘJ  is precisely WJ, so that we obtain a faithful linear action of N(W, J) –
NormW (WJ)/WJ on ΘJ. This action of N(W, J) further restricts to an action on Cone(J) that
is compatible with the stratification in (3.4):  if g ∈N(W, J), then we have g · (x · CL) = (gx) · CL
where g is any lift of g in NormW (WJ).
```

</details>

Scope of this source link: **specialization**.

- Raw mathlib endpoint monodromy has codomain Q^op. First-path-first original/generated convention is handled explicitly by landmark4.
- Do not attribute the original general infinite-W relative-cone covering to this finite-W module.

**Article:** [Lemma 3.24, printed page 12](https://arxiv.org/pdf/2509.21915v3#page=12).

<details><summary>Original article statement extraction</summary>

```text
Lemma 3.24. Recall the action of N(W, J) on Cone(J) from Lemma 3.23.
   (1) Each g ∈N(W, J) acts on Cham(J) by g · (x, I) = (y, I), where y is the minimal length
        representative of the coset gxWI for g ∈NormW (WJ) any representative of g.
   (2) The action of N(W, J) on Cham(J) is transitive on the first label in the sense that any two
       chambers of the form (x, I) and (y, I) lie in the same N(W, J)-orbit.
   (3) The action of N(W, J) on Cham(J) is free.
   (4) The action of N(W, J) on Cham(J) preserves adjacency:  precisely  if ωa(C) = C′ with
       C, C′ ∈Cham(J), then ωa(g · C) = g · C′ for any g ∈N(W, J).
```

</details>

Scope of this source link: **specialization**.

- Raw mathlib endpoint monodromy has codomain Q^op. First-path-first original/generated convention is handled explicitly by landmark4.
- Do not attribute the original general infinite-W relative-cone covering to this finite-W module.

**Alphabeta Math:** [Relative free action, normal cover and exact sequence](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-relative-cover-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a finite-rank Coxeter system and $J\subseteq S$. Write $N(W,J)=\operatorname{Norm}_W(W_J)/W_J$ and let $\mathcal X_J^{\mathbb C}$ be the relative complexified complement of [def-relative-complement-artin-tits-normalisers](item-def-relative-complement-artin-tits-normalisers). The induced diagonal $N(W,J)$-action on $\mathcal X_J^{\mathbb C}$ is free and properly discontinuous: every point has an open neighbourhood disjoint from all its nonidentity translates.

The quotient map is a normal covering, meaning a covering whose deck transformations act transitively on every fibre. For $x\in\mathcal X_J^{\mathbb C}$ and its image $\overline x$, it induces the exact sequence $1\to\pi_1(\mathcal X_J^{\mathbb C},x)\to\pi_1(\mathcal X_J^{\mathbb C}/N(W,J),\overline x)\to N(W,J)\to1$. Fundamental groups use first-path-first multiplication; the last map sends a loop to the unique element taking $x$ to the endpoint of its lift starting at $x$.
```

Scope of this source link: **specialization**.

- Raw mathlib endpoint monodromy has codomain Q^op. First-path-first original/generated convention is handled explicitly by landmark4.
- Do not attribute the original general infinite-W relative-cone covering to this finite-W module.

**Alphabeta Math:** [Faithful normaliser-quotient action on the relative cone](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-normaliser-linear-action-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a Coxeter system with finite vertex set $\Gamma_0$, and let $V$ be its canonical real representation with simple-root basis $(\alpha_i)_{i\in\Gamma_0}$ and dual space $\Theta=V^*$, equipped with the contragredient action. Fix $J\subseteq\Gamma_0$. Write $W_J=\langle s_j:j\in J\rangle$, $\Theta_J=\{f\in\Theta:f(\alpha_j)=0\text{ for all }j\in J\}$, and $C_L=\{f\in\Theta_L:f(\alpha_i)>0\text{ for all }i\notin L\}$ for $L\subseteq\Gamma_0$. Let $\mathrm{Cone}$ be the union of the $W$-translates of the closed fundamental chamber, and put $\mathrm{Cone}(J)=\mathrm{Cone}\cap\Theta_J$.

The normaliser $\operatorname{Norm}_W(W_J)=\{g\in W:gW_Jg^{-1}=W_J\}$ preserves $\Theta_J$, and the kernel of its action on $\Theta_J$ is exactly $W_J$. Consequently its quotient $N(W,J)=\operatorname{Norm}_W(W_J)/W_J$ acts faithfully by linear maps on $\Theta_J$. This action preserves $\mathrm{Cone}(J)$ and its stratification into the translates $xC_L\subseteq\Theta_J$: for every such stratum and every lift $g\in\operatorname{Norm}_W(W_J)$ of $\bar g\in N(W,J)$, one has $\bar g\,(xC_L)=(gx)C_L$.
```

Scope of this source link: **specialization**.

- Raw mathlib endpoint monodromy has codomain Q^op. First-path-first original/generated convention is handled explicitly by landmark4.
- Do not attribute the original general infinite-W relative-cone covering to this finite-W module.

**Alphabeta Math:** [Normaliser action on labels, orbits and adjacency](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-normaliser-chamber-action-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a finite-rank Coxeter system with vertex set $\Gamma_0$ and fix $J\subseteq\Gamma_0$. For $I\subseteq\Gamma_0$, write $W_I$ for the standard parabolic subgroup generated by the simple reflections indexed by $I$, and let $\ell$ be Coxeter length. The chamber-label set $\mathrm{Cham}(J)$ consists of the pairs $(x,I)$ such that $W_Jx=xW_I$ and $x$ has minimum length in $xW_I$. Write $N(W,J)=\operatorname{Norm}_W(W_J)/W_J$ for the normaliser quotient.

Under the chamber bijection $(x,I)\mapsto xC_I$, the quotient action on the relative cone induces an action on $\mathrm{Cham}(J)$. For $\bar g\in N(W,J)$ and any representative $g\in\operatorname{Norm}_W(W_J)$, it is given by $\bar g\cdot(x,I)=(y,I)$, where $y$ is the unique minimum-length element of $gxW_I$. Any two labels with the same second component lie in the same orbit, and the action is free: a quotient element fixing a label is the identity.

If $\omega_{a,I}(x,I)=(xv_{a,I},K)$ is a simple wall crossing to an adjacent chamber, then $\omega_{a,I}(\bar g\cdot(x,I))=\bar g\cdot\omega_{a,I}(x,I)$. Thus the action preserves adjacency and the crossing index $a$.
```

Scope of this source link: **specialization**.

- Raw mathlib endpoint monodromy has codomain Q^op. First-path-first original/generated convention is handled explicitly by landmark4.
- Do not attribute the original general infinite-W relative-cone covering to this finite-W module.

- Finite-W specialization of original general relative free normal covering and exact sequence.

- Raw mathlib endpoint monodromy has codomain Q^op. First-path-first original/generated convention is handled explicitly by landmark4.
- Do not attribute the original general infinite-W relative-cone covering to this finite-W module.
- Lean uses the standard braid-presentation Artin group. The general all-types comparison with the topological Artin definition in article §2.2 is not separately formalized here. The actual finite-Coxeter relative-space fundamental-group and exact-diagram identifications proved in milestone4 are retained; this caveat does not deny those comparisons.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Landmark1.isQuotientCoveringMap_orbitProjection` | [`landmarks/ArtinLandmarks/Covering.lean:106`](../../../../landmarks/ArtinLandmarks/Covering.lean#L106) | [`landmarks/ArtinLandmarks/Covering.lean:106–110`](../../../../landmarks/ArtinLandmarks/Covering.lean#L106) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Landmark1.isQuotientCoveringMap_orbitProjection</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) (J : Set.{u_1} I)
  [Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)],
  IsQuotientCoveringMap.{u_1, u_1, u_1} (ArtinNormalisers.Theorem18.orbitProjection.{u_1} M J)
    (ArtinNormalisers.Artin.coxeterNormalizerQuotient.{u_1} M J)
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [Relative complement and orbit space](../02-complement/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/verification.json`](../../../../deligne/evidence/theorem18-local-final/verification.json)
- [`docs/navigation/data/source-inventory.json`](../../data/source-inventory.json)
- [`docs/theorem18/landmarks/github-evidence/run-43498322108/landmark1-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43498322108/landmark1-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43498322108/run.json`](../../../theorem18/landmarks/github-evidence/run-43498322108/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43498322108/verification.json`](../../../theorem18/landmarks/github-evidence/run-43498322108/verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/run.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/verification.json)
- [`landmarks/ArtinLandmarks/Covering.lean`](../../../../landmarks/ArtinLandmarks/Covering.lean)
- [`landmarks/reviews/landmark1-a.json`](../../../../landmarks/reviews/landmark1-a.json)
- [`landmarks/reviews/landmark1-a.md`](../../../../landmarks/reviews/landmark1-a.md)
- [`landmarks/reviews/landmark1-b.json`](../../../../landmarks/reviews/landmark1-b.json)
- [`landmarks/reviews/landmark1-b.md`](../../../../landmarks/reviews/landmark1-b.md)
- [`landmarks/source-inventory.json`](../../../../landmarks/source-inventory.json)

[Successful final CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363). [Source-correspondence review A](../../reviews/source-correspondence-a.md) and [review B](../../reviews/source-correspondence-b.md).
