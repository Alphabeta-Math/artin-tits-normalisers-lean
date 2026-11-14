# Relative complement and orbit space

The actual relative hyperplane complement and its normalizer orbit space.

Kind: **Definitions**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

### Source correspondence for `ArtinNormalisers.Theorem18.Complement`

Relation: **specialization**.

**Article:** [Equation (3.26), printed page 13](https://arxiv.org/pdf/2509.21915v3#page=13).

<details><summary>Original article statement extraction</summary>

```text
Notation 2.1 and refer to the space
                        ´
                       C                          :=  Cone(J)◦× Cone(J)◦¯ \ [ H × H                     (3.26)                X J
                                              H∈HJ
as the complexified hyperplane complement of the arrangement (Cone(J)◦, HJ). Note that
when Γ is spherical, we have that Cone(J)◦= ΘJ, and
                             C ∼= pΘJ ⊗R Cq \ [ H ⊗R C.                    X J
                                        H∈HJ

                                                                                C
```

</details>

Scope of this source link: **specialization**.

- Do not identify this definition with the original general infinite-W cone complement.

**Alphabeta Math:** [Relative complexified hyperplane complement](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-def-relative-complement-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a Coxeter system with finite $S$, and let $J\subseteq S$. In the real dual representation space $\Theta$, let $\Theta_J$ be the subspace on which the simple roots indexed by $J$ vanish. Let $\mathrm{Cone}(J)$ be the intersection of the Tits cone with $\Theta_J$, and let $\mathrm{Cone}(J)^\circ$ be its interior in $\Theta_J$. Let $\mathcal H^J$ be the set of distinct hyperplanes obtained by restricting to $\Theta_J$ those root hyperplanes that do not contain $\Theta_J$.

The **relative complexified hyperplane complement** is the space

$$\mathcal X_J^{\mathbb C}=(\mathrm{Cone}(J)^\circ\times\mathrm{Cone}(J)^\circ)\setminus\bigcup_{H\in\mathcal H^J}(H\times H).$$

It has the subspace topology inherited from the product topology. If $W$ is finite, a case also called **spherical type**, then $\mathrm{Cone}(J)^\circ=\Theta_J$. Under the real-linear identification $(x,y)\mapsto x\otimes1+y\otimes i$ of $\Theta_J\times\Theta_J$ with $\Theta_J\otimes_{\mathbb R}\mathbb C$, the space is

$$(\Theta_J\otimes_{\mathbb R}\mathbb C)\setminus\bigcup_{H\in\mathcal H^J}(H\otimes_{\mathbb R}\mathbb C).$$
```

Scope of this source link: **specialization**.

- Do not identify this definition with the original general infinite-W cone complement.

- The Lean space is defined using all of the relative flat for every M; it represents article(3.26) under finite W, where Cone(J)^interior=Theta_J.

- Do not identify this definition with the original general infinite-W cone complement.
- Lean uses the standard braid-presentation Artin group. The general all-types comparison with the topological Artin definition in article §2.2 is not separately formalized here. The actual finite-Coxeter relative-space fundamental-group and exact-diagram identifications proved in milestone4 are retained; this caveat does not deny those comparisons.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Theorem18.Complement` | [`ArtinNormalisers/Theorem18/Geometry.lean:227`](../../../../ArtinNormalisers/Theorem18/Geometry.lean#L227) | [`ArtinNormalisers/Theorem18/Geometry.lean:227–228`](../../../../ArtinNormalisers/Theorem18/Geometry.lean#L227) |
| `ArtinNormalisers.Theorem18.OrbitSpace` | [`ArtinNormalisers/Theorem18/NormalizerAction.lean:286`](../../../../ArtinNormalisers/Theorem18/NormalizerAction.lean#L286) | [`ArtinNormalisers/Theorem18/NormalizerAction.lean:286–288`](../../../../ArtinNormalisers/Theorem18/NormalizerAction.lean#L286) |
| `ArtinNormalisers.Theorem18.orbitProjection` | [`ArtinNormalisers/Theorem18/NormalizerAction.lean:294`](../../../../ArtinNormalisers/Theorem18/NormalizerAction.lean#L294) | [`ArtinNormalisers/Theorem18/NormalizerAction.lean:294–296`](../../../../ArtinNormalisers/Theorem18/NormalizerAction.lean#L294) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Theorem18.Complement</summary>

```lean
{I : Type u_1} → CoxeterMatrix.{u_1} I → Set.{u_1} I → Type u_1
```

Source definition/construction:

```lean
/-- The actual complement, carrying its inherited product/subspace topology. -/
def Complement (M : CoxeterMatrix I) (J : Set I) := ↥(complementSet M J)
```

</details>

<details><summary>ArtinNormalisers.Theorem18.OrbitSpace</summary>

```lean
{I : Type u_1} → CoxeterMatrix.{u_1} I → Set.{u_1} I → Type u_1
```

Source definition/construction:

```lean
/-- The source's actual topological orbit space `X_J / N(W,J)`. -/
def OrbitSpace :=
  Quotient (MulAction.orbitRel (Artin.coxeterNormalizerQuotient M J) (Complement M J))
```

</details>

<details><summary>ArtinNormalisers.Theorem18.orbitProjection</summary>

```lean
{I : Type u_1} →
  (M : CoxeterMatrix.{u_1} I) →
    (J : Set.{u_1} I) →
      ArtinNormalisers.Theorem18.Complement.{u_1} M J →
        ArtinNormalisers.Theorem18.OrbitSpace.{u_1} M J
```

Source definition/construction:

```lean
/-- The actual orbit map; the target carries precisely its quotient topology. -/
noncomputable def orbitProjection : Complement M J → OrbitSpace M J :=
  Quotient.mk (MulAction.orbitRel (Artin.coxeterNormalizerQuotient M J) (Complement M J))
```

</details>

## Immediate dependencies

Important prerequisite paths:

This entry is foundational within the selected twenty; its external and implementation dependencies remain in the exact record below.

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`ArtinNormalisers/Theorem18/Geometry.lean`](../../../../ArtinNormalisers/Theorem18/Geometry.lean)
- [`ArtinNormalisers/Theorem18/NormalizerAction.lean`](../../../../ArtinNormalisers/Theorem18/NormalizerAction.lean)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/verification.json`](../../../../deligne/evidence/theorem18-local-final/verification.json)
- [`docs/navigation/data/source-inventory.json`](../../data/source-inventory.json)
- [`docs/theorem18/github-evidence/run-43492004104/lean-theorem18-foundations-verification.json`](../../../theorem18/github-evidence/run-43492004104/lean-theorem18-foundations-verification.json)
- [`docs/theorem18/github-evidence/run-43492004104/lean-theorem18-foundations.zip`](../../../theorem18/github-evidence/run-43492004104/lean-theorem18-foundations.zip)
- [`docs/theorem18/github-evidence/run-43492004104/run.json`](../../../theorem18/github-evidence/run-43492004104/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/run.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/verification.json)
- [`docs/theorem18/reviews/foundations-a.json`](../../../theorem18/reviews/foundations-a.json)
- [`docs/theorem18/reviews/foundations-a.md`](../../../theorem18/reviews/foundations-a.md)
- [`docs/theorem18/reviews/foundations-b.json`](../../../theorem18/reviews/foundations-b.json)
- [`docs/theorem18/reviews/foundations-b.md`](../../../theorem18/reviews/foundations-b.md)
- [`docs/theorem18/source-inventory.json`](../../../theorem18/source-inventory.json)

[Successful final CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363). [Source-correspondence review A](../../reviews/source-correspondence-a.md) and [review B](../../reviews/source-correspondence-b.md).
