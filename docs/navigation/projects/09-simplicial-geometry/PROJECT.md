# Finite simplicial arrangement geometry

The actual finite arrangement has the proved simplicial chamber hypotheses.

Kind: **Prerequisite**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

### Source correspondence for `ArtinNormalisers.Asphericity5.actualChamber_isSimplicialRegion`

Relation: **specialization**.

**Article:** [Corollary 6.14, proof, printed page 27](https://arxiv.org/pdf/2509.21915v3#page=27).

<details><summary>Original article statement extraction</summary>

```text
Proof. Note that XJ  is a complexified hyperplane complement from a real, central (since the
hyperplanes are linear) finite hyperplane arrangement in a vector space (recall that we are in
spherical-type). Moreover, the chambers of the real arrangement are open simplicial cones. There-
                                    C                   C     C
fore Deligne’s Theorem [9] applies, and XJ  is a K(π, 1). Since X J →X J /N(W, J) is a normal
                                      C
cover (see paragraph before (3.28)) and π1(X J /N(W, J), x) ∼= N(A, J) by Theorem 6.7, the result
follows.                                                  □

                                                                  C
```

</details>

Scope of this source link: **specialization**.

- Finite central relative arrangement simpliciality clause only; this declaration alone is not a Garside/fundamental-groupoid/asphericity theorem.

**Alphabeta Math:** [Spherical relative arrangements and Deligne topology](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-spherical-deligne-topology-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a finite-rank Coxeter system, let $J\subseteq S$, and use its relative space $\Theta_J$, relative cone $\mathrm{Cone}(J)$, relative hyperplanes $\mathcal H^J$, positive arrangement category $\mathcal D^+(J)$ and groupoid completion $\mathcal D(J)$. Suppose $W$ is finite, also called spherical type. Then $\mathrm{Cone}(J)^\circ=\Theta_J$, and $(\Theta_J,\mathcal H^J)$ is a finite central simplicial arrangement: its hyperplanes are finite in number, pass through the origin, and each chamber is a linear image of an open positive orthant in $\Theta_J$.

The category $\mathcal D^+(J)$ has a finite-type atomic categorical Garside structure. Thus its completion $\mathcal D(J)$ is a Garside groupoid in the sense of being the groupoid completion of that Garside category. It is equivalent to the fundamental groupoid $\pi_1(\mathcal X_J^{\mathbb C})$ of the relative complexified complement. These deductions use the finite simplicial hypotheses; no extension to a general nonsimplicial or infinite arrangement is asserted.
```

Scope of this source link: **specialization**.

- Finite central relative arrangement simpliciality clause only; this declaration alone is not a Garside/fundamental-groupoid/asphericity theorem.


- Finite central relative arrangement simpliciality clause only; this declaration alone is not a Garside/fundamental-groupoid/asphericity theorem.
- Lean uses the standard braid-presentation Artin group. The general all-types comparison with the topological Artin definition in article §2.2 is not separately formalized here. The actual finite-Coxeter relative-space fundamental-group and exact-diagram identifications proved in milestone4 are retained; this caveat does not deny those comparisons.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Asphericity5.actual_arrangement_simplicial_hypotheses` | [`asphericity/ArtinAsphericity/FiniteArrangement.lean:56`](../../../../asphericity/ArtinAsphericity/FiniteArrangement.lean#L56) | [`asphericity/ArtinAsphericity/FiniteArrangement.lean:56–75`](../../../../asphericity/ArtinAsphericity/FiniteArrangement.lean#L56) |
| `ArtinNormalisers.Asphericity5.actualChamber_isSimplicialRegion` | [`asphericity/ArtinAsphericity/Simpliciality.lean:168`](../../../../asphericity/ArtinAsphericity/Simpliciality.lean#L168) | [`asphericity/ArtinAsphericity/Simpliciality.lean:168–175`](../../../../asphericity/ArtinAsphericity/Simpliciality.lean#L168) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Asphericity5.actual_arrangement_simplicial_hypotheses</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) (J : Set.{u_1} I)
  [Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)],
  Set.Finite.{u_1} (ArtinNormalisers.Theorem18.restrictedArrangement.{u_1} M J) ∧
    (∀ (H : Submodule.{0, u_1} ℝ ↥(ArtinNormalisers.Theorem18.relativeSubspace.{u_1} J)),
        Membership.mem.{u_1, u_1} (ArtinNormalisers.Theorem18.restrictedArrangement.{u_1} M J) H →
          Ne.{u_1 + 1} H Top.top.{u_1} ∧
            IsClosed.{u_1} ↑H ∧
              Membership.mem.{u_1, u_1} H 0 ∧
                Eq.{1} (HAdd.hAdd.{0, 0, 0} (Module.finrank.{0, u_1} ℝ ↥H) 1)
                  (Module.finrank.{0, u_1} ℝ
                    ↥(ArtinNormalisers.Theorem18.relativeSubspace.{u_1} J))) ∧
      ∀ (C : ArtinNormalisers.Chamber3.ActualChamber.{u_1} M J),
        ∃ (n : ℕ) (b :
          Module.Basis.{0, 0, u_1} (Fin n) ℝ
            ↥(ArtinNormalisers.Theorem18.relativeSubspace.{u_1} J)),
          Eq.{u_1 + 1} (ArtinNormalisers.Chamber3.Chamber.region.{u_1, u_1} C)
              (Set.ofPred.{u_1} fun (x : ↥(ArtinNormalisers.Theorem18.relativeSubspace.{u_1} J)) =>
                ∀ (i : Fin n), LT.lt.{0} 0 (((Module.Basis.repr.{0, 0, u_1} b) x) i)) ∧
            Eq.{u_1 + 1} (closure.{u_1} (ArtinNormalisers.Chamber3.Chamber.region.{u_1, u_1} C))
                ↑(PointedCone.hull.{0, u_1} ℝ (Set.range.{u_1, 1} ⇑b)) ∧
              PointedCone.IsSimplicial.{0, u_1}
                (PointedCone.hull.{0, u_1} ℝ (Set.range.{u_1, 1} ⇑b))
```

</details>

<details><summary>ArtinNormalisers.Asphericity5.actualChamber_isSimplicialRegion</summary>

```lean
∀ {I : Type u_2} (M : CoxeterMatrix.{u_2} I) (J : Set.{u_2} I)
  [Finite.{u_2 + 1} (CoxeterMatrix.Group.{u_2} M)]
  (C : ArtinNormalisers.Chamber3.ActualChamber.{u_2} M J),
  ArtinNormalisers.Asphericity5.IsSimplicialRegion.{u_2}
    (ArtinNormalisers.Chamber3.Chamber.region.{u_2, u_2} C)
```

</details>

## Immediate dependencies

Important prerequisite paths:

This entry is foundational within the selected twenty; its external and implementation dependencies remain in the exact record below.

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`asphericity/ArtinAsphericity/FiniteArrangement.lean`](../../../../asphericity/ArtinAsphericity/FiniteArrangement.lean)
- [`asphericity/ArtinAsphericity/Simpliciality.lean`](../../../../asphericity/ArtinAsphericity/Simpliciality.lean)
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
