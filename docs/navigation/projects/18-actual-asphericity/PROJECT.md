# Asphericity of the original spaces

Actual universal-cover, complement and orbit-space asphericity at every point.

Kind: **Prerequisite**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

### Source correspondence for `ArtinNormalisers.Deligne5.actualComplement_isAspherical`

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

- Generated thm-finite-simplicial-asphericity states a general finite-central-simplicial-arrangement theorem AND CW structure. Lean endpoint here is the actual relative arrangement and literal TauCeti higher-homotopy predicate, with no general theorem/CW claim.
- Do not treat a fundamental-groupoid equivalence or simple connectedness as an asphericity proof.
- No blanket source-to-source match for all canonical-cell/partition/carrier constructions.

**Article:** [Section 3.5, construction and finite simplicial specialization, printed page 14](https://arxiv.org/pdf/2509.21915v3#page=14).

<details><summary>Original article statement extraction</summary>

```text
3.5. The Deligne groupoid. The Deligne groupoid was introduced in [9] to study the topology
of finite simplicial arrangements (and prove the K(π, 1) conjecture for finite real reflection groups).
Although our setting is more general than that of Deligne, the construction of the Deligne groupoid
can be carried out similarly. However, the key features proven by Deligne, namely that the Deligne
groupoid is a Garside groupoid equivalent to the fundamental groupoid of the complexified com-
plement, only hold (to our knowledge) in the setting of finite simplicial arrangements.
  To the locally-finite arrangement (Cone(J)◦, HJ), we associate an oriented graph on the set
of vertices Cham(J). To every pair of adjacent chambers we associate a 2-cycle, i.e. given two
adjacent chambers (x, I) and (y, K) there is one arrow (x, I) →(y, K) and another opposite arrow
(y, K) →(x, I). We continue to use the notation ωa,I as above to label these arrows.
 A path in this graph from (x, I) to (y, K) is a geodesic if it is a path of minimal length between
(x, I) and (y, K). Equivalently, it crosses every hyperplane H ∈HJ at most once.
  Define D+ := D+(J) as the category with:
     • objects given by Cham(J); and
     • morphisms HomD+((x, I), (y, K)) are paths from (x, I) to (y, K) modulo the relation gen-
       erated by the identification of any two geodesic paths with the same source and target.
The arrangement groupoid D := D(J) associated to (Cone(J)◦, HJ) is defined as the groupoid
completion of D+.  If Γ is of spherical-type, then (Cone(J)◦, HJ) = (ΘJ, HJ) is a finite simplicial
arrangement, and we call D the Deligne groupoid. In this case, D is equivalent to the fundamental
            C             C
groupoid of XJ , denoted π1(X J ) [9].
```

</details>

Scope of this source link: **specialization**.

- Generated thm-finite-simplicial-asphericity states a general finite-central-simplicial-arrangement theorem AND CW structure. Lean endpoint here is the actual relative arrangement and literal TauCeti higher-homotopy predicate, with no general theorem/CW claim.
- Do not treat a fundamental-groupoid equivalence or simple connectedness as an asphericity proof.
- No blanket source-to-source match for all canonical-cell/partition/carrier constructions.

**Alphabeta Math:** [Deligne asphericity used for the relative complement](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-finite-simplicial-asphericity-artin-tits-normalisers).

Original statement Markdown:

```text
Let $V$ be a finite-dimensional real vector space and let $\mathcal H$ be a finite collection of linear hyperplanes. Suppose every chamber, meaning every connected component of $V\setminus\bigcup_{H\in\mathcal H}H$, is an open simplicial cone: it is the image of an open positive orthant under a linear isomorphism onto $V$. Write $V_{\mathbb C}=V\otimes_{\mathbb R}\mathbb C$, with complex scalar multiplication $z\cdot(v\otimes w)=v\otimes zw$ and its finite-dimensional Euclidean topology. Then the complexified complement $M=V_{\mathbb C}\setminus\bigcup_{H\in\mathcal H}(H\otimes_{\mathbb R}\mathbb C)$ is nonempty and path-connected, admits a CW structure, and has vanishing homotopy groups in all degrees at least two. Choose a vertex $b$ of such a CW structure and put $\pi=\pi_1(M,b)$. With the identity identification of this fundamental group with $\pi$, the based space $(M,b)$ is a $K(\pi,1)$. Here a $K(\pi,1)$ means a connected based CW complex with a specified fundamental-group isomorphism to $\pi$ and vanishing higher homotopy groups; the latter vanishing is called asphericity.

In particular, let $(W,S)$ be a finite-rank Coxeter system with $W$ finite, and let $J\subseteq S$. For its relative space $\Theta_J$, relative hyperplanes $\mathcal H^J$ and relative complexified complement $\mathcal X_J^{\mathbb C}$, the space $\mathcal X_J^{\mathbb C}$ admits a CW structure and, after choosing a vertex basepoint, is a $K(\pi,1)$ for its own fundamental group with the identity identification.
```

Scope of this source link: **related-only**.

- Generated thm-finite-simplicial-asphericity states a general finite-central-simplicial-arrangement theorem AND CW structure. Lean endpoint here is the actual relative arrangement and literal TauCeti higher-homotopy predicate, with no general theorem/CW claim.
- Do not treat a fundamental-groupoid equivalence or simple connectedness as an asphericity proof.
- No blanket source-to-source match for all canonical-cell/partition/carrier constructions.

**Alphabeta Math:** [Spherical relative arrangements and Deligne topology](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-spherical-deligne-topology-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a finite-rank Coxeter system, let $J\subseteq S$, and use its relative space $\Theta_J$, relative cone $\mathrm{Cone}(J)$, relative hyperplanes $\mathcal H^J$, positive arrangement category $\mathcal D^+(J)$ and groupoid completion $\mathcal D(J)$. Suppose $W$ is finite, also called spherical type. Then $\mathrm{Cone}(J)^\circ=\Theta_J$, and $(\Theta_J,\mathcal H^J)$ is a finite central simplicial arrangement: its hyperplanes are finite in number, pass through the origin, and each chamber is a linear image of an open positive orthant in $\Theta_J$.

The category $\mathcal D^+(J)$ has a finite-type atomic categorical Garside structure. Thus its completion $\mathcal D(J)$ is a Garside groupoid in the sense of being the groupoid completion of that Garside category. It is equivalent to the fundamental groupoid $\pi_1(\mathcal X_J^{\mathbb C})$ of the relative complexified complement. These deductions use the finite simplicial hypotheses; no extension to a general nonsimplicial or infinite arrangement is asserted.
```

Scope of this source link: **related-only**.

- Generated thm-finite-simplicial-asphericity states a general finite-central-simplicial-arrangement theorem AND CW structure. Lean endpoint here is the actual relative arrangement and literal TauCeti higher-homotopy predicate, with no general theorem/CW claim.
- Do not treat a fundamental-groupoid equivalence or simple connectedness as an asphericity proof.
- No blanket source-to-source match for all canonical-cell/partition/carrier constructions.

- Actual finite-Coxeter relative-space higher-homotopy conclusion used in original Corollary6.14; supplied through a formal actual universal-cover/carrier comparison.

- Generated thm-finite-simplicial-asphericity states a general finite-central-simplicial-arrangement theorem AND CW structure. Lean endpoint here is the actual relative arrangement and literal TauCeti higher-homotopy predicate, with no general theorem/CW claim.
- Do not treat a fundamental-groupoid equivalence or simple connectedness as an asphericity proof.
- No blanket source-to-source match for all canonical-cell/partition/carrier constructions.
- Lean uses the standard braid-presentation Artin group. The general all-types comparison with the topological Artin definition in article §2.2 is not separately formalized here. The actual finite-Coxeter relative-space fundamental-group and exact-diagram identifications proved in milestone4 are retained; this caveat does not deny those comparisons.

### Source correspondence for `ArtinNormalisers.Deligne5.actualOrbit_isAspherical`

Relation: **specialization**.

**Alphabeta Math:** [Deligne asphericity used for the relative complement](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-finite-simplicial-asphericity-artin-tits-normalisers).

Original statement Markdown:

```text
Let $V$ be a finite-dimensional real vector space and let $\mathcal H$ be a finite collection of linear hyperplanes. Suppose every chamber, meaning every connected component of $V\setminus\bigcup_{H\in\mathcal H}H$, is an open simplicial cone: it is the image of an open positive orthant under a linear isomorphism onto $V$. Write $V_{\mathbb C}=V\otimes_{\mathbb R}\mathbb C$, with complex scalar multiplication $z\cdot(v\otimes w)=v\otimes zw$ and its finite-dimensional Euclidean topology. Then the complexified complement $M=V_{\mathbb C}\setminus\bigcup_{H\in\mathcal H}(H\otimes_{\mathbb R}\mathbb C)$ is nonempty and path-connected, admits a CW structure, and has vanishing homotopy groups in all degrees at least two. Choose a vertex $b$ of such a CW structure and put $\pi=\pi_1(M,b)$. With the identity identification of this fundamental group with $\pi$, the based space $(M,b)$ is a $K(\pi,1)$. Here a $K(\pi,1)$ means a connected based CW complex with a specified fundamental-group isomorphism to $\pi$ and vanishing higher homotopy groups; the latter vanishing is called asphericity.

In particular, let $(W,S)$ be a finite-rank Coxeter system with $W$ finite, and let $J\subseteq S$. For its relative space $\Theta_J$, relative hyperplanes $\mathcal H^J$ and relative complexified complement $\mathcal X_J^{\mathbb C}$, the space $\mathcal X_J^{\mathbb C}$ admits a CW structure and, after choosing a vertex basepoint, is a $K(\pi,1)$ for its own fundamental group with the identity identification.
```

Scope of this source link: **related-only**.

- Generated thm-finite-simplicial-asphericity states a general finite-central-simplicial-arrangement theorem AND CW structure. Lean endpoint here is the actual relative arrangement and literal TauCeti higher-homotopy predicate, with no general theorem/CW claim.
- Do not treat a fundamental-groupoid equivalence or simple connectedness as an asphericity proof.
- No blanket source-to-source match for all canonical-cell/partition/carrier constructions.
- The orbit-space asphericity follows from actual-complement asphericity by the proved surjective normal-covering higher-homotopy transfer. These complement/Garside statements are related inputs, not direct specializations asserting asphericity of the quotient X/Q.

**Alphabeta Math:** [Spherical relative arrangements and Deligne topology](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-spherical-deligne-topology-artin-tits-normalisers).

Original statement Markdown:

```text
Let $(W,S)$ be a finite-rank Coxeter system, let $J\subseteq S$, and use its relative space $\Theta_J$, relative cone $\mathrm{Cone}(J)$, relative hyperplanes $\mathcal H^J$, positive arrangement category $\mathcal D^+(J)$ and groupoid completion $\mathcal D(J)$. Suppose $W$ is finite, also called spherical type. Then $\mathrm{Cone}(J)^\circ=\Theta_J$, and $(\Theta_J,\mathcal H^J)$ is a finite central simplicial arrangement: its hyperplanes are finite in number, pass through the origin, and each chamber is a linear image of an open positive orthant in $\Theta_J$.

The category $\mathcal D^+(J)$ has a finite-type atomic categorical Garside structure. Thus its completion $\mathcal D(J)$ is a Garside groupoid in the sense of being the groupoid completion of that Garside category. It is equivalent to the fundamental groupoid $\pi_1(\mathcal X_J^{\mathbb C})$ of the relative complexified complement. These deductions use the finite simplicial hypotheses; no extension to a general nonsimplicial or infinite arrangement is asserted.
```

Scope of this source link: **related-only**.

- Generated thm-finite-simplicial-asphericity states a general finite-central-simplicial-arrangement theorem AND CW structure. Lean endpoint here is the actual relative arrangement and literal TauCeti higher-homotopy predicate, with no general theorem/CW claim.
- Do not treat a fundamental-groupoid equivalence or simple connectedness as an asphericity proof.
- No blanket source-to-source match for all canonical-cell/partition/carrier constructions.
- The orbit-space asphericity follows from actual-complement asphericity by the proved surjective normal-covering higher-homotopy transfer. These complement/Garside statements are related inputs, not direct specializations asserting asphericity of the quotient X/Q.

**Alphabeta Math:** [Spherical normaliser quotient classifying spaces](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-cor-normaliser-kpi-artin-tits-normalisers).

Original statement Markdown:

```text
Assume the Axiom of Choice. Let $(W,S)$ be a finite-rank spherical Coxeter system, meaning that $W$ is finite, and let $J\subseteq S$. Let $A$ be the associated Artin–Tits group and $P$ the kernel of its standard projection to $W$. For $G=W,A$, let $G_J$ be the standard parabolic subgroup generated by the generators indexed by $J$, and put $N(G,J)=\operatorname{Norm}_G(G_J)/G_J$, where the normaliser consists of the elements conjugating $G_J$ to itself. Let $N(P,J)$ be the image of $P\cap\operatorname{Norm}_A(A_J)$ in $N(A,J)$.

Let $X=\mathcal X_J^{\mathbb C}$ be the relative complexified hyperplane complement. The induced action of $N(W,J)$ gives a quotient $X/N(W,J)$. Then $X$ is a $K(N(P,J),1)$ and $X/N(W,J)$ is a $K(N(A,J),1)$. Here $K(G,1)$ means a path-connected space whose fundamental group is isomorphic to $G$ and whose homotopy groups in all degrees at least two vanish.
```

Scope of this source link: **specialization**.

- This Lean declaration proves the higher-homotopy-vanishing clause for the actual quotient, not by itself the full named fundamental-group identification or a CW structure.
- The orbit-space asphericity follows from actual-complement asphericity by the proved surjective normal-covering higher-homotopy transfer. These complement/Garside statements are related inputs, not direct specializations asserting asphericity of the quotient X/Q.

- Actual finite-Coxeter relative-space higher-homotopy conclusion used in original Corollary6.14; supplied through a formal actual universal-cover/carrier comparison.
- The orbit-space asphericity follows from actual-complement asphericity by the proved surjective normal-covering higher-homotopy transfer. These complement/Garside statements are related inputs, not direct specializations asserting asphericity of the quotient X/Q.

- Generated thm-finite-simplicial-asphericity states a general finite-central-simplicial-arrangement theorem AND CW structure. Lean endpoint here is the actual relative arrangement and literal TauCeti higher-homotopy predicate, with no general theorem/CW claim.
- Do not treat a fundamental-groupoid equivalence or simple connectedness as an asphericity proof.
- No blanket source-to-source match for all canonical-cell/partition/carrier constructions.
- Lean uses the standard braid-presentation Artin group. The general all-types comparison with the topological Artin definition in article §2.2 is not separately formalized here. The actual finite-Coxeter relative-space fundamental-group and exact-diagram identifications proved in milestone4 are retained; this caveat does not deny those comparisons.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Deligne5.actualUniversalCover_isAspherical` | [`deligne/ArtinDeligne/UniversalCoverComparison.lean:52`](../../../../deligne/ArtinDeligne/UniversalCoverComparison.lean#L52) | [`deligne/ArtinDeligne/UniversalCoverComparison.lean:52–59`](../../../../deligne/ArtinDeligne/UniversalCoverComparison.lean#L52) |
| `ArtinNormalisers.Deligne5.actualComplement_isAspherical` | [`deligne/ArtinDeligne/Theorem18.lean:90`](../../../../deligne/ArtinDeligne/Theorem18.lean#L90) | [`deligne/ArtinDeligne/Theorem18.lean:90–97`](../../../../deligne/ArtinDeligne/Theorem18.lean#L90) |
| `ArtinNormalisers.Deligne5.actualOrbit_isAspherical` | [`deligne/ArtinDeligne/Theorem18.lean:99`](../../../../deligne/ArtinDeligne/Theorem18.lean#L99) | [`deligne/ArtinDeligne/Theorem18.lean:99–106`](../../../../deligne/ArtinDeligne/Theorem18.lean#L99) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Deligne5.actualUniversalCover_isAspherical</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (J : Set.{u_1} I) (q : ArtinNormalisers.Asphericity5.ComplementUniversalCover.{u_1} M J),
  TauCeti.IsAspherical.{u_1} (ArtinNormalisers.Asphericity5.ComplementUniversalCover.{u_1} M J) q
```

</details>

<details><summary>ArtinNormalisers.Deligne5.actualComplement_isAspherical</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (J : Set.{u_1} I) (x : ArtinNormalisers.Theorem18.Complement.{u_1} M J),
  TauCeti.IsAspherical.{u_1} (ArtinNormalisers.Theorem18.Complement.{u_1} M J) x
```

</details>

<details><summary>ArtinNormalisers.Deligne5.actualOrbit_isAspherical</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  (J : Set.{u_1} I) (y : ArtinNormalisers.Theorem18.OrbitSpace.{u_1} M J),
  TauCeti.IsAspherical.{u_1} (ArtinNormalisers.Theorem18.OrbitSpace.{u_1} M J) y
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [Higher homotopy vanishing of the model](../14-model-asphericity/PROJECT.md)
- [Comparison with the actual universal cover](../17-cover-comparison/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`deligne/ArtinDeligne/Theorem18.lean`](../../../../deligne/ArtinDeligne/Theorem18.lean)
- [`deligne/ArtinDeligne/UniversalCoverComparison.lean`](../../../../deligne/ArtinDeligne/UniversalCoverComparison.lean)
- [`deligne/evidence/theorem18-local-final/coverage.json`](../../../../deligne/evidence/theorem18-local-final/coverage.json)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log`](../../../../deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log)
- [`deligne/evidence/theorem18-local-final/logs/replay-034-ArtinDeligne.Theorem18.log`](../../../../deligne/evidence/theorem18-local-final/logs/replay-034-ArtinDeligne.Theorem18.log)
- [`deligne/evidence/theorem18-local-final/logs/replay-035-ArtinDeligne.UniversalCoverComparison.log`](../../../../deligne/evidence/theorem18-local-final/logs/replay-035-ArtinDeligne.UniversalCoverComparison.log)
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
