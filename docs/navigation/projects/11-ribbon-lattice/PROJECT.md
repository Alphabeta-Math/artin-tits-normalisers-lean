# Ribbon lcms, gcds and simple prefixes

Actual reduced ribbon lattice operations and greatest simple prefixes.

Kind: **Prerequisite**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

No standalone article or Alphabeta statement is assigned to this local formalization result. It supports [Theorem 1.8, p. 3](https://arxiv.org/pdf/2509.21915v3#page=3) and the finite-arrangement argument in the [proof of Corollary 6.14, p. 27](https://arxiv.org/pdf/2509.21915v3#page=27). These are related target passages, not asserted original counterparts.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Homotopy5.positive_reduced_ribbon_lcm_left_with_tails` | [`homotopy/ArtinHomotopy/RibbonLattice.lean:192`](../../../../homotopy/ArtinHomotopy/RibbonLattice.lean#L192) | [`homotopy/ArtinHomotopy/RibbonLattice.lean:192–207`](../../../../homotopy/ArtinHomotopy/RibbonLattice.lean#L192) |
| `ArtinNormalisers.Homotopy5.positive_reduced_ribbon_gcd_left_with_tails` | [`homotopy/ArtinHomotopy/RibbonGcd.lean:88`](../../../../homotopy/ArtinHomotopy/RibbonGcd.lean#L88) | [`homotopy/ArtinHomotopy/RibbonGcd.lean:88–103`](../../../../homotopy/ArtinHomotopy/RibbonGcd.lean#L88) |
| `ArtinNormalisers.Homotopy5.greatest_simple_ribbon_prefix_with_tail` | [`homotopy/ArtinHomotopy/RibbonGcd.lean:140`](../../../../homotopy/ArtinHomotopy/RibbonGcd.lean#L140) | [`homotopy/ArtinHomotopy/RibbonGcd.lean:140–160`](../../../../homotopy/ArtinHomotopy/RibbonGcd.lean#L140) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Homotopy5.positive_reduced_ribbon_lcm_left_with_tails</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  {X Y Z : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M}
  {p q : ArtinNormalisers.Artin.Group.{u_1} M},
  ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M X Y p →
    ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M X Z q →
      ∃ (U : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M) (l :
        ArtinNormalisers.Artin.Group.{u_1} M),
        ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M X U l ∧
          (∃ (a : ArtinNormalisers.Artin.Group.{u_1} M),
              ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M Y U a ∧
                Eq.{u_1 + 1} l (HMul.hMul.{u_1, u_1, u_1} p a)) ∧
            (∃ (b : ArtinNormalisers.Artin.Group.{u_1} M),
                ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M Z U b ∧
                  Eq.{u_1 + 1} l (HMul.hMul.{u_1, u_1, u_1} q b)) ∧
              ∀ (V : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M)
                (r : ArtinNormalisers.Artin.Group.{u_1} M),
                ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M X V r →
                  ArtinNormalisers.Homotopy5.RibbonPrefix.{u_1} M p r →
                    ArtinNormalisers.Homotopy5.RibbonPrefix.{u_1} M q r →
                      ∃ (t : ArtinNormalisers.Artin.Group.{u_1} M),
                        ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M U V t ∧
                          Eq.{u_1 + 1} r (HMul.hMul.{u_1, u_1, u_1} l t)
```

</details>

<details><summary>ArtinNormalisers.Homotopy5.positive_reduced_ribbon_gcd_left_with_tails</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  {X Y Z : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M}
  {p q : ArtinNormalisers.Artin.Group.{u_1} M},
  ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M X Y p →
    ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M X Z q →
      ∃ (U : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M) (d :
        ArtinNormalisers.Artin.Group.{u_1} M),
        ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M X U d ∧
          (∃ (a : ArtinNormalisers.Artin.Group.{u_1} M),
              ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M U Y a ∧
                Eq.{u_1 + 1} p (HMul.hMul.{u_1, u_1, u_1} d a)) ∧
            (∃ (b : ArtinNormalisers.Artin.Group.{u_1} M),
                ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M U Z b ∧
                  Eq.{u_1 + 1} q (HMul.hMul.{u_1, u_1, u_1} d b)) ∧
              ∀ (V : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M)
                (e : ArtinNormalisers.Artin.Group.{u_1} M),
                ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M X V e →
                  ArtinNormalisers.Homotopy5.RibbonPrefix.{u_1} M e p →
                    ArtinNormalisers.Homotopy5.RibbonPrefix.{u_1} M e q →
                      ∃ (t : ArtinNormalisers.Artin.Group.{u_1} M),
                        ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M V U t ∧
                          Eq.{u_1 + 1} d (HMul.hMul.{u_1, u_1, u_1} e t)
```

</details>

<details><summary>ArtinNormalisers.Homotopy5.greatest_simple_ribbon_prefix_with_tail</summary>

```lean
∀ {I : Type u_1} (M : CoxeterMatrix.{u_1} I) [inst : Finite.{u_1 + 1} (CoxeterMatrix.Group.{u_1} M)]
  {X Y : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M} {p : ArtinNormalisers.Artin.Group.{u_1} M},
  ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M X Y p →
    ∃ (U : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M) (d : ArtinNormalisers.Artin.Group.{u_1} M)
      (a : ArtinNormalisers.Artin.Group.{u_1} M),
      ArtinNormalisers.Homotopy5.SimpleRibbon.{u_1} M X U d ∧
        ArtinNormalisers.Ribbon2.PositiveReducedArrow.{u_1} M U Y a ∧
          Eq.{u_1 + 1} p (HMul.hMul.{u_1, u_1, u_1} d a) ∧
            (∀ (V : ArtinNormalisers.Ribbon2.RibbonObject.{u_1} M)
                (e : ArtinNormalisers.Artin.Group.{u_1} M),
                ArtinNormalisers.Homotopy5.SimpleRibbon.{u_1} M X V e →
                  ArtinNormalisers.Homotopy5.RibbonPrefix.{u_1} M e p →
                    ArtinNormalisers.Homotopy5.RibbonPrefix.{u_1} M e d) ∧
              (Ne.{u_1 + 1} p 1 →
                Ne.{u_1 + 1} d 1 ∧
                  LT.lt.{0} (ArtinNormalisers.Ribbon2.degree.{u_1} M a)
                    (ArtinNormalisers.Ribbon2.degree.{u_1} M p))
```

</details>

## Immediate dependencies

Important prerequisite paths:

- [The Garside weight model](../12-garside-model/PROJECT.md)

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/verification.json`](../../../../deligne/evidence/theorem18-local-final/verification.json)
- [`docs/navigation/data/source-inventory.json`](../../data/source-inventory.json)
- [`docs/theorem18/landmarks/github-evidence/run-43590812660/homotopy-prerequisites-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43590812660/homotopy-prerequisites-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43590812660/run.json`](../../../theorem18/landmarks/github-evidence/run-43590812660/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43590812660/source-inventory.json`](../../../theorem18/landmarks/github-evidence/run-43590812660/source-inventory.json)
- [`docs/theorem18/landmarks/github-evidence/run-43590812660/verification.json`](../../../theorem18/landmarks/github-evidence/run-43590812660/verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/archive-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip`](../../../theorem18/landmarks/github-evidence/run-43599459363/deligne-theorem18-verification.zip)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/run.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/run.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-chunks.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/source-reassembly-verification.json)
- [`docs/theorem18/landmarks/github-evidence/run-43599459363/verification.json`](../../../theorem18/landmarks/github-evidence/run-43599459363/verification.json)
- [`homotopy/ArtinHomotopy/RibbonGcd.lean`](../../../../homotopy/ArtinHomotopy/RibbonGcd.lean)
- [`homotopy/ArtinHomotopy/RibbonLattice.lean`](../../../../homotopy/ArtinHomotopy/RibbonLattice.lean)
- [`homotopy/reviews/homotopy-prerequisites-a.json`](../../../../homotopy/reviews/homotopy-prerequisites-a.json)
- [`homotopy/reviews/homotopy-prerequisites-a.md`](../../../../homotopy/reviews/homotopy-prerequisites-a.md)
- [`homotopy/reviews/homotopy-prerequisites-b.json`](../../../../homotopy/reviews/homotopy-prerequisites-b.json)
- [`homotopy/reviews/homotopy-prerequisites-b.md`](../../../../homotopy/reviews/homotopy-prerequisites-b.md)

[Successful final CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363). [Source-correspondence review A](../../reviews/source-correspondence-a.md) and [review B](../../reviews/source-correspondence-b.md).
