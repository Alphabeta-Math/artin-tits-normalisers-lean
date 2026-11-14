# The coherent carrier homotopy

Constructs the genuine numerable comparison homotopy from proved local carrier conditions.

Kind: **Prerequisite**. Verified source: `theorem-1.8-verified` (`3c389334729dbd37d26bdf52dd808e540aae6d37`).

[Important results index](../../index.md).

## Original statements

No standalone article or Alphabeta statement is assigned to this local formalization result. It supports [Theorem 1.8, p. 3](https://arxiv.org/pdf/2509.21915v3#page=3) and the finite-arrangement argument in the [proof of Corollary 6.14, p. 27](https://arxiv.org/pdf/2509.21915v3#page=27). These are related target passages, not asserted original counterparts.

## Lean translation and proof files

Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.

| Declaration | Translation file | Proof / construction file |
|---|---|---|
| `ArtinNormalisers.Deligne5.numerableCarrierHomotopy` | [`deligne/ArtinDeligne/NumerableCarrierHomotopy.lean:241`](../../../../deligne/ArtinDeligne/NumerableCarrierHomotopy.lean#L241) | [`deligne/ArtinDeligne/NumerableCarrierHomotopy.lean:241–282`](../../../../deligne/ArtinDeligne/NumerableCarrierHomotopy.lean#L241) |

Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.

<details><summary>ArtinNormalisers.Deligne5.numerableCarrierHomotopy</summary>

```lean
{X : Type u} →
  [inst : TopologicalSpace.{u} X] →
    {ι : Type v} →
      [inst_1 : LinearOrder.{v} ι] →
        (W : ι → Set.{u} X) →
          (∀ (i : ι), IsOpen.{u} (W i)) →
            (ρ : PartitionOfUnity.{v, u} ι X) →
              (hρ : PartitionOfUnity.IsSubordinate.{v, u} ρ W) →
                (C : Finset.{v} ι → Set.{u} X) →
                  (∀ (F : Finset.{v} ι),
                      Finset.Nonempty.{v} F →
                        Topology.NumerableConnectorCover.IsNerveFace.{u, v} W F →
                          ContractibleSpace.{u} ↑(C F)) →
                    (∀ {A B : Finset.{v} ι},
                        A ⊆ B →
                          Finset.Nonempty.{v} A →
                            Topology.NumerableConnectorCover.IsNerveFace.{u, v} W B → C A ⊆ C B) →
                      (∀ (F : Finset.{v} ι),
                          Finset.Nonempty.{v} F →
                            Topology.NumerableConnectorCover.IsNerveFace.{u, v} W F →
                              ArtinNormalisers.Deligne5.coverFaceParameter.{u, v} W F ⊆ C F) →
                        (r :
                            ContinuousMap.{v, u} (ArtinNormalisers.Deligne5.CoverWeights.{u, v} W)
                              X) →
                          (∀ (F : Finset.{v} ι),
                              Finset.Nonempty.{v} F →
                                Topology.NumerableConnectorCover.IsNerveFace.{u, v} W F →
                                  ∀ (w : ArtinNormalisers.Deligne5.CoverWeights.{u, v} W),
                                    Finsupp.support.{v, 0}
                                          (OAI.HarmonicArtin.OrderWeights.weights.{v} ↑w) ⊆
                                        F →
                                      Membership.mem.{u, u} (C F) (r w)) →
                            ContinuousMap.Homotopy.{u, u}
                              (ContinuousMap.comp.{u, v, u} r
                                (ArtinNormalisers.Deligne5.numerableCoverClassifier.{u, v} W ρ hρ))
                              (ContinuousMap.id.{u} X)
```

Source definition/construction:

```lean
/-- Monotone contractible carriers construct the actual numerable comparison
homotopy. The local face homotopies are produced by parameterized HEP and are
not input data. The original common-intersection spaces need not be contractible. -/
noncomputable def numerableCarrierHomotopy (W : ι → Set X)
    (hW : ∀ i, IsOpen (W i)) (ρ : PartitionOfUnity ι X) (hρ : ρ.IsSubordinate W)
    (C : Finset ι → Set X)
    (hC : ∀ F, F.Nonempty → IsNerveFace W F → ContractibleSpace (C F))
    (hmono : ∀ {A B}, A ⊆ B → A.Nonempty → IsNerveFace W B → C A ⊆ C B)
    (hinter : ∀ F, F.Nonempty → IsNerveFace W F → coverFaceParameter W F ⊆ C F)
    (r : C(CoverWeights W, X))
    (hr : ∀ F, F.Nonempty → IsNerveFace W F → ∀ w : CoverWeights W,
      w.val.weights.support ⊆ F → r w ∈ C F) :
    ContinuousMap.Homotopy (r.comp (numerableCoverClassifier W ρ hρ)) (ContinuousMap.id X) := by
  let D : FiniteCarrierData ι X :=
    { admissible := IsNerveFace W
      hereditary := fun h hF ↦ hF.mono h
      carrier := C
      contractible := hC
      monotone := hmono }
  let R := coverFaceParameter W
  let hR : Antitone R := coverFaceParameter_antitone W
  let f₀ : ParameterizedCarrierFamily D R hR :=
    { map := fun F hne hF ↦
        ⟨fun p ↦ r (numerableFaceChart W F hF p.2),
          r.continuous.comp ((continuous_numerableFaceChart W F hne hF).comp continuous_snd)⟩
      carried := fun F hne hF _x z ↦
        hr F hne hF _ (numerableFaceChart_support_subset W F hF z)
      compatible := fun _ _ ha hb hAB _ z ↦
        congrArg r (numerableFaceChart_map W hAB ha hb z) }
  let f₁ : ParameterizedCarrierFamily D R hR :=
    { map := fun _ _ _ ↦ ⟨fun p ↦ p.1.val, continuous_subtype_val.comp continuous_fst⟩
      carried := fun F hne hF x _ ↦ hinter F hne hF x.property
      compatible := fun _ _ _ _ _ _ _ ↦ rfl }
  let H := f₀.homotopy f₁
  refine numerableFaceTracksHomotopy W hW ρ hρ r
    (fun F hne hF ↦ (H.hom F hne hF).toContinuousMap) ?_ ?_ ?_
  · intro A B hA hB ha hb hAB t x z
    exact H.compatible hA hB ha hb hAB t x z
  · intro F hne hF x z
    exact (H.hom F hne hF).apply_zero (x, z)
  · intro F hne hF x z
    exact (H.hom F hne hF).apply_one (x, z)
```

</details>

## Immediate dependencies

Important prerequisite paths:

This entry is foundational within the selected twenty; its external and implementation dependencies remain in the exact record below.

[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.

## Compilation and verification evidence

The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.

- [`deligne/ArtinDeligne/NumerableCarrierHomotopy.lean`](../../../../deligne/ArtinDeligne/NumerableCarrierHomotopy.lean)
- [`deligne/evidence/theorem18-local-final/coverage.json`](../../../../deligne/evidence/theorem18-local-final/coverage.json)
- [`deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log`](../../../../deligne/evidence/theorem18-local-final/logs/build-exact-frontier.log)
- [`deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log`](../../../../deligne/evidence/theorem18-local-final/logs/project-statements-axioms-physical.log)
- [`deligne/evidence/theorem18-local-final/logs/replay-026-ArtinDeligne.NumerableCarrierHomotopy.log`](../../../../deligne/evidence/theorem18-local-final/logs/replay-026-ArtinDeligne.NumerableCarrierHomotopy.log)
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
