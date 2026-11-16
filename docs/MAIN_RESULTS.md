# Original main results: Theorems 1.3, 1.4 and 1.8

This is the main-results release. The separate investigation of new results from the open-questions/solutions page is preserved on a local, unpushed branch and is not part of this release.

| Main result | Exact formalization scope | Statements, proof paths and evidence |
|---|---|---|
| Theorem 1.3 / Theorem 4.7 | Arbitrary-rank algebraic covering; finite-rank geometry as explicitly directed from the portal. | [PROJECT](../theorems13-14/PROJECT.md#universalbrinkhowlettcover-theorem-13--47-universal-covering-wall-crossings-and-deck-quotient) · [Lean proof](../theorems13-14/Proofs/UniversalBrinkHowlettCover.lean) · [translation](../theorems13-14/translations/UniversalBrinkHowlettCover.json) · [compile/axioms](../theorems13-14/evidence/UniversalBrinkHowlettCover-compile.json) |
| Theorem 1.4 / Theorem 4.21 | Atomic Matsumoto at arbitrary Coxeter type; no spherical-type restriction. | [PROJECT](../theorems13-14/PROJECT.md#atomicmatsumoto-theorem-14--421-atomic-matsumoto) · [Lean proof](../theorems13-14/Proofs/AtomicMatsumoto.lean) · [translation](../theorems13-14/translations/AtomicMatsumoto.json) · [compile/axioms](../theorems13-14/evidence/AtomicMatsumoto-compile.json) |
| Theorem 1.8 | Finite actual Coxeter group, arbitrary subset and all actual basepoints; both exact diagrams and K(G,1) conclusions. | [PROJECT](navigation/projects/19-theorem-1-8/PROJECT.md) · [Lean proof](../deligne/ArtinDeligne/Theorem18.lean) · [verified CI](theorem18/landmarks/github-evidence/run-43599459363/verification.json) |

## Main-results prerequisites

[Theorems 1.3–1.4 PROJECT](../theorems13-14/PROJECT.md) records all 20 prerequisites and both main endpoints, including original article statements with result/page locators, direct Alphabeta URLs, accepted translations, immediate dependencies, proof-source files and compilation evidence. Its [external-proof ledger](../theorems13-14/EXTERNAL_PROOFS.md) preserves actual external uses and existing-repository suppliers.

[Theorem 1.8 proof guide](navigation/index.md) and [source/evidence atlas](navigation/data/evidence-atlas.json) retain the earlier finite-type proof and its verified source tag. Its general all-types topology-to-presentation identification is not a separately formalized theorem; the actual finite-space comparisons used in Theorem 1.8 are proved.

The finite-rank restriction on the geometric part of Theorem 1.3 is the owner-directed portal convention, not a new spherical-type assumption and not a defect-report classification. Its algebraic covering statement remains arbitrary-rank. Theorem 1.4 retains arbitrary Coxeter type.

## Rebuild the combined library

From the repository root:

```bash
cd theorems13-14
lake build
```

This package imports `ArtinDeligne` and builds the new main-results library. Its final [build log](../theorems13-14/evidence/final-build.txt) records a successful 19,480-job build. Each of its 22 endpoints also has a matching source hash, successful compilation and an axiom audit allowing only `propext`, `Classical.choice` and `Quot.sound`. The [state](../theorems13-14/state.json) records completion; accepted source-reading and endpoint-review evidence is preserved in its evidence directory.
