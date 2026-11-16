# Artin–Tits normalisers in Lean

Formal proofs for Garnier–Heng–Licata–Yacobi, [*Normalisers of parabolic subgroups of Artin–Tits groups and Tits cone intersections*, arXiv:2509.21915v3](https://arxiv.org/abs/2509.21915v3).

The original main results **Theorems 1.3, 1.4 and 1.8** are formally proved in this repository. [Main-results guide](docs/MAIN_RESULTS.md) links their statements, Lean proof files and compilation evidence. Theorems 1.3–1.4 and their 20 prerequisites passed the native Step 5 complete-library build and per-endpoint axiom checks; Theorem 1.8 retains its [clean CI archive](docs/theorem18/landmarks/github-evidence/run-43599459363/README.md) and immutable `theorem-1.8-verified` source tag.

New-result work from the open-questions/solutions page is preserved separately on an **unpushed local branch**; it is outside this main-results release.

## Start here

- [Theorems 1.3, 1.4 and 1.8](docs/MAIN_RESULTS.md): statements, formalization scope, proof files and evidence.
- [Theorems 1.3–1.4 PROJECT](theorems13-14/PROJECT.md): all accepted endpoints and prerequisites.
- [Detailed finite-type proof guide](docs/navigation/index.md): Theorem 1.8 and its supporting definitions/results.
- [Main-results dependency graph](docs/main-results-dependencies.mmd): 20 important results and definitions.
- [External Lean proofs and libraries](docs/navigation/external/modules.md): exact repositories, commits, source modules and proof references.
- [Proof architecture and mathematical scope](docs/theorem18/landmarks/milestone5-final-report.md).
- [Compilation and verification evidence](docs/navigation/data/evidence-atlas.json), [final CI archive](docs/theorem18/landmarks/github-evidence/run-43599459363/README.md), and [closeout](docs/theorem18/landmarks/milestone5-closeout.json).

## Main results

| Article result | Scope | Proof and source dossier |
|---|---|---|
| [Theorem 1.3](https://arxiv.org/pdf/2509.21915v3#page=2), p. 2 / Theorem 4.7, pp. 16–17 | Arbitrary-rank algebraic covering; finite-rank geometric convention directed by the owner | [PROJECT](theorems13-14/PROJECT.md#universalbrinkhowlettcover-theorem-13--47-universal-covering-wall-crossings-and-deck-quotient) · [proof](theorems13-14/Proofs/UniversalBrinkHowlettCover.lean) |
| [Theorem 1.4](https://arxiv.org/pdf/2509.21915v3#page=3), p. 3 / Theorem 4.21, p. 20 | Atomic Matsumoto at arbitrary Coxeter type | [PROJECT](theorems13-14/PROJECT.md#atomicmatsumoto-theorem-14--421-atomic-matsumoto) · [proof](theorems13-14/Proofs/AtomicMatsumoto.lean) |
| [Theorem 1.8](https://arxiv.org/pdf/2509.21915v3#page=3), p. 3 | Finite actual Coxeter group; all subsets/basepoints, exact diagrams and K(G,1) conclusions | [PROJECT](docs/navigation/projects/19-theorem-1-8/PROJECT.md) · [proof](deligne/ArtinDeligne/Theorem18.lean) |

See the dossiers for the full original and portal statements, all quantified assumptions, direct dependencies and verified source records.

## Dependency graph: 20 important results and definitions

This overview keeps the main-results branches and important prerequisites readable. The general Coxeter theorems use their own arbitrary-type constructions; the existing finite-type proof of Theorem 1.8 is retained. Exact immediate dependencies and rank conventions are recorded in the linked PROJECT files.

```mermaid
flowchart TD
  n1["1. Coxeter/Artin groups and normalizers"]
  n2["2. Relative cones and complements"]
  n3["3. Lemma 2.8 exact sequence"]
  n4["4. Orbit covering"]
  n5["5. Reduced ribbons"]
  n6["6. Ribbon presentation"]
  n7["7. Finite chamber/groupoid comparison"]
  n8["8. Compatible exact diagrams"]
  n9["9. Universal cover"]
  n10["10. Ribbon lattice"]
  n11["11. Garside weight model"]
  n12["12. Finite carriers and model nullity"]
  n13["13. Packet and coherent carriers"]
  n14["14. Actual cover comparison"]
  n15["15. Original-space asphericity"]
  n16["16. General BH groupoid and expressions"]
  n17["17. Chamber labels and wall paths"]
  n18["18. Theorem 1.3"]
  n19["19. Theorem 1.4"]
  n20["20. Theorem 1.8"]
  n1 --> n3
  n1 --> n5
  n1 --> n16
  n2 --> n4
  n2 --> n9
  n2 --> n17
  n3 --> n8
  n4 --> n7
  n5 --> n6
  n5 --> n7
  n5 --> n11
  n6 --> n8
  n7 --> n8
  n7 --> n13
  n9 --> n13
  n10 --> n12
  n11 --> n10
  n11 --> n13
  n12 --> n15
  n13 --> n14
  n10 --> n14
  n14 --> n15
  n8 --> n20
  n15 --> n20
  n16 --> n18
  n17 --> n18
  n16 --> n19
```

[Main-results guide](docs/MAIN_RESULTS.md) · [Theorems 1.3–1.4 prerequisites](theorems13-14/PROJECT.md) · [Detailed finite-type guide](docs/navigation/index.md). Exhaustive machine records remain in provenance.

## What each PROJECT.md contains

Each of the 20 important entries records:

1. Original article statements, with exact original result labels and printed page numbers.
2. Original Alphabeta Math statements, with direct item URLs.
3. Checked Lean translations and their file paths.
4. Explicit proof-source paths, including declaration locations when statement and proof share a file.
5. All immediate internal and external dependencies, with exact machine records.
6. Compilation, audit, kernel-replay and CI evidence paths.

Correspondence categories and scope differences are explicit. Local formalization helpers have no invented article or Alphabeta original; related parent results are linked separately. [Original-source snapshots and attribution](docs/navigation/data/attribution/README.md) retain exact source identities and verified public-item links.

## External Lean proofs used

[Theorems 1.3–1.4 external-proof ledger](theorems13-14/EXTERNAL_PROOFS.md) records their actual uses and existing-repository dependencies. The detailed reference counts below describe the preserved Theorem 1.8 compiled graph; they are not newly recomputed counts for the added package.

<!-- Root README fragment: resolve local links from the repository root. -->

All external Lean sources are listed below. Counts come from actual compiled type, value and structural references across the full recorded project frontier. Imported modules and selected supplier closures are recorded separately in the [complete source catalog](docs/navigation/external/modules.md) and [machine catalog](docs/navigation/external/catalog.json.gz). Per-result `PROJECT` pages link immediate external dependencies to their exact original source modules.

| Repository at exact commit | Role | Referenced theorems / definitions / other | Defining modules | Selected supplier units | License |
|---|---|---:|---:|---:|---|
| [leanprover/lean4@b35cb10cf2ce](https://github.com/leanprover/lean4/tree/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a) | Lean compiler/kernel, Init and Std foundations; Lean/Lake build SDK | 4,323 / 2,339 / 582 | 145 | — | [Apache-2.0](https://github.com/leanprover/lean4/blob/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a/LICENSE) |
| [leanprover-community/mathlib4@65d730f7150f](https://github.com/leanprover-community/mathlib4/tree/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9) | Mathematical foundation and proofs, definitions and structures referenced by actual compiled terms | 27,185 / 7,648 / 1,813 | 1,444 | — | [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/LICENSE) |
| [TauCetiProject/TauCeti@62bbc0596dc3](https://github.com/TauCetiProject/TauCeti/tree/62bbc0596dc3539d488232e4e924a338548ea0a9) | Selected Coxeter/Artin algebra and topology proof suppliers | 679 / 118 / 16 | 45 | 56 | [Apache-2.0](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE) |
| [openai/math@4eaee8754825](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae) | Selected positive Artin/ribbon algebra and realization/weight proof suppliers | 1,444 / 445 / 33 | 167 | 371 | [Apache-2.0](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/LICENSE) |
| [kangxyz/colib@bac5cab53eb6](https://github.com/kangxyz/colib/tree/bac5cab53eb6526e366e861d289253ec81aa89f0) | Selected cover-nerve realization, domination and simplex extension/gluing proof suppliers | 215 / 70 / 4 | 30 | 37 | [Apache-2.0](https://github.com/kangxyz/colib/blob/bac5cab53eb6526e366e861d289253ec81aa89f0/LICENSE) |
| [leanprover-community/batteries@4af7237d1462](https://github.com/leanprover-community/batteries/tree/4af7237d146261353907b06a01b6f3fc06cfa067) | Transitive library support; actual compiled theorem/definition dependencies as well as elaboration support | 117 / 58 / 19 | 13 | — | [Apache-2.0](https://github.com/leanprover-community/batteries/blob/4af7237d146261353907b06a01b6f3fc06cfa067/LICENSE) |
| [leanprover-community/aesop@7d11bfa88558](https://github.com/leanprover-community/aesop/tree/7d11bfa88558f8d3d90afdf6bd877ed70001498d) | Proof-search tooling plus actual compiled BuiltinRules dependencies | 2 / 1 / 0 | 1 | — | [Apache-2.0](https://github.com/leanprover-community/aesop/blob/7d11bfa88558f8d3d90afdf6bd877ed70001498d/LICENSE) |
| [leanprover-community/plausible@129d1ba9a16b](https://github.com/leanprover-community/plausible/tree/129d1ba9a16bc0660f46c79e9fb041ef5d5d80de) | Inherited testing/tactic infrastructure; no declaration in the recorded logical dependency graph | 0 / 0 / 0 | 0 | — | [Apache-2.0](https://github.com/leanprover-community/plausible/blob/129d1ba9a16bc0660f46c79e9fb041ef5d5d80de/LICENSE) |
| [leanprover-community/LeanSearchClient@c61286b7b63c](https://github.com/leanprover-community/LeanSearchClient/tree/c61286b7b63cbfd563b28e11e81d0a18233a044a) | Inherited theorem-search tooling; no declaration in the recorded logical dependency graph | 0 / 0 / 0 | 0 | — | [Apache-2.0](https://github.com/leanprover-community/LeanSearchClient/blob/c61286b7b63cbfd563b28e11e81d0a18233a044a/LICENSE) |
| [leanprover-community/import-graph@e5d5639bedc7](https://github.com/leanprover-community/import-graph/tree/e5d5639bedc7feecfbcb98e30b3bf26463d9f722) | Inherited import-graph/linter infrastructure; no declaration in the recorded logical dependency graph | 0 / 0 / 0 | 0 | — | [Apache-2.0](https://github.com/leanprover-community/import-graph/blob/e5d5639bedc7feecfbcb98e30b3bf26463d9f722/LICENSE) |
| [leanprover-community/ProofWidgets4@16259c0d07d6](https://github.com/leanprover-community/ProofWidgets4/tree/16259c0d07d61ee37d999d05b5cf96338b8daa11) | Inherited editor/widget infrastructure; no declaration in the recorded logical dependency graph | 0 / 0 / 0 | 0 | — | [Apache-2.0](https://github.com/leanprover-community/ProofWidgets4/blob/16259c0d07d61ee37d999d05b5cf96338b8daa11/LICENSE) |
| [leanprover-community/quote4@b0256621cb88](https://github.com/leanprover-community/quote4/tree/b0256621cb88178e9ad932a53633077b3029e621) | Inherited quotation/metaprogramming infrastructure; no declaration in the recorded logical dependency graph | 0 / 0 / 0 | 0 | — | [Apache-2.0](https://github.com/leanprover-community/quote4/blob/b0256621cb88178e9ad932a53633077b3029e621/LICENSE) |
| [leanprover/lean4-cli@c09cb1e4f1e6](https://github.com/leanprover/lean4-cli/tree/c09cb1e4f1e6e1c231a1175a12b681b075054a1b) | Inherited command-line build/tool support; no imported module or declaration in the recorded graph | 0 / 0 / 0 | 0 | — | [MIT](https://github.com/leanprover/lean4-cli/blob/c09cb1e4f1e6e1c231a1175a12b681b075054a1b/LICENSE) |

The nine inherited Lake packages are mathlib, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq and batteries, plus Cli. Their exact pins and licenses are included even where the graph has no declaration references. Lean v4.36.0-rc2 is pinned to commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`; its Init and Std declarations are counted as foundation dependencies.

The three selected scientific supplier repositories contribute 464 accepted source units; 242 units contain declarations reached by this graph. The remaining 222 units belong to the checked supplier import closures. Source ports, preserved originals, licenses, acceptance receipts and replay evidence are linked in the complete catalog. One audited project-root alias canonically defined in mathlib is recorded separately.

The scientific source is fixed by [`theorem-1.8-verified`](https://github.com/lazyinspirit/artin-tits-normalisers-lean/tree/theorem-1.8-verified), commit `3c389334729dbd37d26bdf52dd808e540aae6d37`. [Clean CI 43599459363](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363) and its [permanent source-bound archive](docs/theorem18/landmarks/github-evidence/run-43599459363/README.md) passed. The catalog records dependencies across the complete project frontier; it does not claim a contraction of the actual universal cover or a two-sided nerve homotopy equivalence.

## Original-source precision

[Source notes](docs/navigation/source-notes/README.md) preserve earlier qualified findings and a subsequently checked scope issue in [Remark 3.27, p. 13](docs/navigation/source-notes/remark-3-27.md). The infinite-dihedral counterexample concerns the unrestricted finite-CW assertion; the verified finite-type Theorem 1.8 is unaffected. This source review is distinct from the Lean proof catalog.

## Build and reproduce the verified evidence

Install [elan](https://github.com/leanprover/elan); the committed toolchain selects Lean `v4.36.0-rc2`. Mathlib is pinned to `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`.

To build the unchanged Lean proof sources from the current checkout:

```bash
cd deligne
python3 scripts/cache_prerequisites.py
lake build ArtinDeligne
```

Full evidence reproduction uses the verified tagged worktree because the archived verifier also binds the original README as an input. The current branch adds navigation documentation.

```bash
git fetch --tags
git worktree add --detach ../artin-tits-verified theorem-1.8-verified
cd ../artin-tits-verified/deligne
python3 scripts/cache_prerequisites.py
python3 scripts/verify.py --execute --mode final --output evidence/my-verification
```

To repeat the archived GitHub workflow at that source:

```bash
gh workflow run deligne.yml --ref theorem-1.8-verified
```

The verifier uses the official bundled kernel algorithm through an exact-module runner and checks all public/private/server declarations. Records distinguish fresh replays from pinned imported context and earlier successful verification packets. Detailed [verification limits](docs/theorem18/landmarks/milestone5-final-report.md#reproduction-and-verification-limits) and the [evidence atlas](docs/navigation/data/evidence-atlas.json) give the exact scope.

## Repository map and history

| Location | Contents |
|---|---|
| `ArtinNormalisers/`, root aggregates | Algebraic Lemma 2.8 and arrangement foundations |
| `theorems13-14/` | Original Theorems 1.3 and 1.4, reviewed translations, proofs, prerequisites and Step 5 evidence |
| `landmarks/` | Landmark 1: normalizer action and covering |
| `ribbons/` | Landmark 2: positive ribbons and presentation |
| `chambers/` | Landmark 3: actual chamber/groupoid comparison |
| `sequences/` | Landmark 4: compatible exact diagrams |
| `asphericity/`, `homotopy/`, `deligne/` | Landmark 5 and the completed Theorem 1.8 |
| `docs/navigation/` | Current result pages, graphs, source/evidence catalogs and regeneration tools |
| `docs/provenance/` | Full proof-source ledger, pins, original/ported source records and compiled dependency graphs |
| `docs/theorem18/landmarks/github-evidence/` | Permanent CI records and source archives |
| `docs/history/` | Historical README and record-navigation guide |

Scientific sources and historical evidence keep their original paths. The [previous README and its source context](docs/history/README.md) is preserved byte-for-byte; earlier milestone reports describe their own recorded checkpoints. The certified proof snapshot remains available through `theorem-1.8-verified`.
