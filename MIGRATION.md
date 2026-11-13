# Dedicated article formalization repository

The owner requested a public repository dedicated to Lean proofs of items from
arXiv:2509.21915v3. This repository is that standalone project.

## Original source and exact preservation

The source was exported from `lazyinspirit/workflow-engines` commit
`b41b7634c78cd3927dd2216246203535ad93d248`, using only its tracked Lean package,
plans, reviews and verification evidence. No engine implementation, private
runtime state, credentials, article-serving corpus or unrelated research was
copied.

| Original location | Dedicated repository location |
| --- | --- |
| `formalizations/artin-normalisers/` | repository root |
| `research/lean-lemma28/` | `docs/` |
| scoped monorepo CI | `.github/workflows/lean.yml` |

All nine reviewed project proof/root source files and all ten upstream supplier
source files retain their exact reviewed bytes and hashes. The two independent
review receipts and source inventory are also preserved byte for byte. Only
packaging changes were required: the verifier's review-directory location,
README links, ignore rules, repository license, and standalone CI paths.

The package uses Apache-2.0, consistent with the retained upstream supplier
license and headers. The paper's authors are credited for the mathematical
article; the formalization was developed with GPT-6.1 Sol/high agents and
independent agent statement reviews under the repository owner's direction.

## Historical evidence and current verification

Copied records under `evidence/` and `docs/` are historical evidence for their
recorded source snapshots. Absolute paths and monorepo references in those
records describe where those actions actually occurred; they were not rewritten
to pretend they ran here. In particular, old input hashes involving README or
verification scripts are not claimed to match the adapted packaging.

The standalone verifier checks the unchanged mathematical source hashes and
review receipts, then creates new source-bound build, axiom and kernel-replay
records for this repository. Fresh GitHub Actions records identify this
repository's actual checked commit. The script retains all failed records as
failures and accepts no new mathematical assumptions during migration.

Future article results should be added as new source modules with exact source
locators, faithful formal statements, independently reviewed definitions and
hypotheses, pinned useful dependencies, genuine build/axiom/replay records and
explicit scope limits. The current completed theorem is the full algebraic
Lemma 2.8 in the standard presentation-defined Artin model; the separate
topological/presentation equivalence is not formalized.
