# Theorem 1.8: current proof entrypoint

The complete scientific endpoint for Garnier–Heng–Licata–Yacobi,
[arXiv:2509.21915v3](https://arxiv.org/abs/2509.21915v3), Theorem 1.8, now
has [root mathematical acceptance](docs/theorem18/landmarks/milestone5-root-acceptance.json)
in the separate [`deligne/`](deligne/README.md) package after both independent
GPT-6.1 Sol/high reviews and the successful [final local verification](deligne/evidence/theorem18-local-final/verification.json).
All 159 commands, including a real clean/rebuild and 64 fresh exact-module
kernel replays, passed. The audit covers 1,391 project and 475 new supplier
declarations, with standard axioms only and zero physical duplicates.
Fresh clean [GitHub CI43599459363](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363) also passed all 159 commands and 64 replays at science commit `3c389334729dbd37d26bdf52dd808e540aae6d37`. The [permanent archive](docs/theorem18/landmarks/github-evidence/run-43599459363/README.md) and [root CI closeout](docs/theorem18/landmarks/milestone5-closeout.json) bind the exact source, reviews and results. The immutable tag `theorem-1.8-verified` points to that science commit.

The endpoint is
[`ArtinNormalisers.Deligne5.theorem_1_8`](deligne/ArtinDeligne/Theorem18.lean).
For arbitrary `I`, `M : CoxeterMatrix I` with `[Finite M.Group]`, every
`J : Set I` and every actual complement basepoint, it combines:

- Both complete actual-map normalizer exact-sequence diagrams, including
  the normalized and positive-traversal conventions.
- The original relative complement as a K(`Artin.pureNormalizerImage M J`,1).
- Its original normalizer orbit space as a K(`Artin.normalizerQuotient M J`,1).

[`theorem_1_8_all_basepoints`](deligne/ArtinDeligne/Theorem18.lean) also
exposes the quotient conclusion at every orbit point;
`corollary_6_14` is the corresponding named corollary. Empty/full subsets,
rank zero, reducible and noncrystallographic finite types are included.

Read the [package guide](deligne/README.md) for rebuild commands and the
[final mathematical report](docs/theorem18/landmarks/milestone5-final-report.md)
for the actual proof architecture, predicate semantics, paper correspondence,
source reuse and verification limits. The [proof-source ledger](docs/provenance/GITHUB-PROOF-SOURCES.md)
retains the earlier accepted cohorts; the two new supplier inventories are
[weights](deligne/vendor/provenance-weights.json) and
[cell extensions](deligne/vendor/provenance-carriers.json).

The verified root README and milestone reports remain recoverable at
`theorem-1.8-verified`. Earlier “not yet proved” statuses describe their
recorded checkpoints. For the complete frozen verifier, use a worktree at
that tag; current navigation and proof-status summaries may change separately.
