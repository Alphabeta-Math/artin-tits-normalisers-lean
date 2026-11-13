# Lemma 2.8 kernel formalization closeout

This is the historical kernel-only milestone. The subsequent
[full algebraic formalization](full/REPORT.md) proves the normalizer lift,
quotient surjectivity and full short exact sequence, with separate source-bound
reviews and verification records. The records below retain their original scope.

The standalone Lake package in `formalizations/artin-normalisers/` proves the
general group-theoretic kernel argument underlying Lemma 2.8 of
arXiv:2509.21915v3 (PDF p. 6). It constructs the actual map between normalizer
quotients and proves both kernel-image equality and existence of a kernel
representative. Its four definitions and seven theorems have no surjectivity
assumption. Article-specific Artin/Coxeter constructions and the terminal
surjectivity/full short exact sequence are outside this milestone.

## Scientific and machine verification

- Two independent GPT-6.1 Sol/high agents accepted every exact definition and
  theorem statement after independent original-source reading. Their final JSON
  receipts bind all four proof/root files by SHA-256. Reviewer A also independently
  ran the ordinary build and axiom audit; reviewer B records semantic review only.
- The final local harness completed all nine commands with exit code 0, including
  a clean **package-scoped** build, compilation of all eleven printed signatures,
  transitive axiom allowlist checks for all 24 project declarations, and official
  kernel replay of each of the three scientific modules sequentially.
- Allowed transitive axioms are only `propext`, `Classical.choice`, `Quot.sound`.
  No `sorryAx`, added mathematical axioms or native-evaluation axioms were accepted.
- Lean is pinned to `v4.36.0-rc2`, mathlib to
  `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`, and all dependency revisions are
  committed in the Lake manifest. Exact commands, versions, hashes, durations,
  exits and real compiler/checker output are retained in `evidence/local/`.

The bundled checker's aggregate prefix invocation crashed locally with SIGSEGV.
The supported per-module invocations all succeed and are used by the harness.
This replays the project declarations using imported environments; it is not
an independent kernel implementation or a fresh replay of all mathlib. Failed
development commands remain accurately labeled in `evidence/development/`.

## External prerequisite search

The GitHub search outside mathlib examined pinned sources from normalizer-lean,
GraphCoveringTheory, group-approximation and lean-coxeter. No additional supplier
was accepted: inspected results were specialized, unrelated to the arbitrary
group theorem, or wrappers around already available mathlib APIs. Rejected
candidates were not presented as formally verified. Exact declarations,
revisions, applicability decisions and verification limits are documented in
`external-prerequisites.md`. No external source defect is asserted.

## Reproduction and GitHub evidence

From `formalizations/artin-normalisers/`, install elan, then run:

```bash
lake exe cache get Mathlib.GroupTheory.QuotientGroup.Basic
python3 scripts/verify.py --output evidence/reproduction
```

The script enforces both accepted review receipts and their matching source
hashes before checking. A scoped GitHub Actions workflow runs the same harness
and uploads genuine success/failure records for the exact GitHub source commit.
The local evidence uses exact input hashes to bind the checked working tree;
its starting Git HEAD is not misrepresented as already containing those files.
The fresh GitHub run [43478940011](https://github.com/lazyinspirit/workflow-engines/actions/runs/43478940011)
completed successfully in 6m9s against source commit
`cce0eae51b895ab80dace76438a4b0da04fe0415`. All nine recorded commands exited 0.
Its downloaded input hashes match the current proof/package inputs, its logs
match their recorded SHA-256 values, and both independent review receipts match.
The complete verification artifact, run metadata and compressed Actions log are
archived under [`github-evidence/run-43478940011/`](github-evidence/run-43478940011/),
with a checksum manifest. These records are retained in Git beyond the Actions
artifact's 90-day retention period.

The first GitHub run was cancelled during unscoped repository checkout, before
any proof check, to replace it with a sparse checkout of this pilot and its
reviews. Its cancellation log is separately labeled in the archive. The second
run is the successful verification cited above. The workflow-only checkout
change leaves all four reviewed proof/root source hashes unchanged.

The implementation and records are scoped to this pilot. Unrelated ongoing
workflow-engine edits and the published research collection are untouched.
