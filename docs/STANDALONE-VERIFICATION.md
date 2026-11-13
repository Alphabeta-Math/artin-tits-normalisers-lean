# Standalone repository verification

The standalone layout completed all 24 verification commands locally, using
source commit `a9ae006` and the exact proof/source-review bindings inherited
from the origin development. The record and original tool output are under
`evidence/dedicated-local/`.

This run rebuilt the project and vendored supplier sources, audited 69 project
and 171 supplier declarations against the standard axiom allowlist, and replayed
all seven scientific project modules and ten supplier modules individually.
The verifier also enforced both independent accepted statement reviews and
the unchanged upstream/source hashes.

The old source-bound records under `evidence/full-local/` and
`docs/full/github-evidence/run-43484468188/` describe the origin repository's
successful checks. They do not certify the adapted standalone script/README
inputs. The dedicated repository's own
[GitHub run 43486289665](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43486289665)
passed in 2m29s against commit `afb0f7bfa6dc36458da7322b7ed9e4b93cbbce35`.
All 24 commands exited zero. All 32 input-file hashes and both independent
review receipts match the standalone package; all downloaded log hashes match
the actual artifact's record. The artifact, complete compressed Actions log,
run metadata and checksums are retained under
`docs/full/github-evidence/run-43486289665/` beyond artifact retention expiry.
