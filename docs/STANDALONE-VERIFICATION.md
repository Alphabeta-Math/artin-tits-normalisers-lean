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
inputs. The dedicated repository's own GitHub verification will be archived
separately after execution.
