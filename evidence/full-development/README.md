# Full-lemma development records

These are real development commands and diagnostics, not a substitute for the
final source-bound verification under `evidence/full-local/`.

- `basic/`: Artin presentation/projection/parabolic wrappers and actual source
  dependency builds. The independent initial presentation draft was replaced
  by direct reuse of the exact verified TauCeti Artin model; it is retained
  only as a labeled development text artifact.
- `coxeter/`: minimal normalizer and conjugated-generator proof diagnostics.
- `lift/`: actual Artin normalizer-lifting proof diagnostics.
- `exact/`: quotient transport and full exact-sequence proof diagnostics.
- `vendor-cache.log`: scoped cache preparation for actual imported mathlib roots.
- `vendor-build.log`: all ten unchanged upstream modules built against the
  project's existing mathlib pin, without using upstream compiled artifacts.
- `provider-axioms.log`: 171 supplier declarations passed the transitive
  standard-axiom allowlist. `provider-replay.json` records successful official
  single-module replay of all ten suppliers and their actual log hashes.
- `full-root-build.log` and `full-axioms.log`: initial successful full aggregate
  build and audit of 69 project declarations, including private helpers.
- `verification-missing-supplier-aggregate/`: an actual final-harness attempt
  built the full proof and passed the project audit, then failed because the
  provider audit imported the optional supplier aggregate `TauCeti.olean`,
  which the package clean had removed and the full target did not require.
  The audit was corrected to import its three actual supplier entry modules
  directly. No mathematical proof or reviewed source changed. This failed
  record is preserved as `ok: false`; only the subsequent successful final
  record supplies completion evidence.

Individual author logs are genuine tool output; a failed attempt does not
describe the final source. Their scopes and exact checks are distinguished
from independent statement-review actions in the reviewers' reports.
