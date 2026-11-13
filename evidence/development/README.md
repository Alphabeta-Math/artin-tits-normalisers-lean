# Author development checks

These are development records, not final source-bound verification evidence.
Commands ran in `formalizations/artin-normalisers/`, with `/home/lazyinspirit/.elan/bin/lake`.
Logs preserve compiler output as produced. The final harness is root-owned.

| Command | Exit | Output |
| --- | --- | --- |
| `lake env lean ArtinNormalisers/NormalizerMap.lean` (before complete cache) | 1 | Missing `ImportGraph.Lean.Syntax.olean`; copied diagnostic in `early-failures.log` |
| `lake env lean ArtinNormalisers/NormalizerMap.lean` (initial subgroup dot notation) | 1 | Invalid `A.normalizer` field notation; copied diagnostics in `early-failures.log` |
| `lake env lean ArtinNormalisers/NormalizerMap.lean` (first explicit normalizer call) | 1 | Required an explicit set coercion; copied diagnostics in `early-failures.log` |
| `lake env lean ArtinNormalisers/NormalizerMap.lean` (explicit set coercions) | 0 | No output |
| `lake build ArtinNormalisers.NormalizerMap` | 0 | Built module; old-style module import warnings |
| `lake env lean ArtinNormalisers/QuotientMap.lean` | 0 | No output |
| `lake build ArtinNormalisers.QuotientMap` | 0 | `quotient-build.log` |
| `lake env lean ArtinNormalisers/Kernel.lean` (first attempt) | 1 | `kernel-lean-attempt-1.log` |
| `lake env lean ArtinNormalisers/Kernel.lean` (second attempt) | 0 | `kernel-lean-attempt-2.log` (empty output) |
| `lake build` | 0 | `root-build.log` |
| `lake build` (current module format, public imports, exposed public declarations) | 0 | `module-migration-build.log`; no warnings |

The first kernel attempt's `sorry` warning is Lean's error recovery after an
ill-typed definition, not a proof hole in the final source. The second attempt
and root build succeed. Earlier diagnostics were copied from actual tool output
after those commands; later logs were captured directly with `tee` and
`set -o pipefail`. No failing source snapshot is claimed or retained.

## Orchestrator audit and harness development

- The first audit probe failed because an unannotated counter was inferred as
  `MessageData`. The counter was corrected to `Nat`. That initial diagnostic
  was displayed in tool output but not saved as a complete log.
- `audit-attempt.log`: exit 1 while the audit used module syntax and the root
  package had not yet migrated; the actual diagnostic rejects that import.
- `audit-attempt-2.log`: exit 0 after migration; all 11 signatures printed and
  all 24 project declarations passed the transitive axiom allowlist.
- `kernel-replay-attempt.log`, `kernel-replay-paranoid.log` and
  `kernel-replay-source.log`: actual empty diagnostics for aggregate replay
  attempts ending in SIGSEGV (exit 139). See `kernel-replay-diagnosis.md` for
  the supported successful sequential alternative and its limits.
- `verification-unscoped-clean-attempt/`: an actual harness run used bare
  `lake clean`, which removed dependency outputs as well as project outputs.
  The orchestrator terminated its unnecessary dependency rebuild; the recorded
  build return code is `-15` (SIGTERM), not a mathematical proof failure.
  The imported dependency cache was restored with
  `lake exe cache get Mathlib.GroupTheory.QuotientGroup.Basic` (exit 0).
  The final harness uses `lake clean artin-normalisers`, the documented
  package-scoped command, and is verified separately under `evidence/local/`.

These development records preserve real failures; none counts as final passing
verification. Historical input hashes in the interrupted harness record bind
its earlier inputs and are not claimed to describe the corrected final script.
