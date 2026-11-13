# Provider kernel replay evidence

The completed pass is `run-20261113T210310Z/verification.json`: all 359
authorized active provider modules were replayed by separate exact-module
`lake env leanchecker --verbose MODULE` processes. Four independent processes
ran concurrently locally; observed peak was four. Elapsed time was 776.98 s.
This is the bundled Lean kernel relative to each imported environment,
including imported mathlib; it is not an independent kernel implementation
or a fresh replay of mathlib.

`inputs.json` binds all 359 active and original upstream source hashes,
359 frozen compiled provider artifacts, provenance, license, compatibility
patches, configuration, toolchain executables and actual pinned mathlib
context. Stat checks ran before/after commands and while waiting; full hash
checks bound the beginning and end. The final record is successful only
after all 359 exit codes were zero and inputs remained unchanged.
Every command has its raw log, exit, real duration, source hashes and input
manifest reference. `postcheck.json` additionally verifies every raw-log
hash and exact replayed-module header, rechecks all bound file hashes, and
records the still-clean tracked mathlib state. `driver.py` preserves the
exact driver bytes bound by this successful pass.

`run-20261113T205839Z` is an intentionally stopped sequential partial
attempt: 28 completed module exits were zero, its verification has
`ok=false`, and cancellation notes retain the actual stopping reason and
the limit of the interrupted command record. No completion is claimed
for that attempt. All 359 modules were replayed afresh in the completed
four-worker pass. The current driver accepts `--workers 2` for the smaller
CI runner; no aggregate-prefix checking is used.

The separate final axiom audit is recorded in
`axiom-20261113T212608Z/verification.json`. It passed for all 359 imported
provider modules and 6,133 declarations, with matching complete type and
axiom records and only `propext`, `Classical.choice`, and `Quot.sound`.
`coverage.json` records every module's source hashes and declaration names;
the audit source and all frozen provider inputs are hash-bound. The source,
raw log and coverage SHA256s are in that audit's verification record.

These provider checks do not claim completion of the full ribbon-normalizer
landmark or Theorem 1.8; project statement reviews and verification are
separate obligations.
