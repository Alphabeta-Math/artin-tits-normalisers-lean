# Landmark 1 development limits and resolved failures

No original-article mathematical error was established. The failures below
concern package integration or Lean elaboration, not counterexamples.

- The first two supplier files retained their original `TauCeti.*` module
  paths. Lake also resolved these paths through the parent library and tried
  to read files absent from the unchanged parent vendor tree. The correction
  is a mechanical relocation to `ArtinLandmarkVendor.Geometric.*`, with one
  recorded import-path substitution in `Sign.lean`. Original exact bytes,
  both hashes, license and the patch are preserved. No statement, proof or
  mathematical namespace was changed.
- Creating the landmark manifest with `lake update` invoked mathlib's
  post-update cache hook. It decompressed already-cached prerequisites;
  the actual output reported no files to download. The subsequent scoped
  cache helper and CI set `MATHLIB_NO_CACHE_ON_UPDATE=1` and explicitly fetch
  only the actual import closure. No dependency pin or parent source changed.
- The first covering integration lacked an explicit `T2Space` instance for
  the named complement type. The inherited subtype topology is Hausdorff;
  exposing that instance fixed synthesis. Style warnings about local instance
  bindings were also removed. The final scientific modules build without
  warnings; no additional mathematical premise was added.
- The first audit harness left two mutable counters untyped. Lean inferred
  `MessageData` from later interpolation and could not elaborate the numeric
  operations. Its actual failed output is retained as
  `landmarks/evidence/development/audit-counter-inference-failure.log`.
  Adding `: Nat` annotations fixed the harness; a later successful audit
  checks all 38 expected modules. The failed run is not a certificate.

Complete raw logs for every early development command were not saved. The
final verification records retain every command, exit and log for their
actual successful run. No early failed build or preliminary reviewer report
is relabeled as successful final acceptance.

The previous parent package is not changed or re-certified by editing its
historical receipts. The new verifier checks all 65 parent input hashes and
the parent statement-review hashes against its archived successful CI record.
New verification has its own scope, source inventory, reviews and package.
Kernel replay uses the official checker relative to imported environments;
it does not claim a fresh replay of the entire parent library or mathlib.
