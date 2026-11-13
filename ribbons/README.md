# Reduced ribbon normalizers

This optional Lake package develops landmark 2 of the article formalization:
the actual reduced ribbon vertex group, its map to the existing Artin
normalizer quotient, the semidirect decomposition, and a complete presentation
by chosen lcm relations. The entry point is [ArtinRibbons.lean](ArtinRibbons.lean);
the combined endpoints are in [Landmark2.lean](ArtinRibbons/Landmark2.lean).
The article's specifically distinguished standard-path classification is not
claimed by these endpoints.

**Full Theorem 1.8 remains unproved.** Geometric groupoid comparisons,
compatibility with geometric fundamental groups, and asphericity are separate
landmarks. Project statement reviews and the overall verifier are separate
from the provider checks below.

From the repository root, with Python 3, Git and the pinned Lean toolchain:

```bash
python3 ribbons/scripts/cache_prerequisites.py
python3 ribbons/scripts/verify.py --fresh-provider-replay --provider-workers 2
```

The full verifier writes a new timestamped evidence directory. It fetches no
dependencies itself. It performs fresh provider replay by default; reusing an
existing local certificate requires an explicit `--provider-record` and exact
source, compiled artifact, executable and log hash checks. Individual commands:

```bash
cd ribbons
lake build ArtinRibbons
lake env lean ProviderAudit.lean
lake env lean ProviderPhysicalAudit.lean
python3 scripts/replay_providers.py --workers 2
```

The cache helper checks that the child inherits the parent's exact dependency
pins and toolchain. It uses the committed manifests without `lake update`,
can share the parent's gitignored dependency directory through a relative
symlink, and fetches **whole Mathlib**, required by the upstream `import Mathlib`
statements. `--plan` displays its validated pins and command without writing
or fetching. Fresh CI must fetch that full closure; the original local builds
used an existing cache. `scripts/verify.py` adds the complete
project review/build/audit/replay checks; CI requests fresh provider replay.

The 359 OAI provider modules come from openai/math commit
`4eaee87548250b2682affda7d05d947c05554bae`, under Apache-2.0. Original bytes,
active hashes, dependency edges and exact patches are retained under
[vendor/](vendor/README.md). Seven compatibility ports preserve all mathematical
definitions, statements and hypotheses: six induction alternative-label
renames and one explicit multiplication congruence replacing a timed-out
broad tactic. Legacy module-system and deprecated-name warnings remain.

The final provider checks on 2026-11-14 passed:

- [Axiom audit](evidence/providers/axiom-20261113T212608Z/verification.json):
  all 359 modules and 6,133 declarations, permitting only `propext`,
  `Classical.choice` and `Quot.sound`; exact types and coverage are logged.
- [Kernel replay](evidence/providers/run-20261113T210310Z/verification.json):
  all 359 exact-module commands exited zero with frozen inputs unchanged.
  Four independent local workers took 776.98 seconds; two workers are used
  for the smaller CI runner. No aggregate-prefix invocation is used.

These are checks by the bundled Lean kernel relative to imported Lean/mathlib
environments, not an independent kernel or a fresh replay of all mathlib.
The intentionally stopped sequential attempt remains recorded with `ok=false`.
[Provider evidence](evidence/providers/README.md) explains the input hashes,
raw logs and limits. Vendor notes/provenance retain their dated handoff state;
the linked certificates record the subsequent completed provider verification.
