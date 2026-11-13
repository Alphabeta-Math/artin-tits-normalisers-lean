# Spherical positive Artin suppliers

The active `OAI/` tree contains the 359-module union of the import closures of
`OAI.Topology.ArtinGroups.Harmonic.SphericalPositiveCommonMultiple` and
`OAI.Topology.ArtinGroups.Harmonic.RestrictionHomRange`,
35,722 upstream source lines. It includes the positive braid presentation,
spherical embedding, cancellation, positive fraction forms, both gcd
existence theorems and the left-lcm universal property. It includes no
extra Salvetti topology closure or ribbon-normalizer theorem.

All files were first copied exactly from openai/math commit
`4eaee87548250b2682affda7d05d947c05554bae`, Apache-2.0. The identical
mathcommunity/oai-math-revised subtree and exact upstream/project pins are
recorded in `provenance.json`. `upstream-original/` preserves every original
byte. Only `OAI/` is active imported source; originals are not imported.
The provenance inventory binds both original and active SHA256s and all
module imports, roots and topological order.

Upstream uses Lean v4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
The target is Lean v4.36.0-rc2 and mathlib
65d730f7150f21fdfa32f3e73a3f549c1f96a0e9, retaining autoImplicit=false.

There are seven focused compatibility ports. Six rename the
`Nat.strong_induction_on` tactic alternative `h` to `ind`, retaining all
binders and proof steps. FusionLabel replaces one broad `congr 1` with
explicit congrArg for multiplication by the same real scalar, avoiding
a deterministic elaboration timeout. All theorem statements, mathematical
definitions, hypotheses and conclusions are unchanged. Exact unified diffs
and semantic justifications are in `compatibility-patches/` and provenance.

RestrictionHomRange adds exactly one unchanged module to the passed
358-module closure. Its 41-module own closure was checked against that
existing inventory, then it compiled successfully without another port.
All prior active bytes and seven compatibility ports remain unchanged.
Its new proof supplies the longest parabolic left-descent prefix.

The 30-module base pilot built after its two branch-label ports. Expansion
first failed at Identity's branch label and FusionLabel's broad congruence;
the expanded target then built successfully after the remaining focused
ports. Both failed and successful command records and unmodified logs are
in `compatibility-evidence/`; the final expanded build also retains its
complete input snapshot. The pilot and expanded records are kept distinct.

Whole Mathlib imports are retained. Builds used the already cached local
Mathlib closure; fresh CI must fetch that closure. Legacy module-system
and deprecated-name warnings remain. The final 359-module transitive axiom audit, kernel replay
and independent statement/diff reviews are still pending: build success
is not formal supplier acceptance. The endpoints have an implementation
restriction to a finite ordered universe-zero ambient type; transporting
them to arbitrary finite parent indexing types remains explicit work.
