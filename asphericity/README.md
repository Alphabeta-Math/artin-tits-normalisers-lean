# Actual geometric and topological prerequisites for asphericity

This package develops prerequisites for landmark 5 on the original relative
arrangement complement. **It does not prove actual arrangement asphericity,
full landmark 5, or full Theorem 1.8.** Current acceptance, verification and
publication status belongs to the separate
[prerequisite report](../docs/theorem18/landmarks/milestone5-REPORT.md).

The [landmark 5 plan](../docs/theorem18/landmarks/milestone5-PLAN.md) and
independent [contract A](../docs/theorem18/landmarks/milestone5-contract-a.md)
and [contract B](../docs/theorem18/landmarks/milestone5-contract-b.md) retain
the full target for both original spaces, every finite actual Coxeter group,
arbitrary `J` and every basepoint, including rank zero and full/empty `J`.

## Mathematical content

- [`FlatCoordinates`](ArtinAsphericity/FlatCoordinates.lean) identifies the
  actual relative flat with complementary real coordinates, continuously
  and linearly. The chart works in arbitrary rank; finite rank gives an
  actual basis, dimension and finrank.
- [`Simpliciality`](ArtinAsphericity/Simpliciality.lean) and
  [`FiniteArrangement`](ArtinAsphericity/FiniteArrangement.lean) prove the
  actual finite, central, proper, closed codimension-one hyperplane and
  strict-basis chamber hypotheses. Every actual chamber closure is the
  hull of a genuine finite basis and is a simplicial pointed cone.
- [`ConvexCover`](ArtinAsphericity/ConvexCover.lean) constructs a finite
  convex open cover of the actual complement, using four strict real or
  imaginary sign choices per retained form. Nonempty intersections of
  **nonempty families** are contractible. The empty-family intersection
  is not declared contractible.
- [`UniversalCoverGeometry`](ArtinAsphericity/UniversalCoverGeometry.lean)
  proves local contractibility and constructs the genuine based-path
  universal cover at the existing M4 point, with its actual coinduced
  topology, surjective covering projection and path/simple connectedness.
  The higher-homotopy covering equivalences assert no vanishing.
- [`DirectedCover`](ArtinAsphericity/DirectedCover.lean) proves a generic
  criterion: a directed open cover by actual contractible subspaces kills
  actual finite-cube homotopy groups. It does not construct such a cover
  of the actual universal cover.
- [`Prerequisites`](ArtinAsphericity/Prerequisites.lean) bundles the actual
  universal-cover and finite good-cover conclusions. The aggregate module
  is [`ArtinAsphericity`](ArtinAsphericity.lean).

The missing core is a genuine contraction or all-degree higher-homotopy
vanishing for the actual complement or its actual universal cover, with any
model comparison proved. Simple connectedness, a fundamental-groupoid
equivalence, or existence of a good cover alone does not supply this result.
The finite cover still needs a nerve comparison and asphericity analysis.

## Reproduction

The package requires `sequences/` by path and inherits Lean `v4.36.0-rc2`,
mathlib `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9` and the recorded
transitive pins. From `asphericity/`:

```bash
python3 scripts/cache_prerequisites.py
python3 scripts/providers/assemble.py --check
python3 scripts/verify.py --plan
python3 scripts/verify.py --execute --mode final --output evidence/reproduction
```

Final mode requires the matching prerequisite inventory and both
`accept-asphericity-prerequisites` review receipts. It verifies only this
prerequisite checkpoint; full-M5, actual-asphericity and full-Theorem-1.8
scope flags remain false. Development checks can use `--mode technical`
with a separate output directory and make no acceptance claim.

The verifier retains actual commands, exits, timing, raw logs and frozen
source/context bindings. Auditing permits only `propext`, `Classical.choice`
and `Quot.sound`; exact-module replay uses the official kernel relative to
imported foundations, not a separate kernel or a fresh replay of mathlib.

## Source provenance

The selected new supplier cohort is eleven complete TauCeti topology modules
at `62bbc0596dc3539d488232e4e924a338548ea0a9`. Statements, definitions and
proof bodies are unchanged; selected import paths are mechanically relocated.
See the [vendor record](vendor/README.md), [provenance](vendor/provenance.json),
[recipe](vendor/import-relocation-recipe.json), and
[root supplier acceptance](../docs/provenance/acceptance-landmark5-topology.json).
Supplier acceptance does not prove arrangement asphericity.

The three bounded source searches and their reading/application limits are
linked in the [report](../docs/theorem18/landmarks/milestone5-REPORT.md).
The [central proof-source register](../docs/provenance/GITHUB-PROOF-SOURCES.md)
preserves selected uses separately from candidate discoveries and historical
verification records.
