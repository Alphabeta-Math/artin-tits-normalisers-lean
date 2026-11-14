# Compatible normalizer and fundamental-group exact sequences

This Lake package formalizes the actual-map comparison in Theorem 6.7 and
Remark 6.12 of Garnier–Heng–Licata–Yacobi, arXiv:2509.21915v3, PDF pp.26–27.
It uses the existing Artin braid presentation, normalizer quotients, relative
arrangement complement and its actual orbit quotient. It requires the
previous `chambers/` package by path.

Current review, verification and publication status is recorded separately in
the [landmark 4 report](../docs/theorem18/landmarks/milestone4-REPORT.md).
The [plan](../docs/theorem18/landmarks/milestone4-PLAN.md) and independent
[contract A](../docs/theorem18/landmarks/milestone4-contract-a.md) and
[contract B](../docs/theorem18/landmarks/milestone4-contract-b.md) delimit the target.

## Mathematical interface

For every `M : CoxeterMatrix I` with `[Finite M.Group]`, every `J : Set I`
and every actual `x : Complement M J`,
[`Landmark4.lean`](ArtinSequences/Landmark4.lean) exposes:

- `Sequence4.theorem_6_7`: both actual short exact rows, the pure and middle
  multiplicative equivalences, and both commuting homomorphism squares;
- `Sequence4.theorem_6_7_positive`: the same diagram using the opposites of
  mathlib's genuine fundamental groups, for positive traversal order;
- `Sequence4.landmark_4`: the ordinary-convention theorem.

The first algebraic group is the existing `pureNormalizerImage`, the quotient
image of the ambient pure subgroup intersected with the Artin normalizer.
Its arrow is the actual subgroup inclusion. The geometric first arrow is
induced by `orbitProjection`. The right vertical arrow is identity on the
same `coxeterNormalizerQuotient`; no automorphism relabels it.

Mathlib fundamental groups use categorical `End` multiplication. Ordinary
fundamental groups therefore receive inverse ribbon labels, and their
endpoint map is the genuine homomorphism
`γ ↦ ((orbitMonodromy γ).unop)⁻¹`. In positive traversal convention the
target fundamental groups are explicitly opposite, and the monodromy reads
the underlying endpoint label directly. Neither plain inversion within a
noncommutative group nor plain `op`/`unop` is silently used as a homomorphism.

All-basepoint transport uses an actual upstairs path `θ` and exactly its
projection `pθ` downstairs. The pure equivalence is constructed from the
proved kernels/ranges and the injective covering map. No simple
connectedness, asphericity, or desired comparison is assumed. The package
does not assert landmark 5 or the K(π,1) conclusions of full Theorem 1.8.

## Reproduction

Use the pinned Lean `v4.36.0-rc2` and mathlib
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. From `sequences/`:

```bash
python3 scripts/cache_prerequisites.py
python3 scripts/providers/assemble.py --check
python3 scripts/verify.py --plan
python3 scripts/verify.py --execute --mode final --output evidence/reproduction
```

Final mode requires the matching frozen inventory and both accepted main
review receipts. For development checks without an acceptance claim, use
`--execute --mode technical` with a separate output directory. The verifier
retains source/context hashes, actual commands, exits, durations and raw
logs; it checks exact-module replays and the complete declared axiom coverage.
The permitted transitive axioms are `propext`, `Classical.choice`, `Quot.sound`.
Official kernel replay is relative to imported environments, not a separate
kernel implementation or a fresh replay of all mathlib.

## Source and proof provenance

Exactly two unchanged TauCeti basepoint-change proofs are extracted into one
new provider module. Their [vendor record](vendor/README.md), exact
[provenance](vendor/provenance.json), [assembly recipe](vendor/extraction-recipe.json)
and [root acceptance](../docs/provenance/acceptance-landmark4-basepoint.json)
retain the source commit, license, selected blocks, wrapper diff and concrete
applications. Archiving the complete original file does not claim its whole
proof closure was imported or verified.

The [M4 search inventory](../docs/provenance/searches/m4-other-inventory.json)
distinguishes inspected candidates from the selected proofs. The central
[GitHub proof-source register](../docs/provenance/GITHUB-PROOF-SOURCES.md)
and historical evidence preserve earlier source choices and their limits.
The package adds new proof and verification records without rewriting the
accepted scientific sources of earlier landmarks.
