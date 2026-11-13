# Sequential landmarks for Theorem 1.8

This independent Lake package continues the article formalization using the
unchanged parent package as a local dependency. The five main landmarks and
their exact acceptance conditions are in
[`docs/theorem18/landmarks/PLAN.md`](../docs/theorem18/landmarks/PLAN.md).

The first landmark proves, for arbitrary `J` and finite actual Coxeter group:

- The actual normalizer quotient acts freely on the actual relative complex
  hyperplane complement.
- The actual orbit map, with the specified subspace/orbit topologies, is a
  quotient covering.
- The genuine fundamental groups form its geometric short exact sequence
  at every basepoint. Endpoint monodromy explicitly targets the opposite
  normalizer quotient under mathlib's multiplication convention.

The proof is in `ArtinLandmarks/{Dominant,RegularStabilizer,Covering}.lean`.
The dominant and pointwise-flat stabilizer lemmas are stronger: they hold
without finite rank or finite Coxeter group assumptions. The finite-orbit
maximum and real-regular stabilizer steps use finite Coxeter group exactly
where needed. No stabilizer, freeness or covering premise is assumed.

**Full Theorem 1.8 remains unproved.** The ribbon identification, equivariant
geometric groupoid comparison, compatibility with the Artin projection and
Deligne asphericity are separate later landmarks. This package does not
silently invert endpoint labels or claim either actual K(π,1) conclusion.

## Existing proofs reused

The GitHub search and exact source reading are recorded in
[`milestone1-github-search.md`](../docs/theorem18/landmarks/milestone1-github-search.md).
Two further pinned TauCeti modules supply root-sign criteria and the
permutation of positive roots other than a simple root. Their actual types
apply to arbitrary Coxeter systems, including noncrystallographic types.
The mathlib finite-subspace-union and finite free-action covering results
apply directly to our actual objects.

`vendor/provenance.json` binds original bytes, local bytes, license and the
single import-path patch used to avoid an overlapping Lake module namespace.
No mathematical statement, proof or declaration namespace was patched.
The two original upstream files are retained as `.lean.txt` sources.

## Reproduce

From the repository root, after installing the pinned Lean toolchain and
Python 3:

```bash
python3 landmarks/scripts/cache_prerequisites.py
python3 landmarks/scripts/verify.py --output landmarks/evidence/reproduction
```

The first command fetches the exact pinned package prerequisites and only the
mathlib import closure used by the parent and landmark sources. It can share
the parent's gitignored dependency cache; no local absolute path is required.
The committed landmark manifest inherits the parent's exact dependency pins.

The verifier checks both independent statement-review receipts, all project
and provider hashes, the mechanically patched source relation, and the entire
unchanged parent context against its archived successful CI input hashes.
It cleans only this new package, rebuilds the landmark target, audits all new
project and all imported provider declarations transitively, and kernel-replays
the two new providers and three new scientific modules individually.

Only `propext`, `Classical.choice` and `Quot.sound` are permitted transitive
axioms. It records real commands, exits, inputs/reviews/log hashes and failures.
Replay is relative to imported mathlib/parent environments; it does not freshly
replay the whole parent library or mathlib, nor use a second kernel.
The parent has its own preserved verification records and source-bound reviews.
