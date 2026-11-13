# Landmark 1 proved: the actual normalizer quotient covering

The first of the [five landmarks](PLAN.md) is proved in Lean. For finite
`M.Group`, every `J : Set I` and every actual relative-complement point,
the natural action of `N_W(W_J)/W_J` is free and the actual orbit map is a
quotient covering. Its genuine fundamental groups form the geometric short
exact sequence, with raw endpoint monodromy explicitly in the opposite group.

**Full Theorem 1.8 remains unproved.** This result does not identify the
fundamental groups with Artin normalizer quotients, prove compatibility with
the Artin projection, or prove arrangement asphericity. Those are later
landmarks, not assumptions smuggled into this one.

## Exact proof and source correspondence

The actual parent objects `Complement`, `OrbitSpace`, the contragredient
normalizer quotient action and `orbitProjection` are used without change.
No alternate nerve or classifying space is substituted. The first three
scientific modules contain 32 explicitly authored definitions, lemmas and
instances, including the private subgroup helper.

1. In [`Dominant.lean`](../../../landmarks/ArtinLandmarks/Dominant.lean), a
   dominant functional is nonpositive on vectors with nonpositive simple
   coordinates. If a nonidentity Coxeter element fixes it, choose a left
   descent; the root-sign criterion forces that simple coordinate to vanish.
   The corresponding reflection also fixes it, and length induction gives
   exactly the standard parabolic on the vanishing coordinates. Applying
   this to the functional with coordinates zero on `J`, one elsewhere,
   proves the pointwise stabilizer of the entire relative flat is `W_J`.
   These statements hold without finite rank or finite Coxeter group.
2. In [`RegularStabilizer.lean`](../../../landmarks/ArtinLandmarks/RegularStabilizer.lean),
   sum the actual finite positive-root set. Each simple reflection permutes
   the other positive roots and negates its own, so it subtracts twice that
   simple root from the sum. Maximize its evaluation on the finite dual
   orbit: a negative simple evaluation would increase the maximum. Thus
   every orbit has a dominant representative.
3. Conjugate a real relative regular point into that chamber. Every zero
   wall of the dominant point corresponds to a root vanishing at the original
   point. Regularity forces such a root to annihilate the entire relative
   flat. The conjugated simple reflection therefore fixes that flat
   pointwise. Subgroup-closure induction and step 1 prove the full ambient
   Coxeter stabilizer is exactly `W_J`.
4. In [`Covering.lean`](../../../landmarks/ArtinLandmarks/Covering.lean),
   the two coordinate evaluations of a complement point are not simultaneously
   zero on any retained root. They define a finite family of nonzero linear
   forms on `ℝ²`. The finite-subspace-union theorem chooses coefficients
   `(a,b)` with every evaluation nonzero, so `a x+b y` is real regular.
   An element fixing both coordinates fixes this combination; by step 3
   the full pair stabilizer is exactly `W_J`. Descending to the actual
   normalizer quotient proves freeness.
5. The actual dual-coordinate homeomorphism gives local compactness in
   finite rank; the relative flat is closed and the complement is open.
   Hausdorffness, continuity, finite proper discontinuity and proved freeness
   satisfy the actual quotient-covering theorem. The previously verified
   genuine covering exact-sequence supplier then applies at every basepoint.

This proves the covering assertion used in equation (3.28), without needing
the full chamber-labeling or simplicial-arrangement theory first. Rank zero,
`J=∅` and `J=I` are included. No crystallographic or irreducibility premise,
positive dimension, nontrivial group or chosen special basepoint is imposed.
The raw opposite-group convention is deliberately retained for landmark 4.

## GitHub prerequisites actually reused

The [bounded GitHub search](milestone1-github-search.md) checked generic
geometric-root/chamber/stabilizer candidates, including sources beyond mathlib.
TauCeti's pinned `Geometric.Sign` supplies the exact arbitrary-Coxeter
root-sign and positive-root-permutation statements. Its prerequisite
`Geometric.RankTwo` is also imported. Crystallographic Weyl chamber theorems
were rejected as a supplier for arbitrary finite Coxeter types.

The two sources are pinned to
`62bbc0596dc3539d488232e4e924a338548ea0a9`. Original exact bytes and license
are preserved. Lake module resolution required relocating the two module
paths, with exactly one import-path patch in `Sign.lean`; all mathematical
namespaces, statements and proof bodies are unchanged. The verifier checks
that original-to-local relationship byte for byte. Both modules compile
against the parent's actual mathlib pin `65d730f...`, rather than assuming
compatibility with upstream's different pin.

Mathlib's finite-subspace-union theorem and finite free-action covering
theorem are applied directly to our actual linear functionals, action and
orbit map. Root signs alone are not presented as an already existing
point-stabilizer theorem: steps 1–4 are the additional formal proofs.

## Verification and independence

Both independent GPT-6.1 Sol/high reviewers accepted all 32 explicit
declarations and the exact source-to-formal correspondence. Their final
receipts bind all four project/root sources, all three configuration files,
both new providers, provenance and the archived parent verification record.
Both read the new project proofs and both complete new provider proofs;
their execution and reading limits remain explicit in the review files.

`landmarks/evidence/landmark1-local/verification.json` records **11 successful
commands**, including a package-scoped clean build, the transitive axiom
audit and **five individual kernel replays** (both new providers and all
three scientific project modules). The audit covers **40 new compiled
declarations**, including generated/private declarations, and **763 supplier
declarations**, across exactly **38 modules**. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted transitive axioms.

The verifier also checks all **65 parent input hashes** and its historical
statement-review hashes against the archived successful parent CI record.
The parent source, package configuration and historical receipts remain
unchanged. The separate landmark package uses the same toolchain and exact
dependency pins. The record binds **85 source/context inputs** and preserves
real commands, exits, timings, review/log hashes and raw diagnostics.

Kernel replay is the official single-module checker relative to imported
mathlib/parent environments. It is not a second kernel or a fresh replay of
all prior mathematics. Failed development attempts are distinguished in
`development-notes.md`; none is counted as a passing certificate. A separate
GitHub workflow repeats the new verification from a fresh checkout and
archives its actual records. Its successful run will be linked only after
completion.

## Next landmark

Landmark 2 is the reduced ribbon groupoid and its actual Artin-normalizer
vertex-group identification. Its positive Artin/Garside and complete ribbon
presentation inputs still require a new GitHub search/application check and
formal proofs. Landmark 1 is complete; landmarks 2–5 are not yet proved.
