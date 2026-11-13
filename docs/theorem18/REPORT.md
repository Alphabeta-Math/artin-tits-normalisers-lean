# Theorem 1.8: verified prerequisites, incomplete main theorem

Subsequent progress: [landmark 1](landmarks/REPORT.md) now proves the actual
normalizer quotient action is free and its orbit map is a quotient covering,
with the geometric fundamental-group exact sequence. The report below retains
the scope and limits of the earlier foundational milestone. The remaining
work is now tracked in the [five-landmark plan](landmarks/PLAN.md).

**Theorem 1.8 is not proved.** This milestone establishes actual geometric
foundations and usable generic topology suppliers. It does not replace the
theorem by a conditional statement assuming its main comparisons or
asphericity. The full algebraic Lemma 2.8 remains proved, with unchanged
mathematical source hashes and unchanged historical statement reviews.

## Results now formalized

The four new proof modules contain 93 explicitly authored declarations and
instances, in 845 lines of source:

- `Geometry.lean`: actual standard root space and its actual dual,
  dual-basis coordinate homeomorphism, relative annihilator, root orbit,
  proper restricted arrangement, real-pair complement and inherited
  topology. Proves root/arrangement finiteness from finite Coxeter group,
  openness, and empty/full parabolic sanity properties.
- `NormalizerAction.lean`: identifies the flat with the actual parabolic's
  fixed subspace; restricts the contragredient normalizer action and descends
  through the actual normalizer quotient; proves preservation and continuity
  on the complement. Defines the actual orbit quotient and its continuous
  open quotient map. Finite-type proper discontinuity is proved in
  mathlib's compact-intersection sense; freeness is not yet proved.
- `ArrangementTopology.lean`: proves nonemptiness and path connectedness
  of the actual finite-type complement. The proof uses complex affine
  lines between safe real pairs: each retained hyperplane excludes at most
  one complex parameter, and the complex plane minus finitely many points
  is path connected. Empty arrangements and zero-dimensional flats are
  included.
- `CoveringSequence.lean`: proves generic covering-induced injectivity,
  range/kernel equality and quotient-covering monodromy surjectivity.
  It requires a genuine quotient covering and keeps the raw endpoint
  target explicitly `Gᵐᵒᵖ`. It does not assert that our orbit map is already
  a covering.

The import-only aggregate is `ArtinTheorem18.lean`. No declaration advertises
these prerequisites as the complete Theorem 1.8.

## Existing GitHub proofs and direct usability

| Supplier | What is usable | Scope still to prove |
| --- | --- | --- |
| Pinned mathlib `Topology.Homotopy.Lifting` | Actual covering injection and endpoint monodromy, including its kernel and surjectivity | Actual quotient action freeness/covering, and comparison with the algebraic projection |
| TauCeti at `62bbc0596dc3539d488232e4e924a338548ea0a9`, existing ten modules | Actual Artin presentation, Coxeter geometry, Matsumoto and parabolic length theory | Further chamber and ribbon/Garside theory |
| Same TauCeti revision, 23 further unchanged modules | Actual higher-homotopy covering isomorphisms, literal asphericity/K(G,1) predicates, asphericity transfer | Asphericity of the actual arrangement complement is an input to transfer, not a conclusion supplied here |
| Inspected `openai/math` ordinary Artin Salvetti sources | Potential future ordinary-model ingredients; not imported or accepted | No inspected theorem identifies the relative complement or its normalizer quotient with those models |

The search inventories give exact revisions, definitions, candidate
decisions and reading limits. The newly imported TauCeti closure is pinned,
byte-identical to upstream, license-preserving and minimal at the whole-module
level. It compiled unchanged against our pinned mathlib despite upstream's
different mathlib revision. The vendor library alone uses upstream's
`autoImplicit=true`; the final audit prints the relevant inferred source
basepoints and their actual hypotheses.

The [additional search](search-additional.md) checks `adamtopaz/OrlikSolomon`
and `facebookresearch/atlas-lean` at exact revisions. The former's complement
comparison concerns open schemes and localization, with no supplied singular
topological realization; the latter's arrangement hit is an incidence
predicate. Neither supplies the missing topological comparison or asphericity,
so neither is imported as a proof prerequisite.

## Actual verification

The following records are successful local executions, not predicted checks:

| Record | Successful commands | Individual modules kernel-replayed |
| --- | ---: | ---: |
| `evidence/full-post-theorem18/verification.json` | 24 | 17 historical algebraic suppliers/project modules |
| `evidence/theorem18-local/verification.json` | 32 | 23 new suppliers and four new project modules |

The first record includes a package-scoped clean build of the unchanged full
Lemma 2.8. The second builds the enlarged optional target and audits **145 new
project declarations**, including generated/private helpers, and **733
supplier declarations**. The driver enforces coverage of exactly 37 defining
modules: all 33 suppliers and all four new project modules. Only transitive
axioms `propext`, `Classical.choice`, and `Quot.sound` are permitted.

Two independent GPT-6.1 Sol/high reviewers read all 93 explicit new project
declarations and proof bodies against independently prepared source contracts.
Both accepted **foundations only**, with no mathematical repair required.
Their receipts bind all five project/root files, all 23 new provider files,
the toolchain/package/manifest configuration, provenance and historical
source inventory. Their exact supplier reading limits are explicit; this is
not a claim that every line of the entire supplier library was human-reviewed.

The records preserve real commands, exits, timestamps, input/review/log hashes
and diagnostics. Local records were produced before the milestone commit;
their recorded worktree state and input digests, rather than that earlier
Git HEAD alone, identify the checked inputs. The workflow performs both
verification scopes on GitHub and uploads separate artifacts. Its run/archive
record is linked separately once the run has actually completed.

The fresh [GitHub run 43492004104](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43492004104)
has now **succeeded** on source commit
`4e6e7851a9ced34df49584e6bdb77f701698f2f5`. Both scopes passed: 56 commands
and 44 individual module replays in total. The downloaded CI records match
all 62 algebraic-context input hashes and all 65 foundation-context input
hashes, their review receipts, and every command-log digest. The permanent
[archive](github-evidence/run-43492004104/README.md) retains both complete
artifact ZIPs, readable verification JSON, full compressed Actions output,
run/job/artifact metadata, archive-validation results and SHA-256 checksums.
Its records still explicitly state that full Theorem 1.8 is unproved.

Kernel replay is the official single-module checker relative to imported
mathlib environments. It is not a second independent kernel implementation,
nor a fresh replay of all mathlib. Failed development attempts and the resolved
audit-visibility issue are retained in `development-notes.md` and the failed
raw audit log. No failed execution is counted as a successful certificate.

## Remaining full-theorem work

The indispensable missing proofs are:

1. Actual finite restricted chambers, simpliciality and regular-point
   stabilizers; then freeness of the normalizer quotient action and the
   actual orbit covering.
2. Spherical positive Artin/Garside theory, reduced ribbon groupoids and
   their identification with the existing algebraic normalizer quotient.
3. An equivariant comparison with the actual arrangement fundamental
   groupoid, both natural-map compatibility equations, the opposite-group
   convention transport, and arbitrary-basepoint transport.
4. Deligne asphericity for the actual finite central simplicial arrangement,
   followed by the already verified generic covering transfer and the two
   actual fundamental-group identifications.

These are substantial established mathematics still requiring Lean proofs;
the completed Lemma 2.8 alone does not imply them. The bounded searches did
not find directly usable Lean suppliers for these decisive comparisons.
This is not a proof that none exist anywhere. No original-article error or
counterexample was established, and missing formal infrastructure is not an
article defect. The complete source-faithful route remains in `PLAN.md` and
`mathematical-route.md`.
