# Landmark 2 closeout and the next geometric bridge

Status: proved; final local verification and both independent statement
reviews passed. Fresh GitHub CI is pending. The aggregate is
[`ArtinRibbons.Landmark2`](../../../ribbons/ArtinRibbons/Landmark2.lean).
The exact implemented scope and retained source findings are in
[`milestone2-REPORT.md`](milestone2-REPORT.md).

## Implemented dependency chain

The separate `ribbons/` package preserves the parent Artin model and pinned
dependencies. Its compiled chain is:

1. Identify the actual Artin presentations on generators, embed the actual
   spherical positive monoid and transport through finite reindexing.
2. Prove positive degree/support, gcd/lcm, parabolic fractions and coprime
   fraction support without assuming a normalizer splitting.
3. Construct actual parabolic longest lifts and all outside elementary
   ratios, including positivity and unique actual ribbon endpoints.
4. Generate the actual reduced subgroupoid, factor positive reduced
   ribbons, and prove cofinal positive loop denominators and naturality.
5. Prove trivial parabolic intersection and actual normalizer
   factorization; derive the canonical normalizer-quotient isomorphism,
   actual semidirect product and Coxeter-projection compatibility.
6. Prove complete fixed pair-lcm relations on typed positive atomic words,
   then the universal signed groupoid presentation. Prove Coxeter length
   additivity for every actual pair-lcm factorization.

No final theorem assumes positive embedding, reduced-ribbon generation,
normalizer surjectivity/splitting, or completeness of arbitrary equalities.
The actual loops are generated Artin-group elements, rather than a renamed
normalizer quotient. Restricting to associates recovers the intended
component without changing its actual arrows.

## Completed local closeout and fresh CI

1. The 24 project files, package configuration and 359 active/original
   supplier files are bound in the source inventory, with all seven
   compatibility diffs and all 65 accepted parent inputs unchanged.
2. Both independent GPT-6.1 Sol/high statement reviews accepted the exact
   mathematical scope. All 999 unique project and 6,133 unique supplier
   declarations passed the transitive standard-axiom audit. Physical
   coverage checks account for 1,000 and 6,193 compiled occurrences,
   respectively; each repeated theorem has identical type/proof/universes.
3. All 24 project modules passed fresh exact kernel replay. The prior
   completed 359-supplier replay certificate was reused only after every
   current bound input/artifact/executable/log hash passed validation.
4. The [complete local verifier](../../../ribbons/evidence/landmark2-local-final/verification.json)
   passed. Earlier failed accounting attempts and interrupted development
   replays remain accurately recorded, with their old snapshots preserved.
5. The source commit will trigger fresh GitHub CI with a fresh rebuild and
   all 359 supplier replays. Its actual result and raw records will be
   archived separately; no future CI success is presumed here.

## Landmark 3 obligations preserved

The fixed lcm presentation is complete, including signed arrows. It does
not assert the literal two-standard-path/equal-atomic-count clauses of
Lemma 5.9. The next proof must either establish those precise finite
wall-crossing facts, including the empty-subset case, or prove an adequate
geometric comparison directly for the complete fixed lcm presentation.
Coxeter length additivity is an algebraic supplier for that work, not an
already proved geodesic-gallery theorem.

Build the actual chamber/arrangement groupoid, construct its paths inside
the existing complement, and prove equivariance and compatibility with the
actual quotient covering. Positive crossings in opposite directions must
remain separate arrows. Do not replace the complement by an unrelated
nerve or classifying space.

The later exact-sequence comparison must preserve the canonical Coxeter
projection, handle the opposite-group convention, and apply at every
basepoint. Deligne asphericity and the full Theorem 1.8 remain later
obligations; none is inferred from the algebraic normalizer result.
