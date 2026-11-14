# Five sequential landmarks for Theorem 1.8

Source: Garnier–Heng–Licata–Yacobi, arXiv:2509.21915v3. This continues the
completed algebraic Lemma 2.8 and the previously verified actual geometric
foundations. It does not change the original theorem or replace the actual
spaces by classifying spaces.

The landmarks will be proved, independently reviewed, compiled, audited and
kernel-replayed **one at a time**, in the order below. Existing GitHub proofs
must be checked for exact definitions, hypotheses and application before use;
imported source pins, modifications and actual verification remain explicit.

## 1. The actual normalizer quotient covering

For every `M : CoxeterMatrix I` with finite `M.Group`, every `J : Set I` and
every point of the actual `Complement M J`, prove the action of the actual
`N_W(W_J)/W_J` is free and the actual map to `OrbitSpace M J` is a quotient
covering. Deduce the geometric short exact sequence at every basepoint.
Raw endpoint monodromy targets the opposite group under mathlib's convention;
the source-convention comparison is explicitly left to landmark 4.

The proof has five dependent steps, not five substitute final landmarks:

1. Prove dominant dual point stabilizers and pointwise relative-flat
   stabilizers are the appropriate actual standard parabolics.
2. In finite type maximize evaluation on the finite sum of positive roots
   to move any real dual point into the closed dominant chamber.
3. Use that conjugation and vanishing-root annihilation to prove the full
   Coxeter stabilizer of a real relative regular point is exactly `W_J`.
4. Choose a real linear combination of a complement point's coordinates
   which is real regular. Thus the ambient pair stabilizer is `W_J` and
   the quotient action is free.
5. Establish local compactness in the actual coordinate/subspace topology,
   apply the verified finite-action covering API, and apply the genuine
   fundamental-group covering sequence.

This route avoids proving a complete chamber-labeling theorem before obtaining
the cover. It does not establish simpliciality or Deligne asphericity.

GitHub reuse: two further TauCeti modules supply generic root signs and the
positive-root permutation theorem. The original upstream bytes and the one
mechanical import-path relocation are preserved in `landmarks/vendor/`.
No crystallographic restriction is introduced. The exact candidate search and
proof route are recorded alongside this plan.

## 2. The actual reduced ribbon normalizer identification

Construct spherical positive Artin/Garside prerequisites, the actual reduced
ribbon groupoid and its required relations. Prove its vertex group at `J` is
isomorphic to the existing presentation-defined `N_A(A_J)/A_J`, with the
canonical Coxeter projection tracked. The source inputs are Theorem 5.6 and
the complete ribbon relations behind Lemma 5.9 and Lemma 6.2.

An abstract groupoid defined to have the desired vertex group, an assumed
normalizer decomposition, or ordinary Matsumoto alone does not complete this
landmark. GitHub searches must check positive monoid embedding, spherical
Garside hypotheses and the literal normalizer/ribbon maps.

## 3. The equivariant geometric groupoid comparison

The compiled implementation uses the interval groupoid on the actual
restricted chambers: positive arrows for all ordered chamber pairs, with
self and sign-`Between` relations. It proves the equivariant comparison with
`FundamentalGroupoid (Complement M J)`, the actual signed ribbon covering onto
the `J`-associate reduced ribbon component, its equivalence with the actual
orbit space's fundamental groupoid, and the strict covering square. Both
actual action cocones satisfy the groupoid orbit-colimit universal property.
The source chain is Lemma 6.6, Proposition 6.3 and their prerequisites.

A combinatorial Salvetti or nerve model is usable only with a proved comparison
to the actual complement. Oppositely directed positive crossings are separate
arrows, not inverses. The implemented interval alternative is compared directly
with these actual objects; an identification with the paper's literal
adjacent-gallery presentation is not asserted. The Coxeter endpoint formula
is proved for all signed ribbon arrows with the same actual quotient
`N_W(W_J)/W_J`. Both final independent reviews and root mathematical acceptance
are recorded; final-mode verification and fresh clean CI passed. See the
[report](milestone3-REPORT.md).

## 4. The compatible normalizer/fundamental-group exact sequences

Use landmarks 1–3 and the existing algebraic Lemma 2.8 to prove both actual
fundamental-group isomorphisms and both commuting squares, with identity on
the actual Coxeter normalizer quotient. Resolve mathlib's opposite-group path
convention explicitly and transport to every basepoint using compatible paths.
This is the full content of the comparison in Theorem 6.7, not merely the
existence of two unrelated group isomorphisms.

## 5. Deligne asphericity and the full Theorem 1.8

Prove the restricted arrangement is finite, central and simplicial. Supply a
formal Deligne theorem or an equivalent contractibility proof with its actual
geometric comparison, and apply it to the actual complement. Transfer
asphericity through the actual cover from landmark 1, then combine it with
landmark 4 to obtain both asserted K(π,1) conclusions. This recovers
Corollary 6.14 and completes Theorem 1.8 without assuming its conclusions.

## Tracking and package boundary

The sequential developments live in independent `landmarks/`, `ribbons/` and
`chambers/` Lake packages, requiring earlier packages by path with the same
pinned Lean/mathlib dependencies. This preserves the parent and earlier
accepted source/configuration hashes and historical proof records. Each new
cohort has its own statement reviews and build/axiom/replay records. Accepted
supplier cohorts do not by themselves establish a milestone's main statement.

| Landmark | Current status |
| --- | --- |
| 1: Actual quotient covering | Proved; both statement reviews, local verification and [fresh GitHub CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43498322108) passed |
| 2: Reduced ribbon normalizer | [Proved](milestone2-REPORT.md); both independent reviews, complete local verification and [fresh CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43516856592) passed |
| 3: Equivariant geometric comparison | [Proved and mathematically accepted](milestone3-REPORT.md); both final independent reviews and complete local technical battery passed; [final-mode fresh CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43568861942) passed ([closeout plan](milestone3-PLAN.md)) |
| 4: Compatible exact sequences | Not yet proved |
| 5: Deligne asphericity/full theorem | Not yet proved |

Missing formal proofs are established mathematics to formalize, not open
problems or defects attributed to the article. No full-theorem completion
is inferred from a successful earlier landmark.
