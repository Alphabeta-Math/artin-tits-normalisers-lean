# Landmark 4: compiled comparison of the actual short exact sequences

Status: all 12 scientific modules and the aggregate target compile. The
complete local technical battery passed and both independent main reviews
accepted the exact frozen sources. [Root mathematical acceptance](milestone4-root-acceptance.json)
is recorded. Fresh clean final-mode CI is pending; no CI success is claimed here.
The two-proof basepoint supplier cohort has separate completed verification,
independent reviews and root acceptance, described below.

The implemented theorem is the actual-map content of Theorem 6.7 and
Remark 6.12 in arXiv:2509.21915v3, PDF pp.26–27. For every finite actual
Coxeter group, arbitrary index universe, every subset `J` and every actual
complement basepoint `x`, the code supplies both vertical multiplicative
equivalences, both short exact rows and both commuting squares. No
simply-connectedness or asphericity premise is used. **Landmark 5 and full
Theorem 1.8 remain unproved.**

## Actual groups, spaces and maps

Write `X = Theorem18.Complement M J`, `Y = Theorem18.OrbitSpace M J` and
`p = orbitProjection M J`, retaining their actual topologies and action.
The algebraic groups are the unchanged

```text
K = Artin.pureNormalizerImage M J
N = Artin.normalizerQuotient M J
Q = Artin.coxeterNormalizerQuotient M J.
```

`K` is the quotient image of the ambient pure Artin subgroup intersected
with the actual Artin normalizer, not the whole pure subgroup. Its arrow
`i:K→*N` is the original subgroup inclusion; `f:N→*Q` is the original
Artin–Coxeter quotient map. The geometric arrow `j_x` is the actual map
on fundamental groups induced by `p`.

Let `μ_x:π₁(Y,p x)→*Qᵐᵒᵖ` be the existing raw endpoint monodromy and
`m_x(γ)=((μ_x γ).unop)⁻¹`. The actual equivalences
`pureFundamentalGroupEquiv` and `normalizerFundamentalGroupEquiv` satisfy

```text
j_x ∘ ΦK_x = ΦN_x ∘ i,
m_x ∘ ΦN_x = f.
```

Both rows are proved short exact, and the right vertical map is identity
on the same `Q`. The bundle is
[`Sequence4.theorem_6_7`](../../../sequences/ArtinSequences/Landmark4.lean).
Empty rank, empty/full `J`, reducible and noncrystallographic finite types
are included; finite rank is a proved consequence of finite Coxeter type.

## End conventions, endpoints and all basepoints

The vertex used in
[`RibbonVertex.lean`](../../../sequences/ArtinSequences/RibbonVertex.lean)
belongs to the actual reduced `J`-associate ribbon component from landmark 3.
It is not the larger positive-parabolic transporter groupoid. Traversing
labels `β` then `γ` multiplies Artin labels as `βγ`, whereas categorical
`End` multiplication reverses traversal. Same-label endomorphisms therefore
identify with the opposite reduced loop group. The ordinary fundamental-group
comparison uses the inverse label through the proved inversion-to-opposite
equivalence.

The middle comparison applies the actual landmark 2 normalizer isomorphism,
the landmark 3 geometric functor on vertex groups, and the literal basepoint
equality supplied by the strictly commuting covering square. An unrelated
counit or downstairs path is not substituted. Actual lifting and signed
deck-label formulas prove

```text
μ_x(ΦN_x a) = op((f a)⁻¹).
```

Normalizing by `op(q)↦q⁻¹` gives the right square above. This is a
multiplicative equivalence from `Qᵐᵒᵖ` to `Q`; plain inversion in a
noncommutative group is not treated as an endomorphism.

[`AllBasepoints.lean`](../../../sequences/ArtinSequences/AllBasepoints.lean)
first proves the comparison for any actual path `θ` from the standard
complement point to `x`, using exactly `pθ` downstairs. Covering-map
naturality proves the first square. Lifting the transported loop follows
`θ` backwards, the old lift, and the deck translate of `θ`; its endpoint
has the same label at `x`. Thus raw monodromy, and then normalized monodromy,
is preserved with no conjugation automorphism of `Q`. Proved path
connectedness supplies `θ` for the final named maps. Independence from all
path choices is neither needed nor claimed.

The pure comparison is derived in
[`StandardPureComparison.lean`](../../../sequences/ArtinSequences/StandardPureComparison.lean)
using the compatible middle equivalence, algebraic kernel identification,
geometric range/kernel equality and injectivity of the actual covering map.
Each pure element has a unique preimage under `j_x`, giving the actual first
equivalence and its inclusion square. The generic
[`KernelComparison`](../../../sequences/ArtinSequences/KernelComparison.lean)
supplier constructs this map rather than assuming it as a field; the
standard application discharges all its hypotheses with prior actual maps.

[`PositiveConventions.lean`](../../../sequences/ArtinSequences/PositiveConventions.lean)
also proves the full diagram with the opposites of mathlib's genuine
fundamental groups. Its positive endpoint map sends `op γ` to
`(μ_x γ).unop`, and `positiveNormalizerEquiv_label` identifies the actual
positive ribbon-image path transported along `pθ`. This implements the
path chain of Remark 6.12 with both squares and the same `Q`. A reversed
positive crossing is not identified with the inverse directed path.

## Exact supplier extraction, search and proof history

The new external supplier is exactly two declarations from TauCeti commit
`62bbc0596dc3539d488232e4e924a338548ea0a9`, in the original
`TauCeti/AlgebraicTopology/FundamentalGroup/BasepointChange.lean`:

- `FundamentalGroup.fundamentalGroupMulEquivOfPath_apply`, lines 129–148;
- `FundamentalGroup.map_fundamentalGroupMulEquivOfPath`, lines 196–212.

Their complete selected statement/comment/proof blocks are unchanged. A
minimal wrapper imports two existing pinned mathlib modules into one new
provider module. The original 651-line file, Apache-2.0 license, exact block
hashes, wrapper/omission diff and deterministic recipe are preserved in
[`sequences/vendor/`](../../../sequences/vendor/README.md). This is not
verification or acceptance of the full upstream file or its unrelated
dependency closure.

The [provider technical record](../../../sequences/evidence/providers/verification.json)
binds the actual build, exhaustive audit and exact-module official kernel
replay: two canonical declarations, two physical occurrences, no duplicates,
and only `propext`, `Classical.choice`, `Quot.sound`. Both independent
supplier reviewers subsequently accepted those exact blocks and applications;
the later [root acceptance](../../provenance/acceptance-landmark4-basepoint.json)
binds their receipts and the technical record. Historical pending-status
fields in the earlier technical snapshot are not rewritten into a claim
that the main milestone was accepted at that time.

The [search report](milestone4-search-other.md) and
[machine inventory](../../provenance/searches/m4-other-inventory.json)
retain eight source-inspected repositories, exact candidate statements,
pins, licenses, reading/closure limits and dispositions; 76 bounded search
hits are separately recorded as hits. Unselected FormalFrontier, Oka,
sphere-six and other alternatives were not imported or silently accepted.
The central [proof-source register](../../provenance/GITHUB-PROOF-SOURCES.md)
and preserved earlier proof histories remain the provenance entrypoints.
Old accepted scientific/configuration/review inputs are not reauthored by
this package. Supplier acceptance is separate from the now accepted main M4 reviews
and the pending clean-CI closeout.

## Verification checkpoint and reproduction

The independent `sequences/` package inherits `chambers/`, `ribbons/`,
`landmarks/` and the parent package with Lean `v4.36.0-rc2`, mathlib
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9` and the same recorded Git pins.
The complete [local technical receipt](../../../sequences/evidence/landmark4-technical-20261114T075200Z/verification.json)
records 57 successful commands, 14 exact-module kernel replays, 151 canonical
project declarations and 151 physical occurrences across 13 modules (12
scientific files plus aggregate), with zero duplicates and standard axioms
only. The provider audit covers both selected declarations. All 955 earlier
accepted repository inputs remain byte-for-byte unchanged.

The [frozen inventory](../../../sequences/source-inventory.json), SHA-256
`7048b5d1bb1926eb499bdad1bd27fd76ca7c47299bd5f92a2416ec3f1c808a2c`,
binds actual source/configuration/provider/context/tooling hashes and complete
physical declaration coverage. Independent final reviews
[A](../../../sequences/reviews/landmark4-a.json) and
[B](../../../sequences/reviews/landmark4-b.json) both accepted that exact
inventory and the actual statements/evidence. Their prose reports retain
reading and execution limits. The technical receipt SHA-256 is
`f76ea11b92312db7bb62780118600b2b37ebdcb16cef0dc42a218cf8a9c061ec`.

Final-mode verification will repeat the required checks on a clean GitHub
runner. Its success is pending, rather than inferred from local verification.

From `sequences/`, the documented reproduction sequence is:

```bash
python3 scripts/cache_prerequisites.py
python3 scripts/providers/assemble.py --check
python3 scripts/verify.py --plan
python3 scripts/verify.py --execute --mode final --output evidence/reproduction
```

Final mode requires the exact frozen inventory and both accepted main
receipts. Technical mode (`--execute --mode technical`) performs checks
without asserting M4 acceptance. The verifier preserves real commands,
exits, timings, raw logs, dependency context and source/artifact bindings.
Official replay is relative to imported foundations, not a second kernel
implementation or a fresh replay of all earlier mathematics.

## Consulted-source findings and remaining scope

No new confirmed article defect was established in the M4 source search or
the independent target contracts. The qualified Lemma 3.5 boundary-choice
observation retains its [unresolved attribution and local-hypothesis
limits](milestone3-source-findings-a.md); it is not promoted to a false-lemma
claim. The distinct Godelle preprint sign, reducible-factor-stripping and
orientation findings remain recorded with their exact locators, verified
examples, corrections and journal-version limits in the
[milestone 2 source records](milestone2-normalizer-route.md). They are not
new defects attributed to the original 2025 article. Bounded source searches
and unselected candidates are not treated as mathematical errors.

The interval-groupoid route supplies the actual geometric comparison; it
does not retroactively assert the previously unclaimed literal adjacent
two-standard-path/equal-count classification. More importantly, this package
does not prove the restricted arrangement's simpliciality, a Deligne
asphericity theorem or either K(π,1) conclusion. Those remain landmark 5;
full Theorem 1.8 is not claimed.
