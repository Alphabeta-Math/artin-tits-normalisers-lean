# Landmark 1: independent semantic review A

Reviewer: GPT-6.1 Sol/high, task `lemma28_statement_review_a`.
Date: 2026-11-14. Final verdict: **accept-landmark1**.
**Landmark 1 is proved; full Theorem 1.8 remains unproved.** The acceptance is
bound to the frozen source/configuration/provider/parent hashes below.

Scope: the first selected landmark only—actual relative point stabilisers,
actual complex-complement freeness, the actual orbit covering, and its
geometric fundamental-group short exact sequence. Neither the other four
selected landmarks nor full Theorem 1.8 is claimed. I have not consulted
reviewer B or executed any new Lean/kernel commands, or edited proof,
configuration, supplier or cache files.

## Original target and reading

I reread the original article's §3.3, Lemmas 3.23–3.24 and the paragraph
leading from the actual relative complement (3.26) to the regular cover and
exact sequence (3.28), PDF pp.12–13. This was through the same frozen original
extraction used in the earlier source contract. Prior visual PDF inspection
of p.13 and the exact geometry contract are recorded in
`docs/theorem18/reviews/statement-a.md`; I do not claim a fresh visual PDF
inspection or independent reading of the cited Bourbaki/Deligne texts here.

The finite-type target uses every Coxeter matrix `M` with `Finite M.Group`
and every `J : Set I`. The space, topology, action and orbit map must be the
already reviewed actual `Theorem18.Complement`,
`Theorem18.quotientComplementMulAction`, `Theorem18.OrbitSpace` and
`Theorem18.orbitProjection`, with the existing actual generated parabolic
`Artin.coxeterParabolic M J`. An assumed chamber-stabiliser or freeness theorem
would not complete the landmark.

The new approach establishes actual full ambient point stabilisers directly,
rather than presupposing chamber labels and transporting their freeness. This
is a sound departure from the article's brief route to the covering paragraph.
The source's finite-type geometry is preserved; no relative arrangement is
replaced by a Coxeter arrangement of the normaliser quotient.

## All reviewed project statements and proofs

I read the complete current sources of `Dominant.lean`,
`RegularStabilizer.lean`, `Covering.lean` and the aggregate, including private
helpers, instance definitions and all proof bodies. No mathematical premise
requiring repair was found in the following argument chain.

### Dominant.lean

`IsDominant` means nonnegative evaluation at every actual simple root;
`zeroIndices` is precisely the set of vanishing simple evaluations.
`evaluation_nonpos_of_nonpos` rewrites a functional using the actual dual
coordinates and sums only the finite support of the input vector. Each
coefficient-product sign has the correct orientation. No finite-rank
assumption is needed.

For `dominant_fixed_iff`, if `u≠1` fixes a dominant functional, choose a left
descent `i` of `u`. The supplier's genuine sign theorem says
`ρ(u⁻¹)α_i<0`, because `i` is a right descent of `u⁻¹`. Applying the dominant
functional gives a nonpositive number, while invariance identifies it with
the nonnegative `φ(α_i)`; hence that coordinate is zero. The actual simple
reflection therefore fixes `φ`, and `s_i*u` has strictly smaller length and
still fixes `φ`. Strong induction expresses `u` in the actual parabolic on
those zero indices. Conversely, every selected generator, and hence its
generated subgroup, fixes `φ` by the parent's already proved fixed-flat
criterion. The theorem assumes neither a point-stabiliser theorem nor
normaliser membership.

`canonicalDominant` is the actual dual-coordinate functional with values 0
on `J` and 1 outside. Its evaluation formula, dominance, zero-index identity,
relative-subspace membership and exact stabiliser are all proved. The final
`pointwise_flat_fixed_iff` tests a pointwise stabiliser at this actual
canonical functional to obtain the upper inclusion, and uses the parent's
parabolic fixed-flat theorem for the reverse inclusion. These results work
for arbitrary Coxeter type, not just finite type.

### RegularStabilizer.lean

`positiveRoots` consists of actual root vectors that are positive in the
coordinatewise partial order. Strict positivity means coordinatewise
nonnegative and nonzero, not that every coordinate is positive.
`positiveRootSum` is a sum over distinct actual positive root vectors, and
its finiteness is proved from finite `M.Group`, including the parent's
finite-index theorem. The private root-set equality identifies the exact
same orbit-root definition with the supplier's root set.

`geometricReflection_positiveRootSum` removes the simple root from that
finite set. The supplier's actual reflection bijection of all other positive
roots permits reindexing the remaining sum, while the simple root changes
sign. Thus the result is exactly `S−2α_i`; no root multiplicities, chamber
transitivity or arbitrary choice of a finite orbit replaces this calculation.

`exists_dominant_dualAction` maximises the real number `(u·φ)(S)` over the
actual finite Coxeter group. Comparing with `s_i*u` gives
`(u·φ)(S)−2(u·φ)(α_i)≤(u·φ)(S)`, hence every simple evaluation is nonnegative.
It therefore proves the dominant-orbit representative instead of assuming
that every point lies in a selected chamber. The finite group is inhabited
by its identity even in rank zero.

`realRelativeRegular` means avoidance of every retained restricted root
hyperplane. The private `flatPointwiseStabilizer` is an actual subgroup of
the ambient Coxeter group fixing the whole actual relative flat.

The forward proof of `realRelativeRegular_fixed_iff` takes a dominant
translate `ψ=u·φ`, so `u*g*u⁻¹` lies in the generated zero-index parabolic by
the preceding proved dominant stabiliser theorem. If `ψ(α_i)=0`, then
`φ(ρ(u⁻¹)α_i)=0`. That actual root must annihilate the entire relative flat:
if some flat functional did not vanish there, the root would be retained and
would contradict regularity of `φ`. Consequently the conjugate
`u⁻¹*s_i*u` fixes the whole flat. Subgroup closure extends this to
`u⁻¹*(u*g*u⁻¹)*u=g`, and the independently proved pointwise-flat theorem
puts `g` in the original `W_J`. This proves the full ambient stabiliser
identity without assuming `g` normalises `W_J`. The reverse direction uses
the actual fixed-flat theorem. No root-subsystem classification or unproved
conjugation-of-parabolics assertion is hidden in this step.

### Covering.lean

`coefficientEvaluation` is a genuine real linear functional on coefficient
pairs `(a,b)`, evaluating `a*x+b*y` at a given root. For each retained root,
the complement condition guarantees that at least one coefficient evaluation
is nonzero, using `(1,0)` or `(0,1)` explicitly. Finite avoidance over `ℝ`
then yields `exists_regular_linearCombination`. This argument applies to
the actual pair complement, including the empty arrangement; it does not
require a positive-dimensional flat or a preselected chamber point.

`complement_pair_stabilizer_iff` sends a pair-fixing group element to a fixer
of that actual generic real combination, then applies the proved real regular
stabiliser theorem. Conversely, `W_J` fixes each relative coordinate.
`quotientComplement_smul_fixed_iff` takes an actual representative in the
actual Coxeter normaliser, extracts the two ambient fixed-coordinate
equalities from the parent's quotient action, and uses the proved pair
stabiliser to show its quotient class is 1. The `IsCancelSMul` instance is
therefore a proved freeness conclusion, not an imported assumption.

The Hausdorff instance uses exactly the parent's inherited complement
topology. The local-compactness instance derives finite index type from
finite `M.Group`, transfers local compactness through the real coordinate
homeomorphism, then through the closed relative subspace and open pair
complement. These are actual topology instances for the same space.

`isQuotientCoveringMap_orbitProjection` applies the actual mathlib finite/
properly-discontinuous-action covering theorem. I checked its source
signature: it needs continuous constant actions, proper discontinuity,
local compactness, Hausdorffness and `IsCancelSMul`; all are supplied by the
actual parent/new constructions. Its quotient map is the same actual orbit
projection with its inherited orbit quotient topology. The ordinary
`IsCoveringMap` conclusion is taken from this proved quotient cover.

`orbitFundamentalGroupMap` is induced by that actual continuous orbit map.
`orbitMonodromy` is its actual endpoint-monodromy homomorphism.
`orbitFundamentalGroup_shortExact` applies the parent's generic covering
sequence only after proving the specific quotient cover, using its already
proved path-connected actual total space. Its only geometric hypothesis is
finite `M.Group`, with arbitrary `J` and basepoint.

The terminal group is explicitly `N(W,J)ᵐᵒᵖ`, the raw endpoint-label
convention in mathlib, not a silently inverted label claimed to be a
noncommutative homomorphism into `N(W,J)`. This is an honest geometric
covering sequence; comparison with the article's conventional algebraic row
and its identity terminal map remains a later compatibility obligation.

All rank-zero and full-`J` cases are included: an empty retained-root family
makes regularity vacuous on the actual zero flat; `W_J=W` fixes it, the
normaliser quotient is trivial, and its point orbit map is a covering. No
`Nonempty I`, `Nontrivial` flat, proper-`J` or finite-`J` assumption occurs.

At preliminary inspection, `ArtinLandmarks.lean` imported only the parent
aggregate and the sign supplier. I notified root, and independently inspected
the frozen final aggregate: it now publicly imports `ArtinTheorem18` and
`ArtinLandmarks.Covering`, which imports the whole new mathematical chain.
The integration issue is resolved without changing the proofs.

## Two new suppliers and exact mechanical relocation

I read both complete relocated supplier files, including all declarations
and proof bodies. `RankTwo` proves the actual alternating-word image formula
with Chebyshev coefficients, their sine formula in finite off-diagonal rank
two, their linear value at a zero/infinite entry, and nonnegativity before
the finite braid length or at all lengths for an infinite entry. Its exact
strict/non-strict bounds are appropriate for the downstream sign argument.

`Sign` proves the root-sign/descent criterion by actual length induction and
rank-two parabolic factorisation. Its root set is the actual orbit of simple
roots in the existing geometric representation. It proves positivity or
negativity, unit form value, the single-support root characterization, and
the simple-reflection bijection on all positive roots except its own simple
root. These are exactly the inputs used by the new dominant-stabiliser and
positive-root-sum arguments. Its representation-faithfulness theorem is
proved from the same sign criterion, not inserted as an axiom. No finite or
crystallographic assumption accidentally narrows the supplier conclusions.

I independently compared each preserved original `.lean.txt` byte-for-byte
with its upstream Git object at TauCeti revision
`62bbc0596dc3539d488232e4e924a338548ea0a9` and checked its SHA-256 against
provenance. I then verified that the relocated `RankTwo` file has exactly
the same bytes and that `Sign` differs by precisely the single recorded
import substitution:

```
import TauCeti.GroupTheory.Coxeter.Geometric.RankTwo
→ import ArtinLandmarkVendor.Geometric.RankTwo
```

There are no mathematical namespace, definition, statement or proof changes.
I also independently checked the seven referenced parent supplier hashes and
all scientific/configuration hashes in the parent's two historical source
inventories; they match. The separate Lake package depends on the parent
through `path=".."`, with its own project/library prefix. Project
`autoImplicit=false` and vendor-only `autoImplicit=true` preserve the existing
scoping convention.

The final provenance metadata directs readers to separate statement reviews
and actual verification records rather than presenting provenance as
acceptance. I inspected that final wording; both original and local
scientific supplier bytes are unchanged. I have not independently run Lean
compilation, transitive axiom audit or kernel replay in this task.

## Final bindings, verification and disposition

I independently reread the final project sources and aggregate, extracted all
32 explicit source-qualified names (including both private helpers), and
matched them with `landmarks/source-inventory.json`. **All 32 have disposition
accept** for landmark 1. The actual compiled signatures in root's final audit
show arbitrary `I`, `M`, `J` and basepoint, with only finite `M.Group` for the
finite-type conclusions; stabiliser/freeness/covering results are not
additional premises. No mathematical repair is required.

My independently computed root-relative project hashes are:

| Source | SHA-256 |
| --- | --- |
| `landmarks/ArtinLandmarks.lean` | `1be1ffb1e3042d4e7973c8cac884b524f2f4e1af09c3f6672558690ceeb2b1f4` |
| `landmarks/ArtinLandmarks/Covering.lean` | `5c700e4c42bdb72e81c4a7499ebab13d1d742bd1e98058446057c12eb389cd94` |
| `landmarks/ArtinLandmarks/Dominant.lean` | `408a97cc6f49b5868d5eafc6aae733b8ae26a1d314b26c81235f5bf493339da4` |
| `landmarks/ArtinLandmarks/RegularStabilizer.lean` | `aeeee397f0fe48325c9f62eee8607e80a1836cb123dc9a022cd8d954c92fd93f` |

I additionally computed and checked the three landmark package configuration
hashes against the inventory. The companion JSON binds all of them and the
two relocated provider source hashes:

```
RankTwo: 53d4bcbfb2dd83abf8a4adb53091c982e191ca3a69be95e751e20306e26591f3
Sign:    c0b7e5f1e0bfa9aa67a1df7b5cc11e65625987089e9909f0366b88068d58bc09
```

The final supplier provenance hash is
`5d30ae8493968f7fb58bbaa7e78514a0afc15501d62abd940061906c3483581a`.
The accepted archived parent verification record hash is
`79f91cb45e5ada75c39968f29b93cc228d0fd38914903cb432c1b8664a332b1d`.
I checked both digests independently, verified the parent's `ok:true` and
`full_theorem_1_8_proved:false` flags, and independently rehashed all **65**
input paths in that archived parent record: all are unchanged. This is a
real separate package over the unchanged parent rather than a new proof
claim about a modified parent model.

Root reports that `lake build ArtinLandmarks` passed. I inspected the actual
final `/tmp/landmark1-pre-review-audit-v2.log`: the displayed signatures are
the intended ones; it reports **40 landmark declarations and 763 supplier
declarations** passing the standard transitive-axiom allowlist. I independently
extracted its defining-module labels and verified exactly the expected
**38 modules**—three new scientific project modules and 35 supplier modules
(33 parent plus two relocated). The audit-log hash I computed is
`072c21e47fb15c78ef2fe4327841155a6b0d1a9d311ec76f78aafa743162103b`.
The final sequence theorem's displayed axioms are only `propext`,
`Classical.choice`, `Quot.sound`. Defining-module selection covers private
helpers and generated declarations despite their namespace names.

The initial audit counter-inference error was fixed by `Nat` annotations in
the audit harness only, with its failed output retained under
`landmarks/evidence/development/`. I inspected the corrected harness and
successful actual output; no scientific proof or supplier repair was needed.
I do not claim to have executed root's build/audit, a clean rebuild, or any
kernel replay myself. Source/semantic review, real compiled evidence and
kernel replay remain distinct forms of evidence; no whole-mathlib or
independent-kernel verification is claimed by this receipt.

The frozen mathematical statements and proofs are sound, directly relevant
to landmark 1, and faithful to the actual source geometry. No foundation,
supplier, configuration or cache file was edited by this reviewer.

This landmark proves neither a Deligne/Salvetti/ribbon fundamental-group
comparison nor the identification of the geometric sequence with the Artin
normaliser sequence. It does not prove asphericity, either `K(π,1)` claim,
or the topological-Artin/presentation bridge. It therefore does not establish
full Theorem 1.8 or any of the four later selected landmarks. No new defect
in the original article or consulted literature is asserted.
