# Landmark 5: other GitHub supplier search

Research date: 2026-11-14. Project baseline:
`22301de0ff626dbfb3d8ae66a6bccc50317de702`.
This report and the [durable machine inventory](../../provenance/searches/m5-other-inventory.json)
are the only project files changed by this task. No candidate was imported,
built, axiom-audited, kernel-replayed, independently reviewed, or accepted.
**No third-party proof was used in the formalization by this search.**

## Decision

No directly applicable Deligne theorem for the actual complexified complement
of a finite central simplicial real arrangement was found in this bounded
search outside mathlib, TauCeti, and openai/math. There are substantive
generic topology candidates in **kangxyz/colib** and its predecessor
**kangxyz/quillen-k-theory**:

- Genuine groupoid nerve realizations have trivial higher homotopy groups.
- Actual partition-of-unity and interpolation maps give domination by an
  actual cover nerve, under explicit local geometric hypotheses.
- Filtered simplicial colimits preserve actual stage homotopy equivalences
  when the canonical transition maps satisfy the stated hypotheses.

These are potentially useful prerequisites. None supplies the missing
arrangement-specific higher-homotopy comparison or contractibility argument.
Immediate reuse is not recommended merely to collect an asphericity-shaped
endpoint; first identify its exact role in a proof about the actual space.

The target remains `Theorem18.Complement M J`, the actual subspace of
`relativeSubspace J × relativeSubspace J` obtained by removing simultaneous
zeros of the retained real root forms, and its actual normalizer orbit space.
Landmark 3's equivalence of fundamental groupoids controls path classes.
It does not identify higher homotopy groups with those of a groupoid nerve.

## Immutable positive candidates and their cost

| Repository | Inspected commit | Toolchain | mathlib pin | License |
| --- | --- | --- | --- | --- |
| [kangxyz/colib](https://github.com/kangxyz/colib/tree/bac5cab53eb6526e366e861d289253ec81aa89f0) | `bac5cab53eb6526e366e861d289253ec81aa89f0` | Lean `v4.35.0` | `56a005855ea17e0b0958f73ec801ae140b0a1679` | Apache-2.0 |
| [kangxyz/quillen-k-theory](https://github.com/kangxyz/quillen-k-theory/tree/c561118b7795eb9780be9ed391c3251d6a4d0afd) | `c561118b7795eb9780be9ed391c3251d6a4d0afd` | Lean `v4.34.1` | `d13f23b723b8a846827a245b89c10fc7d3f11612` | Apache-2.0 |

Both pinned root license files were read and hashed. Colib explicitly
attributes the relevant implementations to the above Quillen revision;
these are related developments, not independent confirmations. Neither
toolchain/mathlib pair matches this project's `v4.36.0-rc2` /
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. Compatibility is untested.

Counts below include the requested root and all transitively imported
repository modules, excluding Mathlib and standard tool dependencies. Lines
include comments and blanks. The machine inventory contains every file hash
and import edge, not just these totals.

| Root suffix after `Colib.` or `Quillen.` | Colib modules / lines | Quillen modules / lines |
| --- | ---: | ---: |
| `Topology.ClassifyingSpace.Groupoid` | 259 / 38,583 | 236 / 37,536 |
| `Topology.Realization.NumerableRealizationDomination` | 18 / 2,123 | 17 / 2,573 |
| `Topology.Realization.MetricRealizationDomination` | 21 / 2,372 | 20 / 2,807 |
| `Topology.FilteredRealization.HomotopyEquivalence` | 74 / 9,731 | 102 / 15,155 |

All Colib closures above have no further third-party mathematical import
beyond Mathlib. The Quillen groupoid and filtered-realization closures also
import `Aglib.CategoryTheory.ExactCategory.Basic`, from
**kangxyz/aglib**, commit `2c34f185fa859e862661f939cd216b07bcccfb26`,
Apache-2.0. Its actual source closure is one additional file, 207 lines,
with Mathlib imports. Thus the complete non-Mathlib groupoid cohort is
237 modules / 37,743 lines for that predecessor. This extra dependency
must not be omitted from a proposed reuse record.

### Actual groupoid realizations

[`Colib/Topology/ClassifyingSpace/Basic.lean`](https://github.com/kangxyz/colib/blob/bac5cab53eb6526e366e861d289253ec81aa89f0/Colib/Topology/ClassifyingSpace/Basic.lean)
defines, in namespace `CategoryTheory`,

```lean
def ClassifyingSpace (C : Type u) [Category.{v} C] : TopCat.{max u v} :=
  SSet.toTop.obj (CategoryTheory.nerve C)
```

Its points and topology are the actual geometric realization. The
[`Groupoid.lean`](https://github.com/kangxyz/colib/blob/bac5cab53eb6526e366e861d289253ec81aa89f0/Colib/Topology/ClassifyingSpace/Groupoid.lean)
endpoint, in namespace `CategoryTheory.GroupoidClassifying`, is

```lean
variable {C : Type u} [Category.{v} C] [IsGroupoid C]
theorem subsingleton_higher_pi_at (x : ClassifyingSpace C) (n : ℕ) :
  Subsingleton (HomotopyGroup.Pi (n + 2) (ClassifyingSpace C) x)
```

The proof is substantive. The actual comma category of a point inclusion
is equivalent to the discrete set of original arrows. Theorem B compares
its realization with the actual homotopy fiber; the long exact sequence
then kills higher homotopy at vertices, and actual paths from arbitrary
realization points to vertices transport the result. The imported
`HomotopyFiber` definition was checked: it is the actual subtype

```lean
{z : X × C(I, Y) // z.2 0 = f z.1 ∧ z.2 1 = y}
```

with inherited topology. The conclusion uses mathlib's genuine
`HomotopyGroup.Pi`, not a newly defined vanishing invariant.

The predecessor endpoint is
`Quillen.GroupoidClassifying.subsingleton_higher_pi_at`, with the same
geometric domain. All-point, arbitrary-universe statements are explicit;
no arrangement, Artin, or simpliciality hypothesis appears.

**Missing bridge:** a suitable actual higher-homotopy comparison between
the complement and this realization. A categorical equivalence
`IntervalGroupoid ≌ FundamentalGroupoid (Complement M J)` cannot discharge
that bridge. Instantiating `C` with either of those groupoids establishes
asphericity of its classifying space, not of the original complement.

### Constructed cover-nerve domination

The Colib namespace is `Topology.NumerableConnectorCover`; the predecessor
uses `Quillen.NumerableConnectorCover`. The actual
[`LocalEquiconnection`](https://github.com/kangxyz/colib/blob/bac5cab53eb6526e366e861d289253ec81aa89f0/Colib/Topology/LocalEquiconnection.lean)
has an open neighborhood of the diagonal in `A × A`, a continuous connector
on that domain times the interval, its two endpoint equations, and a
diagonal-fixing equation. It contains no realization comparison or desired
domination as a field. Connector-convexity requires pairs to lie in this
domain and their interpolations to remain in the specified set.

The numerable theorem has actual data

```lean
E : LocalEquiconnection A
W : ι → Set A
V : κ → Set A
hconvex : ∀ k, E.IsConvex (V k)
href : PointStarRefines W V
hcover : ∀ x, ∃ i, x ∈ W i
vertex : ι → A
hvertex : ∀ i, vertex i ∈ W i
ρ : PartitionOfUnity ι A
hρ : ρ.IsSubordinate W
```

and a linear order on the index type. `PointStarRefines` means
`∀ x, ∃ k, {y | ∃ i, x ∈ W i ∧ y ∈ W i} ⊆ V k`.
Its actual ordered nerve is the simplicial subcomplex of the order nerve
whose vertex lists have a common point in their cover members.

[`exists_numerable_realization_domination`](https://github.com/kangxyz/colib/blob/bac5cab53eb6526e366e861d289253ec81aa89f0/Colib/Topology/Realization/NumerableRealizationDomination.lean)
constructs

```lean
∃ (K : SSet.{v}) (a : C(A, |K|)) (b : C(|K|, A)),
  Nonempty ((b.comp a).Homotopy (ContinuousMap.id A))
```

The displayed proof selects the actual ordered nerve and the constructed
`partitionNerveMap` and `nerveReturnMap`. The classifier uses original
partition coefficients; finite support charts prove continuity into the
weak realization. The return map uses ordered connector interpolation,
with face compatibility and degenerate-coordinate aggregation proved
before descending through the simplicial colimit. The connector constructs
the displayed composite homotopy.

The metric variant
`exists_metric_realization_domination` assumes a metric on `A`, the local
connector, and an open connector-convex cover. Its proof constructs a
positive radius, point-star-refining small balls, and a subordinate partition
using metric paracompactness. It supplies the same domination conclusion.

**Missing bridge:** the returned nerve is not identified with the desired
Deligne/Salvetti complex or an aspherical groupoid realization. Only the
composite on `A` is made homotopic to the identity; the theorem does not
claim a two-sided nerve equivalence. Even applying it to the actual open
arrangement complement would still require proving higher-homotopy
vanishing of an appropriate constructed nerve. It is also not a general
component-good-cover theorem for the existing chamber tubes.

### Filtered realization and contractible cones

[`Topology.FilteredRealization.stageHomotopyEquiv`](https://github.com/kangxyz/colib/blob/bac5cab53eb6526e366e861d289253ec81aa89f0/Colib/Topology/FilteredRealization/HomotopyEquivalence.lean)
has these literal inputs:

```lean
{J : Type u} [SmallCategory J] [IsFiltered J]
F : J ⥤ SSet.{u}
c : Cocone F
hc : IsColimit c
e : ∀ {j k : J} (u : j ⟶ k), ContinuousMap.HomotopyEquiv |F.obj j| |F.obj k|
he : ∀ {j k : J} (u : j ⟶ k),
  (e u).toFun = (SSet.toTop.map (F.map u)).hom
```

It constructs `ContinuousMap.HomotopyEquiv |F.obj j| |c.pt|` with the
canonical cocone leg as its forward map. This is actual filtered-colimit
homotopy invariance. It is not, by itself, contractibility of the nerve
of an arbitrary filtered category. A concrete diagram and the required
transition homotopy equivalences still have to be proved.

Colib also has actual nerve contractions from an initial or terminal
object in `Topology/ClassifyingSpace/Contraction.lean` (19-module /
2,375-line closure). Those hypotheses could contract explicit finite cones;
they do not assert that a filtered category has a terminal object.
`GroupCompletionContractibleUniversal.lean` was also inspected: it assumes
contractibility of the classifying space of the acted-on category `D`
before proving contractibility of its particular localization. It is not
a generic Garside-category K(π,1) theorem with those hypotheses discharged.

## Negative candidates: exact semantic reasons

The inventory retains every inspected pin and source hash. No proof closure
was selected from the following repositories.

| Repository and inspected revision | Actual inspected content / reuse limit |
| --- | --- |
| zstone1/Cubical `5339856b84db66f7ba3b831c00d40264447b8d21` | COM Salvetti face/tope posets, braid-germ presentations and categorical localizations. `Models` takes categorical base/fiber equivalences as input. No inspected actual complex-complement or higher-homotopy comparison. The complete previously obtained 276-entry tree contains no license file. |
| Arthur742Ramos/ComputationalPathsLean `257c659b7973aeda900d86a5da73b208712c7523` | `CoherentPres.isAspherical := syzygies = []`; its `oneRelator_aspherical` proof simplifies that list definition. It is not topological asphericity. `GarsideDeep.NormalFormMap` takes normalization soundness, idempotence and respect for braid equivalence as fields. |
| GrigoryEvko/FX `e01b6e40bb6c283423c27bd7bcc1a6ac07700756` | Positive `B₃` bounded convertibility and simple-stratum algorithms; no generic Garside category realization or arrangement theorem. |
| nickgou-nuke/info-geometry-lean `a392af178af1fe2bcba2ba39eb405700c6ee103c` | Actual specific `I₂(6)` positive-monoid prefix/complement identities. The file explicitly leaves global cancellation/normal forms unclaimed; no topological conclusion. |
| SimiaCryptus/Fun_With_Math `c34e7b3269fedbac94802d7cd214f8e1f59667de` | A supplied list-of-permutations `GarsideBraid` with weighted-chain data. `garside_bruhat_knot_criterion` is `Iff.rfl` on an executable cycle-count predicate; no classifying-space theorem. |
| facebookresearch/atlas-lean `3c0dc6fa04acebac8fb47f38db5e28529b735c63` | The Garside hit is a `theorem_wanted` braid-conjugacy problem statement, not a supplied proof of Deligne asphericity. |
| frogscooper/artin-cat0-29 `2342f7eaf5598646cd53481a3ee3f296daa42ea2` | The inspected OAI-derived endpoint obstructs a geometric CAT(0) action for one presentation, under an injectivity premise. It does not prove an arrangement complement aspherical. |
| Lucent-Financial-Group/Zeta `20678947e54eff067ee6e7f415657ec2061af0cd` | Braided monoidal twist coherence/uniqueness. No actual topological complement or higher-homotopy endpoint. |
| NetRxn/SK_EFT_Hawking `a912c5542d897c22ac8d4cdec07649a4872215a6` | Explicit Fibonacci anyon braiding matrices, including arithmetic `native_decide` proofs. Wrong domain for this task. |
| hyperpolymath/tangle `6f070d6eb3faaac75acc6fb2f667e81d43effef2` | Programming-language type safety and braid-word reduction. No relevant topological comparison. |
| dzackgarza/lean-categories `064b5cfdae80fd27c7af1b0c9a7a8bbc5547e55b` | Its inspected augmented-simplicial-object `IsAspherical` means normalized-homology vanishing and an augmentation `H₀` isomorphism in an abelian category, not actual topological higher-homotopy vanishing. |
| SauersML/group-approximation `b4cbab68177c23556f0db49f8a45a431729f6e23` | `FoxAspherical` is injectivity of a Fox boundary; the endpoint deduces torsion freeness of a presented group. No arrangement/higher-homotopy comparison. |
| frenzymath/HolomorphicAnosov `65f2b33a7309de661a8500e4642e5609a537a8ff` | Genuine CW based-homotopy uniqueness, but it assumes an actual surjective covering with contractible total space. That hypothesis is part of the missing work here. |

These are domain assessments. They do not assert that every proof in a
repository is incorrect or that an intentionally different invariant is
a false Lean theorem. No mathematical defect in the original article was
established.

## Coverage, execution limits, and next obligation

The durable inventory contains all 14 recorded queries, their returned
paths and exact blob revisions, all 36 repositories encountered (including
the transitive Aglib supplier), selected-source hashes, pinned topology
toolchains/manifests/licenses, and complete candidate import DAGs. There
are 35 repositories among the query hits; many were left as uninspected
leads. The general `aspherical` query reached its 100-result cap. Its inline
repository exclusions were not reliably applied by the returned search
results; all raw hits were retained and the body-inspection scope was
applied separately. OAI/TauCeti hits remain recorded without being treated
as other-repository proofs.

Complete immutable trees were obtained for Quillen (8,458 entries) and
Colib (9,751), both untruncated, and their source snapshots downloaded.
Their endpoint/definition modules and selected critical support proofs
were inspected. All candidate closure modules were hashed, their imports
traversed, and their source text screened after removing nested comments
for `sorry`, `admit`, `native_decide`, and custom `axiom` declarations;
no matches were found in those closures. This is not a compiled transitive
axiom audit and does not establish closure correctness. Most imported
proof bodies were not independently reviewed line by line. For negative
candidates only relevant definition/endpoint/proof segments were read;
their unrelated closures were not accepted or exhaustively inspected.

Searches for Salvetti, Garside, simplicial/Deligne arrangements, good covers,
nerve comparison, filtered nerves, and asphericity support a bounded reuse
decision. Empty queries and name-based scans do not establish worldwide
absence of a formal theorem. No toolchain installation, build, cache
operation, vendor change, or scientific-source change was performed.

The concrete remaining bridge is a higher-dimensional geometric comparison
for the actual arrangement, followed by a Deligne/Garside contractibility
argument for its actual covering model. The existing component/groupoid
comparison cannot replace that argument. Once an exact useful topology
endpoint is selected for this route, its complete immutable source cohort
must undergo local compilation, axiom and physical-declaration coverage,
exact-module replay, and independent statement review before reuse.
