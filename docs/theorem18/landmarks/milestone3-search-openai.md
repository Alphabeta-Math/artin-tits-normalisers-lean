# Landmark 3: geometric supplier search

Research date: 2026-11-14. This is a source inspection, not supplier
acceptance. No candidate was built, axiom-audited, or kernel-replayed in
this search. No source, vendor, configuration, or shared cache was changed.

## Actionable result

The best concrete candidate is **TauCeti's groupoid van Kampen theorem**,
already present at the project's previously inspected TauCeti revision.
It proves a colimit statement about Mathlib's actual topological
`FundamentalGroupoid X`, using actual open subspaces and their inclusions.
Its cover-map naturality identifies the colimit-induced functor with the
actual continuous-map-induced functor. It does not assume the arrangement
comparison as a field or replace the complement by a combinatorial space.

This can supply the generic gluing step after constructing the article's
chamber/tube cover of the actual relative complement. It supplies neither
that cover nor its local geometry, chamber generators, minimal-gallery
relations, or their identification with reduced ribbons. Those remain
substantial landmark 3 work. No directly applicable general arrangement
Salvetti/Deligne comparison theorem was found in the inspected sources.

The ordinary Artin Salvetti development in openai/math still has the wrong
domain for immediate use. A newly inspected alternative, zstone1/Cubical,
has substantive combinatorial Salvetti constructions, but no comparison
with an actual complex hyperplane complement in the inspected development.

## Pinned sources

| Repository | Inspected revision | Lean | mathlib revision | License |
| --- | --- | --- | --- | --- |
| [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti/tree/62bbc0596dc3539d488232e4e924a338548ea0a9) | `62bbc0596dc3539d488232e4e924a338548ea0a9` | `v4.36.0-rc2` | `e8ba86fa9744dd8d90f48c1752bc735f61a4ca81` | Apache-2.0 |
| [openai/math](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae) | `4eaee87548250b2682affda7d05d947c05554bae` | `v4.34.1` | `d13f23b723b8a846827a245b89c10fc7d3f11612` | Apache-2.0 |
| [mathcommunity/oai-math-revised](https://github.com/mathcommunity/oai-math-revised/tree/d25fae85c2f5ce5aadac40fb2b4c2d332b393d1c) | `d25fae85c2f5ce5aadac40fb2b4c2d332b393d1c` | `v4.34.1` | `d13f23b723b8a846827a245b89c10fc7d3f11612` | Apache-2.0 |
| [zstone1/Cubical](https://github.com/zstone1/Cubical/tree/5339856b84db66f7ba3b831c00d40264447b8d21) | `5339856b84db66f7ba3b831c00d40264447b8d21` | `v4.30.0` | `c5ea00351c28e24afc9f0f84379aa41082b1188f` | No license file found in complete tree; GitHub metadata reports none |

The current project's mathlib pin is
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. Matching TauCeti's Lean
toolchain does not establish compatibility with this different mathlib pin.
A fresh remote metadata check also found newer TauCeti HEAD
`130523811f55c80f533e6024e190b945755f93c5`; the endpoint analysis and closure
counts below deliberately refer to **62bbc059**, not to that moving HEAD.

## TauCeti: actual open-cover groupoid gluing

All paths in this section are relative to `TauCeti/`, and names are in
`TauCeti.FundamentalGroupoid` unless explicitly qualified.

### Literal spaces, diagram, and colimit

[`Topology/Category/TopCat/Cech/Diagram.lean`](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Topology/Category/TopCat/Cech/Diagram.lean)
defines, for `X : TopCat` and `U : ι → Opens X`,

```lean
abbrev CechIndex (ι : Type u) := OrderDual {s : Finset ι // s.Nonempty}
def cechIntersection (s : CechIndex ι) : Opens X := s.1.inf U
```

Here nonempty means the **index finite set**, not an assumption that the
intersection itself contains a point. Empty and disconnected intersections
are allowed. The topological diagram consists of the actual subtype spaces
`TopCat.of (cechIntersection U s)` and actual inclusions, ordered by reverse
inclusion of finite index sets.

[`AlgebraicTopology/FundamentalGroupoid/Cech/Diagram.lean`](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/FundamentalGroupoid/Cech/Diagram.lean)
defines

```lean
def cechDiagram : CechIndex ι ⥤ Grpd :=
  cechTopDiagram U ⋙ _root_.FundamentalGroupoid.fundamentalGroupoidFunctor
```

`cechCocone U` is the image under that same Mathlib functor of the cocone
of inclusions into `X`. Its point is definitionally the actual fundamental
groupoid of `X`, not a freely generated substitute.

The main endpoint in
[`Cech/Colimit.lean`, line 125](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/FundamentalGroupoid/Cech/Colimit.lean#L125)
is exactly

```lean
def isColimitCechCocone (hU : IsOpenCover U) : IsColimit (cechCocone U)
```

There is no connectedness, contractibility, good-cover, finiteness, or
arrangement hypothesis. The only additional hypothesis is that `U` covers.
The result is a strict categorical colimit in `Grpd`; it is not a theorem
that the geometric realization of a nerve is homotopy equivalent to `X`.
That distinction prevents upgrading it to an asphericity theorem.

### The comparison functor is constructed from genuine paths

[`Glue.lean`](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/FundamentalGroupoid/Glue.lean)
works more generally with `U : ι → Set X` and

```lean
hU : ∀ x, ∃ i, U i ∈ 𝓝 x
F : ∀ i, _root_.FundamentalGroupoid (U i) ⥤ D
hF : ∀ i j,
  map (ContinuousMap.inclusion inter_subset_left) ⋙ F i =
  map (ContinuousMap.inclusion inter_subset_right) ⋙ F j
```

for any target category `D`. It constructs
`glue hU F hF : _root_.FundamentalGroupoid X ⥤ D`.
The proof subdivides paths using a Lebesgue number, evaluates each segment
in a cover piece, proves independence of subdivision, and subdivides an
actual path homotopy into small squares to prove homotopy invariance.
`map_subtypeVal_comp_glue` proves the required local restriction equation;
`eq_glue` proves uniqueness. The local agreement `hF` is the legitimate
input for gluing, not an assumed global equivalence to the target.

`CoverGeneration.iSup_im_map_subtypeVal_eq_top` proves that actual cover
inclusion functors generate the fundamental groupoid; `functor_ext` makes
local equality sufficient for global equality. These may be useful even
if the final construction uses explicit functors instead of colimits.

### Actual continuous-map naturality and equivariance limit

[`Cech/Map.lean`](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/FundamentalGroupoid/Cech/Map.lean)
has data

```lean
U : ι → Opens X
V : κ → Opens Y
f : X ⟶ Y
r : ι → κ
hf : ∀ i, Set.MapsTo f (U i) (V (r i))
```

and constructs `cechMapNatTrans U V f r hf`. The endpoint is

```lean
lemma isColimit_desc_cechMapCocone (hU : IsColimit (cechCocone U)) :
  hU.desc (cechMapCocone U V f r hf) =
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map f
```

Thus the source colimit hypothesis can be discharged by the preceding
open-cover theorem. No target cover hypothesis is needed for this equality.
For each normalizer element, a genuine continuous action map and its
action on cover indices would instantiate this theorem. It does not
construct that action, prove that it preserves a chosen arrangement cover,
or establish coherence for an independently chosen chamber comparison.

`Cech/Refinement.lean` similarly constructs refinement transformations for
`hr : ∀ i, U i ≤ V (r i)` and proves compatibility with actual inclusions.
`Cech/Ext.lean` gives uniqueness from the singleton legs of an open cover.

### Source closure, hypotheses, and proposed minimal pilot

Counts include each named root and all transitively imported TauCeti
modules, excluding Mathlib. Counted source lines include comments and blanks.
The import traversal handles `public import` and `import all` visibility.

| Requested roots | TauCeti modules | Lines |
| --- | ---: | ---: |
| `FundamentalGroupoid.Cech.Colimit` | 9 | 2,504 |
| `FundamentalGroupoid.Cech.Map` | 5 | 565 |
| Colimit + Map union | **12** | **2,823** |
| Colimit + Map + Ext + Refinement union | 14 | 2,957 |
| `FundamentalGroupoid.Pushout` alone | 9 | 2,753 |
| `FundamentalGroup.VanKampen.Presentation.Cover` alone | 19 | 5,316 |

The twelve-module Colimit + Map union consists of:

```text
TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
TauCeti.AlgebraicTopology.FundamentalGroupoid.Cech.Colimit
TauCeti.AlgebraicTopology.FundamentalGroupoid.Cech.Diagram
TauCeti.AlgebraicTopology.FundamentalGroupoid.Cech.Map
TauCeti.AlgebraicTopology.FundamentalGroupoid.CoverGeneration
TauCeti.AlgebraicTopology.FundamentalGroupoid.Glue
TauCeti.Topology.Category.TopCat.Cech.Diagram
TauCeti.Topology.Category.TopCat.Cech.Map
TauCeti.Topology.Category.TopCat.Cech.Refinement
TauCeti.Topology.Homotopy.Path
TauCeti.Topology.MetricSpace.Lebesgue
TauCeti.Topology.UnitInterval
```

All other direct imports in this closure are Mathlib. The topology roots
do not import a whole-repository `TauCeti` root or external packages.
The finite-dimensional arrangement target can use their arbitrary-space
interfaces without changing its definition or supplying an Artin hypothesis.
The twelve-module union is the recommended first compatibility/audit pilot,
if reuse is authorized; no pilot was run here.

The additional based-group presentation endpoint is genuine but less
suitable for the chamber cover:

```lean
def vanKampenCoverQuotientEquiv
    (hCover : ∀ y, ∃ i, U i ∈ 𝓝 y)
    (hTriple : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k)) :
    (Monoid.CoprodI (fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩)) ⧸
      vanKampenCoverRelations U x hx ≃* FundamentalGroup X x
```

It additionally has `hx : ∀ i, x ∈ U i`, requiring a common basepoint in
all members. Its relation subgroup is the normal closure of actual overlap
loop images. It does not present the desired many-object chamber groupoid.
`isPushout_fundamentalGroupoidOn` avoids a single basepoint for a two-set
cover, but requires a chosen set meeting every path component of both
members and their intersection; this geometry must still be proved.

The full fourteen-module Čech union was text-screened for `sorry`, `admit`,
`native_decide`, and custom `axiom` declarations after removing comments;
no matches were found. Full endpoint modules and the concrete path/homotopy
construction in `Glue` were read; auxiliary interval and metric proofs were
not independently checked line by line. Text screening is not a transitive
axiom audit or successful elaboration. Upstream CI/audit comments are not
used here as evidence of local acceptance.

## openai/math: ordinary Salvetti remains an indirect candidate

The exact source-domain assessment in
[the earlier report](../search-openai.md) still applies. The complete
ArtinGroups subtree is `0b8f7c175022e4696404bb2bbabf12746f899d14`, identical
in the two OAI repositories at the revisions above. The actual definitions
and endpoints were re-read, including `Model.lean`, `Realizations/CellUnion.lean`,
and `Realizations/SalvettiProjection.lean`:

```lean
abbrev Artin (M : CoxeterMatrix S) := PresentedGroup (braidRelators M)
abbrev LiftedCell (M : CoxeterMatrix S) := Artin M × SphericalType M
noncomputable def SalvettiCover (M : CoxeterMatrix S) : TopCat :=
  SSet.toTop.obj (CategoryTheory.nerve (LiftedCell M))
def SourceSalvetti :=
  Quotient (Relation.EqvGen.setoid (SourceFaceIdentification M))
noncomputable def sourceFundamentalGroupEquiv (x : SourceSalvetti M) :
  FundamentalGroup (SourceSalvetti M) x ≃* Artin M
```

`SourceSalvetti` glues actual spherical Coxeter permutahedra via explicit
face maps. It is a substantive combinatorial topological space, but it is
not the article's complexified relative arrangement complement. There is
no relative `J`, restricted arrangement `H_J`, or corresponding normalizer
action in these interfaces. `sourceSalvettiProjection_universal` concerns
the nerve realization above, not points of the actual complex complement.
The fundamental-group isomorphism chooses a lift and adjusts the opposite
group through inversion; its type gives no generator or monodromy equation.

The exact `SalvettiProjection` import closure was recomputed: **617 OAI
modules, 59,545 lines**, no missing OAI imports, and `Mathlib` as the only
other direct import. The module identifier
`MulBlockDiagonal'Entry` contains an apostrophe; truncating it would produce
a spurious missing dependency. This large topology closure has not inherited
verification from the separate, accepted 359-module positive algebra closure.
No claim about its full proof correctness follows from this search.

No arrangement-independent good-cover comparison endpoint was identified
in the inspected ArtinGroups sources that bridges to the relative target.
Specializing an ordinary Coxeter matrix cannot be justified by sphericality
alone: the relative arrangement need not be a Coxeter arrangement and its
normalizer need not act transitively on chambers.

## Additional GitHub candidate: zstone1/Cubical

The complete immutable repository tree has 276 entries and is not truncated;
the complete archive was downloaded for source inspection. Its
`CubeChains/Machinery/Arrangement/COM.lean` defines a legitimate abstract
complex of oriented matroids by sign vectors, face symmetry, and strong
elimination. `Sal.lean` defines Salvetti cells as face/tope pairs

```lean
{p : SignVec E × SignVec E //
  p.1 ∈ L.covectors ∧ L.IsTope p.2 ∧ p.1 ⊑ p.2}
```

with the usual face/tope order, and `Sal L` abbreviates this poset. Its
`Braid.lean` constructs type-A covectors as signs of differences of integer
height functions `Fin n → ℤ`. These are real combinatorial contents, not a
formalization of the actual complex complement.

`Concurrency/Salvetti/SalCompare.lean` proves `Models.salEquiv` and
`Models.hbpEquiv`, but its input is explicitly

```lean
structure Models (L : COM E) (K : BPSet) where
  base : (Ch K)ᵒᵖ ≌ COM.Face L
  fibre : Lines K ≅ base.functor ⋙ COM.salFunctor L
```

Thus it transports already supplied combinatorial equivalences. The term
“complexification” here refers to a decorated cubical-presheaf construction,
not to deleting complexified real hyperplanes from a complex vector space.
`Complexification/HPresentation.lean` defines chamber and wall-crossing
objects/morphisms in a categorical localization. It gives no comparison
map into Mathlib's topological fundamental groupoid.

`PaperSalvetti.lean` itself records gaps in identifying degree-two boundaries
with alternating wall paths and in its braid comparison square. The file's
positive braid translation category is not a fundamental groupoid. A source
search across CubeChains found no `FundamentalGroup`, `FundamentalGroupoid`,
`IsCoveringMap`, `TopologicalSpace`, `Continuous`, or `Homeomorph` interface
providing the missing ordinary-topological comparison. No build or compiled
axiom audit was performed, and the absence of an identifiable license is
an additional obstacle to actual reuse. This is not a direct supplier for
landmark 3; importing its categorical Salvetti comparison would leave the
central geometric bridge unproved.

## Remaining bridge and search limits

The useful next step is to construct the article's actual chamber/tube
open cover of `Complement M J`, classify its intersection components and
their path homotopies, and build local functors to the desired chamber
groupoid. TauCeti's gluing theorem could then construct the functor on
all actual path classes, while its naturality theorem could establish
compatibility with the actual normalizer action. Essential surjectivity,
full faithfulness, gallery relations, quotient compatibility, and the map
to the actual reduced ribbon groupoid remain obligations. A generic
van Kampen theorem does not discharge them by naming the resulting colimit.

GitHub code searches included `Salvetti`, `HyperplaneArrangement`,
`vanKampen`, and repository-scoped fundamental-groupoid/equivariance terms.
The 100-result general van Kampen query was capped and contained many
combinatorial disc-diagram developments. Search results were leads, not
accepted proofs. Earlier OrlikSolomon/atlas inspections are recorded in
[search-additional.md](../search-additional.md); their algebraic or poset
interfaces do not supply this ordinary-topological comparison.

The complete local pinned TauCeti source tree (31,750 Lean files) was
searched for Salvetti/arrangement-complement terminology and corresponding
paths; no arrangement comparison was found by those terms. This is a
bounded text search, not a semantic inspection of all files. The earlier
complete OAI Topology/Geometry/AlgebraicTopology subtree inventories remain
the scope of the wider OAI name search; the truncated repository-wide tree
does not justify an exhaustive absence claim. The Cubical endpoint modules
above were read, not every dependency body. No assertion is made that no
applicable formal proof exists anywhere on GitHub.

### Complete register for this search's GitHub leads

The table above records the sources actually read or compared. The table
below records **every repository returned by this agent's saved general
Salvetti, HyperplaneArrangement, and vanKampen code queries**, including
negative and uninspected leads. Each revision is the immutable blob revision
in the returned search URL, not an inferred current default-branch pin.
Except for openai/math and Cubical already discussed, no proof body was
read or executed from these hits in this search. OrlikSolomon and atlas
had earlier inspections recorded separately. No source from these leads
was imported or accepted. Other agents' co-located temporary search files
are not presented as this agent's inspections.

| Search-result repository | Exact result revision | License metadata |
| --- | --- | --- |
| SauersML/group-approximation | `b4cbab68177c23556f0db49f8a45a431729f6e23` | Apache-2.0 |
| adamtopaz/OrlikSolomon | `1568c3994d24e53d39471ffe810cb076cfbccc8c` | Apache-2.0 |
| dzackgarza/lean-categories | `064b5cfdae80fd27c7af1b0c9a7a8bbc5547e55b` | Not identified |
| facebookresearch/atlas-lean | `219463bef604b0624fc2fc623a75a77678ce10e7` | NOASSERTION |
| frenzymath/PoincareConjecture | `62db01af9388dc1d9b56b66d6674f4c09b2318a2` | Not identified |
| igor024/math | `37fa9a502d652590420333ea1e18a2140cf7ebe3` | Apache-2.0 |
| jingyuanli-hk/openai_math | `746117c6ca34e6831fdfae4c25d02f3e1414691a` | Apache-2.0 |
| kadirhanpolat/pytop | `46a35a69c4be34b0d503afa171d9c168bba51946` | MIT |
| marpaia/crnt-lean | `7386777488a41efd92e6abc2bccf889fb611660e` | MIT |
| math-proof/lemma | `d11e6179cdf04f9aa8539166bbf6f26778f3e641` | Not identified |
| openai/math | `4eaee87548250b2682affda7d05d947c05554bae` | Apache-2.0 |
| paulklemstine/Lean | `97c0b27619bf5070a44d5eda332784c5f979af6a` | Not identified |
| psalmprax/science | `c837d8d188fc2bcc2e4ca4895a1e42325331ac08` | MIT |
| qinz1yang/differential-geometry | `13c41a632efb8fbf93101c8a20f2a9214ab33240` | Apache-2.0 |
| rkirov/jacobian-claude | `73212f7ef2bb46a7884710b18fe1e18b8509e3e5` | NOASSERTION |
| zstone1/Cubical | `5339856b84db66f7ba3b831c00d40264447b8d21` | Not identified |

For uninspected leads the license column is GitHub repository metadata
queried on the research date, not a pinned license-file review or reuse
permission determination. `NOASSERTION` is GitHub's literal SPDX field.
The exact search query inventories, including all returned paths and URLs,
are `m3-openai-salvetti-search.json` (68 results),
`m3-openai-arrangement-search.json` (52), and
`m3-openai-vankampen-search.json` (100, capped), under the temporary
directory below. A machine register merges these sixteen hit repositories
with the pinned TauCeti and revised-OAI scoped inspections, preserving
reading/execution limits and the TauCeti module hashes/import edges.

Temporary supporting inventories are
`/tmp/artin-landmark3-search/tauceti-cech-closure.json` and
`/tmp/artin-landmark3-search/oai-salvetti-closure.json`, plus
`/tmp/artin-landmark3-search/m3-openai-candidate-register.json`; they are research
working files, not durable acceptance certificates. Any actual reuse still
requires immutable byte provenance, local elaboration, full declaration and
axiom coverage, exact-module kernel replay, and independent review.

## Subsequent authorized supplier verification

After the read-only search, the parent authorized the nine-module addition
under `chambers/vendor/ArtinChamberVendor/`. The three existing TauCeti
overlaps were byte-compared with upstream and reused unchanged. Original
bytes, Apache-2.0 license, full import graph, hashes, and unified patches are
recorded in `chambers/vendor/provenance.json`. The only source edits relocate
imports among these nine new modules; all namespaces and non-import text
remain unchanged. No proof or mathematical hypothesis port was needed.

All nine explicit targets built successfully against the current pinned
Lean/mathlib. The executed `chambers/ProviderAudit.lean` checked 232 canonical
declarations, including private/generated declarations, for transitive use
of only `propext`, `Classical.choice`, and `Quot.sound`. It also loaded the
physical compiled module parts: all 232 physical occurrences matched the
canonical types, values and universe parameters, with no duplicates.
All nine official exact single-module kernel replays then exited zero,
sequentially, in 52.09 seconds total. Source and compiled-provider input
hashes were unchanged across the audit and replay; parent vendor sources
were preserved. These replays are relative to imported Mathlib and the old
providers, not an independent kernel implementation.

The aggregate executed-check record is
`chambers/evidence/providers/verification.json`; it links the raw build,
audit, and nine replay logs, per-command exits/durations, input inventories,
physical coverage, and actual tool paths/hashes. Source-hash-bound independent
statement/diff review and parent acceptance remain separate obligations.
This verifies generic gluing suppliers only. Landmark 3 and Theorem 1.8 are
not proved by these checks.
