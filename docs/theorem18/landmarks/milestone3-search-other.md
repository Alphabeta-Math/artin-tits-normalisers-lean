# Landmark 3: other GitHub source search

Date: 2026-11-14. This report concerns the actual complement defined in
`ArtinNormalisers/Theorem18/Geometry.lean`, not a substitute classifying space.
The complete geometry file, repository README and landmark plan were read first.
Landmarks 1 and 2 remain proved; this search adds no proof of landmark 3.

## Result and actionable candidate

No inspected repository outside the separately assigned TauCeti/OpenAI search
supplies the full equivariant restricted-arrangement comparison. The closest
actionable generic supplier is **qinz1yang/differential-geometry's genuine
two-open fundamental-groupoid Seifert–van Kampen theorem**, with an eight-file
project import closure. Its literal theorem uses actual topological spaces
and proves a pushout; it does not assume the pushout as a structure field.
It is an alternate generic supplier, not an accepted imported proof.

The other especially relevant search result, the Chen-ranks development,
does define an actual finite complex affine arrangement complement and true
polygonal-path homotopies. It supplies neither the chamber presentation nor
the required comparison/equivariance in the inspected source. Its basic
convex-ball cover is not itself a nerve comparison.

**Execution status for every candidate in this report:** source inspected
only; no build, transitive axiom audit or kernel replay was run. No proof,
configuration or vendor file was modified; no new proof source was copied
or imported. No `lake update`, cache operation or toolchain installation was
performed. A lexical no-hole scan is explicitly not formal verification.

## Exact target boundary

The parent's `Complement M J` is the subtype of
`relativeSubspace J × relativeSubspace J` consisting of pairs `(x,y)` such
that, for every retained actual root `r`, the evaluations `x r` and `y r`
are not both zero. It has the inherited product/subspace topology, transported
from the actual dual coordinates. Retained roots discard those identically
zero on the relative flat; equal restricted hyperplanes are identified in
`restrictedArrangement M J`.

The desired supplier must connect this actual complement to a groupoid
whose generators are geometric positive crossings and whose relations have
been proved to hold and be complete. Reverse positive crossings are separate
generators, not formal inverses. A homotopy-equivalence transport theorem
alone does not construct that equivalence. A generic open-cover theorem
alone does not identify its colimit with the ribbon/Deligne presentation.
The eventual comparison must track the actual normalizer-quotient action and
the `J`-associate component; it cannot assume the quotient acts transitively
on all chambers or use all subsets as one relevant component without proof.

## Complete table of repositories whose source was inspected

All revisions below are full commit pins. “Rejected” means not proposed as a
new supplier for this step; it does not assert that the source theorem is
false. Additional uninspected search hits are recorded separately in the
machine inventory and are not called used or verified proofs.

| Repository and commit | Toolchain; pinned mathlib | License | Inspected source/declarations; application and disposition |
| --- | --- | --- | --- |
| [qinz1yang/differential-geometry](https://github.com/qinz1yang/differential-geometry/tree/13c41a632efb8fbf93101c8a20f2a9214ab33240), `13c41a632efb8fbf93101c8a20f2a9214ab33240` | Lean `v4.35.0-rc3`; mathlib `c55e6e786f49471c72fbddbec5415808896aec1e` | Apache-2.0 | `DifferentialGeometry/Topology/VanKampen/`: full eight-module closure listed below; also `Pi1FiniteConnectedSum.lean` discovery entrypoint and initial `SelectedObjects.lean` definitions. `seifertVanKampen`, `LocalFunctorData`, `LocalFunctorData.extension`, `FundamentalGroupoidOn`, `fundamentalGroupoidMapOn`. Closest genuine generic candidate. Read `FullGroupoid` and discovery entrypoint completely, selected supporting types/proof passages, and mechanically inspected the eight-module import closure; no complete semantic review of that closure. `SelectedObjects` is not part of the proposed small closure. |
| [rkirov/jacobian-claude](https://github.com/rkirov/jacobian-claude/tree/73212f7ef2bb46a7884710b18fe1e18b8509e3e5), `73212f7ef2bb46a7884710b18fe1e18b8509e3e5` | Lean `v4.30.0`; mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` | Apache-2.0 | Entire `Jacobians/SphereTopology/VanKampen.lean` and definition of `TwoOpenVanKampen` in `SphereSimplyConnected.lean`; genuine simply-connected-union corollary, but not groupoid colimit/presentation. Rejected for this comparison. Imported closure not reviewed. |
| [kadirhanpolat/pytop](https://github.com/kadirhanpolat/pytop/tree/46a35a69c4be34b0d503afa171d9c168bba51946), `46a35a69c4be34b0d503afa171d9c168bba51946` | Lean `v4.31.0`; mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` | MIT | Entire `formal/Formal/VanKampen.lean`; `Pushout` is only a cocone, and `pushout_universal` assumes a factor map and its equations. No topological comparison. Rejected; literal type below. |
| [adamtopaz/OrlikSolomon](https://github.com/adamtopaz/OrlikSolomon/tree/1568c3994d24e53d39471ffe810cb076cfbccc8c), `1568c3994d24e53d39471ffe810cb076cfbccc8c` | Lean `v4.36.0-rc2`; mathlib `6db5db0d2279846cc8fb25901bd53221d37a77d8` | Apache-2.0 | Selected definitions/types in `OrlikSolomon/MainTheorem.lean`, searched `Interface/{ProjectiveSpace,ProjectiveComplement}.lean` and book main; `MainTheorem.projectiveSpace`, `HyperplaneArrangement`, `orlikSolomon`. Actual projective **scheme** complement and cohomology-algebra theorem, not the required coordinate-topology/groupoid theorem. Rejected. No complete cohomology implementation audit. |
| [DongzheZheng/Suciu-s-Chen-ranks-conjecture](https://github.com/DongzheZheng/Suciu-s-Chen-ranks-conjecture/tree/3a84cf4619f2c17e55f2e05214e9638e8d3b7634), `3a84cf4619f2c17e55f2e05214e9638e8d3b7634` | Lean `v4.29.0`; mathlib `8a178386ffc0f5fef0b77738bb5449d50efeea95` | No root license file or license notice found in README/inspected source; copying permission not established | Read `ChenRanks/ArrangementObjects.lean`, `ArrangementComplementBallCover.lean`; selected polygonal types/proofs in `ArrangementPolygonalPathHomotopy.lean`. Actual-space near match, but no missing groupoid/Salvetti comparison found. No import recommended; details below. No audit of headline Chen-rank claims. |
| [siddhartha-gadgil/Polylean](https://github.com/siddhartha-gadgil/Polylean/tree/b2379c538307b2ce4a9f9969587232f9d94dd438), `b2379c538307b2ce4a9f9969587232f9d94dd438` | Lean `v4.19.0-rc3`; mathlib `ff99cdaecce8cab2fcc3d3828ab7f79717fbf77a` | Apache-2.0 | Entire `Complexes/Constructions/FundamentalGroupoid.lean`, `Structures/CombinatorialTwoComplex.lean`. A combinatorial edge/relator quotient using a custom `Groupoid`; no comparison to actual topological paths. Rejected as a geometric supplier, despite being Lean 4. |
| [deancureton/sphere-six-complex](https://github.com/deancureton/sphere-six-complex/tree/b783b990d46c5f5ce02a4ecbbb2c02408b452cde), `b783b990d46c5f5ce02a4ecbbb2c02408b452cde` | Lean `v4.35.0-rc3`; mathlib `6b7abb3c7686292736be2955bd3eb9ebf63b456a` | Apache-2.0 | Entire `ForMathlib/AlgebraicTopology/FundamentalGroupoid/Equiv.lean`; `fundamentalGroupMulEquivOfHomotopyEquiv`. Assumes a real homotopy equivalence and wraps mathlib's already available groupoid theorem. Rejected as duplicate, not as invalid. |
| [kangxyz/quillen-k-theory](https://github.com/kangxyz/quillen-k-theory/tree/c561118b7795eb9780be9ed391c3251d6a4d0afd), `c561118b7795eb9780be9ed391c3251d6a4d0afd` | Lean `v4.34.1`; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` | Apache-2.0 | `Quillen/Topology/Realization/HomotopyBridge.lean`, exact declarations and selected proofs: `SSet.realizationSimplicialHomotopy`, `CategoryTheory.classifyingSpaceNaturalTransformationHomotopy`. Genuine realization homotopies; no actual-complement-to-nerve equivalence. Potential later infrastructure only; not recommended now. Cylinder closure not audited. |
| [kangxyz/colib](https://github.com/kangxyz/colib/tree/cf26c9d5d47a6f545202afedc4967f84f483a809), `cf26c9d5d47a6f545202afedc4967f84f483a809` | Lean `v4.35.0`; mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` | Apache-2.0 | `Colib/Topology/Realization/HomotopyBridge.lean`, same named genuine homotopy declarations and selected proofs; file records adaptation from the preceding exact Quillen commit. Duplicate candidate family; no complement comparison, no current import recommendation. Cylinder closure not audited. |
| [facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean/tree/219463bef604b0624fc2fc623a75a77678ce10e7), `219463bef604b0624fc2fc623a75a77678ce10e7` | Lean `v4.35.0`; mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` | `LICENSE` has Apache-2.0 text preceded by an ML-use notice; no reuse or interpretation of that notice asserted here | Entire `v1/Atlas/Buildings/code/Reflection/HyperplaneChambers.lean`; `AffineHyperplane`, `HyperplaneArrangement`, `Chamber`, `HalfSpaceConvex`, `HalfSpaceOpen`. Actual real hyperplanes/chambers, but no complex complement or groupoid comparison in inspected file. Basic half-space facts already in mathlib. Rejected for this supplier role. Other Atlas proofs not reviewed. |
| [SauersML/group-approximation](https://github.com/SauersML/group-approximation/tree/b4cbab68177c23556f0db49f8a45a431729f6e23), `b4cbab68177c23556f0db49f8a45a431729f6e23` | Lean `v4.32.0`; mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` | Apache-2.0 | Opening definitions/`outer_word` proof in `GroupApproximation/GGT/VanKampen/NullWordDisc.lean`; relative word diagrams and prescribed boundary labels. These algebraic van Kampen diagrams do not constitute a topological open-cover theorem. Rejected for M3 comparison. Numerous search hits are not counted as read proofs. |
| [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4/tree/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9), `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9` | Existing project pin, Lean `v4.36.0-rc2` | Apache-2.0 | Exact types/proof portions in `Mathlib/AlgebraicTopology/FundamentalGroupoid/InducedMaps.lean` and `Mathlib/Analysis/Convex/Contractible.lean`; existing baseline API below. Already pinned, not a newly added external dependency. No new verification asserted by this search. |

## Literal strongest generic theorem

At the pinned qinz1yang commit,
[`DifferentialGeometry/Topology/VanKampen/FullGroupoid.lean`](https://github.com/qinz1yang/differential-geometry/blob/13c41a632efb8fbf93101c8a20f2a9214ab33240/DifferentialGeometry/Topology/VanKampen/FullGroupoid.lean)
defines `fullGroupoidSquareIsPushoutStatement U V` as the actual `IsPushout`
in `Grpd` of these four objects and continuous inclusion-induced functors:

```text
FundamentalGroupoid (U ∩ V) → FundamentalGroupoid U
             ↓                         ↓
FundamentalGroupoid V       → FundamentalGroupoid X.
```

The exact exported declaration is:

```lean
theorem seifertVanKampen {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) :
    fullGroupoidSquareIsPushoutStatement U V
```

The namespace is `DifferentialGeometry.Topology.VanKampen`. No path-connectedness,
simply-connectedness, local-contractibility or dimension assumption is hidden
in this declaration. In `Evaluation.lean`, `LocalFunctorData U V G` contains
only functors from the two actual fundamental groupoids into `G`, plus their
agreement after restriction to `U ∩ V`. Its `extension` is **constructed** by
path subdivision and evaluation, descended through proved homotopy invariance;
its extension and uniqueness properties produce the pushout proof. No
extension-existence or desired pushout field is assumed in that data.

Its project closure is exactly these eight modules, in a possible dependency
build order:

1. `DifferentialGeometry.Topology.VanKampen.Subdivision`
2. `DifferentialGeometry.Topology.VanKampen.CoveredPath`
3. `DifferentialGeometry.Topology.VanKampen.Evaluation`
4. `DifferentialGeometry.Topology.VanKampen.HomotopyGrid`
5. `DifferentialGeometry.Topology.VanKampen.CellIdentity`
6. `DifferentialGeometry.Topology.VanKampen.GroupoidTelescope`
7. `DifferentialGeometry.Topology.VanKampen.HomotopyInvariance`
8. `DifferentialGeometry.Topology.VanKampen.FullGroupoid`

All remaining imports are mathlib modules: fundamental groupoid basics,
composable arrows, groupoids, categorical pushouts, product homotopies,
metric-space lemmas and subpaths. A lexical scan with comments removed found
no `sorry`, `admit`, `axiom`, `native_decide` or `unsafe` token in this closure.
That scan neither checks elaboration nor certifies transitive axioms.

Possible actual application: choose genuine open subsets of `Complement M J`,
prove they cover, and apply the theorem to construct/characterize its
fundamental groupoid from the restrictions. For a finite chamber-indexed
cover, one would still have to derive the iterated/multiple-overlap colimit,
identify all intersection components and their paths/relations, and prove the
Deligne/ribbon presentation and normalizer equivariance. These are substantial
new bridges, not consequences of this theorem's name. The separately examined
TauCeti Čech theorem may be a more direct generic API; do not import two
parallel van Kampen implementations without need.

If selected after the actual-cover route is fixed, verification should copy
only this unchanged eight-module closure into an isolated test package using
the project's existing Lean/mathlib pins, preserving Apache headers and
binding upstream/local hashes. A proposed initial command, **not run here**,
is `lake build DifferentialGeometry.Topology.VanKampen.FullGroupoid` after
declaring that test library. Then inspect its elaborated statement and audit
all declarations of all eight modules, allowing only `propext`,
`Classical.choice`, `Quot.sound`; run the existing project's supported
single-module checker form for each module. The upstream package's older
toolchain is not a reason to replace this project's pins. A successful
upstream build alone would not certify the port or its application.

## Literal definitions behind the other close results

The Chen-ranks repository's `ChenRanks.AffineArrangement d ι` has a finite
index type and fields `normal : ι → (Fin d → ℂ) →ₗ[ℂ] ℂ`, `offset : ι → ℂ`,
nonzero normals, and pairwise distinct equation zero sets. It defines

```lean
def Complement := {x : Fin d → ℂ // ∀ i, A.normal i x ≠ A.offset i}
```

with the induced topology. Its `actualPolygonalApproximationHomotopy`, for an
actual `γ : Path x y` in `A.Complement`, constructs a fixed-endpoint path
homotopy from the actual polygonal approximation to the full subpath of `γ`.
`ActualComplementBall` contains an actual center/radius, positivity and proof
the ambient ball lies in the complement; `actualComplementBallAt` constructs
such a ball at each point from proved openness, and
`mem_actualComplementBallBaseSet_at` proves the resulting cover property.

This is not a surrogate space. To apply it here requires a proved finite
complex-coordinate identification of the relative real-pair vector space,
complexification of the distinct retained hyperplanes, and equality of the
two removed sets/topologies. Such a bridge is mathematically possible but was
not constructed by this search. These results still do not supply homotopy
**completeness** of chamber relations or equivariance. Existing project
path-connectedness already addresses a simpler part of this geometry.

The jacobian repository's `TwoOpenVanKampen` expands to: every path-connected
topological `Z : Type` covered by open simply-connected `U,V` with
path-connected intersection is simply connected. Its
`Jacobians.RiemannSphere.VanKampen.twoOpenVanKampen_holds` proves that exact
proposition by actual subdivisions, spokes and path-homotopy telescoping.
It is a genuine corollary, but cannot replace a presentation of the generally
nontrivial fundamental groupoid of a hyperplane complement.

The pytop file is a concrete rejected assumed-conclusion case:
`VanKampen.Pushout datum A` contains only `i₁`, `i₂`, and their compatibility
for **additive commutative** groups. `pushout_universal` is given an arbitrary
`u : A →+ K` plus
`hu₁ : ∀ g₁, u (po.i₁ g₁) = f₁ g₁` and
`hu₂ : ∀ g₂, u (po.i₂ g₂) = f₂ g₂`; its conclusion is just the conjunction
of those equations for each pair `(g₁,g₂)`. Its proof is
`fun g₁ g₂ => ⟨hu₁ g₁, hu₂ g₂⟩`. It constructs no universal factor or
topological path identification. The file's own Scope paragraph states this
limitation; no false topological theorem is attributed to it.

Polylean's `FundamentalGroupoid` is an instance on a
`CombinatorialTwoComplex`: its homs are quotients of combinatorial edge paths
by an inductively defined relator homotopy. It uses a custom `Groupoid` and
`SerreGraph` reversal. It does not prove those are topological paths of a
realized space, so naming it a fundamental groupoid does not fill the bridge.

The two Kang repositories' exact useful form is
`SSet.realizationSimplicialHomotopy (H : SSet.Homotopy f g) :
(SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom`, and the analogous
homotopy of classifying maps from a natural transformation `α : F ⟶ G`.
These relate actual realizations, but no map from our complement, chamber
good cover, or equivariant homotopy inverse is present in the inspected file.

## Existing mathlib APIs and duplication screen

At the project's existing pin,
`FundamentalGroupoidFunctor.equivOfHomotopyEquiv (e : X ≃ₕ Y)` already gives
an equivalence of the actual fundamental groupoids. The neighboring
`homotopicMapsNatIso` constructs the natural transformation of path-class
functors from an actual continuous homotopy. The sphere-six-complex wrapper
then takes endomorphism groups via fully faithfulness; this supplies no new
geometric comparison.

`Convex.contractibleSpace (hs : Convex ℝ s) (hne : s.Nonempty)` already proves
`ContractibleSpace s` in a real topological vector space with continuous
addition and scalar multiplication. This is suitable for genuine convex
finite intersections of a proposed good cover once their inclusion/cover
conditions have been proved. The existing dual-coordinate topology supplies
the appropriate continuous vector-space structure. None of these facts
identifies a nerve with the actual complement by itself.

Searched the pinned fundamental-groupoid/simplicial-groupoid modules and
related file names for a ready-made open-cover comparison. No such result
was located in that bounded inspection; this is not an assertion about all
future or uninspected mathlib declarations.

## Search record, provenance and limits

Used `gh search repos`, `gh search code`, raw pinned GitHub URLs via Python's
HTTPS client, and isolated `/tmp` shallow clones. Search terms included
`Salvetti`, `DeligneGroupoid`, `HyperplaneArrangement`, `FundamentalGroupoid`,
`vanKampen`, `hyperplane complement`, `complexified`, `GoodCover`, and
`nerve contractible`, with Lean/`.lean` filters and a second pass explicitly
excluding `openai/math` and `leanprover-community/mathlib4`.

The observed `Salvetti`, `DeligneGroupoid`, and explicit excluded-repository
`Deligne groupoid`, `complexified`, `GoodCover`, `nerve contractible` queries
returned no results. This is a GitHub-index/API observation, not proof of
worldwide absence. Several earlier requests received HTTP 429/403 search-rate
errors; the affected later query families were retried successfully in the
second pass. Search is bounded by indexing, branch selection and result caps.

The temporary machine inventory is `/tmp/m3-other-inventory.json`. It has
the twelve source-inspected repositories, full commits, licenses, source
hashes, declaration names, application/disposition, reading limits and
explicit false build/audit/replay/acceptance flags. It separately lists
twenty-eight repositories appearing as code-search hits, without calling
those hits proof use. Query records are in
`/tmp/milestone3-other-search.json` and `/tmp/m3-search-round2.json`;
the full qinz import/hash inventory is
`/tmp/m3-qinz-fullgroupoid-closure.json`. These temporary inventories are
provided for the root's central provenance register; this report is the only
repository file authored by this task.

No mathematical defect was established in the consulted source passages.
Rejected applicability, missing local formalization, unknown reuse permission
and unexecuted verification are recorded as such, not as article defects or
false mathematics. No external proof is accepted from theorem marketing,
badges, source appearance or `#check`.
