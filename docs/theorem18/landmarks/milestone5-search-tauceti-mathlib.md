# Landmark 5: TauCeti, mathlib, and bounded supplementary GitHub search

Search snapshot: 2026-11-14. Project baseline: `22301de0ff626dbfb3d8ae66a6bccc50317de702`.
Machine inventory: [`m5-tauceti-inventory.json`](../../provenance/searches/m5-tauceti-inventory.json).

## Result and scope

The inspected sources supply genuine higher-homotopy definitions, covering transfer, an actual path-class universal cover, and compactness tools. This search did **not** establish asphericity of the actual finite central simplicial arrangement complement, an actual comparison with a contractible Deligne complex, or a directed contractible-open exhaustion of its universal cover. These are the outstanding geometric inputs. This is a bounded source search, not a claim that no external proof exists.

At the initial search stage no new proof/module was imported, copied, built, axiom-audited, kernel-replayed, or accepted. Root subsequently selected the 11-module topology cohort described below for actual staging and verification; acceptance remains a separate step. Existing accepted vendor APIs are distinguished below from unselected source candidates. Prior acceptance is recorded in `vendor/theorem18-provenance.json`; that earlier evidence was consulted, not freshly rerun here. A source-inspected candidate is not formally verified by this report.

The existing M3 equivalence of the interval groupoid with the fundamental groupoid of the actual complement supplies information about paths and their homotopy classes. It does not imply vanishing of higher homotopy groups. The actual complement remains the subtype in `ArtinNormalisers/Theorem18/Geometry.lean`, with the inherited topology and the condition that no retained relative root vanishes on both real coordinates; it is not replaced by a classifying space.

## Pins and licenses

| Repository | Full commit inspected | Toolchain / mathlib pin | License and disposition |
| --- | --- | --- | --- |
| `leanprover-community/mathlib4` | `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9` | Project Lean `v4.36.0-rc2` | Apache-2.0; existing dependency, no update. |
| `TauCetiProject/TauCeti` | `62bbc0596dc3539d488232e4e924a338548ea0a9` | Lean `v4.36.0-rc2`; upstream mathlib `e8ba86fa9744dd8d90f48c1752bc735f61a4ca81` | Apache-2.0; existing selected closure plus unselected candidates. |
| `TauCetiProject/TauCeti` latest comparison | `130523811f55c80f533e6024e190b945755f93c5` | Same Lean and upstream mathlib pins | Apache-2.0; five relevant files compared byte-for-byte with the old pin and unchanged. |
| `zstone1/Cubical` | `5339856b84db66f7ba3b831c00d40264447b8d21` | Lean `v4.30.0`; mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` | No LICENSE/COPYING path found in inspected tracked tree; no copying proposed. Combinatorial category comparison only. |
| `Arthur742Ramos/ComputationalPathsLean` | `257c659b7973aeda900d86a5da73b208712c7523` | Lean `v4.33.0`; mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` | MIT; inspected nerve interfaces do not prove a topological nerve theorem. |
| `SauersML/group-approximation` | `b4cbab68177c23556f0db49f8a45a431729f6e23` | Lean `v4.32.0`; mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` | Apache-2.0; search hit was a large umbrella import file, not an arrangement theorem. |
| `itakura-hidetoshi/KuuOS` | `1a03908757fd0fcdb1acd5199b51dffd5208c3f8` | Root Lean `v4.30.0-rc2`; formal subdirectory config/manifest not found at probed paths | Apache-2.0; finite graph/list certificates explicitly do not claim a classical nerve theorem. |

Exact source SHA256s, import lists, selected metadata files, read limits, search-hit repositories, failures and dispositions are preserved in the machine inventory. Search-hit-only repositories were not source-read, used, or verified; their pins are those in returned GitHub blob URLs, not inferred current HEADs.

## The actual all-degree property already available

`vendor/TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean` defines:

```lean
def TauCeti.IsAspherical (X : Type*) [TopologicalSpace X] (x : X) : Prop :=
  PathConnectedSpace X ∧ ∀ n, Subsingleton (π_ (n + 2) X x)

def TauCeti.IsEilenbergMacLaneSpaceOne (G : Type*) [Group G]
    (X : Type*) [TopologicalSpace X] (x : X) : Prop :=
  IsAspherical X x ∧ Nonempty (FundamentalGroup X x ≃* G)
```

Here mathlib's generalized loops are actual continuous maps from the cube `(N → unitInterval)` to `X`, sending its boundary `{y | ∃ i, y i = 0 ∨ y i = 1}` to the basepoint. `π_ n` is the quotient by homotopy relative to that boundary, using `Fin n`. Thus the first predicate quantifies over every dimension at least two. It is not just a statement about π₁, π₂, a discrete groupoid, or an assumed classifying-space equivalence.

The unselected `TauCeti/AlgebraicTopology/EilenbergMacLane/Degree.lean:57` additionally defines:

```lean
IsEilenbergMacLaneSpace G n X x :=
  PathConnectedSpace X ∧
  (∀ k, k ≠ 0 → k ≠ n → Subsingleton (π_ k X x)) ∧
  Nonempty (π_ n X x ≃* G)
```

It requires `[NeZero n]`; at degree one, its theorem `isEilenbergMacLaneSpace_one_iff` relates this to the existing degree-one predicate. This is a definition/packaging API, not a proof of arrangement asphericity. Literal degree definition and surrounding main APIs were read; the entire file was not proof-reviewed.

Mathlib `Topology/Homotopy/Contractible.lean:52` defines `ContractibleSpace X` by `Nonempty (X ≃ₕ Unit)`, and provides `id_nullhomotopic`. The hypothesis is a genuine contraction up to continuous homotopy equivalence, not a marker field.

## Already selected covering-transfer APIs

The existing 23-module higher-homotopy supplier closure rooted at `TauCeti.AlgebraicTopology.EilenbergMacLane.Covering` is recorded as 305,059 bytes in the existing provenance. Its exact inspected useful declarations are:

| Declaration | Essential hypotheses and conclusion | Actual application |
| --- | --- | --- |
| `IsCoveringMap.homotopyGroupPiMulEquiv` | `(hp : IsCoveringMap p) (e : E) (n : ℕ)` gives `π_ (n+2) E e ≃* π_ (n+2) X (p e)` | Transfer genuine higher-homotopy vanishing across an actual cover. |
| `IsCoveringMap.isAspherical` | `hp`, `Surjective p`, `he : p e = x`, `IsAspherical E e` give `IsAspherical X x` | Once the actual complement is aspherical, transfer to the already constructed orbit quotient cover. |
| `IsCoveringMap.isAspherical_totalSpace` | `hp`, `[PathConnectedSpace E]`, `he`, `IsAspherical X x` give `IsAspherical E e` | Reverse transfer if a useful aspherical base becomes available. |
| `IsCoveringMap.isAspherical_of_subsingleton_homotopyGroup` | `hp`, surjectivity, `[PathConnectedSpace E]`, `he`, and `∀n, Subsingleton (π_(n+2) E e)` | Sufficient for the proposed actual-universal-cover route. |
| `IsQuotientCoveringMap.isEilenbergMacLaneSpaceOne` | actual quotient cover, `[SimplyConnectedSpace E]`, basepoint equation, and all higher groups of `E` trivial | Packages a K(G,1) only after the real covering and higher vanishing are proved. |
| `TauCeti.IsEilenbergMacLaneSpaceOne.mk` | actual asphericity and `Nonempty (FundamentalGroup X x ≃* G)` | Combine new asphericity with M4's actual group equivalence. |

The `IsQuotientCoveringMap` theorem must not be applied to `Complement → OrbitComplement` using a simply-connectedness hypothesis that has not been proved for `Complement`.

## A genuine universal-cover candidate

Pinned `TauCeti/AlgebraicTopology/UniversalCover/Basic.lean` constructs

```lean
structure TauCeti.UniversalCover (x₀ : X) where
  proj : X
  path : Path.Homotopic.Quotient x₀ proj
```

Its topology is coinduced from `ofBasedPath x₀`. `BasedPath x₀ := {γ : C(unitInterval, X) // γ 0 = x₀}` has the compact-open subspace topology; the construction is not a discrete sigma topology. It contains an actual constant-path basepoint, and `range_proj x₀ = pathComponent x₀`. For the actual path-connected complement this yields surjectivity of the endpoint map.

Pinned `UniversalCover/Covering.lean:51,116,183` proves:

```lean
UniversalCover.isCoveringMap
  [LocallyPathConnectedSpace X] [TauCeti.SemilocallySimplyConnectedSpace X]
  (x₀ : X) : IsCoveringMap (UniversalCover.proj (x₀ := x₀))

UniversalCover.pathConnectedSpace (x₀ : X) :
  PathConnectedSpace (TauCeti.UniversalCover x₀)

UniversalCover.simplyConnectedSpace
  [LocallyPathConnectedSpace X] [TauCeti.SemilocallySimplyConnectedSpace X]
  (x₀ : X) : SimplyConnectedSpace (TauCeti.UniversalCover x₀)
```

The path-connectedness construction needs no local assumptions. Simple connectedness is proved through actual path lifting and cancellation in endpoint-preserving path-homotopy classes. The covering construction allows empty fibers off the basepoint path component; surjectivity still needs path connectedness of the base. `existsUnique_continuousMap_lifts` is the actual universal lifting property for continuous maps from simply connected, locally path-connected spaces. No `UniversalCover/Construction.lean` or `UniversalCover/SimplyConnected.lean` exists at this pin: the relevant implementation is `BasedPath`, `Basic`, `Covering`.

A recursive import walk gives 13 TauCeti files / 193,800 bytes. Five are already vendored; the eight new files total 119,260 bytes / 2,242 lines:

- `AlgebraicTopology/UniversalCover/{BasedPath,Basic,Covering}.lean`
- `AlgebraicTopology/SemilocallySimplyConnected/{Basic,On}.lean`
- `Topology/Homotopy/TubeNeighborhood.lean`
- `Topology/IsLocalHomeomorph.lean`
- `Topology/SeparatedMap.lean`

The complete path/hash/import inventory is embedded in the JSON. Full `BasedPath`, `Covering`, and semilocal `Basic` were read; universal-cover `Basic` definitions/topology and declaration inventory were read, not every proof. Other closure modules were import-walked, not individually proof-reviewed. At the initial search stage this candidate had not been compiled against the project's different mathlib pin. The subsequent selected-cohort section records the real build and audit.

### Local hypotheses for the actual complement

Unselected pinned `TauCeti/Topology/Algebra/Module/LocallyContractible.lean` is 43 lines, with only mathlib imports. It proves the instance

```lean
TauCeti.RealTopologicalVectorSpace.stronglyLocallyContractibleSpace
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E] : StronglyLocallyContractibleSpace E
```

Mathlib `IsOpen.stronglyLocallyContractibleSpace` transfers this to the actual open complement (`Theorem18.isOpen_complementSet`). Mathlib then supplies `LocallyPathConnectedSpace`; semilocal `Basic` supplies `SemilocallySimplyConnectedSpace` from strong local contractibility. Alternatively, the latter file's `of_forall_exists_mem_nhds_isSimplyConnected` derives semilocal simple connectivity from actual simply-connected neighborhood witnesses. An open contractible tube containing each point is sufficient for that semilocal condition; it is not by itself a proof that such tubes form a neighborhood basis. Full 43-line source and semilocal constructor were read.

### Compact directed-cover route

Pinned mathlib `Topology/Compactness/Compact.lean:188` proves exactly:

```lean
IsCompact.elim_directed_cover [Nonempty ι] (hs : IsCompact s)
  (U : ι → Set X) (hUo : ∀ i, IsOpen (U i))
  (hsU : s ⊆ ⋃ i, U i) (hdU : Directed (· ⊆ ·) U) :
  ∃ i, s ⊆ U i
```

For a finite-dimensional cube representative, continuity and compactness put its entire image in one member of an actual directed open cover. If that member is contractible and contains the basepoint, the representative factors through its subtype as a based generalized loop. Triviality of that subtype's homotopy group and functoriality of the inclusion imply triviality of the original class.

The directly relevant unselected pinned module `TauCeti/Topology/Homotopy/HomotopyGroup/HomotopyEquiv.lean` supplies:

```lean
HomotopyGroup.subsingleton_of_contractibleSpace
  [Finite N] [ContractibleSpace X] : Subsingleton (HomotopyGroup N X x)

HomotopyGroup.map_eq_one_of_nullhomotopic
  [Finite N] [Nonempty N] [DecidableEq N]
  {f : C(X, Y)} (hf : f.Nullhomotopic) (hfx : f x = y)
  (a : HomotopyGroup N X x) : HomotopyGroup.map f hfx a = 1
```

Its recursive TauCeti closure has 13 files, only two new relative to the current vendor tree: this 302-line module and `Topology/Homotopy/HomotopyEquiv.lean` (196 lines). Both were fully read. No CW assumption is present in this route. The missing input remains the actual directed contractible-open cover of the actual universal cover; arbitrary unions of lifted contractible tubes are not automatically contractible. No such theorem was found in the bounded inspected sources.

## Nerve, Whitehead and other nearby candidates

| Exact source/declaration | Literal scope | Disposition / read limit |
| --- | --- | --- |
| TauCeti `Topology/Category/TopCat/Cech/Nerve.lean`, `openCoverMap`, `isOpenQuotientMap_openCoverMap_iff` | Actual topological disjoint union of opens and its map to `X`; open quotient iff cover. `exists_openCoverMap_comp_eq_iff` characterizes maps from connected domains whose range lies in one member. | Useful foundational Čech construction, no homotopy-equivalence theorem. Full source read. |
| TauCeti `AlgebraicTopology/FatRealization.lean`, `fatRealization`, `fatRealization.homotopy` | Genuine quotient of `Σ n, Xₙ × Δⁿ` by face identifications; a continuous family of semi-simplicial maps induces a continuous homotopy. | Definitions and complete declaration inventory inspected; does not itself supply good-cover comparison. Not all proofs read. |
| TauCeti `Topology/CategoryTheory/Nerve.lean`, `topologicalNerve`, `fatClassifyingSpace`, `fatClassifyingSpaceHomotopy` | Actual topology on strings of arrows and their fat realization; functoriality/homotopies of functors. | Imports, definitions, declaration inventory read. No comparison of the actual arrangement complement with a contractible realization. |
| TauCeti `AlgebraicTopology/CechNerve.lean`, `CategoryTheory.Arrow.mapCechNerveHomotopy` | Simplicial homotopies associated to maps of arrows and Čech nerves in a category. | Declaration inventory and selected source inspected; not a geometric nerve theorem. |
| TauCeti `AlgebraicTopology/Singular/Cech/SmallChains.lean`, `openCoverSmallSingularAugmentationRowHomotopyEquiv` | Chain homotopy equivalence of rows of a Čech–singular bicomplex with small chains, in each singular degree. | First 120 lines and declaration scope inspected; a chain homotopy equivalence is not a space homotopy equivalence or higher-homotopy comparison. Latest file equals old pin. |
| TauCeti `AlgebraicTopology/Homotopy/Whitehead.lean`, `contractibleSpace_of_subsingleton_homotopyGroup` | `[CWType X] [PathConnectedSpace X]`, `∀n, Subsingleton(π_(n+1) X x)` imply `ContractibleSpace X`. | Literal conclusion and hypotheses read; assumes the vanishing we still need, plus actual CW type. No proposed closure. |
| TauCeti `AlgebraicTopology/EilenbergMacLane/Contractible.lean`, `IsCoveringMap.contractibleSpace_of_isAspherical` | Covering over T₂ CW base, simply-connected total space, **base already aspherical** imply contractibility. | Full file read. Cannot establish the currently missing asphericity. |
| TauCeti `EilenbergMacLane/HomotopyEquiv.lean`, `IsAspherical.of_homotopyEquiv` | Transfers across actual `X ≃ₕ Y`. | Full file read; would need an actual higher-homotopy comparison beyond M3. |
| TauCeti `EilenbergMacLane/WeakHomotopyEquivalence.lean`, `IsAspherical.isWeakHomotopyEquivalence_iff` | π₁ criterion **assuming both spaces aspherical**. | Full file read; does not derive asphericity from π₁. |
| TauCeti `Topology/Homotopy/GenLoop/Contractible.lean`, `GenLoop.contractibleSpace_of_homotopyRel` | Actual contraction of identity fixing `{e}` implies contractibility of generalized loop space. | Full file read; requires a real pointed contraction. |
| TauCeti `EilenbergMacLane/TopologicalVectorSpace.lean`, `IsQuotientCoveringMap.isEilenbergMacLaneSpaceOne_realTopologicalVectorSpace` | Quotient covering whose total space is an actual real topological vector space. | Full source read; arrangement complement/universal cover has not been identified with such a vector space. |

## Supplementary repositories: exact useful boundaries

`zstone1/Cubical`: fully read `CubeChains/PaperSalvetti.lean`, `CubeChains/Machinery/Arrangement/Sal.lean`, and `CubeChains/Concurrency/Salvetti/SalCompare.lean`. Its literal

```lean
COM.SalCell L := {p : SignVec E × SignVec E //
  p.1 ∈ L.covectors ∧ L.IsTope p.2 ∧ p.1 ⊑ p.2}
```

is a combinatorial face poset. `Models L K` contains category equivalence `base : (Ch K)ᵒᵖ ≌ COM.Face L` and natural isomorphism `fibre : Lines K ≅ base.functor ⋙ COM.salFunctor L`. `Models.salEquiv` and `Models.hbpEquiv` construct category equivalences from those data. They do not compare a realized complex with the actual Euclidean complexified complement. The inspected paper entrypoint records remaining combinatorial gaps. No M5 import proposed; no compilation.

`Arthur742Ramos/ComputationalPathsLean`: fully read `ComputationalPaths/Path/Homotopy/MapperAlgorithm.lean`. Its `GoodCover C` has the field `nerveEquiv : SimpleEquiv A (Nerve C)` and `nerve_lemma h := h.nerveEquiv`. It assumes its equivalence, with no `TopologicalSpace`, continuous homotopies or actual contractibility condition. Also inspected the exact nerve definitions and theorem block in `ComputationalPaths/Path/Topology/SimplicialComplexes.lean`: `OpenCover.contractible` is a computational path between `intersections.reverse.length` and `intersections.length`; `NerveTheorem.homotopy_equiv` is a computational path between two swapped sums of natural-number counts. `nerveTheorem_homotopy_equiv` projects that field. Neither is an actual topological nerve theorem. Remaining portions of the second file were declaration-scanned, not fully proof-read. No import proposed; no compilation.

`SauersML/group-approximation`: inspected declaration/import matches in the 346,902-byte archived umbrella `tools/branch-archive/claude_great-ptolemy-7vplxg/GroupApproximation.lean`, not the full file. The combined Deligne/aspherical search hit consists of unrelated imports (`Kazhdan.FoxAsphericalReduction` and `Manuscript.NonMFNotes.Full.Prose.DeligneType`). No arrangement theorem was located or accepted there; those imported files were not read. No import proposed.

`itakura-hidetoshi/KuuOS`: fully read `formal/KUOS/PlanOS/FiniteCoverNerveCechPathHomotopyV1_14.lean`. `FiniteIndexedCover` covers a finite sample set; `PathValid` is a predicate on vertex lists; `triangleContraction_preserves_path_validity` and `triangleContraction_preserves_endpoints` prove graph/list properties. Certificate fields explicitly include `classicalNerveTheoremNotClaimed` and `coverHomotopyEquivalenceNotClaimed`. No actual topological comparison is claimed by this module; no import proposed. The returned legacy path is a search hit only, not separately source-read.

## Search execution and limits

GitHub code searches used `gh search code QUERY --limit 100 --json path,repository,url`; exact queries/results are in the JSON. Initial four post-Salvetti searches returned HTTP 403 rate limits and are recorded as failures, not empty results. Retrying succeeded. Queries returning exactly 100 hits are capped, not exhaustive. Focused successful searches included `nerveLemma` (zero), `nerveTheorem` (three), `aspherical arrangement` excluding OpenAI and two mirrors (zero), and `Deligne simplicial` excluding OpenAI (zero). Search matching is token based and often returned unrelated names; only the literal types above were treated as candidates.

The latest TauCeti recursive GitHub tree response was untruncated. File-name filtering for Deligne/Salvetti/nerve/Čech/fat-realization and homotopy candidates was followed by the source inspection described above. The five byte-equality comparisons were `UniversalCover/{Basic,Covering}`, `EilenbergMacLane/Basic`, `FatRealization`, and `Singular/Cech/SmallChains`. No latest-only proof has been selected. Root's other search author owns the detailed OpenAI arrangement audit; returned OpenAI/mirror hits here are recorded but were not source-used in this report.

No toolchain installation, package update or cache update occurred. The initial search did not modify project proofs. After root selection, the supplier author staged the explicit topology cohort; its entire new physical/canonical declaration cohort receives real build, axiom and exact-module kernel-replay checks and independent reviews before it can be called accepted.

## Subsequent root-selected supplier cohort (acceptance pending)

Root authorized the exact union of the universal-cover closure, the real-vector-space local-contractibility module and the homotopy-equivalence homotopy-group closure. Measured union: 27 TauCeti modules, of which 16 are existing unchanged accepted sources and **11 are new**, totaling 2,783 upstream lines / 146,191 bytes. All 11 selected full source files have now been read, including every proof body. This later inspection supersedes their earlier search-stage read limits for the selected cohort only.

Active sources are under `asphericity/vendor/ArtinAsphericityVendor`; original full upstream bytes, per-file Apache headers, complete license and mechanical import-only patches are preserved. `asphericity/vendor/provenance.json` binds all active/original/patch hashes and upstream/target pins. `asphericity/evidence/providers/source-inspection.json` records the exact 27-module closure, unchanged reused-dependency hashes, read scope and direct applications. `python3 scripts/providers/assemble.py --check`, run from `asphericity`, reproduces all 11 active files from originals using only the explicit selected-import relocation recipe.

The explicit 11-target Lake build and complete provider axiom/physical census passed: 310 canonical declarations, 310 physical occurrences, zero duplicate names; all physical types/proofs/universe parameters equal their canonical imported declarations and transitive axioms are contained in `{propext, Classical.choice, Quot.sound}`. All 11 exact-module kernel replays passed, each in a fresh official `leanchecker` process, against the same frozen source/tooling/configuration/reused-dependency inputs. `asphericity/evidence/providers/verification.json` records technical success; two independent reviews and root acceptance remain pending. The official checker replays this selected cohort relative to imported prerequisites; it is not an independent kernel implementation. No claim about actual arrangement asphericity, a contractible actual universal cover or completed Landmark 5 follows from the provider cohort.
