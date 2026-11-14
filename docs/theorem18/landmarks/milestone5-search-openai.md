# Landmark 5: OpenAI source search and the remaining geometric bridge

This is a source-search report, **not acceptance of a new supplier or a proof of asphericity**. It continues the [earlier search](../search-openai.md) after landmarks 1–4. Its durable machine record is [m5-openai-inventory.json](../../provenance/searches/m5-openai-inventory.json). No scientific Lean source, provider, package configuration or cache was changed. No candidate was compiled, transitively axiom-audited or kernel-replayed in this search.

The inspected sources contain an ordinary Coxeter–Artin Salvetti contraction and useful generic poset contractions. I found no directly applicable theorem proving asphericity of the **actual restricted complexified arrangement complement**. The search was broader than the former 617-module closure; its precise coverage and limits appear below. This does not assert absence from every repository, branch or possible theorem terminology.

## Pins, licensing and reproducible coverage

A fresh GitHub `commits/main` query returned `4eaee87548250b2682affda7d05d947c05554bae`, dated `2026-10-30T00:35:35Z`, identical to the previously inspected openai/math pin. Thus current `main` supplied no newer version of these proofs. Other branches and tags were not exhaustively searched. The fetched immutable configuration specifies Lean `v4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and Apache-2.0 licensing. This is not the project's current toolchain; source discovery does not establish compatibility.

The inventory records source URLs, SHA-256 hashes, Git blob identities, direct imports, literal selected declaration headers, context/hypotheses, closure coverage and disposition. Every inspected Lean source for which a complete subtree supplied a blob identity matched that identity. The following complete recursive subtree inventories were searched; entry counts include directories.

| Subtree under `lean/OAI` | Tree SHA | Entries |
| --- | --- | ---: |
| `Topology` | `7ea0275d387dc5545a3cd288cde98fa1bfc550d1` | 1311 |
| `Topology/ArtinGroups` | `0b8f7c175022e4696404bb2bbabf12746f899d14` | 891 |
| `AlgebraicTopology` | `379be79523387a94d775f0f6939de4db951ad44d` | 644 |
| `Geometry` | `b0a9be666fb8dfdecda3add9b0d0044374a123a7` | 14720 |
| `GroupTheory` | `7f009e658de6eaaa769ffd2a733f6e8d4ec059f4` | 4239 |
| `Combinatorics` | `b45090b6d5bc04e0962f2c7547b1e4643a5dd1a1` | 16844 |
| `Dynamics` | `3ac4ebd40bdd3f03b13f47975716f8edcacda2e9` | 680 |

All **1288 Topology Lean source bodies** were machine-screened with the recorded patterns: all 881 ArtinGroups files, including 264 outside the earlier closure, and all 407 remaining Topology files. Individual proof bodies were read for the candidates described below; machine screening is not full manual proof reading. Outside Topology, complete subtree **paths** were searched and selected bodies fetched/read. The root recursive tree is truncated, so it was not used to infer exhaustive repository coverage. The existing exact-pin comparison with `mathcommunity/oai-math-revised` (`d25fae85c2f5ce5aadac40fb2b4c2d332b393d1c`) establishes identical relevant old subtrees; this search did not freshly query revised's latest branch.

The ordinary `SalvettiProjection` OAI import closure was independently recomputed from actual sources: exactly the same **617** modules as the old inventory, with no missing OAI source. The selected `SalvettiCoverContractible` closure has 602 modules. Closure completeness is a source fact, not successful compilation or an axiom audit. Previously accepted algebraic providers do not certify this larger topology closure.

## What the ordinary Salvetti endpoints actually say

Names in this subsection are in `OAI.HarmonicArtin`, at the immutable [ArtinGroups source directory](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Topology/ArtinGroups).

`Model.lean` defines the actual braid-presented `Artin M`, `IsSpherical M T := Finite (coxeterParabolic M T)`, and `LiftedCell M := Artin M × SphericalType M`. Its face relation uses ordinary Coxeter reduced words and minimal coset representatives. The cover is literally

```lean
noncomputable def SalvettiCover (M : CoxeterMatrix S) : TopCat :=
  SSet.toTop.obj (CategoryTheory.nerve (LiftedCell M))
```

`Realizations/SalvettiCoverContractible.lean` states, for arbitrary universe `S : Type u`:

```lean
theorem salvetti_cover_contractible [Finite S] (M : CoxeterMatrix S) :
    ContractibleSpace (SalvettiCover M)
```

This is an unconditional **finite-rank ordinary** statement, without a finite-W premise. The full proof closure has not been newly accepted here. Its exact breadth is recorded rather than silently narrowing its hypotheses.

`Realizations/CellUnion.lean` constructs `SourceSalvetti M` as a quotient of spherical Coxeter cell points by explicit face identifications, with the quotient topology. It proves a homeomorphism to the ordinary deck quotient. `Realizations/SalvettiProjection.lean`, under `[Fintype S] [DecidableEq S]`, gives a genuine covering projection `SalvettiCover M → SourceSalvetti M`, its surjectivity, contractible/simply connected source, and

```lean
sourceFundamentalGroupEquiv (x : SourceSalvetti M) :
  FundamentalGroup (SourceSalvetti M) x ≃* Artin M
```

The basepoint is in **SourceSalvetti**, not the actual relative complement. No relative set `J`, restricted arrangement on its flat, or normalizer action occurs in these definitions. `restricted_lifted_contractible` in `RestrictedLiftedContractible.lean` concerns an ordinary standard parabolic matrix `restrictedMatrix M T`; the word “restricted” does not mean the restricted arrangement of the paper. Similarly, `DeligneRealization M` is the nerve of ordinary spherical Artin cosets.

The relative arrangement generally is not a Coxeter arrangement for a new matrix, and its normalizer quotient need not act transitively on chambers. Therefore selecting a new matrix does not instantiate these endpoints. A new actual higher-homotopy comparison would be necessary even if this entire supplier closure passed technical validation. Landmark 3's fundamental-groupoid equivalence controls the 1-type; it supplies no higher-homotopy comparison by itself.

## Generic tools found beyond that endpoint

The literal selected headers and context are in the JSON inventory; this table describes their practical use and limits.

| Supplier | Genuine conclusion and inputs | Disposition for M5 |
| --- | --- | --- |
| `Realizations/DirectedCoverSequence.lean`, `orderWeights_contractible_of_countable_directed_cover` | Contractibility of `OrderWeights P`, from a countable nonempty directed cover by **downward closed** subposets whose realizations are contractible, plus a bounded strictly monotone natural-number rank | Useful potential combinatorial tool. It does not contract actual open subsets of a lifted complement. Its OAI closure has 105 modules. |
| `OrderWeightsContractibleLower.lean`, `orderWeights_contractible_of_lower_fibers` | Contracts a poset realization from an already contractible subposet, contractible lower fibers outside it, and bounded strict rank | Potential attachment lemma; 28 OAI modules. The fibers must actually be proved contractible. |
| `OrderWeightsContractibleLower2.lean`, `orderWeights_contractible_of_lower_preimages` | An order-map criterion using contractible target/lower preimages and rank bounds on both posets | Potential comparison tool; 103 OAI modules. No geometric complement map is supplied. |
| `Topology/Euclidean/IncreasingCover.lean`, `...Globalization.exists_compact_subset_increasing_cover` | Every compact set in a monotone open cover lies in one member | The proof directly applies mathlib `IsCompact.elim_directed_cover`. Prefer that existing theorem over this file's unrelated singular-homology dependencies. |
| `Topology/Homotopy/CubicalNullity.lean`, `OAI.NearbyLagrangian.CubicalFreeNullity.null_of_moving_base` | For finite nonempty cubical dimension, converts an actual free nullhomotopy whose boundary is a moving point into a based `GenLoop` nullhomotopy | Small candidate importing only `Mathlib`. It could finish a genuine compact-image contraction argument; it provides no such geometric contraction. Not yet accepted or compiled here. |
| `Topology/Homotopy/RayTelescope.lean`, `...exists_finite_representative`, `...stage_nullhomotopic_iff` | Compact maps/homotopies into an explicit quotient ray telescope have finite-stage representatives; nullhomotopy can be checked eventually | Imports only `Mathlib`, but its space is a telescope, not the actual lifted complement. A homotopy comparison would remain necessary. |
| `GroupTheory/FiniteType/CWWhitehead.lean`, `OAI.CWWhitehead.contractible_subtype` | Contracts an actual nonempty CW subspace given `CWCylinder.SphereFill` for that space | Cannot supply the missing sphere-filling premise. Its external OAI closure was not fetched completely here. Direct higher-homotopy vanishing avoids requiring this stronger CW conclusion. |

`OrderWeights P` is substantive: finitely supported nonnegative real weights, total weight one, support a chain, and topology coinduced from actual nerve-simplex charts. It is not an artificial contractibility field. Nevertheless, its contraction is a theorem about this realization. Relating that realization to the actual lifted complement remains a mathematical obligation.

The additional Artin module `ParabolicIntersections/RelativeLowerContractible.lean` was read in full. Its `relativeAllEligibleLower_contractible` contracts a harmonic-height/link subposet of the **ordinary** Deligne coset poset, with distinguished-generator, support and cutoff hypotheses. It is not a theorem about restricted real hyperplanes. Other nearby `relative`/`normalizer` hits are ordinary group/poset constructions.

The broader path/body search also found several misleadingly adjacent names:

- `Dynamics/EntropyCounterexample/CoordinateGoodCover.lean` defines legitimate open-cover data with contractible nonempty finite intersections and explicitly contracts sphere slices. Its constructions concern spheres/manifolds. It does not prove a generic nerve homotopy theorem. `RawBaseGoodCover.lean` transports one such example through homeomorphisms.
- `Geometry/SingularHomology/FiniteGoodCoverHomology.lean` proves finite-dimensionality/eventual vanishing of **homology** through algebraic gluing. `TetrahedronGoodCoverBundle.lean` constructs a good cover of a tetrahedral sphere. Neither proves the needed arrangement asphericity or actual nerve equivalence.
- `GroupTheory/SimpleAmenable/Simplicial/BarContractible.lean` supplies positive-degree simplicial **homology** vanishing for special bar constructions. Its filename does not establish topological contractibility of a general Garside category.
- `AlgebraicTopology/Cohomology/Singular/ChartLocalContractible.lean` proves local contractibility of charted spaces. Local contractibility alone says nothing about the global higher homotopy groups in question.

## Faithful remaining proof route

I read the archived original Deligne extracted text at 2.14–2.15 and 3.7A–D (printed pp.290–296), not the whole original paper or a fresh visual PDF. Reviewer A separately reports complete visual reading of §§1–3. The archived PDF has SHA-256 `1905043232e1dadd97696372252bb5f91c202ea1b72379e77a9fecbfe9eed4bc`; its source is [Deligne, *Les immeubles des groupes de tresses généralisés*](https://publications.ias.edu/sites/default/files/Number18.pdf). See [contract A](milestone5-contract-a.md) for the independently reviewed complete route and [contract B](milestone5-contract-b.md) for the exact final theorem scope.

A useful decomposition is:

1. **Actual simplicial arrangement.** Transport the off-parabolic coordinate basis through the existing actual facet/flat maps, proving each actual chamber is the strictly positive cone of a basis. Prove the finite retained forms span the flat when essentiality is needed. Keep duplicate forms harmless. This is concrete geometry, with no topological asphericity conclusion.
2. **Signed combinatorial cover and contraction.** Build the actual positive/signed chamber complex using the proved chamber/ribbon data. Prove its face identifications and the positive length-filtration attachments. Deligne 2.9 contracts the positive complex; 2.14 exhausts the signed one by translated positive complexes; 2.15 concludes contractibility. Generic OAI order-realization lemmas might reduce this work after an actual poset and its rank/fibers are established. The ordinary coset complex cannot simply be renamed.
3. **Actual geometric cover.** Construct a covering of the actual complement by gluing actual tube sheets with the signed chamber transition data, or use an independently proved actual universal covering construction. Prove the local evenly covered neighborhoods; Deligne 3.7A uses facet-star neighborhoods. A mere definition of a covering candidate is insufficient.
4. **Actual higher-topology bridge.** Deligne 3.7B–D refines to a vertex/face-indexed open cover, identifies its nerve with the combinatorial cover, and proves nonempty finite intersections contractible. Intersections containing a chamber center have affine contractions (3.7.5). Other face intersections compare, via an actual pullback and homotopy equivalence, to lower-rank localized lifted arrangements (3.7.7–3.7.8); induction finishes them. One must then prove/use a genuine topological nerve homotopy theorem. Existing tube contractions and the Čech theorem for fundamental **groupoids** do not replace this step.
5. **Higher vanishing and transfer.** Contractibility of the actual covering space implies its higher homotopy groups vanish; covering transfer gives actual complement asphericity, then the already proved quotient covering gives orbit-space asphericity. Combine the actual M4 group equivalences and commuting sequences with the K(π,1) definitions at arbitrary actual basepoints. No new normalizer/group identification is needed here.

A potentially smaller alternative to steps 2–4 is to construct a **directed open exhaustion of the actual simply connected cover whose members have actual nullhomotopic inclusions**, or actual contractions. Compact cubical maps then land in one member by `IsCompact.elim_directed_cover`, and free-to-based nullity gives higher vanishing. This avoids a full CW/Whitehead conclusion and may avoid a global nerve theorem. The decisive new proof is still geometric: the exhaustion members and their contractions/nullhomotopic inclusions must be constructed from Deligne's positive filtration and actual lifted overlaps. Contractibility of arbitrary finite unions of lifted tubes is not a consequence of individual tube contractibility. Their intersections can be disconnected. No inspected OpenAI endpoint supplies this filtration theorem.

A generic Garside classifying-space theorem would have the same limitation unless its actual space is connected to the complement by a proved higher-homotopy equivalence. Likewise the restricted complement lies in ambient reflecting hyperplanes, so it is not simply the ambient regular Coxeter complement with a convenient fixed-point subgroup. A new fixed-point/stratum comparison would need its own proof.

The first inexpensive independently authorable obligations are the flat-coordinate/simpliciality statement, and the generic compact-directed-open-cover higher-nullity lemma. The former discharges a genuine Deligne hypothesis; the latter isolates a small topological endpoint. Neither should be advertised as the full geometric Deligne theorem. Rank zero/full `J` must remain included: the actual flat/complement is a point and the retained arrangement is empty. Any positive-dimensional/spherical convention in a supplier must have a separate zero-dimensional case. Arbitrary `J`, reducible and noncrystallographic finite Coxeter groups remain in scope.

## Execution and claim limits

This search used read-only source/hash/GitHub queries, plus writes to this report and its machine inventory. Full-source keyword coverage and exact import-closure recovery are recorded; they are not kernel validation. No inference is made from a README, theorem name, CI badge, or homology-only conclusion to actual asphericity. No desired contraction, geometric comparison, or asphericity is proposed as an assumed field in a completed theorem.
