# Theorem 1.8 foundations: independent review B

Reviewer: **GPT-6.1 Sol/high**, independently of reviewer A. Final verdict: **accept-foundations-only**, bound to the exact five project source files and 23 new provider sources recorded below and in `foundations-b.json`. **Full Theorem 1.8 is not proved.** Only this review and its companion receipt were written. Historical kernel/full-lemma reviews and proof/cache/evidence files were not modified.

## Scope and actions actually performed

After the frozen-source notice, I read all four final `ArtinNormalisers/Theorem18/*.lean` modules and `ArtinTheorem18.lean` in full, including every explicit statement, definition, instance and proof body. I inspected the actual 23-module source closure listed in `vendor/theorem18-provenance.json`, with the full critical definitions/proofs and bounded auxiliary-interface reading described below. I also read the relevant pinned mathlib definitions and proofs in `Mathlib/Topology/Homotopy/Lifting.lean`, `Topology/Covering/Quotient.lean`, `Topology/Homotopy/HomotopyGroup.lean`, and the fundamental-group multiplication/map definitions. This is source inspection, not acceptance from a README, a badge, or a theorem name.

My read-only Python checks independently verified all five final project source SHA256 digests, all 23 new provider SHA256 digests against the current provenance map, all ten historical provider digests against the historical provenance map, the current new provenance digest, the historical source-inventory digest, and that the combined import closure has no missing non-mathlib import. The provider revision is `62bbc0596dc3539d488232e4e924a338548ea0a9`, upstream mathlib `e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`, project mathlib `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. Source identity and import completeness are distinguished from root's compilation/audit evidence below.

I did not run Lean, a kernel replay, an axiom audit, dependency installation, or cache fetching. Root reports warning-free frozen compilation of all foundation modules and all 33 old/new supplier modules. I inspected its corrected elaborated-type/axiom audit outputs `/tmp/theorem18-pre-review-audit-v2.log` and the final `/tmp/theorem18-pre-review-audit-v3.log`; the latter reports 145 new foundation declarations and 733 supplier declarations after all 33 supplier modules were directly imported. My own actions are the source/math review, hash/import/declaration checks, and evidence reading; the Lean executions are root-produced evidence. The 145 audited project constants include generated declarations; there are 93 explicit source-level declarations in the four scientific modules.

## The four local declarations

For arbitrary topological spaces `E,X`, an actual map `p:E→X`, and the stated covering hypotheses, all four declarations are mathematically true with the literal definitions inspected.

| Fully qualified declaration | Literal mathematical content and judgment |
| --- | --- |
| `ArtinNormalisers.Theorem18.covering_fundamentalGroup_map_injective` | For `hp:IsCoveringMap p` and any `e:E`, the actual induced map `FundamentalGroup.map ⟨p,hp.continuous⟩ e` is injective. **Accept semantically.** The proof reduces equality to path-homotopy classes and invokes the covering map's injectivity on those classes. It assumes neither connectedness nor simple connectedness. |
| `ArtinNormalisers.Theorem18.covering_fundamentalGroup_mapOfEq_injective` | For the same covering and a specified equality `he:p e=x`, the induced map transported to basepoint `x` is injective. **Accept semantically.** The proof composes the previous injection with conjugation along the equality isomorphism. This is a basepoint equality transport, not a hidden choice of an arbitrary basepoint path. |
| `ArtinNormalisers.Theorem18.quotientCovering_fundamentalGroup_range_eq_ker` | For a genuine `hp:IsQuotientCoveringMap p G` and a chosen fiber point `e:p⁻¹'{x}`, the actual induced-map range equals the kernel of the actual endpoint monodromy to `Gᵐᵒᵖ`. **Accept semantically.** The proof rewrites with pinned mathlib's two kernel/range lemmas. No connectedness of `E` is required for this equality because the quotient-covering deck action is free and transitive on each fiber. |
| `ArtinNormalisers.Theorem18.quotientCovering_fundamentalGroup_shortExact` | Adds `[PathConnectedSpace E]` and concludes injection, equality of range with the same kernel, and surjectivity to `Gᵐᵒᵖ`. **Accept semantically.** Its surjectivity is the actual monodromy-surjectivity theorem using paths between `e` and every `g•e`; it is not assumed. It does not assume simply connected `E` and correctly does not claim `π₁(X)≃G`. |

The fourth statement is directly useful once the actual arrangement action and covering have been proved. It is not the full article theorem: no space in its type is yet the actual restricted arrangement, and no group is yet the actual Artin normalizer quotient. The module comments accurately state that limitation.

## What the quotient-covering hypothesis really contains

I read pinned mathlib's `IsQuotientCoveringMap` definition. It extends the actual quotient-map property and continuity of each group translate, requires equality of map values iff membership in the same actual orbit, and requires for every point a neighborhood whose translate can meet itself only for the identity group element. This is substantive freeness/local disjointness data. Supplying this hypothesis to a generic theorem is legitimate; leaving it as a hypothesis for the article's actual quotient map would not prove the article's covering assertion.

In pinned mathlib the range/kernel proof uses that monodromy commutes with deck translations, and therefore a monodromy permutation fixing the chosen fiber point fixes every fiber point. The equality `ker_monodromyPerm e = range(p_*)` is proved by lifting loops and checking whether the lift closes. The endpoint-label map then has the same kernel. This justifies using the global permutation kernel without incorrectly assuming that an arbitrary, nonregular covering has the same property.

No finite group, Hausdorff, local compactness, local path connectedness or semilocal simple connectedness hypothesis is missing from these **generic consequences**: the input is already an actual quotient covering with its requisite local structure. Separate geometric arguments may need such hypotheses to produce that input for the real arrangement.

## Opposite group and exact-sequence convention

The new local module explicitly targets `Gᵐᵒᵖ`, matching the independently identified convention issue in `statement-b.md`. Pinned mathlib's fundamental-group product is the endomorphism product: `p*q` traverses `q` then `p`. For a left action, raw endpoint labels consequently multiply in reverse order, and mathlib defines `fundamentalGroupToMulOpposite` by taking the opposite of the label, not by silently inverting it.

I read that actual definition and its `map_mul'` proof. I also checked its representative characterization: if a lifted loop starts at `e` and ends at `g•e`, its image is `.op g`. Thus the local sequence uses the real endpoint labels and the correct homomorphism convention.

To compare to the article's row terminating in `Q=N(W,J)`, a future implementation must explicitly transport the terminal group. `MulEquiv.inv' Q : Q≃*Qᵐᵒᵖ` sends `g` to `op(g⁻¹)`. It is legitimate to compare the current opposite-target geometric monodromy with `(MulEquiv.inv' Q) ∘ algebraicProjection`, or to compose monodromy with the inverse equivalence and then compare to the original projection. Either route needs the actual comparison equation. The bare function `op:g↦op g` is not a homomorphism for a general noncommutative group. Nor may a chosen fundamental-group isomorphism be assumed to make the right square commute.

Changing a chosen fiber point by a deck element conjugates the endpoint monodromy; mathlib's `fundamentalGroupToMulOpposite_toPermFiber` explicitly records this. Basepoint compatibility in the final theorem therefore remains real work, especially when `Q` is nonabelian. Exactness alone does not remove it.

## Literal asphericity and K(π,1) definitions

I read `TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean` completely, including definitions and proofs. Its literal definition is

```lean
def IsAspherical (X : Type u) [TopologicalSpace X] (x : X) : Prop :=
  PathConnectedSpace X ∧ ∀ n : ℕ, Subsingleton (π_ (n + 2) X x)
```

The notation refers to **mathlib's actual homotopy groups**, not a replacement invariant. I inspected mathlib's underlying generalized-loop/cube-boundary definition and its interpretation as homotopy classes relative to the boundary. Since every degree at least two is uniquely `n+2` for a natural `n`, no positive higher degree has been omitted. `Subsingleton` means the genuine homotopy group is trivial, and based groups contain their identity, so this is not an emptiness loophole. Path connectedness is explicitly included.

The other literal definition is

```lean
def IsEilenbergMacLaneSpaceOne (G : Type u) [Group G]
    (X : Type v) [TopologicalSpace X] (x : X) : Prop :=
  IsAspherical X x ∧ Nonempty (FundamentalGroup X x ≃* G)
```

**Accept these definitions as directly useful weak-homotopy formulations of asphericity and K(G,1).** They do not redefine `FundamentalGroup`, assume a presentation for it, or make asphericity automatic from a fundamental-group name. The definition retains an existential group-isomorphism witness; that witness alone contains no chosen comparison equation with another exact sequence.

There is an explicit meaning boundary: the definitions assert vanishing higher homotopy and path connectedness, **not contractibility of a universal cover** or CW structure. For an actual complement with the appropriate CW homotopy type this is the expected Eilenberg–Mac Lane property; identifying it with a strong classifying-space/universal-cover statement requires the usual additional topology/Whitehead input. The provider's covering file itself warns that weakly contractible does not mean contractible for arbitrary spaces. No such stronger theorem is smuggled into this closure.

The public `isAspherical_iff`, constructor and projection lemmas expose the actual definition. `IsAspherical.of_basepoint` uses a path-connected-space path and the actual finite-dimensional homotopy-group basepoint-change equivalence for `Fin(n+2)`. The product results use actual product homotopy-group equivalences. The K(G,1) basepoint/target-group/product results likewise transport actual isomorphisms. The self-target statement `K(π₁(X),1)↔IsAspherical X` is an honest packaging lemma, not evidence that `X` is aspherical.

## Covering transfer: exact assumptions and limitations

I read the entire `EilenbergMacLane/Covering.lean`, including all proof bodies, and the entire `HomotopyGroup/Covering.lean` and `GenLoop/Covering.lean` chain it uses.

| Supplier | Exact usable conclusion and judgment |
| --- | --- |
| `IsCoveringMap.homotopyGroupPiMulEquiv hp e n` | Actual induced-map isomorphism `π_(n+2)(E,e)≃*π_(n+2)(X,p e)`, for every `n`. No connectedness or surjectivity assumption is needed for a statement about the chosen component/basepoint. **Accept semantically.** |
| `IsCoveringMap.subsingleton_homotopyGroup_iff hp he n` | Triviality of that actual higher group is equivalent upstairs/downstairs, with basepoint equality `he:p e=x`. **Accept semantically.** |
| `IsCoveringMap.isAspherical hp hp_surj he hE` | A **surjective** covering with aspherical total space has aspherical base. `hE` includes path connectedness; surjectivity and continuity transfer it to the base. **Accept semantically.** Surjectivity cannot simply be omitted, since otherwise unrelated base components can remain uncovered. |
| `IsCoveringMap.isAspherical_totalSpace hp he hX` | Requires `[PathConnectedSpace E]`; transfers asphericity of the base to the selected total space. **Accept semantically.** The connectivity assumption is essential for whole-space asphericity. |
| `IsCoveringMap.subsingleton_homotopyGroup_of_isAspherical` | Requires `[SimplyConnectedSpace E]` and asphericity of the base, and concludes vanishing of each **positive** homotopy group upstairs. **Accept semantically.** It does not conclude actual contractibility. |
| `IsCoveringMap.isAspherical_of_subsingleton_homotopyGroup` | Requires surjective covering, path-connected total space, and all actual higher groups upstairs trivial. **Accept semantically.** This repackages a genuine hypothesis, not a theorem making arbitrary covers aspherical. |
| `IsCoveringMap.isEilenbergMacLaneSpaceOne_totalSpace` | Requires path-connected total space and aspherical base; concludes K(H,1) for `H=range(p_* )`, using injectivity of the actual induced map. **Accept semantically.** It does not identify this range with the article's independently defined pure normalizer image. |
| `IsQuotientCoveringMap.isEilenbergMacLaneSpaceOne` | Requires the total space **simply connected** and all its higher groups trivial, and concludes K(G,1) for the acting group after the inverse/opposite-group isomorphism. **Accept semantically.** The complex complement `X_J^ℂ` generally is not simply connected, so applying this theorem directly to its finite Q-cover would be invalid. It can apply to a separately proved universal cover. |

The higher-covering proof is substantive: it lifts a radial contraction of each generalized loop while retaining its parameter, proves the lift equals the chosen basepoint on the cube boundary using boundary connectedness in dimension at least two, and obtains a genuine generalized-loop homeomorphism. It separately proves injectivity on homotopy classes by homotopy lifting relative to the boundary. Thus no assumed higher-homotopy equivalence is being hidden as a structure field. The `Nontrivial N`/`Nonempty N` distinction matches the mathematical distinction between surjectivity in dimension at least two and injectivity already in positive dimension.

These are complete **generic supplier statements** under their own explicit hypotheses. They do not prove Deligne's asphericity theorem for the arrangement, a comparison of a combinatorial model with that arrangement, the article's fundamental-group identifications, or its compatible exact-sequence isomorphism. Passing actual-arrangement asphericity/comparison as a hypothesis can form an intermediate lemma, but cannot complete Theorem 1.8.

## All 23 provider modules: source coverage and relevance

The following inventories the complete listed module closure. “Critical full” means I read its actual definitions/statements/proof bodies in full for this review. “Auxiliary interface” means I inspected the source's definitions/signatures/variable assumptions and selected proof/construction portions, not that I independently reconstructed every analytic or categorical helper. Hashing every file is distinct from fully reading every proof in it.

| Module under `TauCeti` | Role and reading boundary |
| --- | --- |
| `AlgebraicTopology.EilenbergMacLane.Basic` | Critical full: actual asphericity/K(G,1) definitions, basepoint/target/product transports. |
| `AlgebraicTopology.EilenbergMacLane.Covering` | Critical full: higher-group triviality transfer and exact generic K(G,1) hypotheses above. |
| `AlgebraicTopology.FundamentalGroup.Basic` | Critical full: actual induced-map and basepoint-equality transport, nullhomotopy/trivial-source range lemmas, connected-groupoid extension; implicit `a₀` analyzed below. |
| `AlgebraicTopology.FundamentalGroup.Product` | Full source: actual binary/indexed product group equivalences and simply connected product. |
| `AlgebraicTopology.FundamentalGroupoid.Basic` | Full source: actual path-groupoid connectivity, morphism-map composition and equality casts. |
| `Analysis.Normed.Module.Ball.Homeomorph` | Auxiliary interface: unit-ball rescaling and finite-dimensional cube/ball/sphere homeomorphisms, with dimension/norm assumptions. No assertion about arrangement asphericity. |
| `CategoryTheory.Groupoid.SingleObj` | Full source: groupoid/vertex-group equivalence and functor transport; requires connecting morphisms rather than assuming an arbitrary geometric comparison. |
| `Topology.Homotopy.Covering` | Critical full: pi1 injectivity, subgroup lifting criteria with actual path/local-connectivity hypotheses, and simply connected-cover fiber equivalence. |
| `Topology.Homotopy.Cube.Basic` | Auxiliary interface plus selected proof portions: actual cube boundaries/contractions and boundary path connectedness for at least two coordinates. |
| `Topology.Homotopy.Cube.OpenBox` | Auxiliary interface: cylinder/open-box radial deformation with explicit boundary equations. |
| `Topology.Homotopy.Cube.Radius` | Auxiliary interface: center/radius/scale and boundary characterizations, finite-coordinate assumptions where needed. |
| `Topology.Homotopy.Extension.Ball` | Auxiliary interface: actual sphere/closed-ball homotopy extension via radial retraction; not a general assertion that all maps are nullhomotopic. |
| `Topology.Homotopy.Extension.Basic` | Auxiliary interface: HEP definition, explicit extension/retraction statements and closedness/universe assumptions. |
| `Topology.Homotopy.GenLoop.Covering` | Critical full: continuously chosen based lifts in dimension at least two; actual loop-space homeomorphism. |
| `Topology.Homotopy.GenLoop.Map` | Full source: postcomposition of the actual generalized-loop spaces and its homotopy/concatenation compatibility. |
| `Topology.Homotopy.HomotopyGroup.BasepointChange` | Actual transport/equivalence signatures, variable assumptions, and final multiplicative/naturality/existence proof chain; not a full reconstruction of all collar-family helper proofs. |
| `Topology.Homotopy.HomotopyGroup.Collar` | Actual collar/transport definitions, continuity construction and relevant transport-canonicality interface; bounded proof reading. |
| `Topology.Homotopy.HomotopyGroup.Covering` | Critical full: induced-map injectivity/surjectivity and actual higher-group multiplicative equivalences. |
| `Topology.Homotopy.HomotopyGroup.Map` | Auxiliary interface: actual quotient-induced maps/homomorphisms, functoriality and pi1 comparison; no replacement homotopy group. |
| `Topology.Homotopy.HomotopyGroup.Product` | Auxiliary interface: coordinatewise actual generalized-loop/homotopy-group product maps and inverses. |
| `Topology.Homotopy.Path` | Auxiliary interface plus selected homotopy/map proofs: actual path restrictions/subdivision/conjugation/nullhomotopy machinery. |
| `Topology.PiCurry` | Source definitions/signatures and coordinate continuity constructions: actual product-topology reindexing/currying homeomorphisms. |
| `Topology.UnitInterval` | Source structure/signatures and selected elementary proofs: actual finite subdivision and interval-clamping lemmas. |

I found no confirmed false critical supplier statement, missing hypothesis in the four local statements, or proof of a surrogate invariant. I source-screened all 23 modules for `sorry`, `admit`, axiom declarations and unsafe proof escape declarations; no such source match appeared. This bounded screen is not a substitute for transitive axiom audit or replay, and I do not claim every auxiliary lemma was independently reconstructed.

## Upstream `autoImplicit` compatibility

Root reported an initial compilation failure under project-wide `autoImplicit=false`, and now configures `autoImplicit=true` **only** for the vendored `TauCeti` library, keeping project declarations at `autoImplicit=false` and preserving vendor bytes. I inspected `lakefile.toml` and the actual offending source.

In `AlgebraicTopology/FundamentalGroup/Basic.lean`, the lemmas

- `TauCeti.FundamentalGroup.map_range_eq_bot_of_subsingleton`,
- `TauCeti.FundamentalGroup.map_range_le_of_subsingleton`, and
- `TauCeti.FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton`

use `[Subsingleton (FundamentalGroup A a₀)]` without a preceding written binder for `a₀`. The expression `FundamentalGroup A a₀` forces its type to be `A`; under upstream automatic implicit elaboration each lemma therefore has an ordinary implicit `{a₀:A}` parameter and the explicitly written source-triviality instance assumption. Their conclusions are exactly the range-triviality/containment facts for that chosen basepoint, with no inferred comparison theorem or asphericity conclusion. The subsequent simply connected-domain wrappers explicitly bind `(a₀:A)` and discharge the source-triviality instance from simple connectedness.

This option repair is an elaboration-convention compatibility adjustment, not acceptance of a hole or a new mathematical axiom. I subsequently checked the **actual elaborated types** under this configuration in the corrected v2/v3 logs: all three have exactly the ordinary implicit `{a₀:A}` and explicitly expected `Subsingleton` premise. The inspected project types contain no unplanned comparison/asphericity premise. These printed-type checks resolve the earlier pending binder question; an autoImplicit flag alone would not have done so.

## Final geometry review: all 41 declarations

All names in this and the next two inventories have namespace `ArtinNormalisers.Theorem18`. Each judgment applies separately to every listed explicit declaration, including named instances. I read their actual final proof bodies, not only this inventory or the audit's type summaries.

| Names in `Geometry.lean` | Final semantic judgment |
| --- | --- |
| `Vector`, `Dual`, `simpleRoot` | Accept: actual free real vector space, its algebraic dual, and basis root `Finsupp.single i 1`. |
| `dualCoordinates`, `dualTopologicalSpace`, `dualCoordinatesHomeomorph` | Accept: the actual dual-basis linear identification with `I→ℝ`; product-coordinate topology is pulled back along that identification, and the identification is proved a homeomorphism. No discrete/trivial topology is substituted. In finite rank this is the ordinary finite-dimensional dual topology. |
| `dualContinuousAdd`, `dualContinuousSMul`, `dualContinuousNeg`, `dualTopologicalAddGroup`, `dualT2Space` | Accept: genuine topological real-vector/additive operations and Hausdorffness transferred through those coordinates. They do not assert a norm/topology coincidence without proof. |
| `continuous_evaluation` | Accept: evaluation at any actual finitely supported vector is a finite sum of coordinate evaluations and therefore continuous, even before finite rank is established. |
| `relativeSubspace`, `mem_relativeSubspace`, `isClosed_relativeSubspace` | Accept: the exact annihilator of the selected simple roots, with the inherited subspace topology and proved closedness. |
| `root`, `root_one`, `root_ne_zero`, `roots` | Accept: actual root orbit in the supplied standard geometric representation; nonzero roots follow from invertibility of each representation action and nonzero basis vectors. The root set does not assume distinct orbit labels. |
| `retainedRoots`, `restrictedHyperplane`, `mem_restrictedHyperplane`, `retainedRoots_iff` | Accept: retain exactly roots having a nonzero evaluation on the actual relative flat; the restricted kernel is the actual linear subspace, and the equivalence proves this is precisely the proper-restriction condition. |
| `restrictedArrangement`, `restrictedArrangement_proper` | Accept: image of the retained-root set in actual restricted kernels, automatically deduplicating coincident hyperplanes. Every selected kernel is proper. A kernel for an arbitrary unretained `r` may be the full space, but is not included in the arrangement. |
| `simpleRoot_not_retained_of_mem`, `simpleRoot_retained_of_not_mem` | Accept: roots indexed by `J` are excluded because every relative functional kills them; coordinate evaluation gives a nonzero witness for a basis root outside `J`. |
| `relativeSubspace_empty`, `relativeSubspace_univ`, `retainedRoots_univ`, `retainedRoots_empty` | Accept: empty/full-parabolic boundary cases follow from actual dual coordinates and nonzero root separation. No nonempty-rank hypothesis. |
| `complementSet`, `Complement`, `complementTopologicalSpace`, `mem_complementSet_iff_arrangement` | Accept: the literal pair-subspace complement removes simultaneous vanishing in real and imaginary parts, with inherited topology; the theorem checks equality with removing `H×H` for the distinct proper restricted arrangement. This is the source's finite-type formula. |
| `complementSet_univ`, `complementUnivUnique` | Accept: full parabolic leaves an empty retained-root arrangement in a zero-dimensional flat; the complement is one point, not empty. |
| `finite_index`, `roots_finite`, `retainedRoots_finite` | Accept: finite actual Coxeter group implies finite index type by the proved injective simple map; finiteness of the root orbit and retained family follows. Finite rank is derived, not added as an independent mathematical assumption. |
| `isOpen_complementSet` | Accept: for finite `W`, the complement is the finite intersection of complements of closed simultaneous-evaluation kernels, hence open in the actual pair vector space. It asserts no asphericity. |

The dual/root geometry agrees literally with the finite-type specialization in original PDF Sections 2.2/3.1 and equation (3.26). It uses the **dual** representation, not an unproved identification with the root representation. The full root orbit, rather than only positive roots, is harmless because hyperplanes are defined from all roots in the source as well, and the set-image arrangement handles repetitions. In finite type one may define this exact specialized formula directly; it is not necessary to introduce a symbolic infinite-type Tits cone first.

There is an explicit scope limit: the definitions are syntactically available for arbitrary `M`, but the resulting full-flat complement is identified here with the article's `X_J^ℂ` **only under finite type**. For infinite `W`, the article uses `Cone(J)°` and this file supplies no equivalence with it. The module's finite-type wording is accurate; a later claim of an infinite-type complement theorem would require a new bridge.

## Final normalizer-action review: all 32 declarations

| Names in `NormalizerAction.lean` | Final semantic judgment |
| --- | --- |
| `dualAction`, `dualAction_apply` | Accept: genuine contragredient of the actual Coxeter geometric representation, including the essential inverse `w⁻¹` in the evaluation formula. |
| `dualAction_simple_fixed_iff`, `mem_relativeSubspace_iff_fixed` | Accept: the reflection formula proves being fixed by each selected simple generator is exactly annihilating its simple root; subgroup generation then proves the relative flat is exactly the fixed space of actual `W_J`. No theorem assuming this identification is inserted. |
| `dualAction_mem_relativeSubspace`, `CoxeterNormalizer`, `normalizerRepresentation` | Accept: actual Coxeter-parabolic normalizer, restriction of its actual dual action, and preservation derived by conjugation of the generated parabolic. |
| `parabolic_le_normalizerRepresentation_ker`, `quotientRepresentation`, `quotientRepresentation_mk`, `normalizerRepresentation_apply_val` | Accept: proves actual parabolic triviality and descends by a genuine quotient-group lift; representative equations identify the descended representation. This proves inclusion in the kernel, not equality of that kernel with `W_J`; faithfulness remains unproved here. |
| `dualAction_pairing`, `geometricAction_mem_roots`, `geometricAction_mem_retainedRoots` | Accept: actual primal/dual pairing invariance and invariance of the root orbit and proper retained condition under the normalizer. Correct inverse/pairing directions are used. |
| `normalizer_preserves_complement`, `normalizerComplementAction` | Accept: simultaneous-vanishing exclusion is preserved by the genuine diagonal action; the inverse normalizer element supplies the inverse permutation, proving a real group action rather than merely set preservation. |
| `parabolic_le_normalizerComplementAction_ker`, `quotientComplementAction`, `quotientComplementMulAction`, `quotient_smul_eq`, `quotientComplementAction_mk` | Accept: actual parabolic triviality on both coordinates, genuine descent to the existing `Artin.coxeterNormalizerQuotient`, and representative/smul equations. The acting group is not replaced by an abstract easier quotient. |
| `continuous_dualAction`, `continuous_normalizerRepresentation`, `continuous_normalizerComplementAction`, `continuous_quotientComplementAction`, `quotientComplementContinuousConstSMul` | Accept: each true action map is continuous in the coordinate/subspace topology, by actual evaluation maps; quotient representatives establish continuity for every quotient element. Inverse elements give continuous inverse maps. |
| `OrbitSpace`, `orbitSpaceTopologicalSpace`, `orbitProjection`, `continuous_orbitProjection`, `isOpenQuotientMap_orbitProjection` | Accept: the literal orbit-equivalence quotient by that actual action, with the ordinary quotient topology and actual quotient projection, not a classifying-space surrogate. The open quotient-map theorem proves a genuine property of this map. |
| `properlyDiscontinuous_quotientComplementAction` | Accept: with finite `W`, actual `Q` is finite and satisfies mathlib's compact-intersection finiteness property. I inspected that literal definition. This property holds even for nonfree finite-group actions, so it does **not** establish freeness or the stronger local-disjointness premise of `IsQuotientCoveringMap`. The source comments correctly distinguish this. |

No faithfulness, free action, or quotient-covering theorem is assumed or asserted by this module. The actual orbit topology and continuous action are complete foundations; the article's freeness/covering assertion is still missing. In particular, it would be an invalid future inference to use the last theorem alone to instantiate the generic exact sequence.

## Final arrangement-topology review: all 16 declarations

| Names in `ArrangementTopology.lean` | Final semantic judgment |
| --- | --- |
| `pairEvaluation`, `pairComplement`, `mem_pairComplement_iff` | Accept: actual complex evaluation `f(x)+i f(y)` and nonvanishing for every selected real linear form, equivalently exclusion of simultaneous real/imaginary zeros. |
| `pairAffineLine`, `pairAffineLine_zero`, `pairAffineLine_one`, `pairEvaluation_affineLine` | Accept: actual complex affine parameterization `p+z(q-p)` written in real pairs, with correct real/imaginary cross-term signs. The evaluation theorem proves precisely the affine complex equation. |
| `continuous_pairAffineLine` | Accept: continuous in the complex parameter using exactly `[ContinuousAdd E] [ContinuousSMul ℝ E]`; no finite-dimensional or norm assumptions are secretly required for a fixed affine line. |
| `joinedIn_pairComplement` | Accept: for a finite family and existing endpoints in the actual complement, every forbidden functional has at most one zero along the complex affine line. If the affine coefficient vanishes, a forbidden zero would contradict the starting endpoint's nonvanishing. Thus finitely many parameter points are excluded; an actual path in `ℂ` minus that finite set connects `0` to `1`, and its affine image stays in the actual complement. |
| `pairComplement_nonempty` | Accept: a finite family of proper real linear kernels cannot cover the real vector space, using the exact pinned mathlib infinite-field/finite-family theorem. Taking `(x,0)` yields a genuine complement point. No finite-dimensional hypothesis is needed. Empty family and zero-dimensional space are included. |
| `isPathConnected_pairComplement` | Accept: combines proved existence with the actual path argument; properness is used for existence, not assumed as asphericity or a path witness. |
| `retainedEvaluation`, `pairComplement_retainedEvaluation` | Accept: restrict actual root evaluations to the actual relative flat and prove literal equality of this generic pair complement with `complementSet`, by unpacking the retained-root subtype. |
| `complementSet_nonempty`, `isPathConnected_complementSet`, `complementPathConnectedSpace` | Accept: specialize to the finite retained-root family under `[Finite M.Group]`; properness witnesses come from the definition of retained roots. Proves nonemptiness/path connectedness of the actual source complement, not a combinatorial nerve. |

The path argument does not need the linear functionals to be supplied as continuous maps: the path itself is constructed from a continuous complex parameter map and fixed vector arithmetic, and its membership is algebraically checked. No continuity hypothesis is missing from the stated generic theorem. The article's finite-dimensional setting already satisfies the weak topological-vector hypotheses used here. I read the pinned mathlib finite-family nonzero-functional supplier and its proof from finite unions of proper submodules; its field is `ℝ` here, so infinitude is supplied rather than silently omitted.

## Whole foundation inventory and exact scope

The full inventory is **93 explicit declarations**: 41 geometry, 32 normalizer-action, 16 arrangement-topology, and the four covering declarations reviewed above. Named instances are included. The aggregate `ArtinTheorem18.lean` only imports the completed algebraic lemma, these four foundation modules, and the generic provider covering-asphericity module; it declares no full theorem. Its work-in-progress comments accurately state the missing comparison and asphericity proofs. The companion JSON records all 93 qualified names parsed from the actual source. The audit's 145 project constants additionally include compiler-generated proof/equation declarations.

All 93 statements/definitions/instances are accepted for their literal scope. No hidden stronger finite/spherical/rank condition or surrogate space/group was found. The finite-type hypothesis appears exactly where root finiteness, openness, path connectedness, or finite-group proper discontinuity needs it. Neither arbitrary `J` nor rank-zero/full-parabolic boundary cases are excluded. The actual definitions match the independent `statement-b.md` contract for the portion now implemented.

The missing full-theorem work is now narrower than in the preliminary report: actual dual geometry, continuous normalizer-quotient action and real orbit topology, and complement nonemptiness/path connectedness **are proved foundations**. Still missing are faithfulness/freeness at the necessary points, the actual orbit-map covering theorem, the compatible presentation-defined Artin normalizer/fundamental-group comparisons, the required arbitrary-basepoint transports and right-square convention correction, and a proved asphericity theorem for this actual complement. The generic supplier assumes asphericity to transfer it; it does not fill that input. No accepted completion may replace these by assumptions, by a topologically redefined target, or by applying a simply connected-total-space theorem to a complement with nontrivial pi1.

## Resolved audit visibility finding and final evidence limits

During this review I found that `/tmp/theorem18-pre-review-audit.log` contained `lean.unknownIdentifier` errors for the three implicit-`a₀` lemmas, even though the later audit command printed a summary. I notified root immediately. This was an audit visibility failure from private imports, not a mathematical defect in the supplier statements. Root retained the failed output at `evidence/theorem18-development/audit-private-import-failure.log` and corrected the audit's direct imports.

I read `/tmp/theorem18-pre-review-audit-v2.log`, which explicitly prints all three correct elaborated types with ordinary implicit `{a₀:A}` and the expected `[Subsingleton (FundamentalGroup A a₀)]` premise; their conclusions are exactly the source-triviality facts analyzed above. It also prints the actual `IsAspherical` and K(G,1) iff formulas, the generic covering hypotheses, and the finite-type geometric/path statements. This resolves the implicit-binder question under the actual scoped vendor option. I subsequently inspected the final `/tmp/theorem18-pre-review-audit-v3.log`: it retains those correct printed types, contains no `error(` match in the inspected error screen, and reports 145 new project and 733 supplier constants. Root reports exit zero and confirms direct imports across the exact 37 scientific modules (four new project plus 33 suppliers). Root's driver checks the defining-module selection, preventing private-import visibility from silently omitting supplier modules. I did not rerun that audit myself.

The allowlist is `propext`, `Classical.choice`, and `Quot.sound`; a source-hole screen is not substituted for that transitive audit. The source hashes reviewed here do not certify that I personally ran a build or a checker. Root's reported compilation/audit execution and my independent statement/source/hash/evidence review are separate. No original-article mathematical error is established by this work; the audit failure's corrected disposition is retained rather than erased.

## Final byte binding and decision

I independently recomputed all project hashes after the frozen-source notice and checked them against `docs/theorem18/source-inventory.json`:

| Package-relative source | SHA256 |
| --- | --- |
| `ArtinTheorem18.lean` | `ff079b93a23f8c3e2e9535ad54ae71dae12923dcbebc4c4c17923550d593e914` |
| `ArtinNormalisers/Theorem18/ArrangementTopology.lean` | `e17eb88a02201854c545aa4be4a397f0457845921903676d362b5c94e66e272e` |
| `ArtinNormalisers/Theorem18/CoveringSequence.lean` | `5173fd6df5bac7b17fb33344e9d042a5d8d4e258bd22bb087ab02f882584d9f3` |
| `ArtinNormalisers/Theorem18/Geometry.lean` | `310a600d1d1a1b36aefa9190b2705d48f5115fd26e701a4569a7e791bad36098` |
| `ArtinNormalisers/Theorem18/NormalizerAction.lean` | `54b0dc36cf3ef6c399119c8a641e759b1d0474bf94d650c208314f4c4d3c99aa` |

The independently checked new provenance digest is `e4442d85498d9894d93e4c91ac313b116b6a46c4a527d9995dd20dd308bba0fd`; the historical source-inventory digest is `4e09907e8289d6ad65111da7950cd8a64dcc2422db58cd9934c13da83b9df5f4`. The receipt's `provider_source_sha256` is the exact independently recomputed 23-file map in the current provenance. The historical source/provenance files and reviews remain unchanged. This binding covers the current scientific bytes, with the original article/topological comparison limits stated in this review and `statement-b.md`.

The receipt also independently binds the actual reviewed configuration: `lean-toolchain` SHA256 `11c697aebe5b539d74f5069e497a588e7dfab1c4eeb74313f28357e351c55ca3`, `lakefile.toml` SHA256 `a4f4bede07139843865bb695f0c939825a54aefcdb5c5e403c067eec83a116ac`, and `lake-manifest.json` SHA256 `2b09091fec88c9bc3930b46b4ed3013c2f1d22ed539cc1b7e9cc8380fefb52ba`. Their map exactly matches the current source inventory and guards both dependency pins and the vendor-only `autoImplicit=true` setting reviewed above.

Final verdict: **accept-foundations-only**. `full_theorem_1_8_proved` is **false**. No source repair is required for the 93 literal foundation declarations; substantial theorem-completion obligations remain explicitly outside this accepted scope.
