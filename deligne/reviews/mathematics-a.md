# Preliminary independent Deligne mathematics review A

Reviewer: GPT-6.1 Sol / high (`gpt-6.1-sol`, `high`). I independently read every current definition, helper, theorem and proof body, module/import command, local instance and option in the fourteen frozen scientific files listed below: 3,547 lines. No reviewer B mathematical report was consulted. This is a complete preliminary semantic/source reading of this frontier, not final main-project acceptance or a claim that full M5/Theorem 1.8 is proved. No final main machine receipt or declaration audit is asserted. I executed no Lean command.

## Target and scope contract

The original article's Theorem 1.8 (PDF p. 3), Theorem 6.7/Remark 6.12 (pp. 26–27) and Corollary 6.14 (p. 27) concern the actual restricted arrangement complement, its actual normalizer orbit space and both their genuine fundamental groups and higher asphericity. Those statements and the earlier source-reading limits are retained in `docs/theorem18/landmarks/milestone5-contract-a.md`. The article applies Deligne's theorem to the actual finite real central simplicial arrangement; it does not identify a space merely by giving it the desired fundamental group. The current alternative finite-weight proof route is legitimate only once it proves a genuine higher-topological comparison with the original actual space. A path-class/sheet label bijection or equivalence of fundamental groupoids is insufficient for that last step.

The current algebraic/geometric hypotheses remain finite actual `M.Group`, arbitrary index universe and arbitrary standard-parabolic subset/target `B0`; `J=∅`, full J and rank zero are retained. No restricted root system is assumed Coxeter, no irreducibility or crystallographic condition is imposed, and no actual topological target is defined as a classifying space or aspherical by construction. More general local helper hypotheses, such as finite arbitrary ordered vertex types or generic continuous linear forms, are used where their proofs justify them.

The model now proved aspherical is the actual subspace `GarsideWeights M B0` of the genuine `OrderWeights (IncomingVertex M B0)` weak realization. It is **not** `ComplementUniversalCover M J`. I checked that all asphericity conclusions in these fourteen files have the weighted model in their literal types and that the original universal-cover sheets remain genuine subsets of the previously accepted based-path-class cover. A later actual all-dimensional comparison remains required. This is a scope distinction, not an objection to the presently stated weighted-model theorem.

## Incoming algebra, simple transport and orientation

`IncomingOrder` defines a vertex as an actual signed generated reduced ribbon from its varying source to the fixed target. Its source is proved determined by its actual Artin label, using genuine generator/parabolic transport, rather than assumed through an injectivity field. `difference u v = u.value * v.value⁻¹` is a genuine generated arrow between the respective sources. The partial order requires this difference to be an actual positive generated arrow. Its antisymmetry follows from degree nonnegativity in both directions and positivity-degree-zero implying identity, together with actual source uniqueness.

The height is **minus** exponent degree. It increases along the chosen order and strictly increases along strict order; this orientation agrees with deleting a positive left head of the incoming label. The actual source chamber uses representative `(π u.value)⁻¹`, which sends its source parabolic to the fixed target. `fiberTarget_chamber` proves this chamber definition agrees with the original signed fiber action. There is no chamber-injectivity assumption on arbitrary Artin labels: distinct pure incoming labels may have the same actual chamber.

Common right multiplication by an arbitrary genuine target loop is correctly an order automorphism because it cancels in every difference. The code does not infer chamber invariance for arbitrary such loops. `cofinalShift` uses the concrete accepted cofinal-loop powers, and the signed fraction theorem proves sufficiently large such powers make every fixed finite packet positive. This includes degenerate cofinal-loop cases without a positive-rank premise.

`SimpleTransport` connects the independently defined half-turn divisor predicate `SimpleRibbon` with actual canonical positive simple lifts. The forward direction uses genuine positive factors of the actual cofinal half-turn simple lift. For the converse, an actual standard source chamber and genuine endpoint fiber are constructed; source reduction/simple-lift equality prove minimality. Every actual chamber is incident at the origin, so the already proved face-residue/prefix theorem supplies divisibility by the actual half-turn. This proves the equivalence rather than building geometry into `SimpleRibbon`'s definition.

Both genuine positive generated factors of a simple product are simple; prefix/tail statements preserve their actual source/intermediate/target. Their projected minimal transporters and actual Coxeter length additivity imply chamber betweenness of ordered subtriples. A Boolean sequence with no alternating subtriple has one of the two sign orders, and opposite signs force distinct actual vertices, so strict height separation follows. Repeated equal vertices are explicitly permitted. No assertion equates relative edge count with ambient Coxeter length.

`IncomingJoins` proves actual common lower bounds from cofinal positivity of the inverse incoming arrow and concrete loop naturality. Above a common lower vertex, the actual arbitrary ribbon lcm supplies an upper vertex with label `l⁻¹*a.value`; its two connecting factors and its full least-upper-bound property are proved by genuine generated tails. Binary/finite joins and the semilattice instance are derived from this construction. Nonempty finite joins carry an explicit nonempty-packet hypothesis; no unjustified global bottom is added for an empty packet. Simplicity of ordered subintervals follows by actual simple factorization, and joins remain in a proved simple bounded interval with the asserted connecting factors simple. No chamber invariance for arbitrary target loops is used.

## Scalar interpolation and actual canonical-cell geometry

`MonotoneSignInterpolation` is a native finite-sum proof. Zero weights are allowed. If a nontrivial signed sum is zero and negative coefficients precede positive coefficients in height, subtract the maximum active negative height: every weighted term is nonnegative and one positive term is strict. The opposite orientation gives strict negativity. Nontriviality follows from total weight one and nonzero vertex evaluations, not from pretending every coefficient is active.

The actual real interpolation is `Σ w_i*c_i`; the imaginary part is `Σ w_i*(d_i-mean(d))*c_i`. When an actual real form vanishes on the real part, centering removes the mean term and the strict signed-height argument makes its imaginary evaluation nonzero. Thus the literal pair lands in the genuine complex complement. Continuity is actual finite coordinate continuity in the native topological vector space. Common height translation leaves the formula unchanged. At a vertex its imaginary part is zero and its real part the specified actual chamber point. Ordinary face/degeneracy aggregation is proved for both the mean and centered imaginary term; equal labeled vertices are summed before evaluation. No nonlinear associativity assumption or unproved chamber comparison is inserted.

`CanonicalCells` assigns each actual center a four-sign selector, prioritizing its nonzero real evaluation and otherwise its nonzero imaginary evaluation. Every center lies in its own open convex sign cell, so these cells actually cover. The active-center affine-combination argument is substantive: common-cell incidence aligns every nonzero center-real evaluation with the common point's real sign. If the weighted real sum vanishes, each active center's real evaluation must vanish; all their imaginary signs then align with the common point, preventing imaginary cancellation. This works with zero barycentric weights. Adding the common point as an extra center proves the entire actual affine return segment remains in the original complement.

The lower and upper phase chambers are constructed from actual face projections. The lower chamber of a center lies between the common point's phase bounds, and an upper bound inside that phase interval carries the **whole** actual canonical cell into its actual tube. The proof is at the literal sign/tube membership definitions, not an assumed interval/tube correspondence. Distinguish these phase bounds from the opposite-at-a-face residue bounds; the code uses the correct zero/nonzero forms in each setting.

`CanonicalCarriers` restricts cover indices to sign selectors actually realized by complement points. Each chosen center has a proved selector equality, lies in its corresponding cell, and gives genuine nonemptiness. Their cover sets are actual convex-cover members; in finite type the realized-selector index is finite and each member open. Contractibility is proved from a nonempty singleton family and a genuine center, so no empty-intersection contractibility error occurs. Those sets and contractibility transport to the original `Complement M J` through the already proved identity-coordinate homeomorphism.

The active affine carrier lemmas prove membership in one common actual tube: real cancellation forces each active center onto the real wall, where their tube imaginary signs align. Adding the common point proves the entire return path remains carried by that tube, including both endpoints and vanishing coefficients. The actual center/type/chamber wrappers preserve the existing complement topology; they are not substitutes for the original arrangement.

## Genuine universal-cover sheets and signed path labels

`LiftedTubes` uses the accepted TauCeti universal cover, whose elements are actual endpoint/path-homotopy classes with its previously verified topology. Endpoint fibers are genuinely equivalent to the original path classes. A sheet is literally the accepted sheet over an actual open chamber tube, indexed by a genuine fiber point at the original canonical chamber point. Projection restricted to a sheet is proved bijective using actual path connectivity and path-homotopy triviality, continuous and open using the genuine covering projection. It therefore gives a homeomorphism to the actual tube.

The actual application discharges these hypotheses from previously proved contractibility of actual tubes. It does not infer tube or total-space contractibility merely from simple connectivity. The continuous section has its literal projection formula and prescribed fiber basepoint. Its actual open range is the sheet; it is an open embedding. Distinct actual fiber points give disjoint sheets **over the same tube**, and all sheets cover the actual universal cover. No general disjointness of different-chamber sheets is asserted. Sheet contractibility follows from the displayed homeomorphism and actual tube contractibility; contractibility or asphericity of the whole cover does not follow from this local result alone.

`LiftedTubeLabels` uses the already proved fully faithful actual interval-to-complement functor and genuine signed ribbon covering to derive a bijection between these sheet indices and actual incoming reduced ribbons. The incoming label is the inverse of the outgoing path label, and the actual chamber uses the corresponding inverse projection. The source/chamber equations are proved from the existing signed endpoint calculation. They are not imposed as new data fields.

The exact pair gauge is correct in categorical traversal order: if the original path class to A followed by the actual arrow δ equals the class to B, then the incoming labels satisfy `p_A = label(δ) * p_B`. Both implications use actual fully faithful/faithful functors. The actual simple incoming difference is the canonical positive chamber transporter, so the positive gauge and exact transported sheet-index equality follow. No illegal op/unop group homomorphism is used. The earlier M4 opposite-group convention does not change these categorical path-composition formulas.

This is genuine one-dimensional path/sheet labeling and a genuine open-sheet cover. The files do not prove that the weighted realization is homotopy equivalent to, dominates or is dominated by the original universal cover. That later higher comparison must supply actual continuous maps and the needed homotopy/carrier construction; a label equivalence alone cannot replace it.

## Literal weighted subspace and finite continuous folds

`GarsideWeights` is the inherited subspace of the genuine `OrderWeights` realization whose ordered supported pairs have actual `SimpleRibbon` connecting factors. This extra small/simple-chain condition is part of an algebraic support predicate, not a contraction or asphericity field. The auxiliary finite-vertex subspaces retain exactly that predicate. Their inclusions are actual continuous weight maps. Compact maps factor through an actual finite vertex set by the proved weak-realization compact-carrier theorem, and injective support-image equations preserve the literal simple-chain condition in the lift. The finite coordinate criterion uses compactness/Hausdorffness of the **entire finite partially ordered** weighted space, not an invalid extrapolation from a single fixed-chain carrier.

The greatest simple head of an actual positive incoming vertex has an actual positive generated tail, and every positive simple neighbor lies below that tail with simple connecting factor. Nonidentity head removal strictly lowers actual exponent degree. The total `headStep` fixes identities and nonpositive vertices; its natural-number measure strictly decreases whenever it changes a positive vertex. `FiniteAncestry` is proved by strong induction and finite unions, yielding finite head-closed positive enlargements containing the actual identity root. It is a finite termination theorem and asserts no continuity by itself.

`GarsideFolds` proves the required continuity separately. For fixed p and its actual head-tail q, it transfers mass `t*w(p)` from p to q using explicit finite coordinate formulas. Nonnegativity, total one and support containment are proved, including p=q and zero source mass. If p is active and has maximum degree among the finite active packet, chain comparability and strict height show p is below every other active vertex. The proved head-cone theorem then puts every such vertex below q with a simple connector. The transfer therefore remains in the literal chain **and** simple-chain subspace at every time. If p is inactive, the map is the identity; there is no discontinuous support-dependent choice of p.

The resulting map is a joint continuous homotopy by the finite weighted coordinate criterion, with actual endpoint equations. At time one the nonidentity source vertex has zero mass and hence is absent from support. Strong induction on the remaining finite carrier cardinality chooses one maximum-degree vertex from the whole fixed packet, proves erasing it leaves the root and head closure, and concatenates actual deletion homotopies. The remaining root-only weighted point is proved the actual root vertex using total mass one. Applying the theorem to the actual identity map establishes contractibility of each finite positive head-closed **weighted subspace**. This is not merely a combinatorial collapse or pointwise contraction assertion.

## Cofinal compact carriers and based homotopy groups

`GarsideShifts` proves exact cancellation of common right cofinal shifts in every difference, so the simple support predicate is preserved. The particular concrete cofinal loops have actual Coxeter projection one because both parabolic longest squares project to one. Therefore these shifts preserve actual chambers. No analogous invariance under an arbitrary nonpure target loop is claimed. Restricting the actual order-weight homeomorphism gives a genuine homeomorphism of the weighted subspace.

Every compact map into the weighted model has finite support after factorization. One common cofinal shift clears that finite packet to positive vertices; a finite head-closed positive enlargement is then actually contractible by the fold theorem. Finite support restriction is continuous, retains the simple condition, and unshifting its actual inclusion gives a continuous **injective** carrier map factoring the original map exactly. The hypotheses are all proved for the constructed carrier; contractibility is not supplied by an abstract carrier field. No global open directed cover is assumed here, and compact factorization does not purport to construct a global contraction automatically.

`GlobalNullity` uses genuine based generalized loops and genuine based homotopy groups. For a loop f at x, it applies compact factorization to the continuous map on `Unit ⊕ cube`: the extra summand contains x even when the cube index type is empty and hence its boundary empty. Let y be that summand's lift into the finite contractible carrier. The unshifted inclusion j is injective; on every actual cube boundary point, `j(g z)=f z=x=j y`, so injectivity proves `g z=y`. Thus the lifted map is a **based** generalized loop, not merely a freely nullhomotopic cube. The accepted contractible-space theorem, which handles basepoint transport, gives equality of its actual based class with the constant class. Applying the actual induced homotopy-group map and the exact factorization gives the same equality for f.

Quotient induction proves subsingleton genuine homotopy groups for every finite index type and every weighted-model basepoint, including the empty type. A separate compact Bool map puts any two weighted points in one contractible carrier, proving actual path connectivity; the root vertex gives nonemptiness also in rank zero/full-parabolic cases. The final `garside_isAspherical` therefore has the exact TauCeti meaning: path connectedness plus subsingleton actual based higher cube-homotopy groups. Its target is literally `GarsideWeights`, and no actual complement/universal-cover asphericity follows without the missing higher comparison.

## ContractibleExtension and supplier/application limits

The generic extension module was independently read in full for the separate immutable carrier supplier receipt and its unchanged hash is checked again here. A genuinely contractible generic target and a genuine HEP map yield an actual continuous extension, using the reversed target identity contraction. The homotopy version glues exact side data and both whole endpoint maps through the actual cylinder-boundary pushout, then extends through its proved HEP map. The simplex specialization discharges HEP from the explicit boundary proof, including dimension zero and arbitrary target universe. It does not assume the original arrangement or universal cover contractible. Such a generic contractible-target premise is legitimate at this helper level, but a future actual geometric application must prove it for its actual chosen target.

Both new provider cohorts have already been independently read in full and accepted only at supplier scope, under exact hashes: twelve OAI weight modules (including one explicit tactic-only compatibility port) and sixteen Colib HEP/gluing modules (import-only relocations). Their actual literal hypotheses, original/active source reconstruction, license, relevant application proofs, recorded audits and official exact-module replay evidence are bound in `weights-providers-a` and `carriers-providers-a`. I do not rebrand those supplier executions as my own, a new whole-project audit or a higher comparison theorem. Existing M2/M3/asphericity/homotopy suppliers retain their accepted unchanged context and original reading limits. I re-read the actual contractible homotopy-group endpoint in `ArtinAsphericity.DirectedCover`; the current GlobalNullity application meets its genuine finite-index and contractible-space hypotheses.

## Findings, remaining obligations and execution limits

No concrete semantic defect or unsupported scope narrowing was found in any of these fourteen frozen modules. Their mathematical conclusions are substantive and correctly limited. In particular, neither based-nullity, full/empty J nor rank-zero cases were silently omitted. No new literature defect was found. Source citations and the original article/Deligne route are not used as axioms; missing formal higher-comparison mathematics is an established proof obligation, not a newly claimed open problem or article error.

The central remaining obligation is an actual higher-topological comparison between this small-simple-chain weighted space and the original universal cover/complement: actual maps, genuine continuity for their specified weak/subspace and original cover topologies, and a proved homotopy/carrier argument strong enough to transfer every based higher group. A subspace of a weak realization does not acquire a desired hereditary face-colimit topology merely by its name; any later use of such a principle must prove the relevant bridge. The finite-carrier and coordinate arguments currently reviewed do not make that unsupported inference. The announced draft `HereditaryWeights`, `SheetIntervals` and `RelativeGarsideCarriers` modules are intentionally outside this snapshot and will require their own full statement/proof review once frozen. The original actual orbit-space transfer, every-basepoint K(pi,1) statements and bundling with M4 maps also remain outside this preliminary acceptance stage.

I independently computed every hash below and confirmed the current source bytes. I performed ordinary read-only source and pinned API reading, declaration enumeration and hashes, and wrote only this owned review. I did not run Lean, mutate proofs/providers/configuration/caches, or claim a final project build/audit/replay/CI. Root reports these modules compiled; final main acceptance awaits the whole final comparison/full-theorem frontier, its exact source inventory and actual technical verification. No final acceptance JSON is issued here.

## Exact frozen source snapshot and declaration reading inventory

The lists below enumerate explicit named source entries, including private helpers and nested namespaces (names are given as spelled in their file). The anonymous finite-canonical-type instance in `CanonicalCarriers`, all local instances/options/imports, and generated elaboration obligations from each read proof were also considered at source level. This is not a claim to have enumerated or audited the eventual compiled physical constants.

### `deligne/ArtinDeligne/CanonicalCells.lean`

336 lines; SHA-256 `0c207d3119f3f4498d07de377e892fc0842df2c1726031b35819c897c4b9a417`.

`canonicalCellChoice`, `canonicalCellAmbient`, `canonicalCell`, `canonicalCoordinate_mem_iff`, `mem_canonicalCell_iff`, `canonicalCell_real`, `canonicalCell_imag`, `mem_own_halfspace`, `canonicalCell_self`, `isOpen_canonicalCell`, `convex_canonicalCellAmbient`, `isOpen_canonicalCellAmbient`, `canonicalCellAmbient_subset_complement`, `iUnion_canonicalCell`, `product_pos_of_halfspace`, `canonicalCell_real_product_pos`, `canonicalCell_real_product_nonneg`, `canonicalCell_imag_product_pos`, `centerCombination`, `centerCombination_mem_complement_of_active`, `centerCombination_mem_complement`, `centerCombination_with_commonPoint_mem`, `lineMap_commonPoint_centerCombination_mem_of_active`, `lineMap_commonPoint_centerCombination_mem`, `centerCombinationPoint`, `centerCombinationReturnPath`, `phaseUpperChamber`, `halfspace_sign`, `tubeLowerChamber_signs_real`, `tubeLowerChamber_signs_imag`, `canonicalCell_lower_eq_lower`, `canonicalCell_lower_eq_upper`, `canonicalCell_chamberBetween`, `bool_upper_interval`, `canonicalCell_subset_tubeSet`.

### `deligne/ArtinDeligne/CanonicalCarriers.lean`

326 lines; SHA-256 `05f81cb737cd14d2ddbfb2fa0d3181618fbbc145ea1173b1f3049589d89d2c69`.

`canonicalSelector`, `CanonicalType`, `canonicalCenter`, `canonicalSelector_center`, `canonicalTypeOfPoint`, `canonicalTypeSet`, `canonicalTypeSet_eq_convexCoverSet`, `canonicalCenter_mem`, `canonicalTypeSet_nonempty`, `isOpen_canonicalTypeSet`, `convex_canonicalTypeSet_ambient`, `mem_canonicalTypeOfPoint`, `iUnion_canonicalTypeSet`, `contractibleSpace_canonicalTypeSet`, `isPathConnected_canonicalTypeSet`, `isConnected_canonicalTypeSet`, `canonicalTypeChamber`, `canonicalTypeSet_subset_tubeSet`, `active_center_real_eq_zero`, `centerCombination_mem_tubeSet_of_active`, `lineMap_commonPoint_centerCombination_mem_tubeSet_of_active`, `centerCombinationPoint_mem_tubeSet`, `centerCombinationReturnPath_mem_tubeSet`, `actualCanonicalType`, `finite_actualCanonicalType`, `actualCanonicalCenter`, `actualCanonicalTypeSet`, `actualCanonicalCenter_mem`, `actualCanonicalTypeSet_nonempty`, `isOpen_actualCanonicalTypeSet`, `actualCanonicalTypeSetHomeomorph`, `contractibleSpace_actualCanonicalTypeSet`, `isPathConnected_actualCanonicalTypeSet`, `isConnected_actualCanonicalTypeSet`, `actualCanonicalTypeChamber`, `actualCanonicalTypeSet_subset_actualTubeSet`, `iUnion_actualCanonicalTypeSet`.

### `deligne/ArtinDeligne/ContractibleExtension.lean`

179 lines; SHA-256 `36db317b55852eb6ef0d81ffc5983da976d822fc58f4f9f31684327d78f143a1`.

`exists_extension_of_hep`, `cylinderBoundaryData`, `cylinderBoundaryData_side`, `cylinderBoundaryData_cap_zero`, `cylinderBoundaryData_cap_one`, `exists_homotopy_extension_of_hep`, `exists_simplex_boundary_homotopy_extension`.

### `deligne/ArtinDeligne/FiniteAncestry.lean`

77 lines; SHA-256 `7ba9f6bd21d223373a7bed68fe623772aef1a66af67e5d56f944720b14595d6a`.

`exists_finite_closed_ancestry`.

### `deligne/ArtinDeligne/IncomingOrder.lean`

244 lines; SHA-256 `5573ef8fd4b761aaf9c67b4aa770d8fded3be381b06947898dcac54d25ee03d9`.

`IncomingVertex`, `ext`, `source_eq_of_value_eq`, `ext_value`, `difference`, `difference_reduced`, `difference_self`, `difference_mul`, `difference_eq_one_iff`, `partialOrder`, `le_iff`, `height`, `height_monotone`, `height_strictMono`, `height_lt`, `rawFacetLabel`, `chamber`, `chamber_indices`, `chamberFiber`, `fiberTarget_chamber`, `rightMul`, `rightMul_source`, `rightMul_value`, `rightMulOrderIso`, `cofinalShift`, `cofinalShift_source`, `cofinalShift_value`, `eventually_positive`, `finite_eventually_positive`.

### `deligne/ArtinDeligne/IncomingJoins.lean`

211 lines; SHA-256 `14a9b849ec9dd932b1c0f04d752bd370dd7b57629bc6eea33e175c6c8995c578`.

`cofinalLowerVertex`, `eventually_cofinalLower_le`, `finite_eventually_cofinalLower_le`, `exists_common_lower`, `exists_join_of_common_lower`, `exists_join`, `binaryJoin`, `le_binaryJoin_left`, `le_binaryJoin_right`, `binaryJoin_le`, `binaryJoin_eq_of_lub`, `binaryJoin_isLUB`, `semilatticeSup`, `binaryJoin_eq_sup`, `finiteJoin`, `finiteJoin_isLUB`, `le_finiteJoin`, `finiteJoin_le`, `finiteJoin_mono`, `simple_difference_of_interval`, `finiteJoin_simple_interval`.

### `deligne/ArtinDeligne/LiftedTubes.lean`

271 lines; SHA-256 `84390b75260509ce20291efcf50679480ed205e2e26ca1ae96e775d6e56979bf`.

`universalCoverFiberEquivPathClasses`, `universalCover_mk_mem_sheet`, `universalCover_fiberPoint_mem_sheet`, `universalCoverSheetProjection`, `universalCoverSheetHomeomorph`, `universalCoverSheetHomeomorph_apply`, `tubeBasepoint`, `tubeBasepoint_mem`, `tubeBasepointInTube`, `isSimplyConnected_actualTube`, `LiftedTubeIndex`, `liftedTubePathClass`, `liftedTubeSheet`, `isOpen_liftedTubeSheet`, `liftedTubeSheet_subset_projection_preimage`, `fiberPoint_mem_liftedTubeSheet`, `liftedTubeHomeomorph`, `liftedTubeSection`, `liftedTubeSection_projection`, `liftedTubeSection_basepoint`, `range_liftedTubeSection`, `isOpen_range_liftedTubeSection`, `isOpenEmbedding_liftedTubeSection`, `liftedTubeSectionHomeomorph`, `disjoint_liftedTubeSheet_same_chamber`, `liftedTubeSheetContractible`, `exists_mem_liftedTubeSheet`, `iUnion_liftedTubeSheet`, `liftedTubeOpen`, `isOpenCover_liftedTube`.

### `deligne/ArtinDeligne/LiftedTubeLabels.lean`

326 lines; SHA-256 `dd9f10700f0bb3626ccc9debdac2fc9892573d2dcfd9d64f002f2ef35eeb2b21`.

`rebaseEquiv`, `outgoingEquiv`, `tubeBasepoint_standard`, `liftedTubePathEquiv`, `rootedPathIntervalEquiv`, `chamberIntervalObjectEquiv`, `rootedIntervalOutgoingEquiv`, `standardRibbonObject_indices`, `rootedRibbonIncomingEquiv`, `liftedTubeIndexEquivIncoming`, `liftedTubeIntervalArrow`, `map_liftedTubeIntervalArrow`, `rootedRibbonIncomingEquiv_value`, `rootedRibbonIncomingEquiv_source`, `liftedTubeIndexEquivIncoming_value`, `liftedTubeIndexEquivIncoming_source`, `incoming_chamber_of_interval_map`, `rootedRibbonIncomingEquiv_chamber`, `liftedTubeIndexEquivIncoming_chamber`, `incomingLiftedTubeIndex`, `incomingLiftedTubeIndex_chamber`, `incomingLiftedTubeSheet`, `incomingLiftedTubeSheet_subset_projection_preimage`, `transportLiftedTubeIndex`, `transportLiftedTubeIndex_eq_iff`, `liftedTubePathClass_comp_iff`, `liftedTubePathClass_comp_positive`, `transportLiftedTubeIndex_positive`.

### `deligne/ArtinDeligne/MonotoneSignInterpolation.lean`

332 lines; SHA-256 `404e02a2e6d10dc534af2dc5bb3e337d7f00ba270b1bce98aaa52b04bacbd540`.

`NegativeBeforePositive`, `PositiveBeforeNegative`, `SignHeightSeparated`, `exists_pos_and_neg_of_sum_zero`, `sum_height_mul_pos`, `sum_height_mul_neg`, `weighted_coefficients_nontrivial`, `negative_of_weighted_negative`, `positive_of_weighted_positive`, `weighted_height_sum_pos`, `weighted_height_sum_neg`, `weighted_height_sum_ne_zero`, `meanHeight`, `realInterpolation`, `imaginaryInterpolation`, `signInterpolation`, `eval_realInterpolation`, `eval_imaginaryInterpolation`, `signInterpolation_mem_complexComplement`, `meanHeight_translate`, `signInterpolation_height_translate`, `vertexWeight`, `meanHeight_vertexWeight`, `signInterpolation_vertexWeight`, `aggregateWeights`, `aggregateWeights_nonneg`, `sum_aggregateWeights`, `realInterpolation_aggregate`, `meanHeight_aggregate`, `imaginaryInterpolation_aggregate`, `signInterpolation_aggregate`, `continuous_meanHeight`, `continuous_realInterpolation`, `continuous_imaginaryInterpolation`, `continuous_signInterpolation`.

### `deligne/ArtinDeligne/SimpleTransport.lean`

256 lines; SHA-256 `1f3e69ad987bc97a108c06ed14ee9e166b604b7d5487a731d7e9fabeea5d9748`.

`facePrefix_univ`, `cofinalDelta_eq_simpleLift_projection`, `SimpleRibbon.eq_simpleLift`, `rawFacePoint_univ`, `intervalPositive_prefix_cofinalDelta`, `simpleRibbon_intervalPositive`, `simpleRibbon_iff_positive_eq_simpleLift`, `simpleRibbon_one`, `SimpleRibbon.factors`, `SimpleRibbon.prefix`, `SimpleRibbon.tail`, `relativeTransport_simpleFiberTarget`, `chamberBetween_of_simple_product`, `incoming_relativeTransport`, `incoming_chamberBetween`, `bool_sign_order_separated`, `chamber_sign_true_iff`, `chamber_sign_false_of_neg`, `incoming_signHeightSeparated`.

### `deligne/ArtinDeligne/GarsideWeights.lean`

284 lines; SHA-256 `fdf0c6153eb4299d414bed714b9a507ad8bac91e1d851de09e83a1180eae309f`.

`isClosedEmbedding_coordinates`, `continuous_iff_coordinates`, `garsideWeightsSet`, `GarsideWeights`, `GarsideWeights.simple`, `garsideWeightsOnSet`, `GarsideWeightsOn`, `GarsideWeightsOn.include`, `GarsideWeightsOn.continuous_include`, `GarsideWeights.compact_map_finite_carrier`, `IncomingVertex.IsPositive`, `incomingRoot`, `incomingRoot_value`, `incoming_value_eq_one_iff`, `incomingRoot_positive`, `exists_positive_headTail`, `positiveHeadTail`, `positiveHeadTail_spec`, `headStep`, `headStep_eq`, `headStep_eq_self_of_value_eq_one`, `headStep_positive`, `headStep_degree_lt`, `headStep_measure`, `exists_finite_positive_head_closed`, `headStep_cone`.

### `deligne/ArtinDeligne/GarsideFolds.lean`

446 lines; SHA-256 `a21be1d908a5e2c5983c668beedae79d4c4a321528e7e00d3a20470c33a472d4`.

`movedWeights`, `movedWeights_apply`, `movedWeights_nonneg`, `movedWeights_total`, `movedWeights_support`, `movedWeights_zero`, `movedWeights_eq_of_notMem`, `movedWeights_one_source`, `moveOrderWeights`, `continuous_moveOrderWeights`, `active_le_headStep`, `deletion_cone`, `deleteVertex`, `continuous_deleteVertex`, `deleteVertex_zero`, `deleteVertex_one_source`, `deleteVertexHomotopy`, `GarsideWeightsOn.vertex`, `eq_vertex_of_support_singleton`, `finite_positive_head_closed_homotopic_const`, `contractibleSpace_finite_positive_head_closed`, `exists_finite_contractible_positive_enlargement`, `GarsideWeights.restrict`, `GarsideWeights.continuous_restrict_finite`, `GarsideWeights.include_restrict`.

### `deligne/ArtinDeligne/GarsideShifts.lean`

159 lines; SHA-256 `a850d7afb3a06e172c13d47cb889ff61ce47668f3084e85d6389c9acddfd22b5`.

`IncomingVertex.cofinalShift_difference`, `projection_cofinalLoop`, `IncomingVertex.cofinalShift_chamber`, `garsideWeightsSet_shift_iff`, `cofinalWeightsShift`, `cofinalWeightsShift_val`, `GarsideWeightsOn.include_injective`, `unshiftedCarrierMap`, `unshiftedCarrierMap_injective`, `GarsideWeights.compact_map_contractible_carrier`.

### `deligne/ArtinDeligne/GlobalNullity.lean`

100 lines; SHA-256 `2f337a3e28d3f076c66752bfa203e7402c358d339b0dc3eb00e7539dfb6d6088`.

`garsideRootPoint`, `garside_genLoop_class_eq_const`, `garside_homotopyGroup_subsingleton`, `garside_joined`, `garside_pathConnectedSpace`, `garside_isAspherical`.

