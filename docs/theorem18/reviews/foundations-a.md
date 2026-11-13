# Theorem 1.8 foundations: independent semantic review A

Reviewer: GPT-6.1 Sol/high, task `lemma28_statement_review_a`.
Date: 2026-11-14. Verdict: **accept-foundations-only**.
**The full Theorem 1.8 is not proved by these sources.**

I independently read all commands, definitions, instances, theorem statements
and proof bodies in the four new `ArtinNormalisers/Theorem18/*.lean` files and
the `ArtinTheorem18.lean` aggregate. I checked the actual definitions against
the original article and my preceding `statement-a.md` contract, without
consulting reviewer B. I found no remaining mathematical defect requiring
repair in this scoped foundation layer. Historical proof/review files were
not edited.

## Source correspondence and complete project review

The original article passages and actual reading limits are recorded in
`statement-a.md`: Theorem 1.8; §§2–3, particularly (3.1)–(3.3), Lemma 3.23,
(3.26) and (3.28); Lemma 6.6, Theorem 6.7 and Corollary 6.14. My direct visual
PDF reading included pp.3, 7, 13, 26 and 27; the other specified passages were
read from the frozen extraction. No additional original Deligne/Godelle/Van
der Lek source reading is claimed in this foundation review.

There are **93 explicit project declarations/instances** in the four files:
41 Geometry, 32 NormalizerAction, 16 ArrangementTopology and four
CoveringSequence. The aggregate has imports and a truthful scope comment,
without a new theorem declaration. Every explicit declaration, including
instances and inline `[simp]` theorems, has disposition **accept as a
foundation**. The companion JSON lists every name. The following groups
explain the semantic checks on their actual statements and bodies.

### Geometry.lean: actual space, rather than a chosen classifying model

`Vector I` is the actual free real vector space `I →₀ ℝ`; `Dual I` is its
algebraic dual. `simpleRoot` is the actual basis vector. `dualCoordinates`
constructs the dual-coordinate linear equivalence and proves both inverse
laws, using finite support rather than assuming finite rank.

`dualTopologicalSpace` is the topology induced by that genuine coordinate
equivalence, and `dualCoordinatesHomeomorph` proves the identification with
the product topology on `I → ℝ`. Thus in the finite case it is the ordinary
real-coordinate topology. The addition/scalar/negation/topological-additive-
group and Hausdorff instances are transported through the correct maps.
`continuous_evaluation` proves continuity at every vector by its actual finite
linear expansion. These instances do not install a discrete or indiscrete
surrogate topology.

`relativeSubspace J` is exactly the functionals vanishing on all selected
simple roots, with its subspace topology. The membership equivalence and
closedness proof match (3.1). `root` and `roots` use the actual already
formalised standard geometric representation and the orbit of the simple
roots. `root_one` and `root_ne_zero` are proved from its identity/invertibility.
No arbitrary set of vectors is substituted for the source's roots.

`retainedRoots` retains a root precisely when evaluation is nonzero somewhere
on the actual relative flat. `restrictedHyperplane` is the kernel of that
restricted evaluation. `retainedRoots_iff` and
`restrictedArrangement_proper` prove these kernels are proper, and the image
definition `restrictedArrangement` identifies repeated hyperplanes.
`simpleRoot_not_retained_of_mem` and
`simpleRoot_retained_of_not_mem` correctly check the omitted and retained
simple-root cases. No hyperplane containing the whole relative flat is
accidentally removed from the complement.

`complementSet` removes exactly the pairs on which both evaluations vanish;
`Complement` is its actual subtype with inherited product/subspace topology.
`mem_complementSet_iff_arrangement` proves the exact distinct-hyperplane
formulation of (3.26). The choice of direct finite-case real-pair geometry is
allowed by the contract: it does not assert a result for arbitrary Tits-cone
interiors outside spherical type.

The empty/full selected-set identities, `retainedRoots_empty/univ`,
`complementSet_univ` and `complementUnivUnique` are valid boundary cases of
those same general definitions. They do not specialise away the arbitrary
`J` in other results. `finite_index` actually proves finite rank from finite
Coxeter group via simple-generator injectivity. `roots_finite`,
`retainedRoots_finite` and `isOpen_complementSet` then prove the finite-type
finiteness/openness assertions without adding a finite-`J` premise.

The file does not yet prove finite dimensionality/CW type, arrangement
simpliciality, a Salvetti/Deligne comparison, or any asphericity. Their absence
is not a false claim in the present foundation layer.

### NormalizerAction.lean: the actual natural action and orbit topology

`dualAction` is the contragredient of the existing standard representation;
`dualAction_apply` exposes exactly the necessary inverse on the vector
argument. `dualAction_simple_fixed_iff` computes the actual reflection and
uses its diagonal form value 1, proving the functional vanishes on that
simple root exactly when it is fixed. `mem_relativeSubspace_iff_fixed`
extends that condition to the actual generated Coxeter parabolic through a
stabiliser subgroup, in both directions.

`dualAction_mem_relativeSubspace` uses actual normaliser conjugation, so the
restriction `normalizerRepresentation` acts on the correct flat. The
subgroup/kernel containment and `quotientRepresentation` descend through the
already formalised actual `N_W(W_J)/W_J`. The representative/evaluation lemmas
are definitional, with the correct nested subtypes. Only containment in the
kernel is asserted here, not the still-unproved faithful-action conclusion
of the full source Lemma 3.23.

`dualAction_pairing` proves the usual invariant evaluation pairing by
cancelling the inverse actions. `geometricAction_mem_roots`,
`geometricAction_mem_retainedRoots` and `normalizer_preserves_complement`
use that pairing and the inverse normaliser element correctly. Thus
`normalizerComplementAction` is an actual permutation action, with inverses
and multiplicativity proved, rather than an unrelated action picked by
choice. The parabolic/kernel lemma and `quotientComplementAction` descend
this action through the actual quotient. Its `MulAction` instance,
`quotient_smul_eq` and quotient-representative formula identify precisely this
same action.

All four continuity assertions follow the real coordinate topology and
subspace/product inclusions; the quotient continuity proof chooses actual
normaliser representatives. `ContinuousConstSMul` then supplies the correct
discrete-group action continuity requirement.

`OrbitSpace` is the quotient by the actual `MulAction.orbitRel` and its
topology is mathlib's quotient topology. `orbitProjection` is literally the
orbit map. Its continuity and open-quotient-map statements refer to that map.
`properlyDiscontinuous_quotientComplementAction` correctly uses finiteness
in mathlib's compact-intersection sense. It explicitly does not claim
freeness: finite actions with stabilisers are not thereby covering actions.
No covering of this specific orbit map has yet been proved.

### ArrangementTopology.lean: nonempty actual complement and paths in it

`pairEvaluation`, `pairComplement`, its membership characterization,
`pairAffineLine`, its values at 0 and 1, and
`pairEvaluation_affineLine` encode genuine real/imaginary coordinates of a
complex affine line. The multiplication formula has the correct negative
imaginary cross-term. Continuity uses exactly continuous addition and real
scalar multiplication of the underlying topological module.

`joinedIn_pairComplement` is a substantive proof of paths in that actual
subset: on the line joining two complement points, each functional vanishes
at at most one complex parameter. If its slope were zero at a zero, the
initial point would already violate complement membership. Finiteness of the
family makes the forbidden parameter set finite. The proof then uses
path-connectedness of the plane minus that finite set, with 0 and 1 checked
as allowed parameters, and maps the resulting path back into the actual
complement. No linear segment through deleted hyperplanes is assumed safe.

`pairComplement_nonempty` uses the finite-family, proper-functional theorem
over the infinite field `ℝ` to select an actual vector on which no functional
vanishes, and pairs it with zero. It covers the empty family as well.
`isPathConnected_pairComplement` combines nonemptiness with the genuine
joining proof. `retainedEvaluation` is the actual nonzero restricted
functional; `pairComplement_retainedEvaluation` proves equality of the two
sets. The specialisations `complementSet_nonempty`,
`isPathConnected_complementSet` and the `PathConnectedSpace` instance thus
concern the actual arbitrary-`J` finite-type space, without an abstract
connectedness assumption or a combinatorial replacement.

### CoveringSequence.lean: useful generic theorem, not an established orbit cover

The two injectivity lemmas refer to actual path-homotopy classes via
mathlib's `FundamentalGroup.map`/`mapOfEq`. They follow covering hom-set
injectivity and actual equality-induced basepoint transport. No simple
connectedness hypothesis is inserted.

`quotientCovering_fundamentalGroup_range_eq_ker` identifies the image with
the actual endpoint-monodromy kernel. I inspected the underlying mathlib
`IsQuotientCoveringMap`: it requires a genuine quotient map, continuous
action, orbit fibres, and disjoint-translate neighbourhoods, implying
freeness. Its name is not an unconstrained data label.

`quotientCovering_fundamentalGroup_shortExact` correctly adds path-connectedness
of the total space only for surjectivity. All three conclusions use the
actual map and monodromy. The target is explicitly `Gᵐᵒᵖ`, as required by
mathlib's fundamental-group endomorphism multiplication and a left group
action. The code does not silently treat inversion as an endomorphism of a
noncommutative group. Future comparison with the article's `Q` row must prove
the required convention identifications and commuting squares.

This generic theorem assumes `IsQuotientCoveringMap p G`. That is legitimate
for a reusable covering prerequisite. It must not be advertised as the
article's covering row until that hypothesis is actually proved for
`orbitProjection M J` and its specific action.

## New supplier semantics and actual usefulness

I inspected the 23-file whole-module import closure listed in
`vendor/theorem18-provenance.json`, its actual direct import edges, and the
critical definitions and covering-transfer proof chain. The highest-priority
files were read as actual code, including both
`EilenbergMacLane/{Basic,Covering}.lean`,
`Homotopy/HomotopyGroup/Covering.lean`,
`Homotopy/GenLoop/{Map,Covering}.lean`, the used parts of
`Homotopy/HomotopyGroup/Map.lean`, `Homotopy/Covering.lean`, and the actual
fundamental-group basepoint/range statements. I inspected mathlib's literal
generalised-loop, relative homotopy and quotient definitions, not merely
supplier names.

`TauCeti.IsAspherical X x` is literally `PathConnectedSpace X` and
`∀n, Subsingleton (HomotopyGroup.Pi (n+2) X x)`. The latter is mathlib's
quotient of continuous maps from a genuine cube that send the boundary to
the basepoint, by homotopy relative to the boundary. It is not a dummy group
or an always-true proposition. `IsEilenbergMacLaneSpaceOne G X x` additionally
requires `Nonempty (FundamentalGroup X x ≃* G)` for the actual fundamental
group. These are honest weak-asphericity/`K(G,1)` recognition predicates;
they do not assert actual universal-cover contractibility without the
additional CW/Whitehead argument. No such stronger result is claimed here.

The downward covering transfer first transports path-connectedness using
surjectivity and then uses actual induced higher-group equivalences in all
dimensions `n+2`. The higher-group equivalence is the map induced by the
actual covering. Its surjectivity is proved by lifting a parameterised cube
contraction; its lifted boundary is constant because it maps into a discrete
fibre and the cube boundary is connected in dimension at least two. I read
that actual boundary-connectedness argument and its two distinct-coordinate
paths. Injectivity lifts relative homotopies at the zero corner. Hence no
assumption that the complement itself is aspherical is being disguised as
a proved arrangement result.

The remaining support modules supply basepoint transport/collars and
relative extension, product homotopy/fundamental-group equivalences,
fundamental-groupoid and one-object groupoid bookkeeping, actual path
operations, cube/ball homeomorphisms, curry homeomorphisms and unit-interval
facts. I inspected their role in the import chain and selected actual
declarations/constructions; I do not claim to have independently read every
proof line of the 305,059-byte supplier closure. They are useful as the
unchanged minimal whole-module closure of the explicit generic asphericity
transfer prerequisite, even though not every declaration in each module is
used by the local geometry files.

In particular the supplier theorem producing a `K(G,1)` orbit space of a
**simply connected** total space is conditional and is not directly an
asphericity proof for the generally non-simply-connected arrangement
complement. The useful eventual transfer here is the generic covering
asphericity theorem once the actual covering and actual complement
asphericity are proved.

I checked the three implicit-`a₀` range lemmas against the final elaborated
audit output. They really bind `{a₀ : A}` and require
`[Subsingleton (FundamentalGroup A a₀)]`; their conclusions are about induced
map ranges from that particular source group. Their source spelling relies
on upstream `autoImplicit=true`, which is confined to the vendor library.
The project library remains `autoImplicit=false` in the inspected Lake
configuration. There is no free/unbound point or hidden theorem conclusion
in those declarations.

## Frozen bindings and verification evidence

My own read-only SHA-256 computation matched every entry of
`docs/theorem18/source-inventory.json`:

| Project source | SHA-256 |
| --- | --- |
| `ArtinTheorem18.lean` | `ff079b93a23f8c3e2e9535ad54ae71dae12923dcbebc4c4c17923550d593e914` |
| `ArtinNormalisers/Theorem18/ArrangementTopology.lean` | `e17eb88a02201854c545aa4be4a397f0457845921903676d362b5c94e66e272e` |
| `ArtinNormalisers/Theorem18/CoveringSequence.lean` | `5173fd6df5bac7b17fb33344e9d042a5d8d4e258bd22bb087ab02f882584d9f3` |
| `ArtinNormalisers/Theorem18/Geometry.lean` | `310a600d1d1a1b36aefa9190b2705d48f5115fd26e701a4569a7e791bad36098` |
| `ArtinNormalisers/Theorem18/NormalizerAction.lean` | `54b0dc36cf3ef6c399119c8a641e759b1d0474bf94d650c208314f4c4d3c99aa` |

The new provenance SHA-256 is
`e4442d85498d9894d93e4c91ac313b116b6a46c4a527d9995dd20dd308bba0fd`;
the immutable historical source-inventory SHA-256 is
`4e09907e8289d6ad65111da7950cd8a64dcc2422db58cd9934c13da83b9df5f4`.
I independently hashed all 23 new provider files and matched each provenance
entry, then compared each file byte-for-byte with its upstream Git object
at `62bbc0596dc3539d488232e4e924a338548ea0a9`. All matched. The companion
JSON includes the complete 23-file map. These checks bind the actual
reviewed sources, not merely a repository name or revision label.

I also checked every actual new supplier import line against the provenance
graph and verified that its 23 modules are precisely the transitive whole-module
closure of the declared covering/asphericity root. The companion receipt binds
independently recomputed hashes of `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`, including the reviewed project/vendor `autoImplicit`
scoping and dependency pins.

I did not run a new Lean build, audit or kernel replay in this task, preserving
the requested read-only code/cache boundary. Root reported warning-free builds
of the scientific sources and all 33 suppliers. I inspected the actual final
`/tmp/theorem18-pre-review-audit-v3.log`: it displays the correct target and
supplier types and reports **145 new project declarations and 733 supplier
declarations** passing the transitive standard-axiom checks. By my own
read-only extraction of its defining-module labels, it covers exactly the
expected **37 modules**: four new project modules, 23 new and ten historical
provider modules. Its observed SHA-256 is
`9df16d6ad4d6bce5ec6cf979e91d4ffd22b3eabc877bc2384d42e4731e6a6eb2`.
The audit allows only `propext`, `Classical.choice`, `Quot.sound`, selects by
defining module and rejects empty selections; private/generated declarations
and supplier extensions to other namespaces are included.

The initial audit's three unresolved range-lemma names were an import-visibility
issue. Explicitly importing the already unchanged provider file in the audit
harness resolved it; the final output prints the expected
`TauCeti.FundamentalGroup.*` names with `{a₀ : A}`. The initial failure is
retained in development evidence. No mathematical proof repair was required.
The v3 harness additionally direct-imports all suppliers so unused declarations
behind private imports are not omitted. Neither the failed initial run nor
source scans alone are presented as a successful compiled proof check.

This is semantic acceptance of the scoped foundations plus inspection of root's
actual compiled/audit evidence. It is not a fresh independent Lean kernel
implementation, a full mathlib replay, or reviewer-executed kernel replay.

## Remaining main-theorem obligations

These sources have made real progress on the contract: actual arrangement
geometry/topology, the natural continuous quotient action and actual orbit
space, nonemptiness/path-connectedness, a correct generic covering exact
sequence, and honest generic higher-homotopy/asphericity transfer suppliers.

They have **not** proved freeness of the actual action, the actual orbit map's
covering property, the required arrangement/groupoid/Artin comparisons,
the two fundamental-group identifications with compatible inclusion and
monodromy squares, or the actual complement's asphericity. The ambient
topological-Artin/presentation bridge remains unformalised as before.
Consequently neither full Theorem 1.8 nor either required arrangement
`K(π,1)` conclusion follows from this layer alone. The aggregate and inventory
state that limit correctly. No new mathematical error in the original
article or consulted literature is asserted.
