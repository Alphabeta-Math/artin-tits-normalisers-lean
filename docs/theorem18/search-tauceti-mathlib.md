# Theorem 1.8: pinned TauCeti/mathlib supplier search

Date: 2026-11-14. Scope: actual geometric complement, its actual normalizer
quotient, fundamental groups, and asphericity. This task edited this document
only. It did not install packages, change caches/pins, compile TauCeti, audit
new transitive axioms, or replay new kernels. The results below are a
source-level direct-usability screen, not acceptance of external proofs.

## Decision

The pinned sources supply the standard real geometric representation and
roots of an arbitrary Coxeter system, the dual-representation construction,
quotient-covering foundations, the monodromy exact-sequence ingredients, and
generic transfer of asphericity across coverings. These are useful suppliers
for the actual spaces in Theorem 1.8.

They do **not** supply the substantial arrangement-specific comparisons needed
to identify those fundamental groups with the two algebraic normalizer
quotients. No Deligne arrangement groupoid, Salvetti comparison, Garside or
reduced ribbon groupoid, finite simplicial-arrangement asphericity theorem,
or restricted Tits-cone chamber theorem was found in the searched Lean sources.
The completed algebraic Lemma 2.8 therefore remains a supplier for one row of
the desired diagram; it does not establish the geometric row or an isomorphism
between the rows.

## Exact inspected revisions and search boundary

- Project mathlib: `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`, actual sources
  under `.lake/packages/mathlib/Mathlib`, Lean `v4.36.0-rc2`.
- [TauCeti](https://github.com/TauCetiProject/TauCeti/tree/62bbc0596dc3539d488232e4e924a338548ea0a9):
  `62bbc0596dc3539d488232e4e924a338548ea0a9`, inspected in
  `/tmp/lemma28-full-search/tauceti` and `/tmp/full28-tauceti`. A fresh
  `git ls-remote https://github.com/TauCetiProject/TauCeti.git HEAD` returned
  this same SHA, so the pinned source was also remote HEAD at the time checked.
  Toolchain `v4.36.0-rc2`; its own manifest mathlib is
  `e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`, different from the project pin.
  The previous verification of ten vendored algebraic modules does not verify
  the additional geometry/topology modules proposed here.

Used `git ls-tree`, `git grep` over tracked `.lean` sources, and direct source
reading, including outside the sparse checkout. Searched declaration/content
families included `Coxeter`, geometric roots, reflecting hyperplanes,
arrangements and complexified complements, `Salvetti`, `Garside`,
`Brink...Howlett`, `reduced...ribbon`, `Deligne...groupoid/complex`, Tits cones,
asphericity, covering monodromy, and exactness. Public GitHub-targeted web
queries for Lean Deligne/Salvetti/simplicial-arrangement/Garside code yielded
no additional usable source. Those negative search results are bounded;
they are not a proof that no formalization exists elsewhere.

The article was read from `/tmp/theorem18-source.txt`, checked against the
parent-supplied locators: arXiv:2509.21915v3, Theorem 1.8 (PDF p. 3), (3.26)
and the discussion of the normal covering, Theorem 6.7 and Corollary 6.14
(PDF pp. 26–27). This task did not review every article proof or its cited
literature. No mathematical literature error was established.

## Geometric suppliers

### Actual standard representation and roots: useful, source-compatible model

[TauCeti/GroupTheory/Coxeter/Geometric/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Geometric/Basic.lean)
defines `CoxeterMatrix.geometricForm` on `I →₀ ℝ`, simple
`geometricReflection`, and
`CoxeterSystem.geometricRepresentation : Representation ℝ W (I →₀ ℝ)`
(line 475). Its simple-generator action is proved in
`geometricRepresentation_simple`; `geometricForm_geometricRepresentation`
proves invariance of the form. `orderOf_simple_mul_simple` (line 521) and
`simple_injective` (line 527) hold for arbitrary Coxeter systems. These
definitions are the standard representation on the actual presented group,
not an unrelated arbitrary finite reflection group.

[TauCeti/GroupTheory/Coxeter/Geometric/Sign.lean](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Geometric/Sign.lean#L140)
adds, with only `{I W : Type*} [Group W] {M : CoxeterMatrix I}` and
`cs : CoxeterSystem M W`:

- `geometricRepresentation_single_pos_iff` and
  `geometricRepresentation_single_neg_iff`: the coordinatewise sign of
  `ρ(w)(Finsupp.single i 1)` is determined by the right descent condition;
- `geometricRepresentation_injective` (line 153): faithfulness of `ρ`;
- `geometricRoots` (line 165): precisely the set of vectors
  `ρ(w)(Finsupp.single i 1)` for `w : W`, `i : I`;
- root-set invariance under `W` and negation;
- `geometricForm_self_of_mem_geometricRoots`: every root has canonical-form
  square one;
- `pos_or_neg_of_mem_geometricRoots` and `ne_zero_of_mem_geometricRoots`.

Decision: these are direct candidate suppliers for the article's `V` and `Φ`.
For `[Finite W]`, `simple_injective` permits deriving `Finite I`; finite roots
then follow from their explicit `W × I` parametrization. The topology,
finite-dimensionality and root-evaluation hyperplanes still need to be
connected explicitly. No finite-type Tits-cone/chamber theorem was found in
this Coxeter source family.

Pinned mathlib
[RepresentationTheory/Basic.lean:670](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/Basic.lean#L670)
provides `Representation.dual` on `Module.Dual ℝ V`, with action
`φ ↦ φ ∘ₗ ρ(w⁻¹)`. This is the required contragredient action on `Θ`.
`Geometric/Transport.lean` also proves compatibility of the geometric
representation with `parabolicHom` under a matrix-compatible index map,
including extension by zero for an index subset. Neither result constructs
the normalizer-quotient action on `Θ_J` or on the complement.

### Reflecting hyperplanes: relevant linear algebra, comparison required

[TauCeti/RepresentationTheory/ReflectingHyperplane.lean](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/RepresentationTheory/ReflectingHyperplane.lean#L29)
has ambient `[Field K] [Group G] [Finite G] [AddCommGroup V] [Module K V]`
and `ρ : Representation K G V`. Its
`Representation.reflectingHyperplanes` is a `Finset (Submodule K V)` of
distinct fixed spaces of group elements whose fixed-space quotient has
finrank one. `mem_reflectingHyperplanes` gives exactly that existential
condition. `exists_dual_ker_eq_of_mem_reflectingHyperplanes` produces a
nonzero defining linear form, and
`le_fixedSubmodule_iff_of_mem_reflectingHyperplanes` says a group element
fixing such a hyperplane pointwise either acts trivially or has that entire
hyperplane as its fixed space.

Decision: useful optional finite-reflection linear algebra. It is **not**
already an identification with the article's root-kernel hyperplanes on the
dual standard representation. One must prove that identification before
using its `Finset` as the actual arrangement. Defining the article's
hyperplanes directly as root-evaluation kernels may be simpler.

The root-pairing/Weyl-group source family is not a shortcut to arbitrary
finite Coxeter types:
`TauCeti/LinearAlgebra/RootSystem/Coxeter/Presentation.lean`'s
`weylCoxeterHom`/`weylCoxeterSystem` assumes a finite root index type,
characteristic-zero domain, a base, and `P.IsCrystallographic`; surjectivity
additionally uses `P.IsReduced`. That endpoint cannot cover finite
noncrystallographic Coxeter systems under the stated hypotheses. The generic
geometric-root model above avoids this restriction.

### “SimplicialComplex.Arrangement” is not Deligne's arrangement theorem

[TauCeti/Analysis/Convex/SimplicialComplex/Arrangement.lean](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Analysis/Convex/SimplicialComplex/Arrangement.lean#L68)
proves `Geometry.SimplicialComplex.exists_isSubdivision_forall_nonneg_or_forall_nonpos`.
Its inputs are a finite geometric simplicial complex in a finite-dimensional
real normed space and finitely many continuous affine functionals. It returns
a finite subdivision on every simplex of which each functional has constant
weak sign. Its second endpoint similarly subdivides relative to finitely
many convex polyhedra.

Decision: potential triangulation support, not a theorem about complexified
arrangement complements, Salvetti complexes, or contractible universal
covers. The word “simplicial” in this filename cannot justify applying
Deligne's finite simplicial-arrangement theorem.

## Exact covering-space suppliers

Pinned mathlib
[Topology/Covering/Quotient.lean:39](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Topology/Covering/Quotient.lean#L39)
defines `IsQuotientCoveringMap p G`. It packages a quotient map, continuous
constant group actions, equality of fibers with orbits, and neighborhoods
whose translates are disjoint unless the translating group element is one.
It gives `isCoveringMap`, `surjective`, and `fiberEquivGroup`.

`isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul` (line 286)
applies to the actual orbit quotient assuming continuous constant action,
proper discontinuity, local compactness, Hausdorff total space, and
`IsCancelSMul G E` (freeness). For finite `G`, proper discontinuity itself
is supplied by `Finite.to_properlyDiscontinuousSMul` in
`Mathlib/Topology/Algebra/ConstMulAction.lean:597`.

Decision: directly applicable after constructing the actual action and
proving freeness on the actual complement. Finiteness does not prove
freeness. In particular one must establish the quotient action of
`N_W(W_J)/W_J`, not use the nonfree ambient normalizer action whose kernel
contains `W_J`.

Pinned mathlib
[Topology/Homotopy/Lifting.lean:639](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Topology/Homotopy/Lifting.lean#L639)
has, for `hp : IsQuotientCoveringMap p G` and a chosen sheet
`e : p ⁻¹' {x}`:

```lean
hp.fundamentalGroupToMulOpposite e : FundamentalGroup X x →* Gᵐᵒᵖ
```

`fundamentalGroupToMulOpposite_apply_eq_iff` computes it through the endpoint
of the lifted loop. `ker_fundamentalGroupToMulOpposite` (line 701), combined
with `ker_monodromyPerm` (line 612), identifies its kernel with
`(FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range`.
`fundamentalGroupToMulOpposite_surjective` (line 705) assumes
`[PathConnectedSpace E]`. These supply the exactness and surjectivity of
the geometric sequence once the quotient covering and connectedness exist.

For injectivity of its first arrow, pinned mathlib already proves
`IsCoveringMap.injective_path_homotopic_map`; the convenient fundamental-group
wrapper is
[TauCeti/Topology/Homotopy/Covering.lean:74](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Topology/Homotopy/Covering.lean#L74),
`IsCoveringMap.mapOfEq_injective hp he`, for any covering and basepoint
equality. It follows directly from the mathlib path-class injectivity.

**Convention:** mathlib's fundamental-group multiplication is the `End`
convention, `p*q` represented by `q` followed by `p` (see
`FundamentalGroup.mul_def`). The endpoint monodromy homomorphism consequently
targets `Gᵐᵒᵖ`. A map to `G` can be obtained by composing with
`(MulEquiv.inv' G).symm`, but its endpoint convention is then inverted. The
comparison with the article's left-to-right path multiplication must be
proved coherent on generators and the right-hand arrow, not inferred merely
from existence of abstract group isomorphisms.

Do not use `hp.fundamentalGroupEquiv` here: that theorem additionally assumes
`[SimplyConnectedSpace E]`. The complement `X_J^C` is generally not simply
connected; its fundamental group is precisely one of the groups to compute.

## Asphericity and K(π,1) suppliers

[TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean:53](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean#L53)
defines:

```text
IsAspherical X x = PathConnectedSpace X ∧ ∀ n, Subsingleton (π_(n+2) X x)
IsEilenbergMacLaneSpaceOne G X x =
  IsAspherical X x ∧ Nonempty (FundamentalGroup X x ≃* G).
```

Its constructors and basepoint/group-isomorphism invariance provide a
suitable final theorem language. They do not prove the arrangement
complement aspherical.

[TauCeti/Topology/Homotopy/HomotopyGroup/Covering.lean](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Topology/Homotopy/HomotopyGroup/Covering.lean)
proves `IsCoveringMap.homotopyGroupPiMulEquiv hp e n`, identifying
`π_(n+2)(E,e)` and `π_(n+2)(X,p e)` for every `n`; no connectivity
hypothesis is needed for this based statement.
[EilenbergMacLane/Covering.lean](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/EilenbergMacLane/Covering.lean#L89)
then supplies `IsCoveringMap.isAspherical hp hp_surj he h`, transferring
asphericity from total space to base, and `isAspherical_totalSpace` in the
reverse direction assuming path-connected total space.

Decision: directly useful. After a genuine proof that `X_J^C` is aspherical,
the actual quotient is aspherical by its surjective covering map. Combine
that with the actual fundamental-group identifications to obtain the two
`K(π,1)` conclusions.

The universal-cover recognition theorem
`TauCeti.UniversalCover.isEilenbergMacLaneSpaceOne` in
`AlgebraicTopology/UniversalCover/Classification/EilenbergMacLane.lean`
assumes path connectedness, local path connectedness, semilocal simple
connectedness, an actual fundamental-group isomorphism, and vanishing higher
homotopy groups of the actual universal cover. It organizes a proof after
these inputs have been obtained; it supplies none of the missing
arrangement-specific contractibility argument. Similarly, constructing an
abstract classifying space of `N(A,J)` cannot identify the specific
geometric quotient in Theorem 1.8.

`LocalCoefficient/QuotientCovering/Exact.lean` was also inspected: its
“exactness” is exactness of associated local coefficient systems of
representations, not the fundamental-group short exact sequence. It is not
a direct supplier for the requested comparison.

## Missing constructions and comparison maps

The following remain explicit proof obligations; none can be replaced by an
assumption in an asserted completion of Theorem 1.8:

1. Define `Θ_J = {φ : V* | ∀ j∈J, φ(α_j)=0}` in the dual standard
   representation. Define the restricted hyperplanes as the proper
   restrictions of the actual root hyperplanes. Exclude restrictions equal
   to all of `Θ_J`; including those would make the purported complement
   empty. Prove correspondence with the article's excluded parabolic roots.
2. Define the actual subtype of `Θ_J × Θ_J` obtained by deleting `H×H`
   for these restricted hyperplanes, with its subspace topology. Prove the
   required finiteness, openness, nonemptiness, path connectedness and local
   topology. A placeholder topological space or abstract classifying space
   is not this construction.
3. Construct the normalizer action, prove it preserves `Θ_J` and its
   arrangement, show `W_J` acts trivially, and descend to the actual
   `N(W,J)`. Prove the descended action free on the actual complement, then
   invoke the quotient-covering suppliers above.
4. Define chamber adjacency and positive path relations, construct the
   actual Deligne arrangement groupoid, and prove its comparison with the
   fundamental groupoid of the actual complement. Alternatively develop
   a Salvetti model with its proved homotopy comparison; an abstract
   presentation complex alone is insufficient.
5. Construct the ribbon/reduced-ribbon groupoid of the actual Artin group
   and identify its vertex group with the actual normalizer quotient.
   Prove the chamber-path/positive-lift functor into it respects all
   relations and is an equivalence, compatibly with `N(W,J)` and the
   geometric monodromy. These are the missing inputs behind the comparison
   of sequences, not consequences of ordinary Matsumoto alone.
6. Prove that the restricted finite real arrangement is simplicial and
   prove/apply a formal Deligne finite-simplicial-arrangement theorem to
   obtain asphericity of its complexified complement. No such applicable
   Lean theorem was found. Generic convex contractibility theorems do not
   apply to a hyperplane complement.

The source families worth developing or searching further are the precise
ones used in the article: Deligne's finite simplicial-arrangement theorem,
Salvetti/van der Lek comparison of arrangement paths with fundamental groups,
and Godelle's spherical Artin ribbon/Garside groupoids. They are literature
routes, not accepted formal suppliers in this inventory. A directly usable
new candidate must expose its actual definitions and full hypotheses,
compile against agreed pinned dependencies, pass a transitive axiom audit
excluding `sorryAx`/custom mathematical axioms, and undergo fresh kernel
replay before acceptance.
