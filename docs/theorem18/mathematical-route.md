# Theorem 1.8: complete mathematical target and dependency route

Research date: 2026-11-14. Scope: the actual Theorem 1.8 of
Garnier–Heng–Licata–Yacobi, arXiv:2509.21915v3, not another abstraction of
Lemma 2.8. This document records mathematical analysis and bounded source/API
inspection. It is not a Lean proof, verified provider certificate, build log,
or declaration that Theorem 1.8 has been formalized. Only this document was
authored in this task; no proof files or package caches were changed.

## The target must use the actual spaces

Let `M` be a spherical Coxeter matrix with index set `I`, `W=M.Group`, and
`A` the actual standard Artin presentation already used by this package.
Spherical means `W` is finite. Since the simple-generator map is injective,
this also forces `I` finite; a `Fintype I` argument is a convenience for
coordinates, not an additional mathematical restriction. Arbitrary
`J : Set I` is allowed, including the empty set and the whole set. Neither
irreducibility nor crystallographic type is assumed. In particular the
noncrystallographic finite types must be covered.

Use the standard real geometric representation `V` with basis `α_i` and its
contragredient representation on `Θ=V*`, with its ordinary finite-dimensional
real-vector-space topology. Define the actual subspace and restricted
arrangement, following (3.1)–(3.3), PDF p.7:

```text
Θ_J = {f ∈ Θ : ∀ j ∈ J, f(α_j)=0},
H_α = {f ∈ Θ : f(α)=0},
𝓗^J = {H_α ∩ Θ_J : α a real root and Θ_J ⊈ H_α}.
```

The exclusion `Θ_J ⊈ H_α` is essential: otherwise the restricted set contains
the whole ambient flat and its complement becomes empty. Distinct roots can
give the same restricted hyperplane. Treat `𝓗^J` as a set of actual proper
hyperplanes, or prove an equivalent root-indexed complement condition; do
not assume roots and restricted hyperplanes are in bijection.

Since `W` is finite, the Tits cone is all of `Θ`, and its relative interior
in `Θ_J` is `Θ_J`. Thus the actual space in (3.26), PDF p.13, can be defined
without general infinite Tits-cone machinery:

```text
X = { (x,y) ∈ Θ_J × Θ_J : ∀ H ∈ 𝓗^J, ¬(x∈H ∧ y∈H) }.
```

Give this subtype its induced topology. It is the complement of the union
of the actual `H×H`, canonically homeomorphic to the complexified complement
`(Θ_J ⊗_ℝ ℂ) \ ⋃ H_ℂ`. The pair model is already the source's definition,
so formalizing a tensor-product homeomorphism is optional for this theorem.
Prove its agreement with the finite-type specialization of (3.26).

Let `N=N_W(W_J)/W_J`. The action must be the descended, restricted
contragredient action, diagonal on pairs. Let `Y=X/N` be its **topological
orbit quotient**, with actual projection `q:X→Y`. Neither `X` nor `Y` may
be replaced by a classifying space by definition.

For every `x∈X`, the complete conclusion is a pair of multiplicative
equivalences

```text
u : N(P,J) ≃* π₁(X,x),
v : N(A,J) ≃* π₁(Y,q x),
```

an actual covering monodromy homomorphism `δ:π₁(Y,q x)→*N`, short exactness
of the covering sequence, and the two equalities

```text
v ∘ inclusion = q_* ∘ u,
δ ∘ v = articleNormalizerProjection.
```

These make the source's two short exact sequences isomorphic with identity
on `N`. Merely proving two unrelated abstract group isomorphisms omits the
compatibility assertion of Theorems 1.8 and 6.7.

Finally prove that **these actual spaces** are K(π,1) spaces for the displayed
groups. A sufficient explicit formal meaning is that they are path connected,
have the displayed fundamental groups, and have trivial homotopy groups in
every dimension at least two. The stronger geometric version constructs
contractible universal covers of both spaces. Since these are manifolds
(or have the proved Salvetti CW homotopy type), the usual versions agree.
A mere `SimplyConnectedSpace X` would be false in general, and a statement
only about `π₁` does not establish the K(π,1) conclusions.

## Faithful route through the original proof

The source routes Theorem 1.8 (PDF p.3) through Theorem 6.7 (pp.26–27) and
Corollary 6.14 (p.27). The following separates the indispensable substantive
inputs from consequences of established group and covering-space APIs.

1. **Finite reflection geometry and chamber labels.** Prove the standard
   representation's finite-type chamber theorem and parabolic stabilizers.
   In particular the real restricted arrangement is finite, central and
   simplicial; its chambers are the actual relatively open faces `x·C_I`
   lying in `Θ_J`. The source's Theorem 3.9, pp.9–10, identifies these with
   `(x,I)` satisfying `W_J x=x W_I` and minimality of `x` in `xW_I`.
   Prove this identification for the actual real chambers, not merely
   define a combinatorial type called “chambers.” Propositions 3.17 and
   3.29 identify adjacent crossings and geodesic galleries with the
   indicated Coxeter products and length additivity.

2. **The actual finite normalizer action and cover.** Lemmas 3.23–3.24,
   PDF p.12, prove that the normalizer preserves `Θ_J`, that its kernel
   on this flat is exactly `W_J`, and that `N` acts freely on chambers,
   preserves adjacency, and has orbits indexed by the associates `I`.
   Prove the induced action preserves `𝓗^J` and `X`. Prove that this
   action on `X` is free, and then that `q` is a regular cover with
   fibers the `N`-orbits, as used in (3.28), p.13.

   In finite type, the extension from chamber freeness to complex freeness
   has a short independent proof. If `g` fixes `(x,y)∈X`, choose a real
   number `t` avoiding the finitely many zeros of
   `a_H(x)+t a_H(y)` over `H∈𝓗^J`, where `a_H` defines the hyperplane.
   No such linear polynomial is identically zero by the definition of `X`.
   Then `x+t y` lies in a real chamber and is fixed by `g`; this chamber
   is fixed, so chamber freeness gives `g=1`. The group `N` is finite,
   making proper discontinuity immediate. This avoids extending the
   infinite-type local-finiteness arguments of Lemma 3.5/Proposition 3.6.

3. **Positive galleries and the Deligne groupoid.** Define `D+` as the
   category of directed chamber galleries modulo identifying all geodesics
   with the same endpoints, and `D` as its groupoid completion (§3.5,
   PDF p.14). There are *two independent positive arrows* across an
   adjacency, one in each direction. They are not inverse arrows.
   The `N` action preserves this construction (Remark 3.30).

4. **Spherical Artin/Garside/ribbon algebra.** Define the actual positive
   Artin monoid inside the actual Artin group, or construct the positive
   presented monoid and prove its embedding. This is now needed, unlike
   in the Lemma 2.8 proof. Prove spherical Garside properties, parabolic
   positive monoids, longest elements/positive lifts `Δ_I`, and the
   positive ribbons `μ_(a,I)=Δ_I⁻¹Δ_(I+a)`.
   Define the reduced ribbon groupoid `R` as the subgroupoid of the
   actual ribbon groupoid generated by these ribbons (Definitions 5.1
   and 5.5, PDF pp.21–22). Prove:

   - the restriction of the canonical quotient map gives
     `R_J ≃* N(A,J)`, via the internal decomposition
     `N_A(A_J)=A_J ⋊ R_J` (Theorem 5.6, citing Godelle [14],
     Proposition 4.4);
   - the lcm relations (5.8) present `R` (Godelle [17],
     Corollary 4.18; see Remark 5.7);
   - these lcm relations are precisely the two positive lifts of the
     rank-two standard Coxeter paths, Lemma 5.9, pp.22–23, using the
     Coxeter rank-two join result Lemma 4.15 and the positive-simple
     divisibility/weak-order correspondence.

   These are substantive new inputs. A black-box “ribbon interface”
   assuming the quotient isomorphism would leave a central part of
   Theorem 1.8 unproved.

5. **Comparison of the algebraic groupoid covering.** Define
   `G:D→R` by `(x,I)↦I` and elementary crossing `ω_(a,I)↦μ_(a,I)`.
   Lemma 6.1, p.23: geodesic Coxeter length additivity and ordinary
   Matsumoto show this is well defined. Lemma 6.2, p.24: elementary
   lifts exist, and the complete lcm presentation plus Lemma 5.9 make
   lifts independent of relations. Proposition 6.3 and Corollary 6.4,
   pp.24–25: using the chamber-orbit theorem and unique lifting,
   `D/N ≅ R`, and the two groupoid covers agree.

   Full general-type Brink–Howlett universal-cover theory and the whole
   atomic Matsumoto theorem (Theorem 4.21) need not be formalized first
   if their *particular finite-type* chamber and rank-two inputs are
   proved directly. The source's §6 route uses the specified rank-two
   and presentation inputs, not Theorem 4.21 as an additional axiom.

6. **The indispensable geometric/topological comparison.** Prove an
   `N`-equivariant equivalence `p:D ≌ FundamentalGroupoid(X)` with
   actual continuous path classes. Lemma 6.6, pp.25–26, chooses
   chamber points `a_C` equivariantly in contractible open sets

   ```text
   X_C = {(x,y)∈X : ∀H, x∈H → y lies on the C-side of H}.
   ```

   For adjacent chambers, the two components of `X_C∩X_C'` select
   the two positive wall-crossing paths. Well-definedness and full
   faithfulness use the arrangement fundamental-groupoid theorem;
   the source cites Van der Lek, Corollaries I.2.18 and I.2.19 and
   Theorem I.4.10. Equivariance follows from the actual action on the
   open sets and their components. This induces the corresponding
   equivalence on orbit groupoids and the **actual** quotient `Y`.
   An abstract equivalence of combinatorial groupoids alone supplies
   no path-space comparison.

7. **Identify the exact maps and transport basepoints.** Take vertex
   groups in the compatible covering square. For a loop ribbon `β`,
   its lifted gallery from `(e,J)` ends at the chamber labelled by the
   Coxeter class of `π(β)`. Hence the deck map agrees with the actual
   quotient homomorphism from Lemma 2.8. Combine `R_J≃N(A,J)`, the
   equivariant topological comparison and the already proved algebraic
   kernel theorem to get Theorem 6.7. The source proof first uses the
   chamber point `a_(e,J)`; for arbitrary `x∈X`, use a path from that
   point to `x` and its projection simultaneously. Independent,
   unrelated changes of basepoint can destroy the written diagram.

8. **Asphericity of the actual arrangement complement.** Apply a
   *proved* finite-simplicial-arrangement theorem of Deligne to the
   actual `𝓗^J`. This is Corollary 6.14's nontrivial input. It supplies
   a contractible universal cover of `X`. Show this cover also covers
   `Y` by composition with `q`, or prove covering invariance of all
   higher homotopy groups. Thus `Y` is aspherical as well. The two
   identified fundamental groups give the two K(π,1) assertions.
   Do not replace this step by defining a classifying space of `D`:
   proving that such a space has the homotopy type of the actual
   complement is exactly the missing geometric assertion.

## A possible shared construction, and unsuccessful shortcuts

A sound implementation can share work across steps 6 and 8 by constructing
the finite **actual Salvetti complex** from faces and chambers, proving an
`N`-equivariant homotopy equivalence/deformation retract with the actual
complement, deriving the directed-gallery fundamental-groupoid presentation,
and proving contractibility of its actual universal cover by the
Deligne/Garside lattice argument. This may avoid separate reconstruction of
Van der Lek's presentation proof and Deligne's geometric gluing, while
retaining their mathematical content. It still requires topology of a
realized cell/simplicial complex, an actual homotopy comparison, and a
contractibility proof. A statement that assumes any of these decisive
bridges is only conditional progress.

One can also follow Deligne's original geometric construction directly:
build the gallery complex, prove its contractibility, glue copies of the
chamber opens over the actual complement, prove that this is a covering,
and compare its good-cover nerve with the contractible gallery complex.
Deligne's §3, Theorem (3.7), printed pp.293–296, supplies exactly this
blueprint. The proof relies on the prior gallery-contractibility theorem
(2.15), not merely on the existence of a gallery groupoid.

The following apparent reductions do not eliminate the core work:

- `Θ_J` is the real fixed flat of `W_J`, but for nonempty `J` its
  complexification lies in reflecting hyperplanes removed from the
  full Coxeter regular complement. Its intersection with that full
  complement is empty. The relative `X` is not its fixed-point subset.
- A centralizer or normalizer description involving `Δ_J²` may offer
  another proof of the ribbon algebra; it does not identify the actual
  relative complement's fundamental group or prove its asphericity.
  Such a description must itself be proved under the relevant
  parabolic-closure hypotheses.
- A subspace or fixed-point set of an aspherical space need not be
  aspherical. No inheritance theorem of that form can replace Deligne.
- No CAT(0) metric on arbitrary spherical Artin universal covers has
  been supplied by the inspected sources. Do not assume such a metric
  to make a fixed-point or convexity argument.
- The restricted arrangement generally is not a reflection arrangement
  of `N`; the source explicitly notes that `N` need not be transitive
  on all its chambers (Remark 3.25). Ordinary Artin–Coxeter topology
  for `N` is not a replacement for the ribbon construction.

## Composition and monodromy conventions

The source composes paths and groupoid morphisms from left to right (§2.4,
PDF p.6). Mathlib defines `FundamentalGroup X x` as the categorical vertex
group, with

```lean
FundamentalGroup.mul_def : p * q = .of (q.asHom.trans p.asHom)
```

(`Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`,
line 44). Accordingly, for a left deck action the existing mathlib
monodromy homomorphism has target `Nᵐᵒᵖ`, not `N`:
`IsQuotientCoveringMap.fundamentalGroupToMulOpposite`.
Use opposite groups consistently, or compose with the canonical inversion
isomorphism `Nᵐᵒᵖ≃*N` and consistently invert the source's path-class
identifications. The resulting commutative squares must be proved with
these choices. Ignoring this issue can produce an antihomomorphism disguised
as the asserted quotient map. It is a convention translation, not a
mathematical defect in the paper.

The positive arrow `C'→C` is not the inverse path class of the positive
arrow `C→C'`: the two use different intersection components. The paper
emphasizes this in its footnote on PDF p.26. Identifying them would already
destroy the classical rank-one example.

## Degenerate cases and useful validation examples

- `J=∅`: `Θ_J=Θ`; `X` is the ordinary finite Coxeter arrangement
  complement, `N=W`, and the conclusion recovers the classical
  pure/Artin fundamental groups and their exact sequence. This case
  includes Deligne's spherical Artin asphericity, showing the general
  target cannot be solved by elementary normalizer algebra alone.
- `J=I`: `Θ_J={0}`, there are no proper restricted hyperplanes,
  `X` and `Y` are singletons, and `N(W,J)`, `N(A,J)`, `N(P,J)` are
  trivial. Do not impose positive dimension, nonempty arrangement,
  or nontrivial fundamental group in a helper theorem.
- Rank zero is the same trivial case. Reducible diagrams are allowed;
  product decompositions can simplify proofs but cannot be hypotheses.
- Relative dimension one has restricted complement `ℂ*` when a
  restricted hyperplane is present. The finite real scalar action
  has order at most two. The rank-one classical case, in particular,
  has two positive chamber-crossing arrows rather than one arrow
  and its inverse; it detects the convention error above.
- Type `A₃`, `J={3}`, in Example 3.12, PDF p.10, gives a two-dimensional
  flat with three distinct restricted lines. The source's `D₄`,
  `J={2}`, pp.27–30, has seven distinct restricted planes and 32
  chambers. Neither root enumeration nor an arbitrarily chosen
  normalizer representation can silently replace these spaces.

## What inspected formal libraries actually supply

The dedicated README records the completed full algebraic Lemma 2.8 and
explicitly excludes the topological/presentation comparison. The vendored
TauCeti modules supply Artin presentations, Matsumoto, parabolic length
theory, and elementary geometric representation/order results. Inspection of
`vendor/TauCeti/GroupTheory/Coxeter/Geometric/Basic.lean` found
`geometricRepresentation` (475), its simple-generator formula,
form preservation, exact rank-two order, and `simple_injective` (527).
It does not supply a proved real chamber theorem, restricted arrangements,
Salvetti topology, ribbons/Garside normalizer splitting, or Deligne
asphericity. Existing algebraic verification does not certify these new
claims.

The pinned local mathlib source has substantial foundations to reuse:

- `AlgebraicTopology/FundamentalGroupoid/{Basic,FundamentalGroup,InducedMaps}.lean`:
  actual path-homotopy groupoids, vertex groups, continuous-map-induced
  homomorphisms, and basepoint change along a path.
- `Topology/Covering/Quotient.lean`:
  `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`, using
  a free action (`IsCancelSMul`), locally compact Hausdorff space, and
  continuous scalar maps. `Topology/Algebra/ConstMulAction.lean:597`
  has `Finite.to_properlyDiscontinuousSMul`.
- `Topology/Homotopy/Lifting.lean`: path and homotopy lifting;
  `IsCoveringMap.injective_path_homotopic_map` (477) for the injection
  on `π₁`; `IsQuotientCoveringMap.ker_monodromyPerm` (612) identifies
  the monodromy kernel with the range of the actual covering-induced
  `π₁` map; `fundamentalGroupToMulOpposite` (639), its kernel formula
  (701), and surjectivity for path-connected total space (705).
  Thus a new general regular-cover short-exact-sequence theory need
  not be built from nothing.
- `Topology/Homotopy/HomotopyGroup.lean` defines actual higher
  homotopy groups and identifies `π₁` multiplicatively with the
  fundamental group. `Topology/Homotopy/Contractible.lean` supplies
  contractible spaces and homotopy-equivalence transport. CW and
  simplicial-complex foundations exist, but are not the required
  arrangement model or its contractibility proof.

A bounded search of the pinned mathlib source and vendored provider found
no `Salvetti`, finite simplicial arrangement asphericity, or ribbon groupoid
implementation. No ready-to-use higher-homotopy covering equivalence was
located in the inspected lifting file; its proof can be obtained by lifting
cube maps and homotopies, or bypassed by constructing a common contractible
universal cover. This is an API search result, not a claim of nonexistence
in every Lean repository. No new build or axiom audit was run here.

## Source reading and unresolved proof obligations

Read the dedicated README in full; read the original paper's §§3.5, 5 and 6
in the frozen extraction, together with the relevant definitions and
chamber/action passages of §§3.1–3.4 and Theorem 1.8. Visually checked the
original PDF page images 3, 13, 22, 26 and 27. The original files are in
`../workflow-engines/.research-workflow/artin-tits-normalisers-2509-21915-20261113/`.

Read Deligne's original introduction, the statement (2.15), and the complete
§3 construction/proof of (3.7) in the locally stored OCR extraction under
`escalation-support/deligne/`. Its introductory theorem is explicitly for
finite central real arrangements with open simplicial chambers, not only
reflection arrangements. The detailed prerequisites in Deligne §§1–2 were
not fully reconstructed in this task. This source reading identifies a
proof route; it does not supply Lean proof terms.

Read Godelle's locally stored *Parabolic subgroups of Garside groups II:
ribbons* (arXiv:0811.0751v1) introduction and the statements/proofs of
Corollary 4.18, Proposition 4.19, and Theorem 4.25 in
`escalation-support/ribbon-normaliser/godelle.txt`. Theorem 4.25(ii)
provides the broader semidirect product of the actual conjugation groupoid
by its parabolic groups and reduced ribbon groupoid; its spherical Artin
specialization is another route to the input of original Theorem 5.6.
The assumptions include the proved spherical Garside/ν-structure. Those
earlier constructions were not fully reconstructed here. The 2003 Godelle
[14] Proposition 4.4 and Van der Lek's original thesis were not directly
read in this task. Their locators above are the original paper's precise
citations, not claims of independently verified full original-source proofs.

There is currently no unconditional formal supplier for steps 1, 3–6 or 8
in the inspected package. Those are mathematical authoring obligations,
not open problems and not acceptable additional hypotheses on a declaration
advertised as the full Theorem 1.8. A structurally sound final theorem that
assumes its arrangement comparison or asphericity is useful scaffolding
only; it does not fulfill the requested theorem.

No false conclusion or counterexample to Theorem 1.8 was established by this
analysis. Source brevity and missing formal infrastructure are not evidence
that the article's theorem is false. No generated portal proof was treated
as an external proof supplier or used to certify an original-article defect.
