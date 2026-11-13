# Landmark 1: GitHub source search for actual geometric freeness

Date: 2026-11-14. Target: the standard contragredient action of an arbitrary
finite Coxeter group, an arbitrary subset `J` of its simple indices, the real
point stabilizer theorem, and freeness of the actual `N_W(W_J)/W_J` action
on the actual relative complexified complement. Crystallographic-only
results are insufficient.

## Decision

The best directly relevant new formal supplier is still TauCeti's generic
geometric-sign development. It provides the root signs and simple-reflection
permutation of positive roots needed for a local proof of the point-stabilizer
theorem. It does not already state that theorem or complexified-complement
freeness. No directly usable general point-stabilizer/chamber theorem was
found in the additional GitHub candidates inspected.

The exact upstream Sign import closure contains nine TauCeti modules,
155,476 bytes. Seven modules are already in the unchanged parent package.
Only `Geometric/RankTwo.lean` and `Geometric/Sign.lean` are new, totaling
21,094 upstream bytes. At the parent's subsequent authorization these were
prepared under the separate `landmarks/vendor/` tree. Lake's first build
attempt with their original module paths resolved dependencies through the
parent library and failed. The parent then authorized mechanical relocation:

- `ArtinLandmarkVendor.Geometric.RankTwo` has unchanged source bytes;
- `ArtinLandmarkVendor.Geometric.Sign` substitutes its one RankTwo import
  with `ArtinLandmarkVendor.Geometric.RankTwo`;
- the original exact upstream sources remain as `.lean.txt` under
  `landmarks/vendor/upstream/`;
- mathematical declaration namespaces, statements and proofs are unchanged.

`landmarks/vendor/provenance.json` records both upstream/local hashes,
paths, the exact single import patch, all old-module references and mathlib
roots. The relocated local Lean source total is 21,086 bytes. This search
does not assert that compilation, transitive axiom audit, or kernel replay
of those sources has passed. The parent owns those acceptance checks. No
parent source, configuration, review record, vendor module, or cache was
changed by this task.

## Pinned upstream/current source

A fresh `git ls-remote ... HEAD` returned the following revisions. TauCeti
has no newer remote-HEAD chamber additions beyond the previously searched
revision.

| Repository | Remote HEAD inspected |
| --- | --- |
| `TauCetiProject/TauCeti` | `62bbc0596dc3539d488232e4e924a338548ea0a9` |
| `mlyean/lean-coxeter` | `8d36c58a038cc0642a46cf5165a1b0660348f105` |
| `competemath/tengoku` | `55b33953662e4e2bc6ba91b7a55fbd048c0a9350` |
| `nickgou-nuke/info-geometry-lean` | `a392af178af1fe2bcba2ba39eb405700c6ee103c` |
| `dzackgarza/lean-categories` | `2b3f0449a1983ce19d05683fbc12133f5b7f4a1b` |
| `formalabstracts/formalabstracts` | `b0173da1af45421239d44492eeecd54bf65ee0f6` |
| `AxiomMath/CFSG` | `5437cdc31389dd9aeaa5c2a9465a4e164f8dea33` |

Search queries and raw responses, exact staged candidate files, remote-HEAD
receipts, and the Sign closure graph are under
`/tmp/artin-landmark1-search/`. Temporary staging is investigative evidence,
not an installed dependency or an assertion of mathematical acceptance.

## Direct generic supplier: exact APIs and hypotheses

In
[TauCeti/GroupTheory/Coxeter/Geometric/Sign.lean](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Geometric/Sign.lean#L140),
the ambient parameters are just

```lean
{I W : Type*} [Group W] {M : CoxeterMatrix I} (cs : CoxeterSystem M W)
```

There is no finiteness, crystallographic, positive-definiteness, or
root-pairing hypothesis. Write `ρ = cs.geometricRepresentation` and
`α i = Finsupp.single i (1 : ℝ)`. The exact useful conclusions are:

```lean
cs.geometricRepresentation_single_pos_iff (w : W) (i : I) :
  0 < ρ w (α i) ↔ ¬ cs.IsRightDescent w i

cs.geometricRepresentation_single_neg_iff (w : W) (i : I) :
  ρ w (α i) < 0 ↔ cs.IsRightDescent w i

cs.geometricRepresentation_injective : Function.Injective ρ

cs.geometricRoots : Set (I →₀ ℝ) :=
  {v | ∃ (w : W) (i : I), ρ w (α i) = v}

cs.pos_or_neg_of_mem_geometricRoots (hv : v ∈ cs.geometricRoots) :
  0 < v ∨ v < 0

cs.ne_zero_of_mem_geometricRoots (hv : v ∈ cs.geometricRoots) : v ≠ 0

cs.geometricReflection_pos_of_mem_geometricRoots
    (hv : v ∈ cs.geometricRoots) (hpos : 0 < v) (hne : v ≠ α i) :
  0 < M.geometricReflection i v

cs.bijOn_geometricReflection_geometricRoots (i : I) :
  Set.BijOn (M.geometricReflection i)
    {v | v ∈ cs.geometricRoots ∧ 0 < v ∧ v ≠ α i}
    {v | v ∈ cs.geometricRoots ∧ 0 < v ∧ v ≠ α i}
```

The strict order on `Finsupp` means coordinatewise nonnegative and nonzero
for `0 < v`; it does not mean every coordinate is strictly positive.
The file also proves invariance of `geometricRoots` under `ρ w` and
negation. Its rank-two input is a proof via explicit trigonometric
coefficients, not an assumed root-sign property.

These declaration names remain unchanged after module relocation. The
correct new import is `ArtinLandmarkVendor.Geometric.Sign`.

The new files' direct mathlib import roots are:

```text
Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
Mathlib.Data.Finsupp.Order
Mathlib.GroupTheory.Coxeter.Length
```

Their entire closure additionally uses the existing parent modules:

```text
TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle
TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
TauCeti.GroupTheory.Coxeter.Basic
TauCeti.GroupTheory.Coxeter.Dihedral
TauCeti.GroupTheory.Coxeter.Geometric.Basic
TauCeti.GroupTheory.Coxeter.Parabolic
TauCeti.GroupTheory.Coxeter.StrongExchange
```

The full fifteen distinct mathlib roots, including private imports, are
bound in the staged `sign-closure.json` and landmark vendor provenance.
Upstream uses Lean `v4.36.0-rc2` and mathlib
`e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`; the project retains mathlib
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9` and the same Lean toolchain.
Common Lean version alone does not establish compatibility.

## Closest point-stabilizer supplier: wrong hypotheses

[TauCeti/LinearAlgebra/RootSystem/FundamentalDomain.lean:188](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/LinearAlgebra/RootSystem/FundamentalDomain.lean#L188)
does contain the substantive boundary stabilizer result:

```lean
TauCeti.stabilizer_eq_closure_wallReflections
    (P : RootPairing ι R M N) (b : P.Base)
    {x : M} (hx : x ∈ TauCeti.dominantChamber P b) :
  MulAction.stabilizer P.weylGroup x =
    Subgroup.closure (TauCeti.wallReflections P b x)
```

Its actual ambient hypotheses are

```lean
[CommRing R] [AddCommGroup M] [Module R M]
[AddCommGroup N] [Module R N]
[LinearOrder R] [IsStrictOrderedRing R] [Finite ι]
[P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced]
```

`wallReflections P b x` consists of simple reflections indexed by
`i ∈ b.support` with `P.coroot' i x = 0`. The proof inducts on inversion
count. This is genuinely a proved point-stabilizer statement in its model,
but it cannot be applied to the original arbitrary finite standard Coxeter
representation without new results removing/replacing the crystallographic
root-pairing assumptions and proving the model/action comparison. In
particular finite Coxeter types `H₃`, `H₄`, and general `I₂(m)` cannot be
silently discarded.

The same source family supplies
`existsUnique_mem_orbit_inter_dominantChamber_of_finite_weylGroup`, adding
`[Finite P.weylGroup]`, and `Weyl/Chamber.lean` supplies chamber freeness
and covering under the same crystallographic/reduced conditions. These are
useful proof patterns, not direct suppliers for this milestone.

The `competemath/tengoku` copy of `FundamentalDomain.lean` was fetched at its
pinned remote HEAD and its statement/hypotheses inspected. It retains
`P.IsCrystallographic`, `P.IsReduced`, and `P.flip.IsReduced`; it provides no
escape from this restriction. It is not proposed as a dependency.

## Other GitHub candidates: actual source screen

- [mlyean/lean-coxeter](https://github.com/mlyean/lean-coxeter/tree/8d36c58a038cc0642a46cf5165a1b0660348f105):
  current HEAD is unchanged from the earlier inspected exchange/Bruhat/
  geometric-representation development. No chamber/point-stabilizer
  declaration was found in its actual Coxeter sources.
- [nickgou-nuke/info-geometry-lean, CoxeterMatsumoto/Geometric.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/a392af178af1fe2bcba2ba39eb405700c6ee103c/src/InfoGeometry/Exceptional/CFSGPort/CoxeterMatsumoto/Geometric.lean):
  inspected the source, not its presentation. It constructs the standard
  representation and exact orders of products of two simple reflections.
  Its displayed endpoints are `orderOf_simple_mul_simple`, `simple_injective`,
  and related representation formulas. It contains no point-stabilizer or
  chamber-domain theorem. It is an alternative basic representation supplier
  with no missing conclusion supplied here.
- [dzackgarza/lean-categories, WeylChambers.lean](https://github.com/dzackgarza/lean-categories/blob/2b3f0449a1983ce19d05683fbc12133f5b7f4a1b/LeanCategories/Lattices/Valued/WeylChambers.lean):
  the actual input is an integral lattice `L : FiniteProjectiveLatticeCat ℤ ℤ`
  and a chosen sheet of its Lorentzian positive cone. For example
  `convex_chamberOf` assumes `(integralSignature L).1 = 1`, a positive
  sheet vector, and a regular point, and concludes convexity of its chamber.
  Its mirror/chamber permutation and separation results do not state
  point stabilizers or simple transitivity. This is the wrong action and
  does not supply the missing theorem.
- [AxiomMath/CFSG, E6Three/StabilizerFour.lean](https://github.com/AxiomMath/CFSG/blob/5437cdc31389dd9aeaa5c2a9465a4e164f8dea33/CFSG/LieType/Chevalley/E6Three/StabilizerFour.lean):
  inspected representative actual endpoints. For instance
  `adAct_eq_self_of_triPairing` has
  `{w : WeylGroup .E6} {x : Fin Tag.E6.rank → ZMod 3}`; later conclusions
  count particular finite-field stabilizers using certificates. These do
  not specialize to an arbitrary real contragredient Coxeter system.
  Other broad CFSG search matches were not audited as a whole.
- `formalabstracts/formalabstracts/src/group_theory/sporadic_group.lean`
  defines sporadic groups using Steiner stabilizers and Coxeter
  presentations. It is a Lean 3 definitions hit, with no relevant general
  geometric stabilizer proof.
- `TauCeti/Geometry/Convex/Cone/Chamber.lean` defines positive/negative
  chambers in continuous duals associated to additive submonoids, and proves
  convexity/openness. It has no Coxeter action or point-stabilizer conclusion.

None of these screened alternatives warrants a dependency installation or
compatibility port for this milestone.

## Missing bridges and a concrete generic proof route

The Sign supplier supports the following independent local route. These are
remaining obligations, not source results claimed to have been proved here:

1. Derive finite index type from `simple_injective` and finite `W`, then finite
   roots from their explicit `W × I` parametrization. Let `δ` be the sum
   of all positive geometric roots. The positive-root permutation theorem
   gives `ρ(s_i) δ = δ - 2 α_i`. Maximize `φ(ρ(w)δ)` over finite `W`;
   comparing with simple-reflection translates puts a conjugate of `φ`
   in the closed dominant chamber. This works on the actual dual standard
   representation without crystallographic assumptions.
2. Prove the dominant-point stabilizer theorem by length descent. If
   dominant `φ` is fixed by `w ≠ 1`, choose a left descent `i` of `w`.
   The Sign theorem makes `ρ(w⁻¹)α_i` negative. Its evaluation under `φ`
   equals `φ(α_i)` by invariance, while dominance makes the former
   nonpositive and the latter nonnegative. Hence `φ(α_i)=0`, so `s_i`
   fixes `φ`. Shorten `w` and induct to show that the stabilizer is
   generated by the simple reflections whose simple-root values vanish.
   Conjugate back for arbitrary real points.
3. Connect this to root-reflection generation for the actual root kernels
   and to `W_J`. A convenient route avoids proving a complete parabolic
   root-subsystem equality: define the dominant functional `c_J` with
   simple-coordinate values zero on `J` and one outside `J`. The dominant
   stabilizer theorem gives `Stab(c_J)=W_J`. A root `β` in the span of
   `J` has `c_J(β)=0`; its conjugated simple reflection fixes `c_J` by
   the geometric root-reflection formula, hence belongs to `W_J`.
   Establishing that reflection formula and the functional/span comparison
   are explicit remaining bridges. Ordinary parabolic length theory alone
   does not assert them.
4. For a pair `(φ,ψ)` in the actual relative complement, choose a real
   `t` avoiding the finitely many cancellations for root evaluations.
   Then roots vanishing on `φ+tψ` are exactly those vanishing on both
   `φ` and `ψ`; by complement membership every such root annihilates all
   of `Θ_J`, hence lies in the span of `J`. Any element fixing the pair fixes that real
   combination, so the stabilizer theorem places it in `W_J`. Combined
   with the proved trivial action of `W_J`, this gives the desired
   freeness of the quotient group, once all action/model bridges are made.
5. Invoke the actual finite-action quotient-covering construction only after
   freeness. Pinned mathlib has `Finite.to_properlyDiscontinuousSMul` and
   `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul` under
   continuous constant action, Hausdorff locally compact total space and
   `IsCancelSMul`. An injective representation alone does not prove free
   action on points; a finite group alone only supplies proper discontinuity.

## Search mechanics and limits

Used authenticated `gh search code` with Coxeter/stabilizer, geometric
representation/chamber, fixed-point, contragredient, and root-pairing
queries, followed by actual pinned raw source and local Git-object reading.
Two requests hit GitHub's search rate limit; no negative conclusion is drawn
from them. Two exclusion queries were rejected by `gh search code`'s query
encoding and were then successfully reissued through `gh api search/code`
with the full query passed as a structured field. Their responses are retained
with the other query receipts. Search result counts and names were used to
select sources to read, not as evidence that their theorems prove the target.

No external proof is accepted from this search alone. Source suitability,
compatibility compilation, transitive axiom audit, official kernel replay,
and correspondence to the actual geometric statement remain distinct checks.
No mathematical literature error was established in these readings.
