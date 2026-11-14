# Landmark 5 / full Theorem 1.8: independent contract B

Reviewer: **GPT-6.1 Sol/high** (`gpt-6.1-sol`, reasoning effort `high`). Status: **independent preauthoring mathematical contract; no new M5 scientific source or full-Theorem-1.8 proof accepted**. Repository HEAD independently read: `22301de0ff626dbfb3d8ae66a6bccc50317de702`.

## Source reading and established context

I independently reread the original arXiv:2509.21915v3 extracted text of Theorem 1.8 and its surrounding hypotheses on PDF p.3, Theorem 6.7 and its proof/Remark 6.12 on pp.26–27, and Corollary 6.14 with its complete proof and Remark 6.15 on p.27. I also reread §3.5's distinction between the arrangement groupoid and the finite simplicial Deligne situation. This was actual extracted-text reading, not a new visual PDF inspection. I did not consult reviewer A or an A-authored M5 plan.

I reread the literal existing `Geometry`, `ArrangementTopology`, `NormalizerAction` orbit definitions, M1 covering conclusion, M3 actual-form/complement homeomorphism/tube/Čech/comparison APIs, M4 final complete sequence bundle, TauCeti's full `EilenbergMacLane/Basic.lean` and `Covering.lean`, its higher-homotopy covering proof, and mathlib's literal homotopy-group quotient/notation definitions. This reuses my complete prior independent semantic reviews of M1–M4 rather than pretending to freshly re-audit every historical proof. I also read two additional pinned upstream files by read-only `git show`: `EilenbergMacLane/HomotopyEquiv.lean` and `EilenbergMacLane/Contractible.lean`. Neither is thereby accepted as a new imported supplier; their transitive prerequisites and technical verification have not been reviewed here.

No Lean build, axiom audit, kernel replay, CI, installation or cache mutation was run. Read-only source/hash/Git commands were used. No scientific source was edited. Only this owned contract is written. A source-tree filename scan was not a comprehensive search of all mathematical statements in all repositories, and absence of a ready Lean theorem is not evidence that Deligne's mathematical theorem is false.

## Exact complete target

For every universe `I : Type u`, actual `M : CoxeterMatrix I`, `[Finite M.Group]`, arbitrary `J : Set I`, and every actual `x : Theorem18.Complement M J`, prove both actual spaces are aspherical and have the M4-identified groups as their fundamental groups. Set, without redefining any of them:

```
X = Theorem18.Complement M J
Y = Theorem18.OrbitSpace M J
p = Theorem18.orbitProjection M J
P = Artin.pureNormalizerImage M J
N = Artin.normalizerQuotient M J
Q = Artin.coxeterNormalizerQuotient M J.
```

The minimum literal final asphericity/K(π,1) declarations should provide:

```lean
TauCeti.IsAspherical (Theorem18.Complement M J) x
TauCeti.IsAspherical (Theorem18.OrbitSpace M J) (Theorem18.orbitProjection M J x)
TauCeti.IsEilenbergMacLaneSpaceOne (Artin.pureNormalizerImage M J)
  (Theorem18.Complement M J) x
TauCeti.IsEilenbergMacLaneSpaceOne (Artin.normalizerQuotient M J)
  (Theorem18.OrbitSpace M J) (Theorem18.orbitProjection M J x)
```

The full `theorem_1_8` must bundle the **complete existing M4/Theorem-6.7 commuting short exact sequences** and these two K(π,1) assertions, with witnesses given by the existing actual named M4 equivalences (their inverses supply `FundamentalGroup … ≃* P/N`). It must retain actual subgroup inclusion, the continuous orbit-projection-induced map, the canonical Artin-to-Coxeter normalizer quotient map and identity on the **same actual Q**. It must retain M4's explicit raw/normalized opposite convention and positive-label companion; no new abstract comparison or target-group automorphism may replace that map compatibility.

All actual basepoints are quantified, not only a preferred chamber point. An additional statement at arbitrary `y : Y` follows by surjectivity of p and a preimage x; it is useful to expose this and must not rely on a new nonempty-fiber premise. Noncomputable basepoint/path choices are harmless after actual existence is proved. `Finite M.Group` already implies `Finite I` using existing `finite_index`; there must be no independent finite-rank hypothesis. No proper/nonempty J, J empty, positive dimension, rank ≤1, irreducibility, crystallographic condition, or assumed Deligne/asphericity/comparison result may be a final argument.

The exact source scope includes J empty, J full, rank zero, noncrystallographic and reducible finite Coxeter systems. For full J the existing actual complement has a proved unique point and no retained forms; the actual orbit-space and group degeneracies must be handled, not excluded. A proof uniform in the dimension is preferable, with explicit zero-dimensional treatment if a supplier's simplicial-arrangement definition excludes it.

The established mathematical-model limit remains explicit: A is the actual standard braid-presented Artin group and the paper's equivalence between its initially topological Artin definition and that standard presentation is not itself newly Lean-proved. No new scope reduction to an abstract replacement space is permitted. A finite CW-model conclusion from Remark 6.15 is useful but is not a separate assertion of Theorem 1.8; do not silently add or claim it without its own proof.

## Literal higher-homotopy and K(π,1) meaning

The existing definitions are substantive:

```
TauCeti.IsAspherical X x :=
  PathConnectedSpace X ∧ ∀ n : ℕ, Subsingleton (π_ (n + 2) X x)

TauCeti.IsEilenbergMacLaneSpaceOne G X x :=
  TauCeti.IsAspherical X x ∧ Nonempty (FundamentalGroup X x ≃* G).
```

Here mathlib's `π_ k X x` is `HomotopyGroup (Fin k) X x`, the quotient of actual continuous generalized k-loops by actual based homotopies relative to the cube boundary. It is not an arbitrary groupoid vertex group, homology group or type chosen to be trivial. `Subsingleton` means the real homotopy group is trivial because it already contains the constant class. All n must be proved, not only π₂ or a finite list of examples.

The remaining hard input is therefore exactly actual higher-homotopy vanishing for X. Path connectedness is already proved. M4 then supplies the two group identifications. Full literal K(π,1) recognition does not require that a new universal-cover type first be introduced if vanishing is proved directly. If instead a universal-cover route or a claim of contractibility is used, the cover, local hypotheses, covering map, simple connectedness and actual contraction must be proved. Weak contractibility alone does not imply contractibility for arbitrary spaces: a Whitehead step requires a genuine CW/CW-type hypothesis. In this geometric setting finite-dimensional Euclidean-open geometry or a proved Salvetti homotopy type is an appropriate route to that regularity, but it must not be assumed as an unproved typeclass instance.

## The paper's inference and the precise missing bridge

Corollary 6.14 explicitly applies **Deligne's theorem for finite real central simplicial arrangements** to the actual restricted arrangement in Θ_J. The hyperplanes are linear, so centrality is appropriate; finiteness is spherical type; and the chambers are asserted to be open simplicial cones. It then uses the actual normal covering and Theorem 6.7. These are correct mathematical implications. The project must formalize this input or an equally strong route; citing the paper or naming a declaration `Deligne` does not prove it in Lean.

The existing code proves that the retained roots give proper, continuous restricted linear kernels; the distinct arrangement is their image (repeated roots do not add hyperplanes), is finite in finite W, and its real-pair complement is precisely the original X with its inherited topology. It proves genuine chamber tubes, actual open coverage, and contractibility of each tube and each realized **sign component** of a tube intersection. M3 proves a fundamental-groupoid Čech colimit and an actual interval-groupoid equivalence with Π(X), then descends to Π(Y). M2 proves actual reduced-ribbon presentations, positivity, cofinal loops/fractions and normalizer splitting. None of these existing statements itself computes πₙ(X) for n≥2 or provides a homotopy equivalence of spaces.

An equivalence `D ≌ FundamentalGroupoid X`, including the strict covering square, retains only the 1-type. It does not give `X ≃ₕ |Nerve D|`, does not show the canonical map is a weak homotopy equivalence, and does not imply X aspherical. A connected simply connected sphere is an immediate conceptual counterexample to the general inference from a trivial fundamental groupoid to contractibility. Similarly, identifying an algebraic group as a Garside group or constructing its abstract K(G,1) does not identify the homotopy type of the actual X.

## A viable full-scope route and its obligations

The most direct source-faithful route is a formally proved finite-central-simplicial arrangement theorem returning actual higher-homotopy vanishing (or a contractible actual universal cover), then instantiate it with the restricted Coxeter arrangement. Its input object must contain independently defined genuine geometric/combinatorial data, not a field that already states the desired asphericity or a homotopy equivalence to a chosen K(G,1).

1. **Actual simplicial arrangement data.** Produce a finite-dimensional real model/homeomorphism for the existing `relativeSubspace J` topology using `finite_index`; prove each retained kernel has the required codimension and identify duplicate kernels correctly. Prove the finite arrangement's chambers are simplicial cones in that actual relative space, for every chamber and every J. The existing facet labels/positive roots and chamber transports are relevant, but a label bijection alone is not a linear or topological simpliciality proof. A finite family of linear forms or a central arrangement is not automatically simplicial. If a supplier requires essentiality, establish it from the surviving simple coordinates or rigorously split lineality as a contractible factor; do not add essentiality to the final theorem. Zero dimension and empty arrangements need matching definitions.
2. **A genuine homotopy-type comparison.** Build a Salvetti/Deligne topological or simplicial model and prove a homotopy equivalence, weak equivalence sufficient for all homotopy groups, deformation retraction, or other direct comparison with actual X. A numerable good-cover/Čech homotopy-descent construction could reuse M3's explicit contractions, but the existing categorical colimit of fundamental groupoids is insufficient. The comparison must preserve the full higher coherences, not just paths and their relations.
3. **Contractibility/asphericity of the model.** Prove the universal-cover/Deligne complex contracts, or that all its higher homotopy groups vanish. A Garside route may use actual cancellative positive categories, common multiples, finite simple divisors, normal forms and an appropriate directed/filtered order complex. Every required lattice/Ore/fraction/termination condition must be proved for the exact category used. The existing M2 chosen pair-LCM relations and cofinal fractions are useful algebra, but their universal presentation alone is not a proof of contractibility of a realization. If Quillen-A, a nerve theorem, localization/classifying-space theorem or Whitehead is used, its actual topological conclusion and complete hypotheses must be supplied and checked.
4. **Transfer to actual X.** Use the proved homotopy comparison or actual-cover contraction to obtain `∀ n, Subsingleton (π_ (n+2) X x0)` for an actual point x0, then all x via actual path/basepoint change. A proof at the abstract model alone, with no actual-space bridge, leaves M5 incomplete.
5. **Actual quotient and full bundle.** Transfer higher homotopy through the M1 actual cover X→Y; combine with actual path connectedness and the M4 equivalences to prove both K(π,1) conclusions and retain the full commuting sequence bundle.

An alternate direct proof using a refined component-sensitive Čech model and M2 positive-fraction algebra is mathematically viable if steps 2–4 are actually established; it need not first prove the source's literal adjacent-gallery dictionary. It must not market an unproved dictionary or reuse an interval presentation as though groupoid presentation alone implied a classifying-space comparison.

### Concrete good-cover pitfall

The current chamber tubes are **not generally a good cover with contractible whole nonempty intersections**. The proved objects are contractible realized pieces `tubeIntersectionPiece F ρ`, and these pieces are exactly intersection components. In the one-form rank-one case the two opposite chamber tubes intersect where the real coordinate is nonzero: two components, not one contractible intersection. The nerve of only the two chamber indices would discard the resulting loop. Thus one cannot apply the ordinary good-cover nerve theorem directly to `actualChamberTubeOpen` using only the individual tube and component contractions.

A valid reuse must refine to a genuine good cover or use the full component-sensitive Čech simplicial object/homotopy colimit, prove the required functorial face/degeneracy/component maps and actual homotopy descent (with numerability/paracompactness/local finiteness as required), and then prove the resulting model aspherical. Contractible finite-intersection components are valuable input, not a shortcut around these missing global statements.

## Exact covering transfer already available

The literal supplier theorem

```
IsCoveringMap.isAspherical
  (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
  (he : p e = y) (hX : TauCeti.IsAspherical X e)
```

returns `TauCeti.IsAspherical Y y`. It is proved using the genuine equivalences on all π_(n+2). For actual p, `Landmark1.isQuotientCoveringMap_orbitProjection M J` supplies both `isCoveringMap` and `surjective`, so with e=x and he=rfl it applies without any new geometric or group hypothesis. It needs **no** simple connectedness of X and **no** assumption that its fundamental group is trivial.

Afterward the literal K(P,1)/K(N,1) witnesses can use `(Sequence4.pureFundamentalGroupEquiv M J x).symm` and `(Sequence4.normalizerFundamentalGroupEquiv M J x).symm`. Their inverses have the exact orientation required by the K(π,1) definition. M4's ordinary mathlib multiplication and normalized endpoint map remain unchanged; its genuine FG-op companion already explains positive path traversal. There is no reason to alter Q, its monodromy map or its basepoint conventions for M5.

Do **not** use `IsQuotientCoveringMap.isEilenbergMacLaneSpaceOne` on this cover and conclude K(Q,1): that supplier explicitly requires `[SimplyConnectedSpace X]`, generally false here, and the correct orbit fundamental group is N, not Q. Likewise, the separately inspected upstream `IsCoveringMap.contractibleSpace_of_isAspherical` assumes the base already aspherical (and actual CW/T2/simple-connected-cover hypotheses); it cannot serve as the missing proof of asphericity without circularity. Upstream `IsAspherical.of_homotopyEquiv` is a valid transfer once both an actual homotopy equivalence and asphericity on one side are proved; it constructs neither.

## Supplier/provenance and final acceptance conditions

The newly inspected context is from the already recorded repository `https://github.com/TauCetiProject/TauCeti`, immutable SHA `62bbc0596dc3539d488232e4e924a338548ea0a9`. The additional source-only reads were exactly `TauCeti/AlgebraicTopology/EilenbergMacLane/Contractible.lean` and `.../HomotopyEquiv.lean`; these were inspected as conditional candidate tools, not imported or compiled by me. Mathlib's homotopy-group definitions are the existing pinned dependency. No new external theorem, repository or proof dependency was silently adopted. Any future newly used source and its exact theorem/proof must join the central provenance ledger and receive source/statement/axiom/replay review at its frozen version.

For final acceptance I must inspect every actual final definition/statement/type context and critical proof body, the actual geometric simpliciality and global homotopy bridge, genuine higher-dimensional contraction/vanishing, all final hypotheses and degeneracies, and the literal full theorem bundle. Bind exact source/config/provider/context/inventory/tooling hashes and inspect real complete physical/canonical declaration coverage, allowed transitive axioms, builds and exact-module kernel replays. A conditional recognition theorem, assumed-Deligne field, abstract K(G,1), verified groupoid equivalence, or passing technical badge cannot close M5 by itself.

No M5 acceptance and no full-Theorem-1.8 acceptance is issued by this contract. The remaining mathematical conclusions are true targets; the identified risk is an unsupported formal inference or missing proved bridge, not a counterexample to the paper.
