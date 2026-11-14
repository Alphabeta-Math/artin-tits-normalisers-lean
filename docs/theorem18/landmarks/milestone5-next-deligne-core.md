# Landmark 5: the next Deligne combinatorial core

This investigation uses accepted baseline `c779c15d6c6cc4ad5b2c50ea841c89caedba660d`. It edits no scientific source. The [targeted inventory](../../provenance/searches/m5-next-core-inventory.json) records exact source hashes, declarations, import closures, pins and reading/execution limits. This is a proposed construction and mathematical dependency analysis, not a new proof acceptance or an asphericity certificate.

The next small algebraic step has a concrete proof from M2: **simultaneous elementary prefixes have an actual maximal face prefix, with a positive reduced tail of strictly smaller degree**. The parent assigned its formalization to `ArtinHomotopy/FacePrefixes.lean`; its author now reports a warning-free successful build. The geometric step identifies this prefix's actual lifted endpoint with the opposite chamber in the residue of the corresponding actual face; its author also now reports a successful direct check of that statement in `FaceResidues.lean`, while the final target build/residue-divisor extension was being completed. These build reports are not independent acceptance by this investigation. Neither prerequisite yet contracts the actual lifted cover nerve.

## 1. Actual face prefixes: exact statement and proof

Use `Ribbon2`'s actual Artin group, positive submonoid and actual positive reduced ribbons, with arbitrary `I : Type u`, `M : CoxeterMatrix I`, `[Finite M.Group]`. There is no separate finite-rank, crystallographic, irreducible or nonempty-parabolic hypothesis. Write

```text
P = actualPositiveParabolic M univ
u ≼ v  ↔  ∃q∈P, v = u*q
η(X,T) = Δ_(X.indices)^(-1) * Δ_(X.indices ∪ T)
Z(X,T).indices = parabolicTwistImage M (X.indices ∪ T) X.indices.
```

The now implemented `Homotopy5.RibbonPrefix`, `facePrefix` and `facePrefixTarget` express these actual definitions. For positive `p`,

```text
η(X,T) ≼ p  ↔  ∀a∈T, μ_(X.indices,a) ≼ p.
```

For `hp : PositiveReducedArrow M X Y p`, this divisibility has the stronger typed consequence

```lean
∃ q : Artin.Group M,
  PositiveReducedArrow M (facePrefixTarget M X T) Y q ∧
  p = facePrefix M X T * q
```

No desired decomposition is assumed in a structure field. The proof is short:

1. Existing `parabolicDelta_ratio_positive`, `parabolicDelta_ratio_isRibbon`, `parabolicDelta_ratio_leftReduced`, and `positive_leftReduced_ribbon_generated` give the genuine positive arrow `η : X → Z`.
2. If every specified `μ_a` divides `p`, every generator indexed by `X.indices ∪ T` divides `Δ_X*p`. For indices in X this follows from divisibility of `Δ_X`. For `a∈T`, expand `p=μ_a*q`; then `Δ_X*p=Δ_(insert a X)*q`.
3. Apply accepted `parabolicDelta_left_lcm` to obtain `Δ_X*p=Δ_(X∪T)*q` with q positive. Cancel in the actual group to get `p=η*q`.
4. `η⁻¹*p=q` is a ribbon from Z to Y. If a Z-generator divided q on the left, `IsRibbon.generator_reverse` would transport it across η to an X-generator dividing p, contradicting p's actual left reduction. Existing positive-ribbon generation applies to q.
5. Conversely `parabolicDelta_ratio_elementary_prefix` makes each `μ_a` a prefix of η; compose the positive quotient witnesses.

This generalizes the accepted proofs of `pairRibbonLcm_is_left_lcm` and `positive_ribbon_elementary_tail`, rather than invoking a new Garside assumption. The existing local import boundary is `ArtinRibbons.RibbonLcm`, with 15 project modules in its local import closure; its already accepted external frontier is recorded in the inventory.

Define the actual outside descent set

```text
D_X(p) = {a | a∉X.indices ∧ μ_(X.indices,a) ≼ p}.
```

Then `D_X(η(X,T)) = T \ X.indices`: a purported outside atom b dividing η makes generator b divide `Δ_(X∪T)`, and `generator_leftDivides_parabolicDelta_iff` forces `b∈X∪T`. In particular normalized face types `T⊆X.indicesᶜ` are recovered exactly. Taking `T=D_X(p)` gives the greatest **face** prefix of p. A nonidentity positive generated p has an outside first atom; hence this face type is nonempty, η has positive actual exponent degree, and its actual positive tail has strictly smaller degree. The reported exports include `maximalFacePrefix_prefix`, `maximalFacePrefix_greatest`, `maximalFacePrefix_tail_degree_lt`.

This is a maximal **face** prefix, not a maximal arbitrary **simple** prefix. In ordinary type A₂, the simple word `st` has initial atom descent set `{s}`; its maximal face prefix is s, while its maximal simple prefix is st. Deligne 1.19(iii) is the stronger simple-prefix assertion. This distinction must remain explicit.

## 2. A short arbitrary ribbon-lcm closure proof

The parent's additional proof route is mathematically sound and avoids a recursive word-completion detour. The parent reports that `RibbonLattice.lean` has compiled; this investigation assessed the mathematical route and selected source sections, without independently replaying that new module.

Let p and q be positive reduced ribbons with common source X, and let l be their **ambient positive-monoid left lcm**, supplied by accepted `positive_lcm_left`. For every `i∈X.indices`, both p and q divide `σ_i*l`: if `l=p*a`, the generator transport relation gives `σ_i*l=p*σ_j*a`; similarly for q. The ambient lcm property therefore gives

```text
σ_i*l = l*t_i,   t_i positive.
```

Actual exponent degree gives `degree t_i=1`, so each t_i is an actual generator. Let U be the set of all these transported generator labels. Induction over the two positive subgroup closures proves **equality** `l⁻¹ P_X l=P_U`, not merely an inclusion. No rank/cardinality shortcut is needed. Cofinal positive loop powers provide a common positive reduced-ribbon upper bound r for p and q. Since `l≼r`, any forbidden X-generator prefix of l would also prefix r. Thus l is X-left-reduced; positive-ribbon generation yields an actual arrow `X→U`. Both positive tails have their genuine transported endpoints by the same tail argument as above.

The transported generator set U need not be assumed to have a geometric chamber beforehand. Its reduced ribbon supplies the association, and M3's proved lifting construction supplies the actual endpoint when a source chamber is chosen. Closure under such lcms is stronger than the pair-of-atoms result and useful for simple intervals. It does **not** by itself identify a classifying space with the complement.

## 3. The next actual geometric lemma

There are two small parts. The geometry author reports them directly checked in the new `FaceResidues.lean`; the exact mathematical content remains recorded here because it is a required bridge, not an assumption.

For a finite real form family ℓ, define incidence by the actual condition `z ∈ closure C.region`. Prove its sign characterization: every form nonzero at z has C's sign there. One direction follows by continuity. For the converse, move from z toward an actual point of C along `z+t*c`, `t>0`; all forms are then strictly on C's side and the points converge to z. This uses the real vector topology, not an asphericity premise.

Define the actual opposite chamber `-C` by negating a realizing point and all its signs. Existing `faceChamber ℓ z (-C)` preserves z's nonzero signs and reverses C's signs on forms vanishing at z. Thus, assuming C incident to z, the following is a precise generic target:

```text
z ∈ closure D.region
  ↔ ChamberBetween C D (faceChamber ℓ z (-C)).
```

The proof is the two-case sign test, using `faceChamber_signs_zero` and `faceChamber_signs_nonzero`. This identifies the actual residue with a geometric chamber interval.

Now take an actual raw label `L=(w,X)` for the actual J-arrangement, `T⊆I\X`, and `K=X∪T`. The accepted `rawFacetCoordinates L` is an actual continuous linear equivalence

```lean
relativeSubspace J ≃L[ℝ] ({i : I // i ∉ X} → ℝ).
```

Choose an actual point z in its coordinate face: coordinates indexed by T vanish; all other off-X coordinates are strictly positive. For the first proof it suffices to use the explicit point obtained by pulling back the 0/1 indicator vector. The required new statement is:

```text
the actual fiberTarget from C=actualChamberOfRawLabel L
under π(η(X,T)) equals faceChamber (actualForms M J) z (-C).
```

Its existing endpoint API is `Chamber3.fiberTarget`; the transporter hypothesis comes from η's proved `IsRibbon` and Coxeter projection. This is an assertion about actual chamber signs and actual root evaluations, not an assumed identification of two abstract objects.

The essential root dictionary is concrete. Transport a retained root by w⁻¹. Its evaluation at z vanishes exactly when its support lies in K. For a positive root, all coefficients are nonnegative; its pairing with z is a sum of nonnegative terms, whose coefficients outside K are multiplied by positive coordinates. Negative roots reduce to this by negation. Retention excludes roots supported entirely in X. The inversion roots of the parabolic longest element are exactly the roots of its parabolic subsystem. Consequently `π(η)⁻¹=w_K*w_X` flips precisely the retained roots vanishing on this face, and preserves the other chamber signs. Existing `rawFacet_sign_iff`, the geometric sign/root support APIs, and the actual coordinate evaluations should supply this calculation.

This statement includes the singleton case, which identifies μ-transport with crossing the actual wall, and the full outside set, which identifies the global ratio δ_X with transport from C to −C. The latter is particularly useful for the next simple-prefix argument.

## 4. Greatest simple prefix by bounded degree

A still shorter construction avoids finite-divisor enumeration. The separately assigned `RibbonGcd.lean` now has an author-reported successful warning-free build; this investigation independently checked the mathematical argument, not its full Lean elaboration or kernel replay.

For two positive ribbons p,q with common source X, identity is a common ribbon prefix. Degrees of all such prefixes are nonnegative and bounded by `degree p`. Choose a common prefix d of maximal attained natural degree (`Nat.findGreatest` suffices). For any other common prefix e, their actual ribbon lcm l is another common prefix, by the ambient lcm universal property applied to p and q. Since `d≼l`, its positive cofactor has nonnegative degree; maximality forces degree zero and hence cofactor one. Thus `l=d`, so `e≼d`. Genuine ribbon tails are supplied by the proved prefix-tail lemma.

Apply this to p and `δ_X=Δ_X⁻¹Δ_S`. The resulting head is the greatest actual generated prefix dividing δ_X. A nonidentity p has an outside elementary prefix μ, which also divides δ_X, so the head is nonidentity and the positive tail strictly decreases degree. `Homotopy5.SimpleRibbon` is defined by genuine positive generation plus divisibility by δ_X. This is explicit algebraic data, not an assumed geometric comparison. Reported exports include `greatest_simple_ribbon_prefix` and `greatest_simple_ribbon_prefix_with_tail`.

The remaining bridge between this simple predicate and actual chamber pairs may be shorter than the full local-face calculation of section3. For any actual pair C,D, put `d=relativeTransport C D`. Source-X inverse minimality gives `length(w_X*d)=length(w_X)+length(d)`. Thus `Δ_X*positiveLift(d)=positiveLift(w_X*d)` is a global simple divisor of Δ_S. Cancel Δ_X to get `positiveLift(d)≼δ_X`. Conversely any generated divisor of δ_X is an ambient simple factor of Δ_S; the accepted simple-factor and minimal-transporter results identify its actual lift from C with `intervalPositive C D` for its actual endpoint D. The exact formal bridge is still a theorem to author, not supplied as a premise.

After this bridge, the actual simple arrows dividing p form one principal geometric weak interval `[C,H(p)]`, by M3's between/length equivalence. This is the relative form of Deligne1.19(iii). Localizing the bound to the face opposite δ_F gives a greatest **simple** residue prefix. A greatest arbitrary positive residue prefix is a further statement: prove local support/lcm closure and local cofinality, or a precise greedy compatibility lemma. That stronger projection is Deligne1.24; it must not be silently identified with the simple result.

## 5. What OAI's contraction actually uses

All names here are at openai/math `4eaee87548250b2682affda7d05d947c05554bae`, namespace `OAI.HarmonicArtin`. The earlier broad search freshly checked main at this same pin; this investigation made no new network query. It inspected the actual cached immutable proofs, not just filenames.

`PositiveDescentSet.lean` uses **right suffixes** and proves `positive_descent_fundamental`: the parabolic longest lift for the complete atom-suffix set divides the positive element on the right. `NoncriticalPositiveCell.lean` then toggles the first such atom in a cell's spherical face type. It proves that the partner exists, has the same top vertex, is distinct and incident, and that the toggle is involutive. `PositiveCellPoset[2].lean` orders cells by top degree and a matching-compatible face key.

`PositiveEarlierLinkUpper.lean` handles two genuinely different links:

- If the chosen atom is absent from the face type, the earlier link has a top element given by the matching partner, so its nerve contracts.
- If it is present, the earlier link is the cell's proper boundary with the matched facet removed. `PositiveUpperBoundaryRestriction.lean` identifies this punctured boundary with one in an actual smaller parabolic **ordinary** Coxeter cell. `PositiveUpperBoundaryRank.lean` proves contractibility by induction on face rank and then concludes `positiveCellPoset_contractible`.

Thus ordinary OAI contraction is not an automatic consequence of Ore fractions or directedness. Its ordinary positive-cell poset depends on spherical standard Coxeter types and their actual face incidences. The relative version needs those incidences/localizations proved for the actual restricted arrangement; one cannot instantiate its matrix with a new name. In particular, the localization at a relative face of type `K=X∪T` is the **relative** arrangement for the parabolic system `(W_K,X)`, not in general the ordinary Coxeter arrangement of a matrix on T.

The generic part is separable. `Harmonic/Initial.lean` proves, for arbitrary universe `P : Type u`, partial order, well-founded total earlier relation r, unique earliest c, and actual contractible earlier links,

```lean
orderWeights_contractible_of_earlier_links ... :
  ContractibleSpace (OrderWeights P)
```

Its source closure is 23 OAI modules. It constructs coherent actual contractions by insertion and bounded chains/Zorn. It assumes no desired final contraction, but **the earlier-link contractions remain hypotheses that callers must prove**. The matching endpoint's ordinary source closure is 402 modules; the larger spherical lifted-space endpoint is 600. These counts are not compile or axiom-audit acceptance. The matching's rank-induction endpoint is stated for `S : Type` (universe zero); the generic Initial theorem is universe-polymorphic. Any proposed reuse must preserve the literal scopes.

`DirectedCoverSequence.lean` has a 105-module OAI closure and additionally requires downward-closed pieces, actual piece contractions, and a bounded strict rank. Existing ribbon cofinal fractions can supply an exhaustion once the correct cell poset is built. They do not supply its link contractions or comparison with the actual space.

A smaller additional generic candidate is `Realizations/FiniteWeightsCompact.lean` (12 OAI modules). Its `compact_map_finite_carrier`, for any poset and arbitrary universe/compact source, factors an actual continuous map into `OrderWeights P` through `OrderWeights A` for some finite actual vertex set A. The proof uses the true realization topology and a proved closed embedding of finite weighted subposets. Its full file body was read; no new supplier compilation, axiom audit or replay is claimed here.

## 6. A lighter incoming simple-chain complex

The new greatest-simple-prefix result suggests a smaller contraction proof than copying the ordinary face-cell matching. Use incoming signed arrows `p:C→C₀` in the actual interval groupoid, for one fixed actual chamber C₀. Define positivity by their actual M3 ribbon values and prove its equivalence to positive pair generation. Define the positive order by `p≤q` when `p=r*q` for an actual positive arrow `r:C→D`. Composition order here means first r, then q. Positive exponent degree strictly decreases from p to q unless r is identity.

A **simple chain** is a finite nonempty increasing chain of such vertices whose entire quotient from first to last is simple. This last restriction is essential: taking the full nerve of the positive divisibility poset would give a different realization. The signed/positive simple-chain complexes are explicit simplicial objects defined from actual arrows and the actual δ-prefix predicate, with no contraction or comparison conclusions as fields. A convenient weighted definition avoids choosing endpoints: take `w : OrderWeights P` such that every ordered pair of support vertices has a simple connecting arrow. The condition is hereditary under shrinking support; for a finite chain it is equivalent to simplicity of the total connecting arrow. For finite-stage deletion, adjoining q_H is checked pairwise using the simple factors of H(p).

For a new nonidentity positive incoming vertex p, order the positive region by increasing `degree p`. The older vertices adjacent to p correspond precisely to its nonidentity simple prefixes r, by `p=r*q`. Their chains give its earlier link. The greatest simple prefix H(p) is nonidentity and yields a cone vertex `q_H` in this link: every simple prefix r divides H(p), so every such chain can be joined to `q_H` while its whole quotient remains simple. This is a conical link, not the punctured-cell boundary required by the heavier face matching.

The first genuine contraction target is therefore:

```text
for every non-root positive incoming vertex p,
the earlier simplicial link in the SIMPLE-CHAIN complex is a cone,
with cone vertex the positive tail of greatestSimplePrefix(p).
```

One must prove the displayed link identification and the cone condition from actual prefix/tail equations. An abstract simplicial contraction/attachment lemma can then give positive-region contractibility, or construct the homotopy explicitly by transferring the new vertex's barycentric weight to its cone vertex. Distinct new vertices of the same positive degree cannot occur in one simplex, so such replacements agree on the older overlap. Continuity must be proved in the actual realization topology. OAI's `Initial` theorem concerns an order complex: to use it, pass to the actual finite-simplex face poset and prove the corresponding earlier-link statements; do not apply it directly to a restricted collection of chains as though it were the entire poset nerve.

A weaker conclusion than global contractibility may substantially reduce the topology burden. Define the simple-chain weighted space as the **subspace** of actual `OrderWeights P` whose support has simple total quotient, where P is the actual signed incoming positive-order poset. Apply `compact_map_finite_carrier` to a compact map composed with this actual subspace inclusion. This gives a finite vertex carrier. Clear its denominators simultaneously and close that finite positive set under the deterministic greatest-simple-prefix tail. Strict degree decrease makes each ancestry finite, so the resulting set remains finite and contains the root. In its induced simple-chain complex, remove maximal-degree vertices successively. Transfer a removed vertex's weight linearly to its cone vertex q_H; all other weights stay fixed. The support remains a permitted simple chain, and the old subcomplex stays fixed. Continuity can be proved in finite coordinate weights using the finite closed-embedding theorem. This contracts a genuine finite stage and nullhomotopes the original compact map. Thus higher vanishing may be obtained **without** constructing a coherent infinite contraction or invoking CW/Whitehead. The subspace/finite-stage topology and all restriction/transfer maps still need actual proofs.

The accepted fraction theorem says every signed incoming vertex becomes positive after right multiplication by a sufficiently large power of the fixed target's cofinal loop. For simplices, positivity of the first vertex alone does not automatically make all its tails positive from the algebraic equality; choose one exponent for the finite set of vertices. Simple-quotient relations are unchanged by this simultaneous right translation. Prove compatibility of subcomplex inclusions and exhaustion. Then compact maps can factor into positive translated regions, or an appropriate realization exhaustion theorem can be used. Bare vertex directedness does not establish these topological facts.

Use actual exponent degree, not atomic-word count. Different μ labels can have different positive Artin degrees. No equal atomic-word length or unproved standard-path uniqueness is assumed by this construction.

If finite packets of incoming vertices need canonical joins, remember that their arrows have **common target**, whereas the currently discussed lcm/gcd theorem is for common source. A mirrored right/suffix ribbon lattice, or a proved independence from a chosen common lower bound, is needed. It is not legitimate simply to reuse the common-source theorem on these objects. The common-target mirror has the same generator-transport proof; left common cofinal upper bounds follow from `p*q=c_X^n` and naturality, which imply `q*p=c_Y^n` by cancellation.

## 7. Actual tube intervals and an explicit geometric carrier

The parent reports a successful build of `TubeIntervals.lean`; I read its full source. For each actual complement point p, its proved tube cover chooses Cw. The definitions

```text
A(p)=faceChamber(real p,Cw)
B(p)=faceChamber(-real p,Cw)
```

satisfy the actual theorem

```text
p∈tubeSet D  ↔  ChamberBetween A(p) D B(p).
```

This interval agrees on forms vanishing at `real p`, whereas the incident-face interval of section3 agrees on forms **nonvanishing** at the face point. These are different, useful intervals. In particular, any family of tubes meeting at p has one actual simple interval bound. This uses sign geometry, not simpliciality or asphericity. Choosing one chamber tube for every nonempty convex cover member is also possible using the earlier face-projection argument; its formal refinement lemma remains separate.

A promising explicit carrier for the simple-chain realization has a concrete scalar proof. Let `C_i` be the actual chambers of a simple chain, `c_i` actual chosen points of those chambers, `h_i` globally defined heights, and `t_i≥0`, `Σt_i=1`, its simplex coordinates. Set

```text
hbar = Σ_i t_i*h_i
x = Σ_i t_i • c_i
y = Σ_i t_i*(h_i-hbar) • c_i.
```

The proposed map sends t to the literal real pair `(x,y)`. For incoming vertices ordered as above, the correct height is **`h(p)=-degree(p)`**: heights increase along an actual positive arrow from its source chamber to its later chamber. Using positive incoming degree would reverse the positive arc already in rank one. Heights must be assigned globally to vertices, not independently normalized in each simplex.

Here are independently authorable typed obligations, none assumed completed:

1. **Geodesic subchains.** A simple chain of actual arrows gives `ChamberBetween C_i C_j C_k` for every `i≤j≤k`. Use that every factor of a total simple product is simple, the actual minimal-transporter correspondence, and M3's between/length theorem. Knowing only that every C_i is between the two fixed endpoints is insufficient: when endpoint signs differ, that weaker condition permits repeated sign changes.
2. **One-change scalar covariance.** For any actual form let `a_i=ℓ(c_i)`, which is nonzero. The subtriple condition makes this sign sequence change at most once. If `Σt_i*a_i=0`, both signs have positive weight. With a threshold k between the earlier and later sign heights, `Σt_i*h_i*a_i=Σt_i*(h_i-k)*a_i` has the later sign, strictly. Therefore `ℓ(y)≠0`, with the final chamber's sign. The height hypothesis can allow degeneracies: heights must be strictly separated whenever signs differ; repeated identical vertices have equal heights.
3. **Actual complement and carrier.** The previous scalar result proves `(x,y)∈complexComplementSet ℓ` and `p(t)∈tubeSet C_last`. If all supported chamber evaluations have one sign, `ℓ(x)≠0` already. Thus no zero-form pair is introduced, including on simplex boundaries.
4. **Continuity and simplicial compatibility.** The formulas are finite sums/products of continuous scalar/linear maps. Inserting a zero weight proves face compatibility. Combining repeated equal vertices combines equal points and equal heights, proving degeneracy compatibility by finite-sum reindexing. These actual identities must be proved before descending to the realization.
5. **Deck invariance.** Right multiplication of all signed incoming arrows by a fixed target loop leaves source chambers unchanged and adds one constant to all heights. The centered formula is invariant because `Σt_i=1`. This gives an actual invariant map, not a covering or homotopy equivalence by definition.

The scalar sign calculation is sound, including unequal magnitudes of the evaluations: its proof uses the cancellation `Σt_i*a_i=0` and strict separation of heights, not equality of those magnitudes. In rank zero there are no forms to check; the real-pair map is still defined. At a vertex, y=0 and x is the actual regular chamber point.

To obtain the needed higher-topology conclusion, construct a comparison from the actual convex-cover nerve (or its actual universal lifted nerve) into this simple-chain model, and prove that composing with the carrier is homotopic to the existing actual nerve-to-complement map in the needed direction. The tube-interval theorem supplies interval bounds for each actual overlap; lattice joins and subdivision can turn finite packets into chains. All choices, nested-face compatibility and coherence/homotopy must be proved. A pointwise interval bound alone is not such a comparison, and neither the fundamental-groupoid equivalence nor the new actual carrier alone is asphericity.

## 8. The heavier face-cell/original Deligne routes remain alternatives

If the simple-chain route cannot establish the geometric comparison, `FacePrefixes` also supports an incoming **face-cell** construction. Represent a cell by an incoming top vertex p, a normalized outside face type T, and the actual divisibility `η(C,T)≼p`. Its finite actual vertex set consists of the positive simple-prefix removals bounded by η. Section3 identifies these with chambers incident to the actual coordinate face. Define incidence by these vertex sets and prove recovery of top/type and rank; then toggle a chosen atom of D_C(p) in T. The absent-atom earlier link should have the matching partner as top. The present-atom case needs the actual punctured-boundary/localization theorem and rank induction, as in the ordinary OAI proof. These are genuine new incidence/contraction obligations.

Deligne's original chamber-building alternative has a separate exact bottleneck: 1.24 gives residue-prefix projection; 2.6 gives the unique minimal positive chamber over each lifted face; **2.9.2** proves that a face shared by two chambers at the new height is already present at a lower height. Only then can 2.9.1 collapse each new simplex, or pair an entire-boundary attachment with its capped ball. `FacePrefixes` alone does not prove this shared-face assertion. Signed exhaustion2.14–2.15 also needs the actual embeddings and face identifications.

No ready relative version of this core was located in the previously checked GitHub source; no worldwide absence is claimed. The ordinary proofs provide strategies and generic helpers, not an instantiated relative theorem. The original statements were read in archived extracted text, with exact PDF/text hashes in the inventory; this turn did not reread the whole original visually. No new scientific Lean compilation, transitive axiom audit or kernel replay was run by this investigation. Other authors' new builds are explicitly their reports, subject to the project's independent reviews.

Rank zero and full J remain included. There is one actual chamber and no outside atom; only the root positive region survives and no noncritical contraction case should be invoked. Arbitrary reducible and noncrystallographic finite-W systems remain in scope. No final theorem may acquire an extra nonzero-rank/nonempty-parabolic hypothesis or replace the restricted arrangement by an ordinary Coxeter matrix.
