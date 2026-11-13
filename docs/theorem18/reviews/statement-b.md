# Theorem 1.8: independent semantic contract B

Reviewer: **GPT-6.1 Sol/high**. Status: **preliminary statement contract; no proposed Theorem 1.8 implementation is accepted yet**. Scope is the full geometric theorem, including actual fundamental groups, asphericity, and compatibility of the geometric and algebraic exact sequences. The completed algebraic Lemma 2.8 records remain unchanged. I have not read reviewer A's work, edited proof sources, installed dependencies, fetched caches, or run a Lean build in this task.

## Source reading and interpretation

I read the dedicated repository's `README.md`. No repository `AGENTS.md` or `CLAUDE.md` was present at the inspected repository/ancestor locations. For the mathematics I independently reread the original article through its extracted PDF text at `/home/lazyinspirit/Projects/workflow-engines/.research-workflow/artin-tits-normalisers-2509-21915-20261113/article.txt`:

- PDF p. 3: Theorem 1.8, equations (1.5)–(1.7), and its stated relation to the Section 6 proof.
- PDF pp. 4–5: standard geometric representation, dual representation, root hyperplanes, and the topological Artin/pure-group models followed by the presentation statement.
- PDF p. 7: the ordinary covering-space hypotheses and the article's composition conventions; Section 3.1's definitions of `Θ_J`, `Cone(J)`, and the restricted hyperplanes.
- PDF pp. 12–14: Lemmas 3.23/3.24, the actual action, complement (3.26), normal covering and exact sequence (3.28), and the Deligne groupoid construction in Section 3.5.
- PDF pp. 23–27: the Section 6 comparison chain through Lemmas 6.1/6.2, Proposition 6.3, Corollary 6.4, Lemma 6.6, Theorem 6.7, Remark 6.12, Corollary 6.14, and Remark 6.15.

This is original-source reading through extracted text, not a new rendered-PDF inspection. I did not read the full article anew, Deligne's original proof, Van der Lek's thesis, or the other cited external full texts. Their exact hypotheses/proofs must be separately verified before an imported formal supplier is accepted. An article's citation is evidence of the intended proof input, not a Lean proof of that input.

Theorem 1.8 assumes the **entire Coxeter group `W` is finite**, and takes **every basepoint `x∈X_J^ℂ`**. Theorem 6.7 uses the equivalent phrase “spherical Coxeter diagram” and arbitrary `J`. Corollary 6.14 supplies the asphericity part. Finiteness of `W_J` alone, finite rank alone, or a merely locally finite arrangement does not match this theorem's assumptions. Conversely, no irreducibility, crystallographic/root-lattice condition, nonempty `J`, proper `J`, or chosen chamber basepoint belongs among its mathematical hypotheses.

## Faithful input objects

Let `I` index the simple generators, let `M : CoxeterMatrix I`, and suppose its actual Coxeter group `W=M.Group` is finite. Let `J:Set I`. Retain the actual standard Artin braid presentation `A=ArtinNormalisers.Artin.Group M`, its actual canonical projection `π:A→*W`, the generated subgroups `A_J` and `W_J`, and `P=ker π` already used in the completed algebraic lemma. Define

`Q := N_W(W_J)/W_J`, `E := N_A(A_J)/A_J`,

and `K := image((P∩N_A(A_J)) → E)` under the actual quotient projection. The map `i:K→*E` is subgroup inclusion and `p:E→*Q` is the actual induced canonical projection, not any convenient abstract surjection.

The geometry must be fixed independently of those desired fundamental groups:

1. `V=⊕_{i∈I} ℝ α_i` is the standard real geometric representation, with its actual Coxeter action and root set `Φ={w·α_i}`. The article's `Θ` is the **dual/contragredient** representation, with `(w·φ)(v)=φ(w⁻¹·v)`. In finite rank the algebraic dual may be given its ordinary finite-dimensional real vector-space topology; a continuous-dual model is equivalent only after the finite-dimensional bridge is established.
2. `Θ_J={φ | ∀j∈J, φ(α_j)=0}` is a subspace of that dual. It is not the span of the selected roots, an unrelated coordinate space, or a quotient chosen from `K` or `E`. Using coordinates `I→ℝ` is acceptable through the actual dual basis identification and actual contragredient action.
3. `H_α={φ | φ(α)=0}`. The restricted arrangement is the set of **proper** restrictions `H_α∩Θ_J` for roots with `Θ_J ⊈ H_α`. Hyperplanes containing the whole of `Θ_J` are omitted. Retaining them would remove the whole space in the complexified complement. Repeated restricted hyperplanes may be deduplicated; distinct roots can give the same restricted hyperplane, and no injectivity assumption is permitted here.
4. The exact source formula is

   `X := ((Cone(J)° × Cone(J)°) \ ⋃_{H∈H_J} H×H)`.

   Under the finite-type hypothesis the source specializes this to

   `X = (Θ_J×Θ_J) \ ⋃_{H∈H_J} H×H`,

   with the ordinary product/subspace topology. Equivalently one may use `(Θ_J⊗_ℝℂ) \ ⋃H_ℂ` with a proved identification. The excluded condition for each retained `H` is that **both** the real and imaginary coordinates lie in `H`; excluding when either coordinate lies in `H` would create a different space. A finite-type implementation can directly use the displayed finite-type formula, as long as it explicitly states that specialization. It need not define a general infinite-type Tits cone just to specialize it; any claimed general Tits-cone identification must actually be proved.
5. The restriction of the actual normalizer action to `Θ_J` fixes `W_J` pointwise and descends to the actual **left** action of `Q`. On `X` it acts diagonally on real and imaginary parts. The quotient `Y=X/Q` is the orbit quotient with its quotient topology; its projection `c:X→Y` is the actual orbit map. A classifying space of `E`, a combinatorial nerve, or a topologically redefined type is not `Y` by definition.

Finite `W` implies finite rank because the simple reflection map is injective and takes values in the finite group. A formal development may select `Fintype I` from this fact, or initially work with an explicit finite-index presentation and prove that it covers every finite Coxeter system. It must not quietly replace the theorem's finite-type hypothesis with a stronger unproved restriction. A root-representation model in place of `Θ` also requires a proved equivariant linear homeomorphism: an unproved identification of a finite reflection representation with its dual is a substantive missing bridge.

## Required covering and fundamental groups

For every `x:X`, put `y=c(x)`. The geometric maps are

`c_* : π₁(X,x) →* π₁(Y,y)`

induced by the actual continuous covering map, and the genuine covering monodromy

`δ_x : π₁(Y,y) →* Q`,

constructed by lifting loops from `x` and recording the unique deck label, with the multiplication convention handled as below. The covering conclusion must concern this actual action and map. It requires proofs that `X` is nonempty/path connected, locally path connected and semilocally simply connected, that the `Q` action is continuous/free/properly discontinuous, and that the quotient is a normal covering with the asserted deck/fiber identification. Some of these may follow from stronger geometric results; they cannot all be inferred just from `Q` acting freely on a set of chamber labels.

In finite type `Q` is finite. A free continuous action of a finite group on the relevant Hausdorff space makes the proper-discontinuity step accessible, but freeness still concerns points of the **complex complement**, not only chambers. One useful direct route is: if a normalizer element fixes both real coordinates of a complex point, it fixes a sufficiently generic real linear combination of them; finiteness of the restricted arrangement permits choosing that combination outside every retained hyperplane. The stabilizer of such a relative regular point is `W_J`, so the quotient label is trivial. Each input, including that stabilizer theorem and the quotient action, needs a proof.

The geometric short exact sequence is the actual sequence

`1 → π₁(X,x) --c_*→ π₁(Y,y) --δ_x→ Q → 1`.

Using `FundamentalGroup` from mathlib is appropriate because it is the homotopy-classes-of-loops vertex group. An arbitrary group renamed `fundamentalGroup`, a groupoid vertex group with no proved relation to this space, or a class whose fields assume this exact sequence does not fulfill the contract.

## Convention issue independently checked in pinned mathlib

The original article explicitly composes category paths left to right. The pinned mathlib file `.lake/packages/mathlib/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`, lines 34 and 44, defines the fundamental group as the vertex endomorphism group and states

```lean
p * q = .of (q.asHom.trans p.asHom)
```

Thus `p*q` traverses `q` first. For a left action, if the raw endpoint labels of the lifts of `p` and `q` from `x` are `g_p` and `g_q`, then the raw endpoint label for this product is `g_q*g_p`. The raw endpoint label is anti-multiplicative with these conventions. Mapping to the opposite group, taking the inverse label, or transporting a consistently chosen loop convention can correct it. A final implementation must prove the selected correction is a homomorphism and must check the algebraic projection comparison against it. Simply writing the raw label as a `MonoidHom` without a convention proof is not acceptable. This is a difference of conventions, not a defect in the article or in mathlib.

The existing candidate `sourceFundamentalGroupEquiv` inspected below explicitly uses `MulEquiv.inv'`; this reinforces the need to inspect the direction of its comparison rather than importing the name as an automatically compatible isomorphism.

## Full conclusion and exact-sequence compatibility

A faithful formal conclusion supplies group isomorphisms

`e_K : K ≃* π₁(X,x)` and `e_E : E ≃* π₁(Y,c(x))`

and proves both equations

`c_* ∘ e_K = e_E ∘ i`,

`δ_x ∘ e_E = p`.

The right vertical arrow is the identity on the same actual `Q`, as in diagram (6.8). Merely showing there exist abstract group isomorphisms on the first two terms, or an arbitrary automorphism of `Q` making some other diagram commute, is insufficient for the specified induced sequences. A documented change of conventions is permissible only with proved transports that recover the intended compatible diagram.

The comparison may be constructed at a selected chamber point and then moved to arbitrary `x`, but compatible change-of-basepoint paths must be supplied and used on both `X` and `Y`. The final theorem must apply to every `x:X`, rather than only to a chosen `a_C`. The source's Theorem 6.7 proof first works at the image of `(e,J)` under a groupoid equivalence; completing its arbitrary-basepoint statement requires this routine but real transport. The basepoint in the quotient is **the image of the same `x`**, not an independently chosen point of `Y`.

For `K(π,1)` the contract requires actual asphericity of both `X` and `Y`, together with the above fundamental-group identifications. Acceptable precise formulations include a contractible universal covering space with the requisite covering/universal properties, or path connectedness and vanishing higher homotopy groups for every degree at least two, with the appropriate CW-type comparison when claiming an Eilenberg–Mac Lane/classifying-space model. “Simply connected,” “has fundamental group π,” or “there exists some contractible space with a π-action” alone is not the assertion.

The actual complement is an open subset of a finite-dimensional complex vector space and has the relevant homotopy/CW properties. Corollary 6.14 invokes Deligne's asphericity for **finite real central simplicial arrangements**; all three features must be proved for this restricted arrangement. Its application is not obtained just because the original Coxeter arrangement is simplicial: the restricted arrangement's chambers need their own geometric identification. Once `X` is aspherical, the actual covering `c` induces higher-homotopy isomorphisms, giving asphericity of `Y`. One can then use `e_K` and `e_E` to state the two asserted `K(K,1)` and `K(E,1)` conclusions. The finite CW-model observation in Remark 6.15 is additional to the theorem's displayed conclusion and should not be silently asserted without its own equivariant finite-model argument.

## Concrete bridge obligations

The following are independent mathematical work, not fields to assume in a final “Theorem1.8Data” structure:

1. The actual finite Coxeter root/dual geometry, `Θ_J`, proper restricted hyperplanes, topology, and preservation of those objects by the normalizer.
2. Passage to the quotient action by the actual `W_J`, pointwise triviality of that subgroup, and the freeness/covering identification on the complex complement.
3. The path-based fundamental groups and their induced covering sequence, with the product convention fixed.
4. A geometric-combinatorial comparison, for example an actual equivariant equivalence between the arrangement's Deligne groupoid and `FundamentalGroupoid X`. The source's Lemma 6.6 uses concrete chamber neighborhoods and paths and a Van der Lek theorem; this comparison is substantial and must be proved or supplied by an exactly verified Lean theorem.
5. A comparison from that arrangement/ribbon groupoid to the **existing presentation-defined** Artin normalizer quotient. The source uses Theorem 5.6's ribbon realization and checks the endpoint/deck label agrees with `π`. A formal replacement must establish the same agreement, not redefine the Artin group as the desired vertex group.
6. Both diagram equations and arbitrary-basepoint transport. The completed algebraic Lemma 2.8 supplies only the algebraic row, not these comparisons.
7. Deligne's finite simplicial arrangement asphericity theorem or an equivalent proved contraction of the actual universal cover, plus a proved bridge if the cover is represented by a combinatorial realization. An arbitrary Artin classifying-space construction alone does not give asphericity of this complement.

A different proof route is acceptable if it proves these same objects and conclusions. Generic covering lemmas or conditional comparison packages can be useful prerequisites, but passing the desired comparison/asphericity as a hypothesis does not complete Theorem 1.8.

## Candidate-source semantic screen

I inspected an already available local GitHub-source snapshot under `/tmp/lemma28-full-search/openai-math/lean/`, without downloading, installing, compiling, or certifying that snapshot in this task. This is a bounded source screen, not acceptance of its dependency closure or a worldwide search.

- `OAI/Topology/ArtinGroups/Model.lean` genuinely defines a standard braid-presented `Artin M`. However its `SalvettiCover M` is the topological realization of the nerve of a preorder on `Artin M × SphericalType M`; it is **not** the restricted complex hyperplane complement by definition.
- `Realizations/SalvettiCoverContractible.lean` states contractibility of that realization for every finite indexing type, through `source_salvetti_cover_contractible`. I read that theorem and `Realizations/RestrictedLiftedContractible.lean`'s immediate source. Even if fully kernel-checked, this conclusion alone does not compare the realization with an actual arrangement cover.
- `Realizations/CellUnion.lean` defines `SourceSalvetti` as a quotient of a union of model cells by face identifications. `Realizations/SalvettiProjection.lean` proves a covering and `FundamentalGroup (SourceSalvetti M) x ≃* Artin M`. I read its complete statement/proof and the relevant model definitions. That is a theorem about its model-cell quotient; no actual `X_J^ℂ` or `N(W,J)` action/comparison appears in those inspected statements. Reusing it requires the geometric and equivariant bridge, plus an Artin-presentation isomorphism to this project's actual group with generator compatibility.
- The separate `ComparatorChallenges/HarmonicArtin.lean` contains an explicit `sorry` in its challenge statement. I do **not** infer that the separately proved `Realizations/SalvettiCoverContractible.lean` imports that challenge file; this screen does not establish such a dependency. The challenge file itself is not an accepted supplier.

These are genuine mathematical constructions whose direct sufficiency for the requested theorem is **rejected** until the missing geometric comparison is proved. I do not label them vacuous merely because they are combinatorial models. Conversely, changing the definition of the requested `X` or `Y` to these models without proving equivalence would be a semantic substitution. No false source theorem is established by this screen. Broad searches inside this snapshot were only used to locate candidates; they do not prove that no suitable bridge exists elsewhere.

## Small cases that final definitions and diagrams must survive

- `J=∅`: recover the ordinary finite Coxeter reflection complement, its `W`-quotient, the ordinary pure/Artin fundamental groups, and the classical exact sequence.
- `J=I`: `Θ_J=0`, no proper restricted hyperplanes, and `X` and `Y` are singletons. Both normalizer quotients and the pure image are trivial. Defining hyperplanes without the proper-restriction exclusion would incorrectly make this case empty.
- Type `A₁` with `J=∅`: `X≃ℂ\{0}`, `Q≃C₂` acts by sign, and the quotient covering is represented by `z↦z²` after the usual identification. The induced map on fundamental groups is multiplication by two. This distinguishes a correct sequence comparison from merely producing two abstract isomorphisms with `ℤ` and ignoring the inclusion/covering map.
- Rank zero is included; no mandatory nonempty index or hyperplane assumption is permitted.

## Preliminary decision

The semantic target is the full geometric Theorem 1.8 above, with finite-type hypothesis, arbitrary `J` and basepoint, actual complex complement and orbit quotient, both compatible fundamental-group isomorphisms, and actual asphericity. The existing algebraic Lemma 2.8 is an applicable supplier but is not completion of this target. **No Theorem 1.8 code or final source binding is accepted at this preliminary stage.** I will compare proposed definitions and statements with this independent contract when they become available, before compilation evidence can be treated as evidence of the intended theorem.
