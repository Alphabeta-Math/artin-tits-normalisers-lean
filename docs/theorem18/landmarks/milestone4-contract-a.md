# Landmark 4: independent statement and source contract A

Reviewer: GPT-6.1 Sol, high reasoning effort (`gpt-6.1-sol` / `high`).
Status: preacceptance mathematical contract, 2026-11-14. This document accepts the proposed route as a faithful target; it does not certify landmark 4 or full Theorem 1.8 as proved.

## Source and scope

I independently read arXiv:2509.21915v3, Theorem 6.7 and its proof and Remark 6.12 on PDF pp.26–27, including the displayed sequences (6.8)–(6.13). I checked the original page images as well as the local article text. I also read the adjoining Corollary 6.14 to delimit the later asphericity obligation, the article's path-composition convention, `docs/theorem18/landmarks/milestone4-PLAN.md`, and the relevant actual M1/M2/M3 APIs below. The article's strongest statement here is an isomorphism of short exact sequences for every complement basepoint, with identity on the same Coxeter normalizer quotient. An abstract pair of group isomorphisms alone would be insufficient.

The formal target ranges over every Coxeter matrix `M` with `[Finite M.Group]` and every `J : Set I`. It must retain the existing actual spaces, groups and actions, including reducible cases, empty rank and full `J`. No extra spherical-parabolic, nonempty-rank, irreducibility, selected-chamber-only, freeness, cover, lifting, simply-connectedness or target-comparison premise may remain on the actual main theorem. Existing finite-Coxeter consequences may of course be proved and used.

## Actual objects and the required statement

Use the following fixed notation, all referring to existing definitions:

- `X = Theorem18.Complement M J`, the actual complexified relative arrangement complement; `Y = Theorem18.OrbitSpace M J`, with the actual quotient topology, and `p = orbitProjection M J`.
- `E = Artin.normalizerQuotient M J = N_A(A_J)/A_J`, using the actual braid-presentation Artin group and generated standard parabolic.
- `K = Artin.pureNormalizerImage M J`, the actual image in `E` of the ambient pure group intersected with the Artin normalizer. It is neither the whole ambient pure group nor a newly defined fundamental group.
- `Q = Artin.coxeterNormalizerQuotient M J = N_W(W_J)/W_J`, acting on the existing `X` as already proved.
- `i = Artin.pureNormalizerInclusion M J : K →* E` and `a = Artin.normalizerQuotientMap M J : E →* Q`, the existing inclusion and canonical Artin–Coxeter quotient map.
- For `x : X`, `j_x = Landmark1.orbitFundamentalGroupMap M J x : π₁(X,x) →* π₁(Y,p x)` is induced by the actual continuous `p`; `μ_x = Landmark1.orbitMonodromy M J x : π₁(Y,p x) →* Qᵐᵒᵖ` is actual endpoint monodromy of the proved quotient cover.

Here `π₁` denotes mathlib's actual `FundamentalGroup`, not a replacement group or an assumed classifying-space invariant. Define the explicitly normalized endpoint map

`ν_Q : Qᵐᵒᵖ ≃* Q`, `ν_Q(op q) = q⁻¹`, and `m_x = ν_Q ∘ μ_x`.

For **every** `x : X`, the main theorem must supply multiplicative equivalences

`ΦK_x : K ≃* π₁(X,x)` and `ΦE_x : E ≃* π₁(Y,p x)`

and prove the two actual homomorphism equations

`ΦE_x ∘ i = j_x ∘ ΦK_x`,

`m_x ∘ ΦE_x = a`.

The right vertical arrow is literally `id_Q`. Both rows must be proved short exact: `i` and `j_x` injective, `range i = ker a`, `range j_x = ker m_x`, and `a` and `m_x` surjective. Bundling these existing exactness proofs with the compatible equivalences is appropriate. Equality of kernels alone or an unspecified automorphism of `Q` is not the target.

The raw-monodromy version of the second equation, useful for checking signs, is

`μ_x (ΦE_x e) = op ((a e)⁻¹)`.

In particular, the formula `μ_x (ΦE_x e) = op (a e)` is generally incompatible with this ordinary mathlib-group formulation. Plain `unop` is not a homomorphism from an arbitrary noncommutative opposite group to the original group.

## Opposites and the geometric middle map

The article composes paths in traversal order. Mathlib's `FundamentalGroup` is the endomorphism group of the fundamental groupoid, whose multiplication reverses categorical traversal: its `mul_def` is represented by `q.asHom.trans p.asHom` for `p * q`. These conventions must be stated rather than absorbed into an unspecified group isomorphism.

In the actual reduced ribbon groupoid, first traversing labels `β` and `γ` has label `β * γ`. Consequently the same-label bridge identifies the actual vertex endomorphism group with the **opposite** of the actual reduced ribbon loop group. Equivalently, positive labels give

`E ≃* (π₁(Y,p x₀))ᵐᵒᵖ`

at the standard geometric basepoint `x₀`. Ordinary mathlib fundamental groups instead receive the **inverse** ribbon label. The proposed route using `MulEquiv.inv'` is correct: the pinned mathlib definition is `G ≃* Gᵐᵒᵖ`, `g ↦ op(g⁻¹)`, and its inverse sends `op(g)` to `g⁻¹`.

For clarity, the positive convention also has a faithful exact-sequence formulation: write `ΦE⁺ : E ≃* π₁(Y,p x₀)ᵐᵒᵖ`, similarly `ΦK⁺`, use the opposite of `j`, and use `μ⁺(op γ) = (μ γ).unop`. This last map is multiplicative because **both** source and target conventions have been reversed. It satisfies `μ⁺ ∘ ΦE⁺ = a`. Applying inverse-opposite equivalences to both fundamental groups yields the ordinary convention and `m = ν_Q ∘ μ` above. No commutativity premise is justified or needed.

The middle comparison must be constructed from the actual accepted chain:

1. The M2 canonical isomorphism from actual reduced ribbon loops at `J` to `E`, with its proved canonical projection compatibility.
2. The vertex group of `AssociateReducedRibbonObject M J`, the actual reduced `J`-associate full subcategory used in M3. The larger `RibbonObject` groupoid and its larger loop group are insufficient substitutes.
3. The M3 `actualRibbonOrbitEquivalence` to the actual fundamental groupoid of `Y`, applied on vertex groups with the correct inverse-label convention.
4. The actual equality or proved isomorphism identifying the image vertex with `FundamentalGroupoid.mk (p x₀)`, derived from the strict M3 square. Transport by `eqToIso` or conjugation must keep these endpoints explicit.

The M3 interval-groupoid route already establishes the necessary actual geometric comparison. Requiring the paper's literal adjacent-gallery dictionary or the previously unclaimed whole Lemma 5.9 would add a different obligation. Their absence must remain accurately described, but does not obstruct this route to the actual Theorem 6.7 maps.

## Monodromy: a proof obligation, not a label declaration

The right square requires joining M3's actual signed ribbon endpoint formula to the **existing** quotient-cover monodromy. For an actual path class starting at `x₀`, ending at `q • x₀`, and projecting to the stated based loop, prove `μ(loop) = op q` using actual path lifting/monodromy. Instantiate this with the actual M3 lifted class and strict covering square. Since the ordinary comparison uses inverse ribbon labels, that endpoint is `(a e)⁻¹ • x₀`; normalization then gives `a e` exactly.

The already proved signed endpoint result in `chambers/ArtinChambers/RibbonDeckLabels.lean` identifies the endpoint of a genuine reduced ribbon loop starting at `standardActualChamber` with its `reducedRibbonCoxeterProjection` translate. M2's `reducedRibbon_projection_compatible` identifies that projection with `a`. These existing results concern the actual action of the **same** `Q`; a newly chosen action or quotient automorphism would not suffice.

Generic helpers may assume a supplied actual lifted path and an equality/heterogeneous equality of its projected homotopy class to the given loop. The actual application must construct that path and prove the equalities. They must not remain as assumptions on the actual final theorem. A simply-connected-cover equivalence cannot replace the available general covering theory: `X` generally has nontrivial fundamental group, and M1 proves injectivity of `j`, not injectivity of monodromy.

## Every basepoint and the first square

Theorem 6.7 states an arbitrary `x`, although its proof first uses the standard chamber point. The final theorem must bridge that difference.

Let `θ` be an actual upstairs path from `x₀` to `x`, and let `σ = p ∘ θ` be its actual projected path. Use the corresponding actual basepoint-change multiplicative equivalences on both fundamental groups. Prove:

- Covering-map naturality: transport along `σ` after `j_x₀` equals `j_x` after transport along `θ`.
- Raw-monodromy naturality: `μ_x` after transport along `σ` equals `μ_x₀`, hence the same equation holds for normalized monodromy.

For the second assertion, transporting a lifted loop with endpoint `q • x₀` along `θ` gives endpoint `q • x`: the last lifted segment is the `q`-translate of `θ`. This explains why the terminal map remains identity on the same `Q`. An independently chosen downstairs path can instead introduce conjugation of quotient labels and cannot be used without accounting for it. It is unnecessary and generally false to demand that the resulting comparisons be independent of all path choices; the claim is existence of compatible comparisons at every basepoint, or explicit comparisons parametrized by a chosen upstairs path with the displayed equations proved.

A pure comparison derived from exactness is fully acceptable. After the actual compatible middle isomorphism is proved, `ΦE_x(i k)` lies in `ker m_x = range j_x`. Use injectivity of the actual `j_x` to take its unique preimage, prove the homomorphism laws, and prove bijectivity using both exact rows and bijectivity of `ΦE_x`. The inclusion square then holds by construction with the actual maps. This derives the missing equivalence from independently proved geometry and algebra; it does not assume the desired comparison as a field or redefine `K`.

## Reading limits and final acceptance gates

I read the actual definitions of the algebraic row in `ArtinNormalisers/Artin/ExactSequence.lean`, the actual geometric row in `landmarks/ArtinLandmarks/Covering.lean` and its generic covering-sequence supplier, the M2 canonical normalizer and projection interfaces, and the actual M3 comparison, strict square and signed deck labels. I checked the pinned mathlib `FundamentalGroup.mul_def`, path-based basepoint change, conjugation, actual quotient-cover endpoint monodromy, and `MulEquiv.inv'` definitions. I also inspected the newly authored `EndpointMonodromy.lean` and `RibbonVertex.lean` as preliminary implementations; this is not a frozen-code review. No reviewer B report was consulted. No new Lean build, axiom audit or kernel replay was run by me for this contract.

There is no newly established literature defect in this M4 review. The earlier qualified Lemma 3.5 boundary-choice observation and the distinct Godelle preprint proof-step observation retain their previously recorded scope and dispositions; neither is promoted here to an article error. No new external supplier is accepted merely because its names suggest covering or fundamental-group comparison.

Final acceptance requires inspection of every frozen new formal definition and statement, their proof chains and actual applications, exact source/configuration/dependency bindings, actual successful builds and exhaustive declaration/physical-occurrence axiom checks and exact new-module kernel replay evidence. Generic conditional lemmas are useful; all geometric hypotheses must be discharged on the actual final bundle. This contract is not such a final receipt.

Completing this target establishes the isomorphism-of-exact-sequences part of Theorem 1.8 in the existing standard-presentation algebraic model and actual relative spaces. The separately missing general ambient topology/presentation equivalence is not silently assumed or declared proved. A direct actual relative-space comparison can establish the required group identifications without that assumption. Landmark 5's genuine asphericity/Deligne input remains necessary for the K(π,1) conclusions and full Theorem 1.8.
