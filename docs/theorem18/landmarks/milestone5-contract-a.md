# Landmark 5 and full Theorem 1.8: independent contract A

Reviewer: GPT-6.1 Sol / high (`gpt-6.1-sol`, `high`). Contract dated 2026-11-14 against repository HEAD `22301de0ff626dbfb3d8ae66a6bccc50317de702`. This is an independent statement/source and mathematical-route contract. It does not certify new M5 mathematical code, accept a new supplier cohort, or claim landmark 5/full Theorem 1.8 proved.

## Exact source claim and final scope

I independently read arXiv:2509.21915v3 Theorem 1.8, Theorem 6.7 and Remark 6.12, and Corollary 6.14 on PDF pp.26–27, including its actual Deligne application; the K(π,1) clause of Theorem 1.8 occurs on PDF p.3. The source claims both the compatible exact-sequence identification and that the actual relative complexified complement and its actual normalizer orbit space are K(π,1) spaces for their stated groups. M4 has completed the former. It has not completed the latter.

The final theorem must range over arbitrary `I`, `M : CoxeterMatrix I` with finite actual `M.Group`, and every `J : Set I`. It must include reducible groups, rank zero, `J = ∅` and `J = Set.univ`, with no extra irreducibility, crystallographic, positive-rank, nonempty-complement, caller-supplied simpliciality, cover, asphericity or geometric-comparison assumption. Finiteness of the actual Coxeter group is the sole additional mathematical hypothesis. Consequences such as finite `I`, actual arrangement finiteness and actual path-connectedness may be derived, not added as restrictions.

Retain exactly the existing objects:

- `X = Theorem18.Complement M J`: the inherited-topology subset of `relativeSubspace J × relativeSubspace J` on which no retained root evaluation vanishes in both coordinates.
- `Y = Theorem18.OrbitSpace M J`: the actual orbit quotient by `Q = Artin.coxeterNormalizerQuotient M J`, with its actual quotient topology and `p = orbitProjection M J`.
- `K = Artin.pureNormalizerImage M J`, the existing image in `N_A(A_J)/A_J` of the ambient pure Artin group intersected with the actual normalizer.
- `E = Artin.normalizerQuotient M J`, the existing quotient of the actual braid-presentation Artin normalizer by its actual generated parabolic.

For **every actual** `x : X`, the new mathematical conclusion must include both

`TauCeti.IsEilenbergMacLaneSpaceOne K X x`

and

`TauCeti.IsEilenbergMacLaneSpaceOne E Y (p x)`.

The strongest convenient orbit-space corollary states the latter for every actual `y : Y`, using proved surjectivity of the actual orbit map or proved basepoint independence. A theorem quantified over all `x : X` already reaches every orbit point once surjectivity is explicitly accounted for; a selected-standard-point-only theorem does not complete this contract.

The full public `theorem_1_8` bundle must retain the entire actual M4 exact-sequence proposition, with both concrete multiplicative comparisons, both exact rows and both actual-map commuting squares, **and** these two K(π,1) conclusions. A separate fullM4 theorem plus two explicitly connected asphericity/K(π,1) theorems can be bundled without repeating proofs. Two arbitrary new group isomorphisms or a K(π,1) claim for a groupoid nerve/classifying space would not replace this actual-space statement.

## What the existing formal K(π,1) predicate means

I read the literal accepted TauCeti definitions and proofs, not only their provenance descriptions. At pin `62bbc0596dc3539d488232e4e924a338548ea0a9`:

`TauCeti.IsAspherical X x := PathConnectedSpace X ∧ ∀ n : ℕ, Subsingleton (π_ (n + 2) X x)`.

`TauCeti.IsEilenbergMacLaneSpaceOne G X x := IsAspherical X x ∧ Nonempty (FundamentalGroup X x ≃* G)`.

Here mathlib's `π_ m X x` is `HomotopyGroup (Fin m) X x`: the quotient of genuine continuous based generalized loops on the finite unit cube, by genuine homotopy relative to its entire boundary. The generalized loops send the boundary to `x`. The quotient is inhabited by the constant loop, so `Subsingleton` means actual triviality, not an empty-type/vacuity trick. The index `n + 2` covers **every** dimension at least two. Connectivity, trivial homology, finitely many checked degrees, simple connectedness of an unrelated object, or equivalence of fundamental groupoids is insufficient.

This is the standard homotopy-group meaning of an Eilenberg–Mac Lane space of type K(G,1). The predicate does not carry a CW structure, a chosen universal cover, a proof that a universal cover is contractible, a finite CW model, or a universal principal-bundle classification theorem. It is enough for the literal homotopy-group K(π,1) statement once its actual clauses are proved. No unproved CW hypothesis should be inserted merely to use this predicate, and no stronger CW/classifying-space/universal-cover assertion should be silently inferred from the definition for arbitrary spaces. Such stronger assertions require their own proved hypotheses or a direct construction.

The existing `TauCeti.IsAspherical.of_basepoint` and `IsEilenbergMacLaneSpaceOne.of_basepoint` use actual higher-homotopy/path equivalences and actual fundamental-group basepoint change. They can propagate an independently established asphericity proof from one point to all points, using actual path-connectedness. They do not establish the initial higher-homotopy vanishing.

## M4 conventions remain fixed

Use the accepted actual M4 comparisons

`ΦK_x = Sequence4.pureFundamentalGroupEquiv M J x : K ≃* FundamentalGroup X x`,

`ΦE_x = Sequence4.normalizerFundamentalGroupEquiv M J x : E ≃* FundamentalGroup Y (p x)`.

The group witnesses in the K(π,1) predicates can be precisely `ΦK_x.symm` and `ΦE_x.symm`. Thus the groups are the already identified actual groups, not newly defined fundamental groups or their unspecified quotients. Retain the actual inclusion `i`, covering map `j_x`, canonical Artin–Coxeter quotient map `a`, and the same actual `Q`.

Ordinary mathlib fundamental-group multiplication reverses path traversal. The raw actual endpoint map is `μ_x : π₁(Y,p x) →* Qᵐᵒᵖ`; the accepted normalized terminal map is `m_x = ν_Q ∘ μ_x`, where `ν_Q(op q) = q⁻¹`. The established equations are `ΦE_x ∘ i = j_x ∘ ΦK_x` and `m_x ∘ ΦE_x = a`, with identity on the same `Q`. The raw formula remains `μ_x(ΦE_x e) = op((a e)⁻¹)`. The positive formulation explicitly uses opposite fundamental groups and its already proved original-label geometric formula. M5 must not silently replace these maps or discard the two squares because the K(π,1) predicates themselves retain only existence of group identifications.

## What can already be reused, and the single substantive missing conclusion

The actual arrangement model, M1 quotient cover, M2 normalizer identification, M3 actual geometric fundamental-groupoid equivalences, and M4 compatible every-basepoint comparisons remain unchanged accepted inputs. In particular, actual path-connectedness of `X` and the actual finite-type quotient cover `p` are already proved.

The accepted supplier theorem

`IsCoveringMap.isAspherical hp hp_surj he hX`

transfers asphericity from an actual total space to the actual base of a **surjective** covering map. Its higher-homotopy step is the actual map-induced equivalence `π_(n+2)(total,e) ≃* π_(n+2)(base,p e)`, based on lifting genuine generalized loops and homotopies. Its connectedness step uses continuous surjective image. There is no simple-connectedness or universal-cover premise in this downward transfer. Apply it to M1's actual `p`, whose quotient-cover structure gives surjectivity. Do not use the distinct simply-connected quotient-cover K(G,1) recognition theorem to assert that `X` is simply connected or that `π₁(Y)` equals the deck group Q; neither is generally true here.

Consequently the minimal new **topological endpoint** is an unconditional proof of `TauCeti.IsAspherical (Complement M J) x` under finite actual W, equivalently the already available path-connectedness together with all actual based higher-homotopy groups trivial. One can prove it at a standard point and use actual basepoint change. Once this endpoint is established, covering transfer and the inverse M4 equivalences give both K(π,1) conclusions and the final bundle. This short endpoint description does not make its missing mathematical proof routine: the geometric Deligne argument below is substantial.

An equivalence `D ≌ FundamentalGroupoid X` only controls points up to path-component and based π₁. Its abstract groupoid realization is a homotopy1-type; no actual map identifying that realization with `X` up to homotopy or higher-homotopy equivalence is supplied by a category equivalence. Therefore M3 does **not** already imply asphericity. A Čech colimit in categories/groupoids and gluing functors into a groupoid similarly retain only 1-dimensional data. A nerve/order realization can be used only with an additional proved higher-topological comparison to the actual complement or a genuine covering of it.

## Actual finite, central, simplicial arrangement: a precise bridge

Deligne's original hypothesis is stronger than saying there are finitely many convex sign chambers. It requires each real chamber to be **exactly** the set of strictly positive coordinates in a real basis of the ambient relative vector space.

The actual formal family is `actualForms M J : RelativeRoot M J → relativeSubspace J →L[ℝ] ℝ`. Retention already proves each selected form nonzero. Finiteness follows from the finite actual Coxeter group and `finite_index M`; repeated root forms/hyperplanes are permitted, and the actual distinct arrangement is the image of retained roots under `restrictedHyperplane`. If an imported theorem expects distinct hyperplanes, prove the passage to this finite image without changing the complement. It is false to require all retained root forms to be linearly independent.

Centrality must concern these actual linear kernels, all containing zero. The relative ambient space has its existing real dual-coordinate/subspace topology. If a supplier uses a finite-dimensional normed real vector space or a particular complexification, construct a genuine continuous linear equivalence/homeomorphism with the present model. The real-pair complement is the complexification complement via real/imaginary coordinates, not a newly chosen space with a desired name. `actualComplementHomeomorph` already identifies the native M3 arrangement complement with the actual parent `Complement` by identity on both coordinates.

There is a concrete short simpliciality route from accepted M3 results. For every actual chamber C, choose its actual raw facet label L with indices K and actual continuous linear equivalence

`facetFlatEquiv L : relativeSubspace K ≃L[ℝ] relativeSubspace J`.

M3 proves `C.region = translatedFacet L`; the standard source facet consists exactly of functionals with coordinates zero on K and strictly positive off K. Restrict `dualCoordinates` to obtain a real linear coordinate equivalence

`relativeSubspace K ≃ₗ[ℝ] ({i : I // i ∉ K} → ℝ)`.

Using finite I, pull back the genuine standard coordinate basis and transport it through `facetFlatEquiv L`. Prove thatC is exactly the image of the strictly positive orthant in this basis. This gives a basis of **the relative flat**, not of the larger ambient dual, and not a possibly dependent family of restricted roots. The continuous/topological coordinate bridge must use the existing topology. An actual `Basis` statement, or an explicitly equivalent continuous linear orthant statement with the equivalence proved, is an appropriate final simpliciality lemma.

The actual retained simple roots offJ already force the common kernel in the relative flat to be zero, so essentiality can be proved if the chosen Deligne API asks for it. It should not be imposed as a new hypothesis. The zero-dimensional/full J case must be included by an empty basis and singleton complement, or proved separately before a positive-dimensional spherical construction. A rank-positive helper alone cannot serve as the final theorem.

A relative restriction is not generally a Coxeter reflection arrangement for a new matrix. Ordinary finite-Coxeter Salvetti/Deligne code cannot be applied by blindly replacing its matrix with the relative arrangement. Deligne explicitly notes this distinction while proving the relevant restriction property; see the source record below.

## A faithful Deligne proof route and minimal core lemmas

A genuinely proved general finite central simplicial-arrangement asphericity theorem, instantiated with the preceding actual basis bridge, is acceptable. A caller-supplied field or hypothesis asserting the Deligne conclusion is not. Alternatively construct a genuinely contractible (or adequately higher-homotopically trivial) covering/model of the actual complement and prove the requisite topological comparison. The following is the original proof route as independently read; equivalent routes may replace individual steps only with proved actual counterparts.

1. **Positive gallery algebra attached to this arrangement.** Build minimal positive chamber paths, identify the rank-two relations and prove cancellation and the maximal simple-prefix/principal-ideal property. Deligne's key results are1.12,1.14–1.20, particularly1.19. Facet-local gallery embeddings and their intersection properties1.24 and1.29–1.32 support the higher cells. The antipodal element gives cofinal positive fractions1.26–1.27. M2/M3 may supply algebraic ingredients, but they must be matched to this arrangement and these actual facet-local maps. A named Coxeter longest element or an unrelated ordered set does not supply that identification.
2. **Actual capped chamber complex and positive filtration.** Deligne constructs the spherical chamber complex I⁺ from positive gallery classes, then caps each apartment sphere S(A) with a ball b(A) to form the capped complex Ĩ⁺ (2.2–2.8). A precise face-equivalence/attachment description is essential. The length filtration contracts stage-by-stage by2.9.1. Its supporting lemma2.9.2 identifies how a newly appearing chamber meets the old stage; one collapse handles a proper nonempty union of boundary faces, and the other removes a chamber together with its unique cap when the entire boundary is present. These are statements about actual cells and continuous deformations, not only about comparability of labels.
3. **Signed exhaustion with topology.** The positive complex embeds as a closed subcomplex of the signed complex; even inverse antipodal powers exhaust the signed capped complex (2.14). Deligne uses the CW topology, homotopy-group passage through the exhaustion, and the contraction of the positive model to conclude contractibility 2.15. A union of contractible pieces is not sufficient without the relevant topology/compactness or explicit compatible deformation argument. For the formal K(π,1) predicate, proving higher-homotopy vanishing by compact-cube factorization through justified stages may avoid a later Whitehead theorem; a claim of actual contractibility must prove that stronger step.
4. **A real lifted complement and genuine covering.** In3.4–3.6, the lifted space Ŷ is a topological quotient of disjoint actual tube opens Y(qA), indexed by signed chamber lifts. Overlaps Y(A,B) are selected by actual apartment intersections3.2. Prove the gluing relation transitive, the quotient maps/open images as required, and the actual projectionŶ→Y to the complexified arrangement complement. In3.7A, actual facet-star neighborhoods V(F,C) give explicit evenly covered neighborhoods. A covering functor between fundamental groupoids is insufficient as a replacement without a proved construction of this topological cover.
5. **Actual open cover, finite intersections and localization.** The lifted space has an actual vertex-indexed open cover whose nerve is exactly the capped complex (3.7.4). The index correspondence and all nonempty finite intersections must be proved. Center-containing intersections admit the explicit affine contraction3.7.5. Remaining intersections Ŷ(F) are related by the actual cartesian covering diagram3.7.7 to lifted complements for lower-dimensional localized arrangements, with an actual homotopy comparison3.7.8. The localization stays finite central simplicial; prove the relevant dimension drop and base case, not just an injective map of posets.
6. **Higher topological conclusion.** Rank induction makes every required nonempty finite intersection contractible. A genuine topological nerve theorem/comparison, with all its numerability/paracompactness/local-finiteness hypotheses actually established if that chosen theorem requires them, identifies the higher homotopy or homotopy type of Ŷ with the capped complex. This gives contractibility/asphericity of the genuine cover and hence actual complement asphericity via its actual covering map. An untruncated topological nerve comparison is the needed input; the already accepted 1-groupoid Čech theorem alone cannot perform this step.

This route is more than a literature citation. The irreducible new proof obligation is the actual lifted geometry plus its controlled higher-topological realization/nerve argument (or a faithful alternative giving the same higher-homotopy endpoint). Finite/central/simplicial packaging and M4 bundling alone do not prove M5. A bounded-rank directed order may help contract a realization, but it proves nothing about actual complement higher homotopy until these geometric/topological comparisons have been supplied.

## Primary-source reading, findings and limits

I used the archived original Pierre Deligne, *Les immeubles des groupes de tresses généralisés*, Invent. Math. 17 (1972), 273–302, 30-page publisher scan. Local PDF:

`/home/lazyinspirit/Projects/workflow-engines/.research-workflow/artin-tits-normalisers-2509-21915-20261113/escalation-support/deligne/deligne.pdf`.

The archived source URL is `https://publications.ias.edu/sites/default/files/Number18.pdf`. A fresh attempt to fetch this author-site URL during this review returned HTTP 403; I therefore do not claim a fresh download comparison. I read the archived original PDF/text, checked its title/publication and visually inspected PDF pages 1,5,21 and24, and read the entire general asphericity proof in §§ 1–3, printed pp.273–296/PDF pages 1–24. I did not read the unrelated braid-group center/word-problem applications in the remaining §4, printed pp.296–302, as part of this contract. I have not formally verified the prose proof.

Exact relevant locators and dispositions:

- Main theorem, printed p.273/PDF 1: finite-dimensional real V, finite homogeneous hyperplanes and open simplicial real chambers imply the actual complexified complement is K(π,1). **Disposition:** faithful general theorem to formalize; no root-system/crystallographic/irreducible restriction.
- Hypothesis 1.8, printed p.277/PDF 5: “chaque chambre est l'ensemble des points à coordonnées >0 dans une base convenable de V.” **Disposition:** demands the actual real-basis/positive-orthant bridge above; finite convex chambers alone do not discharge it.
- Remark 1.9.1(ii), same page: the traces on an intersection P of walls not containing P again satisfy 1.8, and need not be a reflection-group arrangement even when the original one is. **Disposition:** supports applying the general arrangement theorem and rejects a blind ordinary-Coxeter substitution. It is not a claimed defect of either paper.
- Positive contraction 2.9/2.9.1/2.9.2, printed pp.288–289/PDF 16–17; signed embeddings/exhaustion 2.14 and contractibility 2.15, pp.290–291/PDF 18–19. **Disposition:** the relevant algebraic/cell/topology dependencies are explicit above; do not infer contractibility from a bare abstract poset name or unproved exhaustion.
- Actual covering 3.7A, pp.293–294/PDF 21–22; actual lifted cover nerve/intersections/localization 3.7.4–3.7.8 and closing rank induction 3.7D, pp.294–296/PDF 22–24. **Disposition:** these establish genuine topology beyond π₁ and must be formally supplied, not hidden in a groupoid-equivalence field.

No new mathematical error in Deligne's theorem or the source Corollary 6.14 is asserted. Short or implicit steps in the published proof remain established mathematics to formalize, not new open problems or author defects. The earlier separately recorded qualified source observations retain their original scopes and do not change this contract. No reviewer B report was consulted.

I read the accepted literal TauCeti asphericity/K(G,1) definitions, basepoint-change endpoints and covering-transfer proof chain, together with mathlib's generalized-loop, boundary-relative-homotopy and higher-group quotient definitions. I did not freshly re-audit/replay all earlier supplier modules or inspect every basepoint collar proof again. Those remain unchanged accepted inputs. I ran read-only source/hash inspections and rendered original pages for reading; no Lean build, axiom audit or kernel replay was executed by me for M5, and no new scientific source/configuration/cache was edited.

## Bound reading inputs and future acceptance

Article PDF SHA-256: `7a18b3e54c6edce92d8256afe6eae4da0d0483b58f3654a338e90a6b745f83da`; article text: `d98828d0f8f7d179ca8437bc6d98b7f8f7f50ae94012fdca1243cb4024390876`.

Deligne PDF SHA-256: `1905043232e1dadd97696372252bb5f91c202ea1b72379e77a9fecbfe9eed4bc`; extracted text: `ab83dc523206dc8484b36a93a5eb6012f6882a47a1b9e3161eae33e13ab98e9c`.

The following literal accepted endpoints were refreshed:

- `vendor/TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean`: `3e44a7116f624a8984e88dcca177f6f80ca566aa33e5dbe07eaca28f5f6d6efa`.
- `vendor/TauCeti/AlgebraicTopology/EilenbergMacLane/Covering.lean`: `bd5738fac0ea6506438d7d2f25f53c967f08fac0845dbaf42148c6fbc8301232`.
- `vendor/TauCeti/Topology/Homotopy/HomotopyGroup/Covering.lean`: `c8142d2fc1eb53411d7ccf13fe4b861fb2e5f0b694c2ecf50df846cdcb48c0d1`.
- `vendor/TauCeti/Topology/Homotopy/HomotopyGroup/BasepointChange.lean`: `fb60626e4e08f26f0eab093d3933453ef282d90b187afd3b1103890caf9bc644`.
- `sequences/ArtinSequences/Landmark4.lean`: `73c1fa143ac1967c44a8f3464c6d6fb1cfe2bc70b30c0b5954c0e494b4ca32b6`.

Future final acceptance requires a complete unconditional actual-space asphericity proof, every actual generic premise instantiated, the full Theorem 1.8 statement retaining M4 maps, exact frozen scientific/configuration/supplier bindings, exhaustive declaration and physical-occurrence axiom coverage and actual new-module kernel replay evidence. A useful supplier cohort or route outline is not completion. No main M5 acceptance receipt is issued by this contract.
