# Independent statement review B: Lemma 2.8 kernel argument

Reviewer: **GPT-6.1 Sol/high**, independent reviewer B. Final decision: **accept all eleven declarations** at the exact source hashes recorded below.

## Scope and reading

I read `CLAUDE.md` and `README.md` fully. This review derives the mathematics independently from the original article's extracted PDF text, without consulting reviewer A. Read source: arXiv:2509.21915v3, *Normalisers of parabolic subgroups of Artin–Tits groups and Tits cone intersections*, PDF p. 6, Lemma 2.8 and its complete displayed proof (`article.txt`, lines 295–312). I also checked the definitions on PDF pp. 1 and 3, equations (1.2) and (1.7), and p. 5, equation (2.4) and the paragraph defining the positive lift. This is a review of the general kernel statement, not a certification of the full article theorem or its other dependencies.

The initial independent mathematical review preceded source availability. I subsequently read all three source modules in `formalizations/artin-normalisers/ArtinNormalisers/` and their aggregate import file, independently of reviewer A, and reviewed every declaration below. I inspected the actual APIs in `/tmp/artin-mathlib-audit`, as listed below. Source compilation and final source-hash binding are reported separately at the end; semantic acceptance does not infer compilation from source inspection.

## Independently derived statement

Let `G` and `H` be arbitrary groups, `f : G →* H` an arbitrary group homomorphism, and `A : Subgroup G` arbitrary. Define

- `B := A.map f`, the actual subgroup image of `A`;
- `N := A.normalizer` and `M := B.normalizer`;
- `C := A.subgroupOf N` and `D := B.subgroupOf M`;
- `K := f.ker.subgroupOf N`, representing precisely `ker(f) ∩ N_G(A)` inside `N`;
- `q := QuotientGroup.mk' C : N →* N ⧸ C`.

The restriction `r : N →* M`, `r(n) = f(n)`, exists without surjectivity: the image of a normalizing element normalizes the subgroup image. The subgroups `C` and `D` are normal in their respective ambient normalizers. Since `r(C) ≤ D`, there is a canonical induced homomorphism

`F : N ⧸ C →* M ⧸ D`, with `F(q(n)) = [f(n)]`.

The correct kernel equality is

`F.ker = K.map q`.

Equivalently, for every `x : N ⧸ C`,

`x ∈ F.ker ↔ ∃ n : N, f (n : G) = 1 ∧ q n = x`.

An equivalent representative statement for any `g : N` is

`F(q g) = 1 ↔ ∃ k : N, f (k : G) = 1 ∧ q k = q g`.

There are no additional hypotheses: neither group is finite, neither `A` nor `B` is assumed normal in its original ambient group, and neither `f`, `r`, nor `F` is assumed or asserted surjective. `K.map q` is independently defined from `f` and the source quotient; defining it as `F.ker` would defeat the substantive claim.

## Independent proof and orientation checks

Fix `g ∈ N`. The target coset is trivial precisely when `f(g) ∈ B = f(A)`. Choose `a ∈ A` with `f(a) = f(g)`. The element `k = g a⁻¹` remains in `N`, because `A ≤ N` and `N` is a subgroup. It satisfies `f(k) = f(g) f(a)⁻¹ = 1`, and `q(k) = q(g) q(a)⁻¹ = q(g)`. Conversely, any source normalizer element killed by `f` maps to the identity target coset, so its quotient image lies in `F.ker`. Every source quotient element has a representative, giving the universally quantified equivalence.

The right multiplication `g a⁻¹` matches the article's `β σ_w⁻¹ A_J = β A_J`. Normality inside the normalizer permits either coset convention, but the proof above directly follows the displayed right coset. No multiplicative section is required: only the elementwise lifting property of `A → f(A)` is used. In particular the article's positive lift is merely one choice of such an element.

The preimage of the target identity before quotienting is `(f⁻¹(B)).subgroupOf N`, not `K`. In general `f(g) ∈ B` does **not** mean `f(g) = 1`. The nontrivial step is that these two subgroups have the same image under `q`. A proof that silently identifies these subgroups would be false even though the final image equality is true.

## Quantification, non-vacuity, and adversarial cases

The target subgroup must really be `A.map f` (or an explicitly equal subgroup). Merely assuming `f(A) ≤ B` guarantees descent but not the asserted kernel equality: with additive groups `G = H = ℤ`, `f = id`, `A = {0}`, and `B = ℤ`, the descended map has full kernel while the quotient image of `ker(f)` is trivial.

The source intersection with the normalizer is essential. Elements of `ker(f)` need not normalize `A`, and therefore need not represent elements of the source quotient at all. Conversely, no assumption that all of `ker(f)` normalizes `A` is needed.

The statement is not conditional on the desired existence of a pure representative: that existence is its conclusion. A witness in `A.map f` is available by the definition of subgroup image and does not assume the conclusion. The source quotient projection's surjectivity is a construction fact, independent of surjectivity of `f` or of `F`.

Useful boundary checks all agree: for `A = {1}`, the assertion reduces to the usual kernel of `f` (with the normalizers equal to the ambient groups); for `A = G`, the source quotient is trivial; for trivial `f`, every source quotient coset has a kernel representative; for injective `f`, the induced map on normalizer quotients is injective although its target may be larger than its image. These cases impose no contradictory or empty assumptions.

Surjectivity of `f` alone cannot be smuggled into a proof of surjectivity of `F`. For example let `G = D₈ = ⟨r,s | r⁴=s²=1, srs=r⁻¹⟩`, let `f` be abelianization to `H ≅ C₂ × C₂`, and take `A = ⟨s⟩`. Then `ker(f)=⟨r²⟩`, `N_G(A)=⟨r²,s⟩`, and `f(N_G(A))=f(A)`. Thus `F : N_G(A)/A → H/f(A) ≅ C₂` is trivial and not surjective, although `f` is surjective. To verify the normalizer computation: an element normalizing the two-element group `A` must centralize `s`; `r^i` or `r^i s` centralizes `s` exactly when `i` is even. This example is a guard against an invalid generalization; it is not an Artin–Tits example and is not evidence that the article's Lemma 2.8 is false.

## Exact mathlib API checks

The following were inspected in the checkout, rather than guessed from names:

- `Mathlib/Algebra/Group/Subgroup/Basic.lean:477`: `Subgroup.le_normalizer_map` states `(normalizer A).map f ≤ normalizer (A.map f)` with no surjectivity hypothesis.
- `Basic.lean:508`: `Subgroup.normal_in_normalizer` supplies `(A.subgroupOf A.normalizer).Normal` without requiring `A.Normal` in `G`.
- `Mathlib/Algebra/Group/Subgroup/Map.lean:284,315`: `subgroupOf` is a subgroup in the subtype ambient group, with membership equivalent to membership of the coerced element in the original subgroup. Thus `f.ker.subgroupOf N` has exactly the intended intersection semantics.
- `Mathlib/GroupTheory/QuotientGroup/Defs.lean:88–105,120`: `mk'`, its surjectivity, its equality criterion, and `eq_one_iff` give the actual quotient projection and coset tests.
- `Defs.lean:309–323`: `QuotientGroup.map C D r h` requires `h : C ≤ D.comap r` and returns a homomorphism between these genuine quotient group types. Its computation on representatives is the desired one.
- `Defs.lean:332–336`: `QuotientGroup.ker_map` yields the image under `q` of `D.comap r`. This by itself is not yet the stronger pure-representative statement; replacing this image by `K.map q` requires the correction by `a⁻¹` above.
- `Defs.lean:327–330`: `map_surjective_of_surjective` requires surjectivity of the composite into the target quotient, not merely surjectivity of an unrelated ambient `f`. This API does not prove full Lemma 2.8 from the current general hypotheses.

## Applicability to the article and remaining obligations

Substitute the Artin–Tits group for `G`, the Coxeter group for `H`, `π` for `f`, and the standard parabolic `A_J` for `A`. Identifying `A_J.map π = W_J` and `ker(π) = P` transports the source and target quotients to (1.2). The subgroup `K.map q` is exactly (1.7): a coset meets `P` if and only if it is represented by a pure element of `Norm_A(A_J)`. For the reverse reading of (1.7), any element of the coset belongs to the normalizer because the representative and `A_J` do.

This establishes the **kernel argument** of PDF p. 6, including the independently defined subgroup and the existential description. A Lean theorem about arbitrary groups does not by itself formalize the Artin–Tits presentation, parabolic subgroups, their image equality, the pure group identification, or the relevant type transports.

Full short exactness additionally needs surjectivity onto `N(W,J)`: every target normalizer coset must have a lift in `Norm_A(A_J)`. Equivalently, because `π(A_J)=W_J`, every element of `Norm_W(W_J)` must have such a normalizer lift (a target coset lift can be corrected by a lift from `A_J`). The displayed proof on p. 6 constructs the map and proves the kernel equality but does not supply this lifting argument explicitly. Ambient surjectivity alone is insufficient, as the independently checked dihedral example shows. This review neither verifies an Artin-specific lifting proof elsewhere nor reports a false article conclusion. Article-defect attribution, if pursued separately, must distinguish that explicit proof omission from the truth of the theorem.

The left-hand injection in the asserted short exact sequence is the inclusion of the independently defined subgroup `(1.7)`; its injectivity is automatic. It is not an injection of the entire pure group `P`. A presentation as `(P ∩ N_G(A))/(P ∩ A)` would additionally need the corresponding first-isomorphism identification; that is a useful corollary but is not required by the kernel target.

## Exact declaration inventory and judgments

The notation `N, M, C, D, K, q, r, F` in this table is as defined in the independent derivation above. All declarations are in namespace `ArtinNormalisers`. All source modules explicitly set `autoImplicit false`; the ambient variables are only `{G H : Type*} [Group G] [Group H]`, and the substantive inputs are `(f : G →* H) (A : Subgroup G)`. No instance assumes normality in the original ambient groups, and no theorem parameter assumes a lifting property, surjectivity, or the desired kernel equality.

| File and declaration | Exact semantic reading | Judgment |
| --- | --- | --- |
| `NormalizerMap.lean`, `normalizerMap` | `N →* M`, with underlying value `n ↦ f(n)`; the target subgroup is exactly the normalizer of `A.map f`. Its membership proof uses `le_normalizer_map`, which only asserts containment of the image of the source normalizer. | Accept. Actual restriction; no claim that the normalizers map onto one another. |
| `NormalizerMap.lean`, `normalizerMap_apply` | Coercion to `H` of `r(n)` equals `f(n)` for every `n : N`. | Accept. Certifies that the restriction did not replace `f` with another homomorphism. |
| `NormalizerMap.lean`, `normalizerMap_maps_subgroup` | `C ≤ D.comap r`, namely `r` sends the embedded source subgroup into the embedded subgroup image. | Accept. This is precisely the hypothesis needed for descent. It is not a surjectivity assertion. |
| `QuotientMap.lean`, `quotientMap` | `F : N ⧸ C →* M ⧸ D`, constructed with the actual `QuotientGroup.map`, the previously defined restriction, and the preceding containment theorem. | Accept. Both source and target are the intended full normalizer quotients. The target has not been replaced by the image of the source. |
| `QuotientMap.lean`, `quotientMap_mk` | `F(q(n)) = [r(n)]` for every source normalizer element. | Accept. This is the canonical induced map's defining representative computation. |
| `Kernel.lean`, `quotientMap_mem_ker_iff` | For every quotient element `x`, `x ∈ ker F` if and only if there exists `n : N` with `q(n)=x` and `f(n)=1`. | Accept. A complete, universally quantified pure-representative characterization. The witness belongs to the normalizer by its type; the right-hand side does not refer to `ker F`. |
| `Kernel.lean`, `kernel_eq_image` | `ker F = K.map q`, with `K = f.ker.subgroupOf N`. | Accept. Independent subgroup image, not a restatement obtained by defining the right-hand side as the kernel. |
| `Kernel.lean`, `articleKernelMap` | A homomorphism with domain the actual ambient subgroup `f.ker ⊓ N : Subgroup G`, formed by including it into `N` and then applying `q`. An element's `n.property.2` supplies its normalizer membership, while `n.property.1` supplies its original kernel membership. | Accept. Implements the article's ambient-intersection construction exactly. No unwanted quotient, intersection reversal, or normalizer of the pure subgroup is substituted. This map is not asserted injective. |
| `Kernel.lean`, `articleKernelImage` | The subgroup `(articleKernelMap f A).range` of `N ⧸ C`. | Accept. Independently defines exactly `q(ker(f) ∩ N_G(A))` as a subgroup. The definition contains no mention of `quotientMap` or its kernel. |
| `Kernel.lean`, `articleKernelImage_eq` | Equality of this range with `K.map q`, reconciling the ambient-intersection and subtype-subgroup constructions. | Accept. Checks both formulations refer to the same subgroup; does not change the theorem's scope. |
| `Kernel.lean`, `kernel_eq_articleKernelImage` | `ker F = articleKernelImage f A`. | Accept. The final result matches the original kernel claim with the original independently defined image. |

There are **four definitions and seven theorems**. `ArtinNormalisers.lean` imports precisely the three reviewed modules and declares no additional mathematical object or theorem. The modules use the standard group, normalizer, subgroup image, quotient group, kernel, and homomorphism-range constructions; there is no local alternate definition of equality or of these group-theoretic constructions. Inspection of all four Lean files found no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or `partial` declaration. This observation is a source check, not a substitute for compilation or an exhaustive audit of mathlib's transitive imports.

## Exact proof/source correspondence

PDF p. 6 first says that `π` restricts to `Norm_A(A_J) → Norm_W(W_J)` and that `A_J` lies in the kernel after projection. These steps correspond to `normalizerMap`, `normalizerMap_maps_subgroup`, and `quotientMap`; the representative equation `quotientMap_mk` identifies the resulting map concretely. General ambient surjectivity is absent because none is required for these steps.

The original kernel proof then assumes `β A_J ∈ ker(π)` and obtains `w := π(β) ∈ W_J`. In `quotientMap_mem_ker_iff`, the proof obtains a representative `g`, converts kernel membership to `f(g) ∈ A.map f` using `QuotientGroup.eq_one_iff`, and extracts `a ∈ A` with `f(a)=f(g)`. This is the exact general form of choosing the original `σ_w ∈ A_J`.

The original identities `β A_J = β σ_w⁻¹ A_J` and `β σ_w⁻¹ ∈ P` correspond to the witness `g * aN⁻¹`, the projection calculation using `q(aN)=1`, and the calculation `f(g a⁻¹)=1`. Multiplication and inverse occur in the correct order for arbitrary noncommutative groups. The reverse implication in the Lean equivalence is the original proof's “other inclusion is clear,” now explicitly proved by mapping a pure representative to the identity target coset.

`kernel_eq_image` packages that witness argument as subgroup equality. `articleKernelMap`, its range, the equality of image formulations, and `kernel_eq_articleKernelImage` additionally ensure that the final right-hand side is the image stipulated in (1.7), rather than the unrestricted pure subgroup, the intersection itself, or a subgroup defined to be the kernel.

The article-specific identifications and missing full-surjectivity obligation stated above remain outside these declarations. No formal Artin–Tits/Coxeter presentation or standard-parabolic identification appears in these files. The general theorem therefore proves precisely the group-theoretic **kernel portion** of Lemma 2.8 under the identified substitutions, not the full lemma or its short exact sequence. No new original-article mathematical error is established by this semantic review; the standalone-surjectivity proof omission and its limitations remain distinguished above.

## Decision and final binding status

**Accept all eleven exact formal declarations semantically.** They prove the intended general group-theoretic kernel claim and the full existential coset characterization, without strengthened hypotheses, weakened quotient targets, vacuous assumptions, or conclusions hidden in definitions. **Do not describe this as a proof of full Lemma 2.8 or its short exact sequence.**

## Final source inspection and SHA256 binding

After the orchestrator reported the author's warning-free compilation of the aggregate root module, I reread all four final Lean files in full and independently recomputed their SHA256 hashes with `sha256sum`. All four matched the hashes supplied in that confirmation. This review's accepted decision binds to exactly these bytes:

| Exact repository path | SHA256 |
| --- | --- |
| `formalizations/artin-normalisers/ArtinNormalisers.lean` | `ad0b9f18a334eed2aa41c85618bb635ddf2cfefcd5947a79264fa7e618962461` |
| `formalizations/artin-normalisers/ArtinNormalisers/NormalizerMap.lean` | `5ea6d9a6b7add5ea6d20a3a3fe225ac1094ab28d31d4515e04088b99bc1124d9` |
| `formalizations/artin-normalisers/ArtinNormalisers/QuotientMap.lean` | `544b3a7f491df63d313d75b7b8a87c201f6d90f8838d4979a498ccefa3677eb6` |
| `formalizations/artin-normalisers/ArtinNormalisers/Kernel.lean` | `b6a55545a3bc4029ca936a2c2b10f77cfeb049ee1cef38074c61db59f75c30ff` |

The final migration adds `module`, `public import`, and `@[expose] public section`, exposing the same definitions and theorem statements. I rechecked every explicit `Subgroup.normalizer (A : Set G)` and `Subgroup.normalizer (A.map f : Set H)` in the final source: these are the intended source and target subgroup normalizers, with no replacement by the normalizer of an unrelated set or subgroup. The final `articleKernelMap` domain is explicitly `↥(f.ker ⊓ Subgroup.normalizer (A : Set G))`, the carrier type of the intended ambient intersection. The explicit target subgroup argument to `QuotientGroup.eq_one_iff` in the kernel proof selects exactly `D` from this review. These elaboration repairs leave all eleven inventory judgments unchanged.

The accepted inventory is complete for these four bound files: `normalizerMap`, `normalizerMap_apply`, `normalizerMap_maps_subgroup`, `quotientMap`, `quotientMap_mk`, `quotientMap_mem_ker_iff`, `kernel_eq_image`, `articleKernelMap`, `articleKernelImage`, `articleKernelImage_eq`, and `kernel_eq_articleKernelImage`. The aggregate root file contains only the three public imports. Every declaration is accepted; none is rejected or left semantically unresolved.

Compilation provenance is explicit: the orchestrator relayed the author's warning-free compilation, and I independently checked the exact compiled-source hashes and mathematical statements; I did not run a separate compilation in this reviewer turn. The root-owned `Audit.lean` and verification script are outside this four-file statement review and are not implicitly certified by it. I did not read reviewer A's work or edit any proof source. This final binding does not expand acceptance to full Lemma 2.8, Artin-specific identities, normalizer-lift surjectivity, a first-isomorphism presentation of the kernel, the entire dependency library, or an assertion that the article theorem is false.
