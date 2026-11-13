# Independent statement and source review A

Status: **FINAL ACCEPT** of all eleven exact formal declarations in the four
hash-bound source files below. This accepts the induced-map and kernel
formalisation, with the article-specific and surjectivity limits stated below.
Date: 2026-11-14. Reviewer task: `lemma28_statement_review_a`.
Reviewer model and effort: GPT-6.1 Sol/high, independently assigned by the owner.

## Reading and scope

I read `CLAUDE.md` and `README.md` fully. I independently read the article's
extracted definitions and surrounding context on PDF pages 1, 3, 5 and 6, and
visually inspected the original PDF page-6 image at
`.research-workflow/artin-tits-normalisers-2509-21915-20261113/pages/page-6.png`.
The source is Garnier–Heng–Licata–Yacobi, *Normalisers of parabolic subgroups of
Artin–Tits groups and Tits cone intersections*, arXiv:2509.21915v3, Lemma 2.8,
equation (2.9), PDF page 6. I have not reviewed the whole article or independently
established surjectivity for its Artin–Tits normaliser quotient map.

I inspected mathlib sources in `/tmp/artin-mathlib-audit`, commit
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`, especially
`Algebra/Group/Subgroup/{Basic,Map}.lean` and
`GroupTheory/QuotientGroup/Defs.lean`. This preliminary review is a mathematical
and API-semantic review, not a claim of successful compilation of final code.

## Precise accepted mathematical statement

Let `G`, `H` be arbitrary groups, `f : G →* H`, and `A : Subgroup G`.
Put `B = A.map f`, `N = A.normalizer`, and `M = B.normalizer`.
Define the normal subgroups `AN = A.subgroupOf N` and `BM = B.subgroupOf M`.
Then `r(n) = f(n)` defines a homomorphism `r : N →* M`, and it induces

```
F : N ⧸ AN →* M ⧸ BM.
```

For `q = QuotientGroup.mk' AN` and `K = f.ker.subgroupOf N`,

```
F.ker = K.map q.
```

The image subgroup has the equivalent article-style description

```
x ∈ K.map q ↔ ∃ n : N, f (n : G) = 1 ∧ q n = x.
```

Equivalently, a source quotient class belongs to the kernel exactly when its
coset contains a representative killed by `f`. The theorem requires neither
`Function.Surjective f` nor any finiteness, Coxeter, Artin–Tits, or spherical
type hypothesis.

## Independent argument

1. Conjugation by `n ∈ N` preserves `A`; applying `f` shows conjugation by
   `f(n)` preserves `f(A) = B`. This proves that `r` has the stated codomain.
2. `A` is normal in its normaliser and `B` is normal in its normaliser. Further,
   `r(AN) ≤ BM`. Thus `F(q(n))` is the target quotient class of `f(n)`.
3. If `f(n)=1`, that target class is the identity, so `K.map q ≤ F.ker`.
4. Conversely, let `F(q(n))=1`. Then `f(n) ∈ B=f(A)`, so choose `a∈A`
   with `f(a)=f(n)`. Since `A≤N`, both `a` and `n*a⁻¹` are in `N`.
   Moreover `f(n*a⁻¹)=1` and `q(n*a⁻¹)=q(n)`. This supplies the required
   representative in `K`. No choice of preimages outside `f(A)` is used.
5. Membership in `K.map q` is precisely the displayed existential statement by
   the definition of subgroup image and subgroup restriction.

This also proves the article-style predicate is a subgroup; it need not be
postulated as an unrelated subgroup with the desired membership property.

## Translation risks and API checks

- **Ambient group of the quotients.** `G ⧸ A` is generally not a quotient group:
  `A` need not be normal in `G`. The correct source is
  `A.normalizer ⧸ A.subgroupOf A.normalizer`, with the corresponding target.
  `Subgroup.normal_in_normalizer` supplies precisely those normality instances
  (`Basic.lean:508`). Adding `[A.Normal]` or `[B.Normal]` would unnecessarily
  narrow the statement.
- **Meaning of `subgroupOf`.** `H.subgroupOf K` means `H.comap K.subtype`, so
  it represents `H ∩ K` inside the group `K`, with no assumption `H≤K`
  (`Map.lean:282–285,315`). Consequently `f.ker.subgroupOf N` correctly encodes
  `ker f ∩ N`. It does not assert that every element of `ker f` normalises `A`.
- **Normalizer image direction.** `Subgroup.le_normalizer_map`
  (`Basic.lean:477`) proves the inclusion needed for the codomain restriction
  for arbitrary homomorphisms. It does not say the restricted map is onto.
  Equality results for bijections must not be mistaken for equality results
  for surjections.
- **Target denominator.** `B` must be exactly `A.map f` (or an independently
  supplied equality with it). The weaker inclusion `A.map f≤B` constructs a
  quotient map but need not give this kernel description: the lift in argument
  step 4 requires an element of `A` mapping to `f(n)`.
- **Constructed maps.** The normaliser map must send each subtype element to
  `f` of its ambient value. The quotient map must have the representative
  formula `F(q(n)) = QuotientGroup.mk' BM (r n)`. A theorem about a different
  homomorphism named similarly would not establish the intended translation.
- **Raw kernel versus quotient kernel.** In general `r.ker` is smaller than
  `BM.comap r`. `QuotientGroup.ker_map` (`Defs.lean:333`) gives
  `F.ker = (BM.comap r).map q`, not immediately `K.map q`. The coset
  representative correction is the essential additional step.
- **Coset convention.** `QuotientGroup.mk'_eq_mk'` (`Defs.lean:104`) identifies
  `q(x)=q(y)` with `∃z∈AN, x*z=y`. This agrees with the article's `β A_J`
  notation. The correction `n*a⁻¹` works with right multiplication; normality
  also makes equivalent left-multiplication formulations valid.
- **Existence versus all representatives.** The coset need only have one
  representative in `ker f`. Requiring every representative to be killed
  would be false unless `A≤ker f`. For example, `f=id` and a nontrivial `A`
  already show that the identity quotient class can have representatives not
  killed by `f`.
- **Nested coercions.** A representative `n : N` has ambient value `(n : G)`;
  `r n : M` has value in `H`; the target quotient identity criterion is
  membership in `BM`, equivalently ambient membership in `B`. These must not
  be confused with equality `f(n)=1` before the representative correction.
- **Names and universes.** General statements should bind arbitrary group
  types, possibly in different universes. `MonoidHom` is the appropriate Lean
  homomorphism structure for groups; `Group`, rather than `CommGroup`, is the
  necessary assumption. The proof uses multiplication in its written order.
- **Choice.** The mathematical proof is existential elimination, not an
  asserted canonical section. Noncomputability or classical Lean axioms, if
  present in final code, should be reported accurately from the declarations'
  actual axiom output rather than inferred from this argument.

## Connection with the original article and limits

The article defines `N(P,J)` as the image of
`P ∩ Norm_A(A_J)` in `N(A,J)` on PDF page 3, equation (1.7). This is exactly
`K.map q` under `G =` the article's Artin–Tits group, `H=W`, `f=π`, and
formal `A = A_J`, with `π(A_J)=W_J` and `ker π=P`. Be careful that the letter
`A` has different meanings in the general theorem and the article.

The article's page-6 proof corrects `β` to `β σ_w⁻¹`, where `w=π(β)∈W_J`.
The abstract proof replaces that positive lift by any `a∈A_J` with `π(a)=w`.
It retains the essential proof step while avoiding formalisation of positive
lifts, Coxeter length, or parabolic presentations. Merely showing
`π(σ_w)=w` would not suffice for the displayed article equality: one also
needs `σ_w∈A_J`. The abstract image hypothesis records exactly that requisite
preimage-in-the-subgroup property.

The accepted theorem establishes the induced map and its kernel, and the
canonical inclusion of its image subgroup is injective. It does **not**
establish the right-hand surjectivity in the full short exact sequence (2.9).
The original page-6 proof contains the kernel computation but no explicit
lifting argument for an arbitrary normaliser quotient element. No assertion
here that the article's surjectivity is false follows from that observation;
its validity under the article's special hypotheses is outside this result.

As a boundary check, surjectivity of `f` and `f(A)=B` alone do not establish
that extra conclusion. Let `G=A₄`, `V=V₄`, `H=A₄/V≅C₃`, `f` the quotient,
and `A=⟨(12)(34)⟩`. Then `B=1` and `N_G(A)=V`, so the induced map
`V/A → C₃` is trivial and not onto. I verified this finite example by direct
enumeration of the twelve even permutations: `|A|=2`, `|V|=4`, `V` is normal,
and `N_G(A)=V`. This is a counterexample to an abstract generalisation only,
not an Artin–Tits counterexample and not evidence of a false article statement.

No source mathematical error is asserted in this preliminary review. The
surjectivity issue is retained as a scope limitation, not promoted to an
article finding without the required original-hypothesis evidence.

## Preliminary verdict

Accept the proposed general statement as a faithful formal target for the
kernel argument of Lemma 2.8, subject to checking exact final declarations and
their proof/check evidence. Do not title its accomplishment as a proof of the
whole lemma or its full short exact sequence.

## Exact declaration review

I subsequently read every declaration and proof body in
`formalizations/artin-normalisers/ArtinNormalisers/{NormalizerMap,QuotientMap,Kernel}.lean`
and the root `ArtinNormalisers.lean` import module. I did not consult another
reviewer's report. The code contains four definitions and seven theorem
declarations. All use only the shared variables `{G H : Type*}`, `[Group G]`,
and `[Group H]`; the type universes may differ. There are no extra normality,
commutativity, surjectivity, finiteness or nontriviality hypotheses.

| Declaration | Body and statement check | Source correspondence and verdict |
| --- | --- | --- |
| `normalizerMap` | Sends `n : A.normalizer` to the subtype element with ambient value `f n`; its membership proof uses `A.le_normalizer_map f` on the actual image witness `n`. Unit and multiplication proofs use subtype extensionality and the homomorphism laws of `f`. | Generalises the restricted morphism in the first paragraph of the article's Lemma 2.8 proof. Accept. |
| `normalizerMap_apply` | Precisely identifies the ambient value of the preceding map, by definitional equality. | Verifies the intended restriction, preventing an arbitrary substitute morphism. Accept. |
| `normalizerMap_maps_subgroup` | Its domain is the embedded subgroup of the source normaliser, and its target is the preimage of the embedded image subgroup. For `n` in that domain, it uses the same ambient `n` as the witness in `A.map f`. The proof `hn` means ambient membership in `A`. | Supplies the denominator containment behind the article's descent to quotients. It does not claim that `f` kills `A` before passing to the target quotient. Accept. |
| `quotientMap` | Is exactly `QuotientGroup.map` on `normalizerMap`, with both denominators as subgroups of their normalisers. The previous containment is the well-definedness proof. Normality is supplied by mathlib's normal-in-normaliser instance. | The induced morphism of Lemma 2.8, with `B=f(A)` built into the type. Accept. |
| `quotientMap_mk` | Computes on every source representative, with `normalizerMap` on the target side and the correct target denominator. Its proof is definitional equality. | The equation needed to interpret the article's `π̄(β A_J)` as `π(β)W_J`. Accept. |
| `quotientMap_mem_ker_iff` | The right side existentially quantifies `n : A.normalizer`, requires its quotient class to be the supplied `x`, and requires ambient equality `f (n : G)=1`. The forward proof obtains a representative `g`, changes target-quotient triviality into `f g∈A.map f`, obtains `a∈A` with `f a=f g`, embeds `a` into the normaliser, and constructs `g*a⁻¹`. It proves both equal quotient class and ambient kernel membership. The reverse proof sends the killed representative to the target denominator using its unit element. | This is the precise article-style coset predicate and the complete kernel argument of the second paragraph, with an arbitrary subgroup lift in place of the positive lift `σ_w`. Accept. |
| `kernel_eq_image` | An equality of subgroups of the same source normaliser quotient. Extensionality and the previous iff turn both sides into the same existential; only the order of the two conjuncts changes. Membership in `f.ker.subgroupOf A.normalizer` definitionally means ambient `f n=1`. | Identifies the kernel with the image of the pure-kernel intersection, as in (1.7) and the end of the Lemma 2.8 proof. Accept. |
| `articleKernelMap` | Its domain is explicitly the ambient subgroup `f.ker ⊓ A.normalizer` of `G`. The inner homomorphism embeds its subtype into `A.normalizer` using exactly the second membership conjunct; composition with the quotient homomorphism then takes its quotient class. No injectivity of this map is claimed. | Gives an independent map realising the image in the article's definition, without defining that image to be the desired kernel. Accept. |
| `articleKernelImage` | Is the `range` subgroup of the preceding actual homomorphism. It is not defined as `(quotientMap f A).ker`. | Directly encodes the image-based definition of `N(P,J)` in equation (1.7). Accept. |
| `articleKernelImage_eq` | The two directions explicitly repackage an element of the ambient intersection as an element of the kernel subgroup inside the normaliser, and conversely. First membership conjunct gives `f n=1`; second gives normaliser membership. The quotient value is preserved by definitional equality. | Checks that the two legitimate encodings of the article's image agree; no substantive theorem is assumed under a change of notation. Accept. |
| `kernel_eq_articleKernelImage` | Rewrites the independent image definition with `articleKernelImage_eq`, then applies `kernel_eq_image`. Its conclusion is precisely equality of the two subgroups. | The kernel conclusion in the article's explicit ambient-intersection notation. Accept. |

The root module contains only the three expected imports and no additional
definitions, assumptions or claims. The code inspected has `autoImplicit=false`
in every implementation module and in its project options. The inspected
`lakefile.toml`, `lake-manifest.json` and `lean-toolchain` agree on mathlib commit
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9` and Lean `v4.36.0-rc2`.

The proofs visibly preserve multiplication order and use only the precise
quotient equivalence needed. In particular, `hfa : f a = f g` is used to prove
`f(g*a⁻¹)=f g*(f g)⁻¹=1`; no commutative rearrangement is hidden. The
existential coset formulation is proved directly, and the separate image
description is independently built, avoiding circular definition of the
article's subgroup as the quotient kernel.

Initial exact-code semantic verdict: accept all eleven declarations as the
intended generalisation of the induced-map and kernel portion of Lemma 2.8.
No substantive signature or definition changes were requested.

## Final revision, verification and disposition

After the author's compiled-revision notice, I independently reread all four
final source files in full and computed their SHA-256 hashes. They agree with
the notice:

| File relative to `formalizations/artin-normalisers/` | SHA-256 |
| --- | --- |
| `ArtinNormalisers.lean` | `ad0b9f18a334eed2aa41c85618bb635ddf2cfefcd5947a79264fa7e618962461` |
| `ArtinNormalisers/NormalizerMap.lean` | `5ea6d9a6b7add5ea6d20a3a3fe225ac1094ab28d31d4515e04088b99bc1124d9` |
| `ArtinNormalisers/QuotientMap.lean` | `544b3a7f491df63d313d75b7b8a87c201f6d90f8838d4979a498ccefa3677eb6` |
| `ArtinNormalisers/Kernel.lean` | `b6a55545a3bc4029ca936a2c2b10f77cfeb049ee1cef38074c61db59f75c30ff` |

The final revision replaces shorthand normaliser expressions by explicit
`Subgroup.normalizer (A : Set G)` and
`Subgroup.normalizer (A.map f : Set H)`, makes the type coercion on the ambient
intersection explicit with `↥`, and specifies the target denominator parameter
in the forward `QuotientGroup.eq_one_iff` application. These are the same
subgroups, types and proof steps reviewed above, with their coercions visible.
The module migration adds `module`, `public import` and
`@[expose] public section`. It does not add mathematical assumptions or alter
the conclusion. All four definitions and all seven theorem declarations in the
inventory have final disposition **ACCEPT** at these exact hashes.

I independently ran, from the package directory:

- `lake build ArtinNormalisers`: exit 0, `Build completed successfully (1914 jobs).`
  This was an ordinary build in the existing package environment, not an
  independently performed clean rebuild.
- `lake env lean Audit.lean`: exit 0. Its `#check` commands displayed all eleven
  expected declarations with independent type universes and only group
  hypotheses. Its transitive axiom audit reported
  `Audited 24 project declarations; axiom allowlist passed`, including generated
  auxiliary proof declarations.

I read the actual `Audit.lean` body: it enumerates declarations whose root
namespace is `ArtinNormalisers`, runs `Lean.collectAxioms` on each, rejects an
empty audit, and rejects every axiom outside `propext`, `Classical.choice`, and
`Quot.sound`. The observed axiom lists contain only those three axioms or
subsets of them. In particular the accepted core theorems transitively use
`Classical.choice`; I do not claim a choice-free Lean artifact. This is a
trusted-Lean-environment check, not an independent implementation of the kernel
or a fresh replay of all imported mathlib proofs. I did not independently run
`leanchecker`; any such evidence belongs to the owner's verification record.

The exact final formal statements faithfully capture the article's induced
homomorphism and kernel argument, and the independently constructed image
subgroup agrees with the existential coset predicate through the accepted
theorems. The article's Artin–Tits and Coxeter groups, their specific parabolics,
the equalities `π(A_J)=W_J` and `ker π=P`, and the positive-lift construction
are not formalised here. Nor is surjectivity of the normaliser quotient map.
Accordingly this is acceptance of the general kernel argument underlying
Lemma 2.8, not of a formal proof of its entire short exact sequence or the
article's other results. No original-article mathematical error is asserted.
