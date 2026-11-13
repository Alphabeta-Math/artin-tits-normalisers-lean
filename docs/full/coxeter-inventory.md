# Coxeter and Artin suppliers for the full Lemma 2.8

Research date: 2026-11-14. This records a source inventory, an implementation
architecture, and the subsequent implementation of the Coxeter normalizer
helpers requested by the parent task. It does not certify the entire article
lemma, supplier axiom audit, or kernel replay. The inventory phase changed no
proof-package source, dependency checkout, cache, or toolchain. The subsequent
implementation changed only the new local `CoxeterNormalizer.lean` module.
Read `CLAUDE.md` and `README.md` in full first.

## Implemented local helper module

`formalizations/artin-normalisers/ArtinNormalisers/Artin/CoxeterNormalizer.lean`
now proves the following, for arbitrary `cs : CoxeterSystem M W`, set `J`,
and group element `d`, with no finiteness hypothesis:

- `ArtinNormalisers.Coxeter.minimal_inv_of_mem_normalizer`;
- `ArtinNormalisers.Coxeter.exists_conjugate_simple_of_minimal`;
- `ArtinNormalisers.Coxeter.exists_inverse_conjugate_simple_of_minimal`;
- `ArtinNormalisers.Coxeter.isReduced_append_simple_of_minimal`;
- `ArtinNormalisers.Coxeter.isReduced_prepend_simple_of_minimal`;
- `ArtinNormalisers.Coxeter.exists_minimal_normalizer`.

The actual command `lake build ArtinNormalisers.Artin.CoxeterNormalizer`
passed against the unchanged package pin; its success is recorded in
`formalizations/artin-normalisers/evidence/full-development/coxeter/build-3.log`.
The previous two failed elaboration attempts remain in `build-1.log` and
`build-2.log`. The correction uses the public
`CoxeterSystem.isMinimalCosetRep_iff` API instead of unfolding the provider's
sealed `IsMinimalCosetRep` definition. The parent task owns the complete
supplier/package axiom audit and kernel replay; none is asserted here.

## Baseline and recommendation

The existing package pins Lean `v4.36.0-rc2` and mathlib
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. Its actual Coxeter source
directory contains exactly `Matrix.lean`, `Basic.lean`, `Length.lean`, and
`Inversion.lean`. These provide presentation-based `CoxeterMatrix.Group`,
`CoxeterSystem`, `simple`, `wordProd`, length, reduced expressions, descents,
reflections, and inversion sequences. They do not contain exchange,
standard parabolic/minimal-coset theory, Matsumoto, or an Artin presentation.
This conclusion is from the checked-out `.lean` sources and declaration
searches, not the mathlib README or TODO comments alone.

The best candidate found is
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti/tree/62bbc0596dc3539d488232e4e924a338548ea0a9),
SHA `62bbc0596dc3539d488232e4e924a338548ea0a9`, inspected at
`/tmp/full28-tauceti`. It has the same Lean toolchain, `v4.36.0-rc2`, and
Apache-2.0 licensing. Its manifest pins a different mathlib,
`e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`. Source compatibility with the
package's existing mathlib must therefore be established by an actual build;
the common Lean version does not establish it. The parent task owns that
build and any vendoring/migration decision. The small relevant source closure
should be tested against the existing pin before contemplating a pin change.

Unlike the earlier candidate, TauCeti uses mathlib's existing explicit
`cs : CoxeterSystem M W` throughout, rather than requiring a second bundled
Coxeter-group typeclass. Its exact sources supply all the major Coxeter
inputs and the standard Artin presentation. What remains is the
article-specific normalizer-lifting proof and its connection to the already
proved generic quotient/kernel theorem.

## Exact source inventory

All TauCeti paths below are relative to the repository at the stated SHA.
The linked lines are the inspected source locators.

| Required ingredient | Actual supplier | Scope and relevant dependencies |
| --- | --- | --- |
| Coxeter presentation, words, simple involutions, braid equality | Pinned mathlib `Mathlib/GroupTheory/Coxeter/Basic.lean`; `CoxeterSystem.wordProd_braidWord_eq` at line 507 | `CoxeterSystem M W` records an isomorphism with the presented Coxeter group. A zero matrix entry means infinity. |
| Reduced expressions and length | Pinned mathlib `Mathlib/GroupTheory/Coxeter/Length.lean`; `exists_isReduced` line 83, `length_inv`, `length_mul_le`, `length_simple`, `length_mul_simple` line 178 | No finite-rank or finite-group hypothesis. Reducedness is the length equation. |
| Strong exchange and deletion | [TauCeti `StrongExchange.lean`](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/StrongExchange.lean#L433): `CoxeterSystem.strongExchange`, `strongExchange_right`, `exchangeCondition` line 454, `exchangeCondition_right`, `deletionCondition` line 527, `exists_isReduced_sublist` line 569 | Imports mathlib inversion theory and TauCeti `Basic`. The exchange proof constructs a reflection cocycle; it does not assume exchange as an axiom. Strong exchange permits an unreduced input word; the simple-reflection exchange variants add reducedness of the deleted word. |
| Standard parabolic subgroup | [TauCeti `Parabolic.lean`](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Parabolic.lean#L115): `CoxeterSystem.parabolic J := Subgroup.closure (cs.simple '' J)` | `simple_mem_parabolic`, `parabolic_le_iff`, `wordProd_mem_parabolic`, `exists_wordProd_eq_of_mem_parabolic`. |
| Reduced words in the defining indices | Same file, [line 192](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Parabolic.lean#L192): `exists_isReduced_wordProd_eq_of_mem_parabolic` | For `w ∈ P`, returns `ω`, reducedness, every letter in `J`, and `cs.wordProd ω = w`. This stronger index-level existence statement is useful even though the theorem about an arbitrary reduced word only concludes its simple reflections belong to `P`. |
| Minimal representatives | Same file, [line 256](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Parabolic.lean#L256): `IsMinimalCosetRep J u := ∀ v ∈ P, ℓ u ≤ ℓ (u*v)`; `exists_isMinimalCosetRep` line 263 | For every `w`, returns `v ∈ P` with `w*v` minimal. The coset orientation is explicit: multiplication by `P` on the right. |
| Parabolic length additivity | Same file, [line 307](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Parabolic.lean#L307): `length_mul_of_isMinimalCosetRep hu hv` | Gives `ℓ(u*v)=ℓ u+ℓ v`. Derived from exchange; no Matsumoto or geometric representation. The file additionally proves unique factorization, a chosen minimal representative, and the left-descent version of additivity. |
| Dihedral input to Matsumoto | TauCeti `Dihedral.lean`: `exists_wordProd_alternatingWord_mul_of_isLeftDescent_pair` | Imports `Parabolic`. Gives the rank-two factorization and length used in Matsumoto's different-head induction. |
| Exact orders of simple products | TauCeti `Geometric/Basic.lean`: `CoxeterSystem.orderOf_simple_mul_simple` line 521; `simple_injective` line 527 | Constructs the geometric representation, proving rank-two orders. Imports two TauCeti trigonometry files as well as mathlib. Needed by TauCeti's Matsumoto proof; our subsequent normalizer argument does not additionally require injectivity. |
| Braid relation on words | TauCeti `BraidEquivalence.lean`: `CoxeterSystem.IsBraidMove`, `BraidEquivalent`, `BraidEquivalent.prod_map_eq` | Relation generated by replacement in arbitrary prefix/suffix context; monoid-valued soundness proved directly. |
| Matsumoto | [TauCeti `Matsumoto.lean`](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Matsumoto.lean#L83): `TauCeti.braidEquivalent_of_isReduced_wordProd_eq`; monoid-valued `TauCeti.matsumoto` line 136 | For two reduced words with equal Coxeter product and a family satisfying braid relations, their evaluated products agree. Imports `BraidEquivalence`, `Dihedral`, `Geometric/Basic`. The inspected proof is induction on word length using common-head cancellation and the rank-two bridge. |
| Universal reduced-word lift | Same file, [line 192](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Matsumoto.lean#L192): `TauCeti.existsUnique_reducedWordLift` | Returns a unique function `F : W → G` agreeing with every reduced expression. It is a function, not a group homomorphism. Instantiating with Artin generators defines the canonical positive lift locally. |
| Actual Artin braid presentation | [TauCeti `Artin.lean`](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Artin.lean#L117): `TauCeti.ArtinGroup M := PresentedGroup (artinRelationsSet M)`; `ArtinGroup.gen`; `prod_map_gen_braidWord` line 153 | The relator is the quotient of the two braid-word products in `FreeGroup B`. Diagonal entries give trivial relators, and a zero entry gives two empty words. No unintended square relation is imposed. Imports TauCeti `Basic` and mathlib order-of-element theory. |
| Canonical map `π` | Same file, [line 269](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/GroupTheory/Coxeter/Artin.lean#L269): `ArtinGroup.toCoxeterGroup cs`, `toCoxeterGroup_gen`, `toCoxeterGroup_surjective` | Obtained from the presented-group universal property and Coxeter braid equality. No normalizer lifting is asserted here. |

The complete immediate TauCeti module closure needed by these imports is:

```text
GroupTheory/Coxeter/Basic
GroupTheory/Coxeter/StrongExchange
GroupTheory/Coxeter/Parabolic
GroupTheory/Coxeter/Dihedral
GroupTheory/Coxeter/BraidEquivalence
GroupTheory/Coxeter/Geometric/Basic
GroupTheory/Coxeter/Matsumoto
GroupTheory/Coxeter/Artin
Analysis/SpecialFunctions/Trigonometric/Angle
Analysis/SpecialFunctions/Trigonometric/Bounds
```

`Geometric/Basic` imports the last two files privately, but they are still
build dependencies. At inspection time those two files were absent from the
parent's sparse working tree; their contents were not inspected by this task.
Any further dependencies of those files must be included by the parent
supplier audit. This list is the closure visible from the inspected Coxeter
files, not a claim that their trigonometry import closure was audited.

## Missing local work: an explicit implementable proof chain

Let `A = TauCeti.ArtinGroup M`, let `P = cs.parabolic J`, let
`A_J = Subgroup.closure (ArtinGroup.gen M '' J)`, and set
`π = ArtinGroup.toCoxeterGroup cs`. No spherical, finite-rank, or finite-group
assumption is needed for the following argument.

1. **Image of the standard Artin subgroup.** Prove `A_J.map π = P` by
   `MonoidHom.map_closure` (pinned mathlib
   `Algebra/Group/Subgroup/Map.lean:582`) and `toCoxeterGroup_gen`.
   No theorem saying the abstract Artin group on `J` embeds into `A` is
   required: both subgroups are defined as generated subgroups in the ambient
   groups, matching the article's standard subgroups.

2. **Minimality on both sides for normalizers.** Suppose
   `x ∈ N_W(P)` and `hmin : cs.IsMinimalCosetRep J x`. Prove
   `cs.IsMinimalCosetRep J x⁻¹`. For `z ∈ P`, normalizer membership gives
   `x⁻¹*z⁻¹*x ∈ P`; apply `hmin` to this element and use
   `ℓ(x⁻¹*z)=ℓ(z⁻¹*x)` and group simplification. Because TauCeti's public
   `IsMinimalCosetRep` definition is sealed across modules, the implemented
   proof uses the equivalent absence of right descents: a right descent of
   `x⁻¹` is a left descent `i` of `x`, while additivity for the parabolic
   element `x⁻¹*s_i*x` would force `ℓ(s_i*x) ≥ ℓ x`, a contradiction.
   This is a proved local lemma, not a hypothesis on the final theorem.

3. **A minimal normalizer permutes the simple generators in `J`.** For
   `i ∈ J`, set `c=x*s_i*x⁻¹ ∈ P`. Right additivity gives
   `ℓ(x*s_i)=ℓ x+1`. Additivity for `x⁻¹` and `c⁻¹`, followed by inversion,
   gives `ℓ(c*x)=ℓ c+ℓ x`. Since `c*x=x*s_i`, arithmetic gives `ℓ c=1`.
   Use `exists_isReduced_wordProd_eq_of_mem_parabolic` on `c`; its reduced
   `J`-word has length one and hence is `[j]` for some `j ∈ J`. Thus
   `x*s_i=s_j*x`. Repeat this lemma for `x⁻¹` to obtain the reverse
   existence statement. This avoids proving an entire normalizer complement
   structure or proving index membership from simple-reflection injectivity.

4. **A reduced-word Artin lift of the minimal normalizer normalizes `A_J`.**
   Choose a reduced word `α` of `x` and let
   `a=(α.map (ArtinGroup.gen M)).prod`. For the `i,j` from step 3,
   both `α ++ [i]` and `[j] ++ α` have Coxeter product `x*s_i=s_j*x`.
   Their common length is `ℓ x+1`; right additivity shows both are reduced.
   Apply `TauCeti.matsumoto cs (ArtinGroup.gen M)` with
   `ArtinGroup.prod_map_gen_braidWord M` to get
   `a*σ_i=σ_j*a`, hence `a*σ_i*a⁻¹=σ_j`.
   Applying step 3 to `x⁻¹` gives, for every `j ∈ J`, a suitable `i ∈ J`,
   so the same equations also give `a⁻¹*σ_j*a=σ_i`. Extend both inclusions
   from generators to the subgroup closure. Pinned mathlib's
   `Subgroup.mem_normalizer_iff_map_conj_eq`
   (`Algebra/Group/Subgroup/Basic.lean:409`) and `MonoidHom.map_closure`
   are suitable APIs. Consequently `a ∈ N_A(A_J)` and `π a=x`.

   **Important convention:** the positive lift of `x⁻¹` need not equal
   `a⁻¹`. Use inverse conjugation at the Coxeter level to obtain the
   generator equations for the same `a`. Do not silently identify these
   two Artin elements.

5. **Lift an arbitrary normalizer element.** For `w ∈ N_W(P)`, choose
   `v ∈ P` such that `x=w*v` is minimal, using
   `exists_isMinimalCosetRep`. Since `P ≤ N_W(P)`, the element `x` still
   normalizes `P`. Step 4 gives its Artin normalizer lift `a`. Choose a
   word in `J` for `v⁻¹` using `exists_wordProd_eq_of_mem_parabolic`;
   evaluating that word in Artin generators gives `b ∈ A_J` with
   `π b=v⁻¹`. Then `a*b ∈ N_A(A_J)` and `π(a*b)=w`.
   This proves surjectivity of the restricted normalizer map, which is
   stronger than the quotient-surjectivity statement needed by the lemma.
   Equivalently factor `w=x*y` with `y=v⁻¹`.

6. **Connect to the existing package.** Instantiate `normalizerMap π A_J`
   and `quotientMap π A_J`, rewriting `A_J.map π=P` by step 1. Step 5
   gives normalizer-map surjectivity. Quotient-map surjectivity follows by
   choosing a quotient representative and then its normalizer lift. The
   existing `kernel_eq_image` / `kernel_eq_articleKernelImage` supplies
   the kernel identification, with pure Artin group defined as `π.ker`.
   This final theorem must expose the actual Artin presentation and its
   canonical `π`, with the lifting result proved, rather than quantify
   over an assumed lifting or normalizer-decomposition hypothesis.

An optional canonical `positiveLift : W → A` can be defined from
`existsUnique_reducedWordLift`. Its independence from reduced expression
and the formula `π (positiveLift w)=w` follow from that supplier and word
evaluation. For the existence proof above, choosing one reduced word per
minimal element already suffices and avoids introducing an unnecessary
global definition. Neither route changes the standard Artin group.

## Earlier candidate and bounded search limits

The earlier checkout `/tmp/artin-lean-coxeter-audit` is
[mlyean/lean-coxeter](https://github.com/mlyean/lean-coxeter/tree/8d36c58a038cc0642a46cf5165a1b0660348f105),
SHA `8d36c58a038cc0642a46cf5165a1b0660348f105`, Lean `v4.35.0`, mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Apache-2.0. Its actual
`Coxeter/StrongExchange.lean` proves `Coxeter.strong_exchange` at line 51,
`exchange_property`, `deletion_property`, `exists_reduced_subword`, and
right variants. The proof imports `PermutationRepresentation`, which imports
its own `Coxeter.Basic` typeclass wrapper. `GeometricRepresentation` proves
simple-product orders and injectivity. The repository also contains Bruhat
order, but searches of all its Coxeter sources found no parabolic,
Matsumoto, normalizer, or Artin braid-presentation development. It is therefore
a substantially poorer base than TauCeti for this task.

A web search for Lean Coxeter/Matsumoto/Artin declarations also found
`openai/math/lean/ComparatorChallenges/ArtinParabolicIntersections.lean`.
The fetched current file defines an Artin presentation and standard subgroup,
but its four mathematical endpoints explicitly end in `sorry`; it is a
statement fixture, not a reusable completed proof supplier. No formal result
from it is accepted. Its current main revision was not bound by this task,
so it is not proposed as a dependency even for its definitions.

Search results and source inspection are bounded evidence. This task did not
prove that no other suitable library exists, compile either external
repository, audit their elaborated axioms, or replay their kernels. No
mathematical error was established in the inspected external proofs. A
missing library result, a different dependency pin, or a challenge statement
containing `sorry` is not a claim of a literature error.
