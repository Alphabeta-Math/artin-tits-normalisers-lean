# Full Lemma 2.8: mathematical route and formal obligations

Date: 2026-11-14. This is a source-reading and mathematical dependency report,
not a compilation, axiom audit, kernel replay, or acceptance of an external Lean
package. No proof files were changed for this report.

## Exact target and source correspondence

The source is Garnier–Heng–Licata–Yacobi, arXiv:2509.21915v3, PDF p.6,
Lemma 2.8, with definitions (1.2), (1.7), and §2.2–2.3, PDF pp.2–5. I read
these passages in the frozen extraction
`.research-workflow/artin-tits-normalisers-2509-21915-20261113/article.txt`,
including its explicit PDF-page markers. I have not independently checked the
PDF image in this task.

The complete algebraic statement is the existence of the standard induced map
and the short exact sequence

`1 → N(P,J) → N_A(A_J)/A_J → N_W(W_J)/W_J → 1`,

where `P = ker π` and `N(P,J)` is the **image** of
`P ∩ N_A(A_J)` under the quotient projection. Its arrow is subgroup inclusion.
It is not a quotient of all of `P` by `A_J`, and the first arrow is not the
generally noninjective projection from `P ∩ N_A(A_J)` itself.

The source fixes arbitrary `J` in §2.3; §2.2 explicitly postpones the
spherical assumption to §§5–6. Neither finiteness of `W_J` nor finite type can
be imposed on this lemma. The proof below also works for an arbitrary index
type `B`, including infinite rank. The portal's authored statement is finite
rank; extending it removes its use of finiteness rather than weakening it.

The article defines `A` topologically as `π₁(Xᶜ/W,Z)` on PDF p.5, then
explicitly states that `A` also has the standard Artin presentation, referring
to Van der Lek [30]. An unconditional Lean theorem for the standard
presentation-defined Artin group formalizes the full **algebraic** lemma.
Documentation must say that the equivalence with the source's topological
model is not itself formalized unless an actual Lean construction proves it.
No topology, covering-space theorem, or K(π,1) theorem is logically necessary
for the algebraic statement.

## A root-free proof of normalizer lifting

Use a Coxeter system `(W,(s_i)_{i∈B})`, a subset `J ⊆ B`, and
`H = W_J = ⟨s_i : i∈J⟩`. Write `ℓ` for minimum word length. In this report
`wH` is a left coset, whose elements are obtained by right multiplication.

1. Given `w ∈ N_W(H)`, choose `v ∈ H` such that `d = wv` has minimum
   length in `wH`. This requires only well ordering of natural numbers.
   Then `d ∈ N_W(H)`, and `dH = Hd`.

2. Minimality gives the standard length-additivity property
   `ℓ(du) = ℓ(d)+ℓ(u)` for every `u∈H`. The inverse `d⁻¹` also has minimum
   length in its own left coset: if `u∈H`, then
   `ℓ(d⁻¹u)=ℓ(u⁻¹d)`, and `u⁻¹d = d(d⁻¹u⁻¹d)∈dH`, so this is at least
   `ℓ(d)=ℓ(d⁻¹)`. Thus the same length-additivity applies to `d⁻¹`.

3. For `i∈J`, put `u=d⁻¹s_i d∈H`. The equality `du=s_i d` gives
   `ℓ(d)+ℓ(u)=ℓ(s_i d)≤ℓ(d)+1`. Since `s_i≠1`, also `u≠1`, hence
   `ℓ(u)=1`. Every parabolic element has a reduced word with letters in
   `J`; consequently `u=s_j` for some `j∈J`. The same argument for `d⁻¹`
   gives `d s_i d⁻¹=s_k` for some `k∈J`.

4. These two inclusions show that conjugation by `d` maps the set of simple
   generators of `H` onto itself. No finite-set argument or injectivity of
   the index map `i↦s_i` is needed. Moreover `ℓ(s_i d)=ℓ(d)+1` and
   `ℓ(d s_i)=ℓ(d)+1` for `i∈J`: either follows from the corresponding
   length-additivity and the conjugation equalities (or minimality and the
   standard length ±1 lemma).

5. Fix one reduced word `δ` for `d`, and let `β` be its product in the
   Artin generators. If `s_i d=d s_j`, both words `[i]++δ` and
   `δ++[j]` are reduced and have the same Coxeter product. Matsumoto's
   theorem, evaluated in the Artin group, yields `σ_i β=β σ_j`.
   Applying both conjugation inclusions from step 3 shows
   `β A_J β⁻¹=A_J`. Thus `β∈N_A(A_J)` and `π(β)=d`.

6. Since `π(A_J)=H`, choose `a∈A_J` with `π(a)=v⁻¹`. Then
   `βa∈N_A(A_J)` and `π(βa)=dv⁻¹=w`. Therefore the map on normalizers
   itself is surjective; a fortiori the induced map on their quotients is
   surjective. For quotient surjectivity alone, `β` already lifts the coset
   `wH=dH`.

The reverse normalization inclusion in step 5 uses the relation for `d⁻¹`
to identify a generator `j` with `s_i d=d s_j`, and evaluates those words
using the **same** `δ`. It does not assert the generally false identity
`σ_(d⁻¹) = σ_d⁻¹`. Positive lifts are a set-theoretic section, not a group
homomorphism.

Together with the existing `kernel_eq_articleKernelImage` and injectivity of
subgroup inclusion, this proves every part of the short exact sequence. A
theorem whose hypotheses assume normalizer lifting, surjectivity on these
quotients, or a length-additive section does not by itself complete Lemma 2.8.

## Why length additivity needs no geometric representation

For completeness the required parabolic lemma follows directly from ordinary
exchange. Every `u∈H` has a reduced word in `J`, by deletion of pairs from any
`J`-word. Induct on such a reduced word `i::α` for `u`, and suppose `α++δ`
is reduced by induction. If adding `i` on the left caused a descent, exchange
deletes one letter of `α++δ`. A deletion in `α` would yield an expression
for `u` shorter than its reduced word, after cancelling `d`. A deletion in
`δ` would give a shorter element `d'` of `Hd=dH`: algebraically
`d' = (wordProd α)⁻¹ s_i (wordProd α) d`. This contradicts minimality.
Hence the concatenation is reduced, proving additivity. This argument uses
only finite words even when `J` or `B` is infinite.

Independently read textbook support is available locally in
`research/physics-algebras-planning-2026-10-17/sources/05-hecke/`:

- Björner–Brenti, *Combinatorics of Coxeter Groups*, Proposition 2.4.1,
  printed p.39: reduced parabolic words and equality of ambient/parabolic
  length; Proposition 2.4.4 and Corollary 2.4.5, printed p.40 (PDF p.49):
  parabolic factorization, additive lengths, and unique minimal left-coset
  representatives. The relevant complete proof passages were read in the
  extracted `bjorner-brenti-coxeter-book.txt`.
- Theorem 3.3.1(ii), printed p.76 (PDF p.85), and its proof: any two reduced
  expressions are connected by braid moves. Its proof uses the rank-two
  weak-order join property; citing its name does not make this dependency
  available in Lean. I read this theorem and proof, including the conclusion
  of part (i) on printed p.77.

No unproved mathematical claim is being presented as an open problem here.
The missing work, when an API is unavailable, is formal authoring of
established results.

## Precise formal dependency chain

1. **Standard presentations.** Define the Artin group as a `PresentedGroup`
   with relations equating the two braid-word products. Define `σ_i` and
   prove its braid relations from the quotient presentation. For a
   `CoxeterMatrix`, entry `0` means infinite order/no relation; its two
   zero-length braid words are both empty, so adding their equality is
   harmless. The diagonal relation is tautological as well.
2. **Projection.** Apply the presented-group universal property to
   `i↦s_i`. Mathlib's `CoxeterSystem.wordProd_braidWord_eq` proves that all
   defining Artin relations hold in `W`. Prove `π(σ_i)=s_i`.
3. **Parabolics.** Define `A_J = Subgroup.closure (σ '' J)` and identify
   `A_J.map π` with `cs.parabolic J`, using subgroup closure and generator
   formulas. No theorem that the abstract Artin group on `J` embeds in `A`
   is necessary: the statement uses the actual generated subgroup.
4. **Minimal representatives.** Use minimal-coset existence, parabolic
   length additivity, inverse minimality for normalizers, and a reduced
   `J`-word for every element of `W_J`. Prove step 3 above as a local
   normalizer-generator lemma.
5. **Word evaluation.** Use Matsumoto in its monoid-valued evaluation form.
   Apply it directly to the chosen word for `d`. A global positive lift is
   optional; Artin-monoid cancellativity, monoid-to-group injectivity,
   Garside structure, root systems, and ribbon groupoids are unnecessary.
6. **Normalizer lift and quotient surjectivity.** Prove the actual lifting
   statement, then surjectivity of the concrete induced quotient map, with
   the `A_J.map π = W_J` transport explicitly checked.
7. **Exactness.** Reuse `ArtinNormalisers.kernel_eq_articleKernelImage` in
   `formalizations/artin-normalisers/ArtinNormalisers/Kernel.lean`. Define
   the source `N(P,J)` by that image subgroup and use its inclusion. Prove
   its image is the kernel and that inclusion is injective.

## Inspected Lean availability and limits

The current project pins mathlib
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9` and Lean `v4.36.0-rc2`.
Its actual source files provide:

- `Mathlib/GroupTheory/Coxeter/Basic.lean`: Coxeter presentations,
  `wordProd`, append/cons/reverse formulas, braid words, and
  `wordProd_braidWord_eq` (line 507). Its introductory TODO explicitly
  lists Matsumoto (line 78). Its `injective_simple` declaration concerns
  the map **from Coxeter-system structures to their simple functions**;
  it does not prove the generator-index map injective.
- `.../Length.lean`: `exists_isReduced` (line 83),
  `length_inv` (105), `length_mul_le` (114), `length_simple` (149),
  `length_eq_one_iff` (159), `length_mul_simple` (178),
  `length_simple_mul` (185), descent/inverse translations, and reduced
  prefix/suffix facts. A search of this Coxeter directory found no
  parabolic or Matsumoto supplier.

The isolated `/tmp/artin-lean-coxeter-audit` is revision
`8d36c58a038cc0642a46cf5165a1b0660348f105`, pinned to Lean/mathlib
`v4.35.0`. I read `Coxeter/StrongExchange.lean`, the introductory and
relevant construction sections of `Basic.lean` and
`PermutationRepresentation.lean`, and searched all its Coxeter sources.
Available source declarations include `Coxeter.exchange_property` (line 60),
`deletion_property` (82), and `exists_reduced_subword` (105).
Strong exchange imports the combinatorial permutation representation, not
the real geometric representation. No Matsumoto or parabolic library was
found there. Its separate geometric representation proves generator
injectivity and the exact order of products of two generators. This report
does not claim its build compatibility, axiom closure, or kernel replay.

The root subsequently identified `/tmp/full28-tauceti`, revision
`62bbc0596dc3539d488232e4e924a338548ea0a9`. It uses the same Lean toolchain
but its manifest pins a different mathlib revision,
`e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`; version compatibility must be
actually checked. I read these precise provider declarations and their proof
bodies, without compiling them:

- `TauCeti/GroupTheory/Coxeter/Parabolic.lean`: `cs.parabolic` (115),
  `exists_isReduced_wordProd_eq_of_mem_parabolic` (192),
  `IsMinimalCosetRep` (256), `exists_isMinimalCosetRep` (263),
  `length_mul_of_isMinimalCosetRep` (307), and
  `length_mul_of_forall_not_isLeftDescent` (507). The relevant declarations
  have arbitrary `B`, `W`, and `J`; nearby declarations with `[Fintype W]`
  do not add that hypothesis to these declarations. Its length-additivity
  proof is the exchange argument above, in the right-handed orientation.
- `.../Matsumoto.lean`: `TauCeti.matsumoto` (136) accepts any monoid-valued
  generator map satisfying the braid equalities, and two reduced words with
  equal Coxeter products. This exactly supplies step 5. The stronger
  `existsUnique_reducedWordLift` (192) is optional. The file imports braid
  equivalence, dihedral, and geometric foundations; although the final
  argument is root-free, this provider's actual transitive proof of ordinary
  Matsumoto still uses its geometric representation to identify rank-two
  orders. That dependency must not be omitted from the audit description.

No source-level `sorry` or new axiom was found in these two inspected
TauCeti files. This narrow observation is not a transitive axiom audit and
does not certify the package. Provider source inspection, citation, and
successful compilation are separate from the required full build,
transitive-axiom allowlist, and kernel-replay checks.

## Existing portal proof and source findings

I read the full authored portal item
`../prestige-math-library/research-portal/artin-tits-normalisers-2509-21915/items/lem-normaliser-exact-artin-tits-normalisers.md`
and its positive-lift and generic normalizer suppliers. The item is explicitly
an `ai-generated` proof; it supplies an informal route, not a formal Lean
dependency or independent published evidence. Its finite-rank proof chooses
a distinguished double-coset representative, uses a parabolic-intersection
theorem to obtain generator conjugation, and uses finiteness to get a
permutation. That route is sound under its stated finite-rank hypotheses;
the length argument here removes the double-coset intersection and finite-set
dependencies. This is a justified simplification, not adoption of an unread
literature proof.

The original p.6 proof proves the map and its kernel but supplies no explicit
argument for the terminal surjectivity. Ambient surjectivity alone would
not justify that inference. This is the known missing-proof-step issue
that motivates the full formalization; the argument above supplies it for
the actual Artin–Coxeter projection. It is not a counterexample to the
lemma or a newly established false theorem. No additional mathematical
error was established in the inspected textbook, provider source passages,
or portal proof. The topological/presentation equivalence was not read in
Van der Lek's original thesis and is not independently source-certified here.
