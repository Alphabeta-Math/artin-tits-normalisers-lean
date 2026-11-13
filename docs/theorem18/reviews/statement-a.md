# Theorem 1.8: independent statement acceptance contract A

Date: 2026-11-14. Reviewer: GPT-6.1 Sol/high, independently assigned task
`lemma28_statement_review_a`. Status: **preliminary target contract only**.
No new Theorem 1.8 proof or supplier has yet received final acceptance.
Historical Lemma 2.8 reviews remain unchanged. I have not consulted another
reviewer's report or modified mathematical code or dependency caches.

## Reading actually performed

In the dedicated repository I read `README.md` fully and `docs/full/REPORT.md`,
including its express limitation: the existing result is the full algebraic
Lemma 2.8 for the actual Artin braid presentation, while its equivalence with
the article's topological Artin-group model is not formalised. This repository
has no root `CLAUDE.md` or `AGENTS.md` in the inspected file inventory; no such
file was read here. The earlier workflow-repository instructions and old reviews
have not been copied into new mathematical assumptions.

For arXiv:2509.21915v3 I independently reread the frozen article extraction
from the sibling workflow repository, including:

- Theorem 1.8, its two short exact sequences and definitions (1.2), (1.5)–(1.7),
  PDF pp.1–3.
- §2.2–2.3, PDF pp.4–6: the standard geometric and contragredient
  representations, reflection hyperplanes, topological Artin/pure groups,
  standard generators, parabolics, and algebraic normaliser exact sequence.
- §3.1, PDF p.7: (3.1)–(3.3), relative interior and restricted arrangement;
  §3.3, PDF pp.12–13: Lemmas 3.23–3.24, the natural action, (3.26) and (3.28);
  §3.5's definition of the arrangement/Deligne groupoid, PDF p.14.
- §5, PDF pp.21–22: definitions of ribbon/reduced ribbon groupoids and
  Theorem 5.6 identifying its vertex group with the normaliser quotient.
- §6's proof outline and Lemmas 6.1–6.2/Proposition 6.3/Corollary 6.4,
  PDF pp.23–24; Lemma 6.6 and its equivariant path construction, PDF
  pp.25–26; the complete Theorem 6.7 proof and (6.8)–(6.13), PDF p.26;
  the full Corollary 6.14 proof and Remark 6.15, PDF p.27.

I visually inspected original page images 3, 7, 13, 26 and 27 in this task,
including the theorem and the exact-sequence diagrams. Reading the other
passages above was through the frozen text extraction, not a claim of visual
PDF inspection of every page. I have not read the original Deligne, Godelle,
Van der Lek or Paris sources for this new task. Their citations in the article
are prerequisite leads, not accepted formal suppliers or independent source
certification. No new Lean build, axiom audit, kernel replay or supplier search
was executed by this reviewer in this statement-contract task.

## Exact mathematical objects

The final theorem must work for every finite Coxeter group of the specified
Coxeter system and every subset `J` of its simple-generator indices. Spherical
type is a legitimate hypothesis of Theorem 1.8. An implementation may represent
the finite group or index set by `Finite`/`Fintype`; any extra finiteness
assumption must either follow from the source hypotheses by a proved lemma or
be disclosed as a restricted result. A special case `J=∅`, `J=univ`, rank one,
one diagram, crystallographic type, or finite-type classification examples
does not establish the general theorem.

Use the actual standard geometric representation with roots `Φ` and dual
space `Θ=V*`. The relative subspace is

```
Θ_J = {φ : Θ | ∀j∈J, φ(α_j)=0}.
```

The restricted arrangement contains the distinct subspaces

```
H^J = {H_α ∩ Θ_J | α∈Φ and Θ_J is not contained in H_α}.
```

Repeated roots may define the same restricted hyperplane; a root-indexed union
is fine if its underlying subset is proved equal to this one. Hyperplanes
containing the whole relative subspace must be omitted: including one would
delete every point and change the theorem.

In the spherical case `Cone=Θ` and `Cone(J)°=Θ_J`, with interior taken in
`Θ_J`, not `Θ`. These equalities must be proved if the construction passes
through the Tits cone. Alternatively the finite-case space may be defined
directly as the following actual subspace of `Θ_J × Θ_J`:

```
X_J = {(u,v) | ∀H∈H^J, ¬(u∈H ∧ v∈H)}.
```

It carries the inherited product/subspace topology. Equivalently, it is the
actual complex vector-space complement
`(Θ_J ⊗_R C) \ ⋃H∈H^J (H ⊗_R C)`, provided the real-pair/complexified
identification is constructed and proved a homeomorphism. An arbitrary type
named `RelativeComplement`, a discrete copy of the underlying set, a groupoid,
or a classifying space defined from the desired algebraic group is insufficient.

The finite-dimensional real coordinate model is acceptable if its linear
topological identification with the standard dual representation and its
relative subspace, roots and hyperplanes is proved. A primal fixed-space model
requires a proved compatible dual identification, for example using an
invariant positive-definite form in finite type. Merely giving a representation
on an unrelated vector space does not establish this source correspondence.

## Natural action, quotient and actual covering maps

Let `Q=N_W(W_J)/W_J`, using the already defined actual generated parabolic.
The action must descend from the standard contragredient action
`(g·φ)(v)=φ(g⁻¹·v)` of `N_W(W_J)` on `Θ_J`; `W_J` acts trivially there.
It acts diagonally on the real-pair complement, or by its complexification.
Subspace/arrangement preservation, well-defined descent, continuity, freeness
on `X_J` and the required properly-discontinuous/covering properties must be
proved from the actual finite Coxeter data. No arbitrary action selected
solely to make the result true is acceptable.

The space `Y_J` is the topological orbit quotient `X_J/Q`, with quotient
topology, and `p:X_J→Y_J` is the actual continuous orbit map. Prove it is the
claimed regular covering with its deck action identified with `Q`, and prove
the connectedness/local hypotheses used for its fundamental-group sequence.
Since `Q` is finite in spherical type, a valid finite-free-action covering
theorem can be used once its topological hypotheses are met.

The action need not be transitive on all chambers (Remark 3.25), and the
restricted arrangement need not be the reflection arrangement of `Q`.
Replacing it by a Coxeter arrangement for a purported normaliser Coxeter
group would require a genuine proved equivalence, not similarity of notation.
These are especially important traps when reusing classical `J=∅` code.

## The required conclusion, with compatibility

For every `x:X_J`, let `y=p(x)`, and write:

```
K = pureNormalizerImage M J = N(P,J),
E = normalizerQuotient M J = N(A,J),
Q = coxeterNormalizerQuotient M J = N(W,J).
```

These must be the existing actual presentation-based groups or groups proved
equivalent to them by the appropriate maps. The left arrow `i:K→*E` is their
actual subgroup inclusion; the right arrow `πbar:E→*Q` is induced by the
actual Artin–Coxeter projection. Let `p_*:π₁(X_J,x)→*π₁(Y_J,y)` be induced
by `p`, and `μ:π₁(Y_J,y)→*Q` be the covering monodromy taking a loop to the
endpoint deck transformation of its lift beginning at `x`.

Theorem 1.8 requires group equivalences

```
eK : K ≃* π₁(X_J,x),
eE : E ≃* π₁(Y_J,y)
```

and the two commuting equations

```
eE ∘ i = p_* ∘ eK,
μ ∘ eE = πbar.
```

The vertical map on `Q` is the identity as in diagram (6.8), not an
unspecified automorphism. An equivalently oriented diagram using inverse
isomorphisms is fine. If loop multiplication, category-composition order or
left/right deck-action conventions yield an opposite group, prove the
appropriate identification and these actual equations; inversion alone is
not a homomorphism on a noncommutative group. Two abstract group isomorphisms
with no compatibility proof do not establish the isomorphism of sequences.
The geometric row must itself be the exact covering sequence, with its
actual maps, not a copied algebraic sequence renamed as fundamental groups.

The target is any basepoint, not only the chamber basepoint chosen in the
source proof. A proof at a preferred basepoint can be transported using
actual paths, with induced basepoint-change isomorphisms and the required
compatibility. Nonemptiness and connectedness must not be left vacuous or
assumed as part of a definition.

The asphericity assertion must concern both actual spaces: `X_J` is a
`K(K,1)` and `Y_J` is a `K(E,1)` under the displayed identifications. Acceptable
encodings include contractibility of a genuine universal cover, or the
vanishing of all higher homotopy groups with the connectedness and homotopy
type hypotheses needed by the chosen definition. Proving only `π₁` or only
homology does not prove `K(π,1)`. A contractibility statement about an
unrelated combinatorial type or a discrete universal-cover name is not the
required topological statement. Proving `X_J` aspherical and using the actual
covering to transport higher homotopy groups to `Y_J` is a legitimate route.

## Bridges that still require proofs

The current algebraic package supplies Lemma 2.8, not the following bridges.
Each must be authored or reused through an actually compiled, audited and
applicable formal theorem; none may be inserted as a hypothesis of the final
main theorem.

1. **Representation/arrangement bridge.** Connect the precise finite Coxeter
   representation and relative arrangement to the constructed topological
   `X_J` and its natural `Q` action; prove the geometric hypotheses used by
   each supplier, in particular finite central simplicial arrangement where
   Deligne's theorem is applied.
2. **Topological Artin bridge.** Connect the actual Artin braid presentation to
   the relevant topological/groupoid model with generator and projection
   compatibility. A proof directly identifying the existing algebraic groups
   with the actual relative-space fundamental groups can establish the main
   theorem without separately naming the source's ambient topological
   `A`; but one may not claim that missing ambient identification has already
   been formalised. The `J=∅` instance provides a useful compatibility check.
3. **Normaliser/ribbon bridge, for the article's route.** Construct the actual
   ribbon generators/morphisms inside the Artin group, prove their vertex
   group maps isomorphically to the existing normaliser quotient, and prove
   its projection is the canonical `πbar`. A groupoid freely generated by
   names without its presentation/normaliser comparison is insufficient.
4. **Arrangement/groupoid topology bridge.** Prove the Deligne or Salvetti
   model corresponds to the actual complement. The article's Lemma 6.6
   needs `Q`-equivariance so this comparison descends to the correct quotient
   and covering. A bare nonequivariant equivalence need not supply the
   quotient comparison or monodromy compatibility.
5. **Asphericity bridge.** Prove the applicable finite simplicial arrangement
   theorem or an equivalent genuine asphericity theorem. The article's
   Corollary 6.14 invokes Deligne [9]; invoking its name or defining a
   structure field containing the desired result does not formalise it.
6. **Covering and basepoint bridge.** Connect the actual orbit cover,
   path-lifting monodromy and basepoint changes to the algebraic maps and
   derive the exact commutative diagram, for arbitrary `x`.

These are obligations for a full proof, not additional hypotheses to be
packaged into an alleged final theorem. A structure called `Theorem18Data`
whose fields include an isomorphism/asphericity is acceptable as an intermediate
interface only if its actual instance is later constructed for every finite
Coxeter datum without assuming those same fields.

## Acceptable alternate models and supplier rejection tests

A Salvetti CW complex, Deligne groupoid nerve, another arrangement model,
or a classifying space may be an intermediate. To substitute it in the final
statement requires a proved homeomorphism or the homotopy equivalence needed
for the exact conclusions, plus enough equivariance or explicit covering-map
compatibility to identify the actual orbit quotient and its monodromy. An
equivariant homeomorphism is strongest; an ordinary homotopy equivalence of
underlying spaces alone does not automatically compare quotient spaces.
Using a classifying space `BG` is legitimate after establishing the relevant
equivalences with `X_J` and `Y_J`, not by defining those spaces to be `BG`.

For every proposed supplier, inspect actual definitions, elaborated types,
proof dependencies and universe/topology/group instances. Common rejection
cases include:

- Axioms, `sorryAx`, unbuilt proof files, or desired conclusions stored as
  structure fields never instantiated from the actual geometry.
- A declaration named `Salvetti`, `Aspherical`, `FundamentalGroup` or
  `Deligne` with an unrelated/trivial type, an abstract group presentation
  in place of actual path-homotopy classes, or a `Kpi1` predicate defined
  as an always-true proposition.
- A classical Artin/Coxeter `J=∅` theorem silently applied to a relative
  arrangement, or a crystallographic/irreducible/rank bound that excludes
  source cases such as noncrystallographic finite type or reducible diagrams.
- A proof of simpliciality assumed instead of established for this restricted
  arrangement, or a simplicial abstract complex mistaken for a simplicial
  real hyperplane arrangement.
- A nonequivariant Salvetti comparison used to identify `X_J/Q` without a
  justified quotient comparison, or an arbitrary abstract group isomorphism
  used in place of the covering-compatible one.
- A `π₁` computation advertised as asphericity, or a contractible cover
  assumption advertised as its construction/proof.

Final acceptance will require exact frozen source hashes, every relevant
definition/helper signature checked against this contract, applicable supplier
conclusions, real build/axiom-audit/kernel evidence and honest model/reading
limits. No conclusion about the existence or adequacy of new supplier code is
asserted by this preliminary review. No new mathematical error in the original
article or its cited literature has been independently established here.
