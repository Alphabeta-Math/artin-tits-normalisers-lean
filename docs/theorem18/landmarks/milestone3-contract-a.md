# Landmark 3: independent source and semantic acceptance contract A

Reviewer: **GPT-6.1 Sol/high** (`gpt-6.1-sol`, reasoning effort `high`).
Date: 2026-11-14. Status: **preauthoring target contract only**. No Landmark 3
proof or new supplier is accepted by this document. Full Theorem 1.8 remains
unproved. Existing Landmark 1/2 reviews and proofs remain unchanged.

## Reading actually performed

I read the current landmark plan, the full README, the earlier full-theorem
statement contract and `docs/theorem18/search-openai.md`. I checked the current
repository head directly: `b793bf9dd4c5c9637d8dde51c6a635f849b943c4`.
I reread the frozen arXiv:2509.21915v3 extraction in the sibling workflow
repository, especially §2.4's precise groupoid-cover/orbit definitions,
§3.1–3.5, §4.1–4.2, and §6 through Corollary 6.14. Relevant specific inputs
are (3.1)–(3.4), Theorem 3.9, Proposition 3.17, Lemmas 3.20/3.23/3.24,
Proposition 3.29, §3.5, Proposition 4.6/Theorem 4.7/Lemma 4.10,
Corollaries 4.13/4.26, and Lemmas 6.1/6.2/6.6, Proposition 6.3,
Corollary 6.4 and Theorem 6.7. I visually inspected original PDF pages
14, 25 and 26 during this task, including the two comparison diagrams and
the reverse-crossing footnote. Other passages were read through extraction,
not a visual inspection of every page.

I reread the actual parent `Theorem18/Geometry` and `NormalizerAction`
models, the actual Landmark 1 `Covering` endpoints, and the relevant actual
ribbon definitions, signed universal property, Coxeter projection and
`AtomicCoxeter` length input. I inspected mathlib's actual
`FundamentalGroupoid` and induced continuous-map functor definitions:
objects are points, and morphisms are endpoint-fixed homotopy classes of
actual continuous paths. I did not read the entirety of Van der Lek's thesis,
Deligne's original paper, or all ordinary Salvetti supplier proofs in this
task. A citation or a previous source search is not acceptance of those
unread formal prerequisites. No new Lean build, axiom audit, kernel replay
or new remote supplier search was executed by me in this contract task.
I did not consult reviewer B or modify proof, provider, configuration or
cache files.

## Fixed source objects and quantifiers

The target works for arbitrary `I : Type u`, actual `M : CoxeterMatrix I`
with `[Finite M.Group]`, and every `J : Set I`. No extra nonemptiness,
positive dimension, proper-J, irreducibility, crystallographic or rank bound
is acceptable in the claimed full landmark. Finite index and finite J may
be derived from finite `M.Group`, as existing proofs already do.

Use these existing objects, with their existing instances and maps:

```
X := ArtinNormalisers.Theorem18.Complement M J
Q := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
Y := ArtinNormalisers.Theorem18.OrbitSpace M J
p := ArtinNormalisers.Theorem18.orbitProjection M J
```

Here X is the actual open subspace of `relativeSubspace J × relativeSubspace J`
with all and only the proper restricted root hyperplanes `H × H` removed.
Its topology is inherited from the actual dual-coordinate real topology.
Coincident root hyperplanes are identified in `restrictedArrangement`;
hyperplanes containing the whole relative flat are omitted. Q acts by the
existing quotient of the contragredient normalizer action, diagonally on the
two coordinates. Y is its actual orbit quotient with quotient topology,
and p is its actual quotient map. Landmark 1 already proves the genuine
free quotient covering; this may be reused without re-proving freeness.

No type merely named `Complement`, a new discrete topology, an abstract
classifying space, or a quotient action chosen to make the comparison true
may replace these objects. A different coordinate or CW/nerve model needs a
proved geometric comparison with these actual spaces and sufficient
compatibility with this actual action and orbit map.

## Actual chambers and wall crossings

Construct the chambers of the actual real restricted arrangement
`relativeSubspace J \ union restrictedArrangement`. A sign-vector, face-poset
or algebraic label implementation is acceptable only after proving it
represents the actual connected components/open chambers, not by naming
unrelated combinatorial objects “chambers.”

The source's algebraic chamber labels are pairs `(x,K)` with
`W_J x = x W_K` as actual cosets and x the minimal-length representative
of `x W_K`. Their geometric image is `dualAction M x '' C_K`, where
`C_K` annihilates exactly the selected simple roots and evaluates strictly
positively on every outside simple root. Prove the label-to-chamber
bijection, with representative independence and actual source/target
identifications. An equivalent label model may be used through a proved
bijection preserving all the following maps.

For every outside `a ∉ K`, the actual simple crossing must reach

```
(x * v_(a,K), K ∪ {a} \ {twist_(K∪{a})(a)})
v_(a,K) = w_K⁻¹ * w_(K∪{a}) = π(elementaryMu M K a).
```

Prove this is a well-defined chamber label, that the two actual chambers
are adjacent across the actual corresponding restricted hyperplane, and
that every adjacent crossing has precisely the appropriate outside label.
The reverse crossing endpoint must be tracked through the actual longest
permutation. A group element of the correct projected type or a target set
of the same cardinality is insufficient.

The action of Q on chambers must be induced by its existing linear action.
On labels it acts by left multiplication followed by the actual minimal
coset representative; it does not change K. Prove freeness, adjacency and
geodesic preservation, and that chamber orbits correspond exactly to the
associates K of J. **Q need not be transitive on all chambers** (Remark
3.25). Replacing this arrangement by a purported Coxeter arrangement for Q,
or reducing the orbit category to one object for that reason, changes the
target.

For a gallery, “geodesic” must be actual shortest adjacency length, or the
proved equivalent statement that each distinct actual restricted hyperplane
is crossed at most once. It must not simply be defined to mean Coxeter
length additivity without proving the geometric equivalence. Establish the
finite-type instance of Proposition 3.29 from every starting chamber:
Coxeter length of the projected product equals the sum of the actual
projected elementary lengths exactly when the actual gallery is geodesic.
A proof only at the preferred chamber needs a proved transport to all starts.

## Genuine arrangement/Deligne groupoid

The positive category D+ has these actual chambers as objects and directed
adjacency galleries as paths, modulo the congruence generated by identifying
geodesics with the same actual endpoints. Its groupoid completion D must
have a proved localization/universal property or an equivalent explicit
presentation and evaluation theorem. Defining every morphism merely by
its Coxeter endpoint product produces the thin Brink–Howlett universal
cover, not D; that map forgets nontrivial loops (Remark 4.5).

Each adjacency gives **two separate directed positive generators**. The
positive generator from C′ to C is not the inverse of the positive generator
from C to C′ in D. Groupoid inversion is added separately. The original
footnote on PDF p.26 and the two distinct components used below make this
essential, already for the rank-one arrangement.

Prove the actual Q action extends to genuine groupoid automorphisms of D,
with group laws and its effect on generators. Its orbit groupoid D/Q must
use the free-on-objects groupoid quotient of §2.4, or a model proved
isomorphic to it: object orbits and compatible arrow orbits, with target
alignment by the unique group translate when composing. The action
(semidirect/translation) groupoid of the object set alone is not this
quotient. A quotient of each fixed hom-set without aligning translates is
also not a definition of D/Q. Prove the quotient functor U:D→D/Q has the
required unique arrow lifts and is the normal cover with this actual Q action.

## Correct ribbon component and comparison

The existing `Ribbon2.ActualReducedRibbonGroupoid M` has **all subsets** as
objects. It contains all associate components and is generally disconnected.
For this fixed J, define R(J) as its actual J-associate full subgroupoid,
or its connected component at `actualRibbonObject M ⟨J⟩` with a proved
identification with all associates. Do not compare connected D(J)/Q with
the unrestricted global ribbon groupoid. Prove every associate is attained
by a chamber label and that the actual generated arrows have the stated
component endpoints.

Construct G:D→R(J), sending `(x,K)` to K and each actual directed crossing
at a to the existing actual `elementaryMu M K a`, with the source formula
for its endpoint. Prove G is well-defined on geodesic relations and the
groupoid completion. It must use actual Artin labels and preserve their
multiplication; neither the larger positive-transporter groupoid nor a
formal groupoid with the desired vertex group is a substitute.

Prove G is a groupoid covering: for each actual reduced ribbon arrow and
each prescribed source chamber above its source, there exists exactly one
lift, including its actual target chamber and arrow. Prove it is Q-invariant
with trivial Q action on the ribbon base. Then construct an actual
isomorphism, or a genuine equivalence with the corresponding object bijection,

```
H : D/Q ≌ R(J),       U ⋙ H.functor = G.
```

This is the content of Lemmas 6.1/6.2, Proposition 6.3 and Corollary 6.4,
not a claimed automatic consequence of Landmark 2's vertex-group theorem.
Track the actual Coxeter projected product in lift endpoints. At the
preferred source `(1,J)`, a reduced loop label β lifts to a chamber whose
normalizer-orbit displacement is the actual class of `π(β)` in Q, rather
than an arbitrary automorphic relabeling of Q. Group-level conversion to
raw monodromy and the opposite convention is left to Landmark 4.

Landmark 2's **fixed chosen-lcm presentation** is an acceptable route to
unique lifting. Prove the two chosen words lift from every source chamber
to geodesics with the same actual endpoint. Its `AtomicCoxeter` theorem
supplies Coxeter length additivity; it does not supply chamber steps,
geodesicity or endpoints. After the genuine geometric criterion above,
these are equal morphisms in D+. Then apply the proved signed universal
property with its actual object/generator assignments and only the chosen
relations. All signed arrows, compositions and inverse lifts must follow;
positive-word completeness alone is insufficient. This route need not
prove the literal whole Lemma 5.9/precisely-two distinguished paths or the
whole infinite-type §4 atomic-Matsumoto theorem. It must prove every finite
geometric consequence actually consumed here. In particular weighted
Coxeter length additivity is not by itself equality of atomic step counts.

## Equivariant comparison with actual path-homotopy groupoids

Construct a genuine equivalence

```
E : D ≌ FundamentalGroupoid X.
```

For the article's explicit construction, define the actual chamber open set

```
X_C = {(u,v) ∈ X | for every H, u ∈ H implies v ∈ side_H(C)}.
```

Prove its needed openness, contractibility/path properties and the actual
adjacent-intersection components. The crossing C→C′ uses the component
`X_(C,C′)` specified by the real coordinate lying on C's side of the common
wall, while C′→C uses `X_(C′,C)`. Choose actual points `a_C∈X_C`
equivariantly, and map a generator to the actual path-homotopy class obtained
through its specified component. Prove independence from the internal
point/path choices, the geodesic relations, and full faithfulness and
essential surjectivity. Mere existence of the points and paths or proving
only that some functor exists does not establish an equivalence.

A different geometric construction, such as a genuine relative Salvetti
comparison and van Kampen, is acceptable with equally explicit generator,
action and orbit-map control. An ordinary Coxeter Salvetti theorem for a
different M cannot be applied just by changing the diagram parameter:
restricted arrangements need not be Coxeter arrangements. Nonequivariant
homotopy equivalence with a model does not automatically identify quotients.
If a supplier comparison requires finite central **simplicial** geometry,
those hypotheses must already be proved for this actual restricted arrangement
before M3 is accepted. The later M5 position in the plan cannot defer an M3
input. A formally proved more general real-arrangement comparison may instead
be used under its actual discharged hypotheses.

Let T_g be the actual chamber groupoid action and S_g the functor induced
by the existing continuous action on X. Prove E equivariant on objects
and morphisms (`T_g ⋙ E.functor = E.functor ⋙ S_g`, with the appropriate
composition conventions). Strict equivariance matches Lemma 6.6. A coherent
natural-isomorphism formulation is acceptable only with its unit and group
laws and an actual proved descent/covering comparison; unstructured natural
isomorphisms do not provide descent. Any resulting basepoint transports
must be explicit and retain the same actual deck labels.

## Actual orbit-space equivalence and covering square

Construct the genuine equivalence

```
B : D/Q ≌ FundamentalGroupoid Y
```

and prove the square

```
U ⋙ B.functor = E.functor ⋙ FundamentalGroupoid.map ⟨p, continuous_p⟩.
```

The bottom functor on objects sends `[C]` to the actual point `p(a_C)`.
The right functor sends actual path-homotopy classes to their images under
the existing orbitProjection. A specified coherent natural isomorphism in
place of strict equality is acceptable only with the proved compatibility
of the corresponding covering and endpoint transports. Two unrelated
abstract equivalences of the upper and lower groupoids do not suffice.

One route proves the actual quotient of `FundamentalGroupoid X` by Q is
isomorphic to `FundamentalGroupoid Y` using Landmark 1's genuine covering,
unique continuous path lifting and homotopy lifting with the necessary
local hypotheses discharged. This identification is a theorem, not a
new definition of `FundamentalGroupoid Y`. Combine that theorem with the
proved equivariant E to obtain B. Consequently R(J) is equivalent to
`FundamentalGroupoid Y` through H and B, and G corresponds to the actual
topological covering-induced functor. Prove the equivalence is of covers
with the **same** actual Q action/deck labels; do not silently allow an
unspecified automorphism of Q.

D has finitely many chamber objects while the fundamental groupoid has all
points of X as objects. Thus an equivalence, with proved essential
surjectivity, is the appropriate claim; bijectivity of those object types is
neither expected nor needed. Statements only about automorphisms at one
chosen object fall short of this promised groupoid landmark.

## Boundary with later landmarks and acceptance gate

M3 includes the groupoid-level square, actual covering/lift compatibility,
correct ribbon component and actual action. These are its mathematical
content and cannot be deferred as optional compatibility checks.

M4 still must assemble actual group isomorphisms at every basepoint between
`pureNormalizerImage` and `FundamentalGroup X x`, and between the actual
Artin normalizer quotient and `FundamentalGroup Y (p x)`. It must prove both
group-level exact-sequence squares, using the existing canonical subgroup
inclusion and Artin–Coxeter projection, with identity on Q. In particular,
mathlib's categorical End and raw endpoint monodromy conventions lead to
opposite groups; their explicit transports and compatible basepoint changes
remain required. M3 may supply intermediate lemmas for this but is not by
itself an advertised completion of Theorem 6.7 for every x.

M5 must prove actual higher-homotopy/asphericity assertions for X and Y
using an applicable Deligne theorem or genuine universal-cover argument.
A fundamental-groupoid equivalence alone does not imply asphericity.
Simpliciality proved early for an M3 supplier is a geometric prerequisite,
not proof of the later asphericity conclusion. No `K(π,1)` claim is accepted
from M3 alone.

Final M3 acceptance requires every construction above to be instantiated
from actual M,J with no assumed chamber theorem, gallery relation-lifting,
fundamental-group comparison, equivariance, quotient comparison or desired
isomorphism hidden as a field/premise. Generic conditional interfaces are
fine only when their actual instances are subsequently constructed. Every
helper's actual elaborated type and all supplier hypotheses must be reviewed,
with frozen project/configuration/provider/provenance hashes, real builds,
transitive-axiom checks and complete physical-module kernel replay evidence.
Physical serialized occurrences and unique imported names must be accounted
for separately if identical generated declarations overlap, as in Landmark 2.

Empty J, full J, rank zero, reducible and noncrystallographic finite systems
remain part of the claim. Full J gives the actual one-point complement,
trivial Q and a one-chamber identity groupoid; a proof requiring an outside
atom or positive dimension must handle that case rather than exclude it.
No new source error or mathematical defect in the article is asserted by
this contract. The remaining obligations are proofs to formalize, not new
hypotheses or claimed open problems.
