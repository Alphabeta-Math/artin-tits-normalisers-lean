# M3 orbit-colimit route: independent contract review A

Reviewer: **GPT-6.1 Sol/high** (`gpt-6.1-sol`, reasoning effort `high`).
Date: 2026-11-14. Disposition: **mathematically acceptable route, conditional
on actually proving the concrete hypotheses and conclusions below**. This is
not final code acceptance, not a supplier receipt, and not a claim that M3,
M4, M5 or full Theorem 1.8 is proved.

## Inspected source and current code boundary

I checked this proposal against the original article's §2.4 orbit-groupoid
and covering definitions and §§3/4/6, especially Proposition 6.3,
Corollary 6.4 and Lemma 6.6, and my earlier M3 target contract. I inspected
the current `GroupoidCover`, `CoveringGroupoid`, `IntervalGroupoid`,
`IntervalAction`, `ForwardEquivariance`, the concrete `RibbonCover` map,
and the relevant chamber-fiber/family lifting interfaces. I checked the
actual mathlib definitions of `SingleObj` and `Grpd`.

`IsCoveringFunctor F := ∀x, Bijective (mapOutgoing F x)` uses the **total
outgoing-arrow set** `Σ y, x ⟶ y`, retaining both the actual endpoint and
arrow. This is the appropriate actual unique-lift property. It is not
merely injectivity/surjectivity on each arbitrarily fixed hom-set.
`CoveringGroupoid` has an explicit proof for actual topological covering
maps using actual monodromy, lifted path-homotopy classes and injectivity
of the path-class map. `ForwardEquivariance`'s concrete finite-type endpoints
contain no point-covariance premise: they instantiate the generic point
version with the proved canonical equivariant chamber points. This supports
the proposed interfaces; it is not a frozen all-declaration review of their
changing dependency closure or an independent compilation claim.

I did not execute new Lean builds, audits or replays, consult reviewer B,
or modify proof, provider, configuration or cache files. Only this owned
route-review Markdown file was written. No changing mathematical source
hash is accepted or bound by this preliminary route assessment.

## Exact objects that must remain fixed

Write:

```
D = the concrete interval groupoid on actual restricted-arrangement chambers
X = the existing actual Complement M J
Y = the existing actual OrbitSpace M J
Q = the existing actual coxeterNormalizerQuotient M J
P = FundamentalGroupoid.map of the existing continuous orbitProjection X→Y
R = the actual J-associate component of the existing generated reduced
    ribbon subgroupoid, with its actual Artin labels and composition
G : D ⥤ R = the concrete canonical positive-lift ribbon functor
E : D ⥤ FundamentalGroupoid X = the actual forward geometric functor
```

The quantified datum is arbitrary I, M with finite M.Group, and every J,
including rank zero/full J. R must already be defined independently of the
orbit quotient and the desired comparison. The current unrestricted
`intervalRibbonFunctor` targets the global actual ribbon groupoid; the
functor to R must be explicitly corestricted with its proved object property.
Its object map must hit **every actual object of this associate component**.
Essential surjectivity alone is insufficient for the strict colimit argument.

The present interval presentation is genuinely based on actual chamber
signs and geometric betweenness, with opposite directed positive arrows
retained separately. The proposed colimit step does not itself prove its
identification with the article's adjacent-gallery Deligne presentation.
A report calling it that literal presentation must supply that bridge.
An honestly named alternate geometric interval model, with a proved actual
path-groupoid equivalence and all the canonical covering/projection data
here, can supply the needed main-theorem comparison without advertising
an unproved literal adjacent-gallery theorem. No combinatorial model is
accepted just from its name or intended geometric interpretation.

## The concrete hypotheses needed for each orbit cocone

For an actual strict Q action T on a groupoid C and a functor F:C⥤B,
prove the following concrete facts:

1. **Actual strict action laws:** T₁=identity and T_(q*r)=T_r⋙T_q for
   the left-action convention, as functor equalities including all arrows.
2. **Strict invariance:** T_q⋙F=F, as actual functor equality for every q.
3. **Actual unique outgoing lifts:** IsCoveringFunctor F.
4. **Literal object surjectivity:** every b:B equals F.obj c for some c:C.
5. **Actual object fibers are precisely Q orbits:**
   `F.obj c = F.obj d ↔ ∃q, d = (T_q).obj c` (up to the explicitly chosen
   equivalent orientation of the equality).
6. **Free actual object action**, rather than an ineffective action or a
   merely abstract group isomorphic to Q.
7. **Nonempty connected source**, when identifying the *entire* deck group
   with Q, not merely embedding Q among deck transformations. Otherwise
   deck transformations can act independently on disconnected components
   and form a larger group. Actual D has positive arrows between every pair
   and needs a proved chamber object; the lower actual fundamental groupoid
   inherits the already proved nonemptiness/path connectedness of X.

For the upper cocone take C=D, B=R, F=G and the actual chamber Q action.
For the lower take C=FundamentalGroupoid X, B=FundamentalGroupoid Y,
F=P and the functor induced by the existing actual action on X.

The lower conditions must come from the real orbit cover: actual p is
surjective, p(x)=p(y) exactly means actual Q-orbit equality, pointwise
freeness is Landmark 1, and the actual path/homotopy lift gives condition 3.
The equality `p(q•γ)=p(γ)` must be proved on actual path classes to obtain
strict functor invariance. The upper conditions must be proved using actual
chamber labels, canonical positive lifts and the existing M2 relations,
including the signed relation-lifting and uniqueness proof. Neither can be
left as a premise of the advertised unconditional M3 endpoint.

No transitivity on *all* chambers is required: only transitivity on each
actual object fiber, which corresponds to one standard-facet index K.
The global nontransitive action is retained.

## Why these conditions prove a genuine quotient

Define the actual action diagram A_C:SingleObj Q⥤Grpd with its sole object
C and its arrow q mapped to T_q. Mathlib defines

```
q ≫ r = r*q               in SingleObj Q,
F ≫ G = F ⋙ G             in Grpd.
```

Thus the displayed left-action law gives the correct functor composition
law. Invariance makes F the actual leg of a cocone over this diagram.
Do not silently reverse Q or precompose its action with an arbitrary
automorphism. Bundle the correct object/hom universes; any necessary lift
must have actual proved bridges, not restrict I to Type 0.

The colimit property can be proved from the cover, surjectivity, orbit-fiber
and strict-action/invariance facts above, rather than assumed. Source
connectedness is additionally needed for the full deck-group equality,
not for existence of this orbit colimit. Given any cocone with leg K:C⥤T invariant under the actual action:
choose a preimage c_b for each b. For an arrow a:b→b′, lift a uniquely
from c_b to an actual endpoint d. Fiber transitivity relates d to the
chosen c_b′ by a Q translate. Invariance of K supplies the required object
transport, so K of the lifted arrow defines the descended arrow. Unique
lifting and strict invariance prove independence, identity and composition,
and give the **functor equality** `F⋙desc(K)=K`. Object surjectivity and
outgoing lift surjectivity prove uniqueness of the whole descended functor.
These are the `desc`, `fac` and `uniq` clauses of `IsColimit`, and must
hold for every cocone in the chosen category, not just one desired target.

The same hypotheses identify actual orbits directly:

- The induced map on object orbits is bijective onto B's actual objects,
  by object surjectivity and the exact fiber characterization.
- Align the sources of two total arrows by a Q translate. If F gives the
  same total outgoing arrow, covering injectivity forces equality of the
  translated endpoint and translated arrow. Hence arrow fibers are exactly
  the actual action orbits, with the target transports accounted for.
- Covering lift uniqueness also supplies precisely the source alignment
  needed for composition in the source's orbit groupoid.

Consequently this is the free-on-objects orbit quotient of §2.4, not an
unrelated object satisfying an accidentally weak universal property. These
orbit-identification consequences should be exposed as lemmas or follow
explicitly from the final stated hypotheses/proof, so the report's quotient
claim remains reviewable without relying on naming.

After **proving** `IsColimit` for the independently defined actual G cocone,
using it as the witness of `HasColimit A_D` is legitimate. Defining D/Q by
`Limits.colimit A_D` then chooses an object whose actual projection is
`colimit.ι A_D star`. Colimit uniqueness gives the canonical isomorphism
from that object to R, with its hom commuting with the canonical projection
and G. That is a proof that the existing R represents a genuine quotient;
it is not circularly defining R to be the desired quotient. No dependent
arrow-double-quotient implementation is required.

If the construction is done in Cat instead of Grpd, prove the corresponding
Cat universal property or an explicit preservation theorem. Do not infer
colimit preservation merely from `Grpd.forgetToCat` being fully faithful.
It suffices to carry out both actual orbit cocones and their comparison
consistently in Grpd for this groupoid conclusion. This is an ordinary
strict colimit, not a homotopy quotient/Grothendieck construction: for a
nonfree trivial action those constructions differ (ordinary orbit of a
point is a point, while a homotopy orbit can retain BQ). The actual free
object action and cover/orbit lemmas prevent that substitution here.

## Critical caveat: equivalence is not a Grpd isomorphism

The geometric E is a categorical **equivalence**. It generally is not an
isomorphism object in the ordinary category Grpd: D has chamber objects,
while FundamentalGroupoid X has every actual point of X as an object.
Thus one must not write a proof that treats E as a strict inverse pair
or asserts automatic preservation of ordinary 1-category colimits because
its component is an equivalence. Likewise IsCoveringFunctor is sensitive
to literal endpoints and cannot simply be transported through arbitrary
categorical equivalences as though they were object-bijective covers.

The safe direct comparison is:

1. Prove actual strict equivariance `T_q⋙E=E⋙S_q` with the same actual Q
   and lower action S_q.
2. Form the invariant cocone with leg E⋙P. Use the proved G colimit to
   construct `B:R⥤FundamentalGroupoid Y`.
3. The colimit factorization theorem gives the canonical strict square
   `G⋙B=E⋙P` (or the precise equality after bundled-functor conversion).
4. Prove B fully faithful and essentially surjective using the actual
   cover and action conditions, as follows. Do not substitute an unproved
   generic colimit-invariance assertion.

For **fullness**, choose a source chamber over the given source of R.
Lift the desired lower arrow from its E-image using P's actual cover.
Its endpoint lies over the desired target. Lower fiber transitivity moves
that endpoint to the E-image of a chosen chamber over that target, using
strict equivariance. E's fullness supplies the upstairs arrow, and G maps
it to the required ribbon arrow.

For **faithfulness**, lift two ribbon arrows with the same B-image from a
common chosen source chamber, using G's cover. P's outgoing injectivity
forces the E-images of their lifted endpoints and arrows to agree. Upper
fiber transitivity relates the two endpoints by q; strict equivariance and
lower object freeness force q=1. The endpoints therefore agree upstairs,
and E's faithfulness gives equality of the arrows, hence of the original
ribbon arrows. This argument does not assume E is injective on objects;
a separately proved actual object-injectivity lemma could also support a
more specialized version.

For **essential surjectivity**, any y has an actual preimage x under p.
E's essential surjectivity gives an isomorphism from some E(c) to x, and
mapping it by P gives an isomorphism from B(G(c)) to y. These are genuine
path classes, not a selected arbitrary object equivalence inserted as a
hypothesis.

This yields an actual equivalence `R≌FundamentalGroupoid Y`, with its
forward functor the already constructed B and the required covering square.
Composing with the canonical colimit-to-R isomorphism gives the promised
bottom comparison for D/Q. Proving P itself the corresponding lower orbit
colimit additionally certifies that its base is the actual topological
orbit quotient at the groupoid level. All squares are over the **identity
index category SingleObj Q** and the actual same action, which retains the
deck labels required downstream.

## Strict versus weak naturality and remaining scope

A cocone over SingleObj Q in ordinary Grpd requires exact equality
`T_q⋙F=F`. A mere natural isomorphism does not provide such a cocone.
An equivariant E in this approach must have exact natural-transformation
naturality as a diagram morphism. The current concrete strict equivariance
is the appropriate input. If any later construction instead gives only
weak natural isomorphisms, its coherent unit/multiplication laws and a
valid strictification or genuinely different 2-categorical descent theorem
must be proved; weak data cannot be silently inserted into `IsColimit`.
The equivalence inverse need not be strictly equivariant if the forward
comparison, its equivalence proof and canonical square are constructed as
above.

**No remaining mathematical objection to the proposed quotient method
itself** follows from using a proved colimit instead of a handwritten
arrow quotient. Acceptance remains conditional on the actual upper/lower
cover, strict invariance, literal object-surjectivity, exact orbit-fiber
facts, nonempty connected sources for the full deck identification, the
proved colimit laws, and the full-faithful/essentially-surjective comparison. A generic conditional theorem is a useful helper, but the final
M3 statement must instantiate every one from M,J without any conclusion
assumptions or unconstructed fields.

M4 still must convert categorical End/opposite multiplication and raw
monodromy conventions, identify the actual algebraic inclusion/projection,
prove both group-level exact-sequence squares over identity on Q, and
transport the result compatibly to every basepoint. M5 still must prove
asphericity for the actual spaces. No such conclusion follows just from
this route assessment or from a fundamental-groupoid equivalence.
