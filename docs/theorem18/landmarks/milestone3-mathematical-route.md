# Landmark 3: the actual equivariant geometric comparison

Status: mathematical implementation route, not a Lean proof or an acceptance
receipt. The starting point is repository revision `b793bf9`, with landmarks
1 and 2 proved. This document changes no mathematical source or provider.
Theorem 1.8 still needs landmarks 3, 4 and 5.

## Exact target and existing objects

Fix `M : CoxeterMatrix I`, `[Finite M.Group]`, and any `J : Set I`. Write
`E = Theorem18.relativeSubspace J`, `X = Theorem18.Complement M J`,
`N = Artin.coxeterNormalizerQuotient M J`, and
`Y = Theorem18.OrbitSpace M J`. These are the actual dual-space flat,
real-pair hyperplane complement, normalizer quotient and orbit space, with
their existing subspace and quotient topologies. In finite type the paper's
`Cone(J)°` is the whole flat, so this is precisely its space (3.26).

Construct the chamber category from the actual finite restricted arrangement:
objects are its nonempty real chambers, positive arrows are adjacent-chamber
crossings, positive relations identify any two shortest galleries with the
same endpoints, and `D` is its groupoid completion. The positive arrows in
opposite directions across a wall are distinct; neither is defined as the
inverse of the other. They become invertible only on groupoid completion.

The complete landmark target consists of the following compatible objects and
maps, not just an abstract vertex-group isomorphism:

1. An actual action of `N` on `D`, induced by its linear action on chambers.
2. An `N`-equivariant equivalence `P : D ≌ FundamentalGroupoid X`, sending
   a chamber `C` to an explicitly chosen real regular point `(c_C, 0)`.
3. A functor `G : D ⥤ R_J`, forgetting the first chamber label and sending
   a wall crossing labelled `(a,K)` to the actual `elementaryMu M K a`.
   Here `R_J` is the full subgroupoid of the already constructed actual
   reduced ribbon groupoid on associates of `J`, not its whole, generally
   disconnected object set.
4. An equivalence, and with matching object wrappers an isomorphism,
   `D/N ≌ R_J`, carrying the orbit projection to `G`.
5. An equivalence `Pbar : D/N ≌ FundamentalGroupoid Y` and a commuting
   square, up to the specified natural isomorphism,
   `P ⋙ FundamentalGroupoid.map orbitProjection = Q ⋙ Pbar`.

This is the content of article §3.5, Lemmas 6.1–6.2, Proposition 6.3,
Corollary 6.4 and Lemma 6.6. It deliberately does not assert the final
basepoint group maps, identity on the Coxeter quotient, or asphericity.
Those are landmarks 4 and 5. The resulting square must retain enough
information on generator paths to prove those later assertions.

## Source and formal supplier boundary

The original text read for this route is
`workflow-engines/.research-workflow/artin-tits-normalisers-2509-21915-20261113/article.txt`,
extracted from the accompanying original `article.pdf`. Relevant exact paper
locators are:

| Original location | Required content |
| --- | --- |
| §3.1, (3.1)–(3.4), Theorem 3.9, pp. 7–10 | Relative flat, proper restricted hyperplanes, chamber labels |
| Proposition 3.17; Lemma 3.20(2),(4), pp. 11–12 | Actual adjacency and longest-element wall formula |
| Lemma 3.24, pp. 12–13 | Free chamber action, label orbits, preservation of wall labels |
| Proposition 3.29, pp. 13–14 | Geodesic iff sum of Coxeter lengths is additive |
| §3.5, p. 14 | Two directed positive crossings, geodesic relations, completion |
| Lemma 4.10; Corollary 4.26, pp. 18,21 | Standard expressions and rank-two gallery relations |
| Lemmas 6.1–6.2; Proposition 6.3, pp. 23–24 | Ribbon comparison and its covering property |
| Lemma 6.6, pp. 25–26, including footnote 1 | Equivariant comparison with the actual complement |

Lemma 6.6 cites Van der Lek, thesis (1983), Corollaries I.2.18–19 and
Theorem I.4.10. I read the article's use of these citations, not the thesis
proofs during this task. They therefore are not claimed as inspected formal
suppliers. The direct open-cover argument below reconstructs the needed
comparison from finite real linear inequalities instead.

Existing project APIs inspected:

* Parent `Geometry.lean`: actual `restrictedHyperplane`, `retainedRoots`,
  finite retained-root set, evaluation continuity and actual complement.
* Parent `NormalizerAction.lean`: contragredient action and actual quotient
  action; `dualAction_pairing` fixes its inverse convention.
* Landmark 1 `Dominant.lean`, `RegularStabilizer.lean`, `Covering.lean`:
  dominant stabilizers, every dual point has a dominant translate, actual
  real-regular stabilizers, free complex action and actual quotient covering.
  These did not yet prove the full chamber-labelling or wall theorem.
* Ribbon `RibbonGroupoid.lean`, `ReducedRibbons.lean`, `RibbonUniversal.lean`:
  actual generated groupoid, associates and
  `RibbonGeneratorData.exists_unique_extension` requiring only chosen pair-lcm
  relations. Its objects initially range over **all** subsets.
* Ribbon `AtomicCoxeter.lean`: actual elementary degrees are their Coxeter
  lengths, and `AtomicWord.pairLcm_coxeter_length_additive` holds for every
  atomic decomposition of the actual pair lcm. This is weighted Coxeter
  length, not yet gallery length or a wall-crossing theorem.

No missing geometry may be replaced by a structure field asserting the
desired equivalence, a classifying space definition of `X`, or a conditional
landmark theorem taking these conclusions as hypotheses.

## A direct finite-arrangement topology proof

This route needs neither a Salvetti realization nor Deligne asphericity.
It applies to finite real linear arrangements before specializing to roots.

First index **distinct hyperplanes**, not retained roots: different roots
can induce the same hyperplane in `E`, as the paper explicitly warns after
(3.3). Choose one nonzero continuous functional `l_H : E → ℝ` for each
hyperplane. The point set is exactly
`{(x,y) | ∀ H, l_H(x) ≠ 0 ∨ l_H(y) ≠ 0}`. A sign chamber is a nonempty
set defined by a choice `sign_C(H) ∈ {−1,+1}` and all strict inequalities
`sign_C(H) * l_H(x) > 0`. Each is open and convex. Prove they are precisely
the connected components of the real regular locus.

For a chamber `C`, define the actual open subset of `X`

```
U_C = { (x,y) ∈ X | ∀ H, l_H(x) ≠ 0 ∨ sign_C(H) * l_H(y) > 0 }.
```

These sets are the `X_C` of Lemma 6.6. The following elementary proofs
provide all their local topology.

* **Open cover:** the displayed disjunctions are open conditions and the
  index set is finite. Given `(x,y) ∈ X`, choose `t > 0` outside the finite
  forbidden values for which some `l_H(x+t y)=0`. If `l_H(x)=0`, its sign
  at `x+t y` equals that at `y`. The chamber of `x+t y` therefore supplies
  `U_C` containing the given point. The existing unrestricted two-coefficient
  regular-combination lemma does not itself impose `t>0`; prove this extra
  one-parameter finite-avoidance lemma.
* **Contractible members:** choose `c_C ∈ C`. First interpolate `y` to
  `c_C` with `x` fixed. At each real zero, the required imaginary sign is
  preserved. Then interpolate `x` to `c_C` with imaginary coordinate
  `c_C`; no imaginary evaluation vanishes. Finally interpolate the imaginary
  coordinate to zero with real coordinate `c_C`. This is a continuous,
  three-stage contraction inside `U_C` to `a_C=(c_C,0)`.
* **Finite-intersection components:** for a nonempty family `F` of chambers,
  let `S_F` be the hyperplanes on which the chamber signs in `F` are not all
  equal. On the intersection of the `U_C`, real evaluation on every `H∈S_F`
  must be nonzero. For a realizable sign assignment on `S_F`, let `R` be
  its open convex real sign region. The corresponding part of the
  intersection is contractible. Choose `C0∈F` and a real regular `b∈R`;
  move the imaginary coordinate to `c_C0`, then the real coordinate to `b`
  inside `R`, then the imaginary coordinate to zero. On common-sign
  hyperplanes the imaginary interpolation preserves the conditions; on
  differing-sign hyperplanes the real coordinate never vanishes.
* These pieces are precisely the path components: their real signs are
  constant on every path, and the displayed contractions make each piece
  path connected. Each nonempty `R` contains a real regular point by
  avoiding the remaining finite proper hyperplanes. For adjacent `C,D`,
  `S_{C,D}` contains exactly their common wall, so there are exactly two
  overlap components. These must be retained, not identified.

All contractions are actual maps of the existing subspace topology. A
norm, invariant scalar product or simpliciality is unnecessary here.

### Gallery comparison from these overlaps

Prove the following generic finite-arrangement gallery facts independently:
adjacent chambers differ in exactly one hyperplane sign; every pair has a
gallery crossing exactly its separating hyperplanes once; and the same
statement holds inside any nonempty open convex region cut out by a partial
sign assignment. One direct proof perturbs the segment endpoints within
their chambers to avoid the finitely many codimension-two intersections.
The finite affine-subspace avoidance and the segment's ordered crossing
parameters are genuine missing lemmas, not consequences of path connectedness
alone. In particular, duplicate restricted hyperplanes must already have
been removed.

Let `d(B,C)` denote the class of any shortest positive gallery in `D`;
its uniqueness is a defining **geodesic relation**, not uniqueness of
arbitrary paths. Define a positive geometric edge `C→D` as the unique path
class from `a_C` to `a_D` inside the simply connected `U_D`. This agrees
with Lemma 6.6's choice through the overlap component whose real coordinate
lies on the `C` side of the wall. Its reverse positive edge lies in `U_C`
instead, and is generally not its inverse.

For a geodesic `C0→C1→…→T`, the wall crossed at a step is not a separator
of the next chamber and `T`. Hence the two real endpoints of that edge lie
in the same component of `U_next ∩ U_T`. Represent the edge by a path in
this component. Its class agrees with the chosen edge because `U_next` is
simply connected. The whole geodesic is therefore represented inside
`U_T`; all geodesics with the same endpoints have the same class. This
constructs the functor `P : D ⥤ FundamentalGroupoid X` without assuming it
faithful or essentially surjective.

For the inverse, an overlap component of `U_C∩U_D` is represented by a real
chamber `B` in its partial-sign region. Assign it the connector

```
k(C,D;B) = d(B,C)⁻¹ ≫ d(B,D) : C ⟶ D.
```

This is independent of `B`: connect two possible choices by a gallery
inside that region. Each crossed wall is a wall where `C,D` agree. Crossing
it moves toward both `C,D` or away from both, so their two geodesic classes
acquire the same prefix, which cancels in the formula. The triple-overlap
cocycle follows by choosing one common `B` and cancelling `d(B,D)`.

There is a formal strictness issue: constant functors with object values
`C` and `D` are isomorphic on overlaps, not equal. To use the actual
TauCeti gluing theorem, choose for every `p∈X` a chamber `χ(p)` with
`p∈U_χ(p)`, choosing `χ(a_C)=C`. On `U_C` use the **same** object map
`p↦χ(p)` and send any path class `p→q` to

```
k(χ(p),C;p) ≫ k(χ(q),C;q)⁻¹.
```

The component notation uses the component containing the indicated point.
On a path in `U_C∩U_D`, its overlap component is constant. The cocycle
then proves strict equality of these local functors on the intersection,
so `TauCeti.FundamentalGroupoid.glue` applies. Its computation and
uniqueness lemmas, and local simply connectedness, prove this glued inverse
and `P` are quasi-inverse. This supplies full faithfulness and essential
surjectivity; generation alone would supply neither faithfulness nor the
full landmark.

## Coxeter geometry still required

The generic comparison does not identify its actual chambers or walls with
ribbon indices. This separate chain remains indispensable:

1. **Dominant fundamental-domain uniqueness.** If `φ` and `w·φ` are both
   dominant, prove `w·φ=φ`. Induct on Coxeter length: a left descent `i`
   gives `w⁻¹α_i<0`, so `(w·φ)(α_i)≤0`; dominance makes it zero, hence
   the simple reflection fixes `w·φ`, reducing the length. This uses root
   signs plus the already proved simple-reflection stabilizer criterion.
2. **Actual chamber labels.** Combine that uniqueness with the existing
   dominant translate and stabilizer theorems to prove that sign chambers
   are exactly `x·C_K`, uniquely labelled by `x W_K x⁻¹=W_J` and
   `x` minimal in `x W_K`. Show their flats agree using the already proved
   parabolic-fixed-space description. Positivity of all root coefficients
   of one sign proves relative regularity on each open face. The resulting
   finite disjoint open partition and convexity identify the actual sign
   components. Conjugacy alone must not be silently promoted to a statement
   about selected simple generators.
3. **Actual wall formula.** Prove that the wall of `x·C_K` indexed by
   `a∉K` is its facet `x·C_(K+a)`, and its unique adjacent chamber has
   label `(x v, K')`, where `v=w_K w_(K+a)` and
   `K'=parabolicTwistImage M (insert a K) K`. Prove that this `v` is the
   existing projection of `elementaryMu M K a`. All parabolics are finite
   under the global finite-group hypothesis, so the connected-component
   version of the formula is unnecessary here.
4. **Geodesic iff weighted length additive.** Prove Proposition 3.29 for
   actual galleries. An efficient alternative to its half-space proof is
   to count ambient positive roots over each distinct restricted hyperplane.
   The count is a positive weight. An adjacent crossing changes all signs
   over exactly one restricted hyperplane; inversion-set length then equals
   the sum of weights of separating hyperplanes. A repeated crossing adds
   a positive excess, giving the equivalence. Merely counting walls cannot
   be identified with ordinary Coxeter length, because these weights can
   differ from one. An arbitrary starting chamber changes the relative
   flat by its inverse label; use that transport explicitly.

Now send actual gallery edges to actual elementary ribbons. Geodesic
weighted length additivity and Matsumoto show a geodesic image is the
positive lift of its endpoint difference, proving `G` well defined.
Conversely the two words of each **chosen** pair-lcm relation have the same
Coxeter evaluation and, by the proved `AtomicCoxeter` theorem and the new
geodesic criterion, lift from any source chamber to geodesics with the
same endpoint. Thus these generating relations lift. The existing complete
signed ribbon presentation gives unique lifting of arbitrary ribbon arrows.
There is no need to prove an additional claim that chosen lcm words are
the only two geodesics, or that their unweighted atomic lengths agree,
to complete this particular route.

The free normalizer action preserves the second label and elementary wall
labels. Its orbits on chamber labels are exactly the associates of `J`.
Unique arrow lifting then proves `D/N≌R_J`, as in Proposition 6.3. A useful
implementation is the category with one representative chamber for each
orbit and arrows `Σ g:N, Hom_D(C_K,g·C_L)`, with composition translating
the second arrow by `g`. Prove it equivalent to the literal orbit groupoid;
do not define it to be the ribbon groupoid and assume the identification.

## Equivariance and the actual quotient

Choose the points `c_C` equivariantly, one point per chamber orbit and
extend along the free action. Freeness on chambers still needs proof;
freeness on individual points alone does not state this. In finite type a
short proof averages the orbit of a point of a chamber preserved by a
normalizer element. Convexity and strict inequalities keep the average
inside that chamber, giving a fixed real regular point; landmark 1 then
forces the quotient element to be the identity.

The linear action permutes the `U_C` and all overlap components. Uniqueness
of path classes in `U_D` proves that the edge functor `P` is equivariant
once the chosen real points are. The auxiliary selector `χ` and a chosen
quasi-inverse do not themselves need to be equivariant. Retain endpoint
casts or a natural-isomorphism formulation wherever objects are not
definitionally equal.

For `Pbar`, use the already proved **actual** quotient covering from
landmark 1: every path between projected chamber points lifts uniquely from
a specified starting lift, its ending lift is uniquely `g·a_D`, and homotopy
lifting identifies path classes exactly. This proves full faithfulness of
`D/N→FundamentalGroupoid Y`; path connectedness proves essential
surjectivity. The map is induced by the actual `orbitProjection`, so its
square with `P` commutes. The covering's path and homotopy lifting theorems
must be applied; the short exact sequence alone is not a replacement for
this groupoid comparison.

## GitHub candidates actually inspected

The local TauCeti checkout at
`/tmp/lemma28-full-search/tauceti` is pinned at
`62bbc0596dc3539d488232e4e924a338548ea0a9`. I inspected statements and the
construction of the following files, not an independent kernel replay of
their unimported closure:

| Supplier in `TauCeti/AlgebraicTopology/FundamentalGroupoid/` | Exact use |
| --- | --- |
| `Glue.lean`: `glue`, `map_subtypeVal_comp_glue`, `glue_obj_mk`, `eq_glue` | Actual neighborhood-cover descent to any category, no connectedness assumptions |
| `CoverGeneration.lean`: `iSup_im_map_subtypeVal_eq_top`, `functor_ext` | Path subdivision and uniqueness of locally specified functors |
| `Cech/Colimit.lean`: `isColimitCechCocone` | Colimit for any open cover, including disconnected overlaps |
| `Cech/Map.lean`: `cechMap_comp_cocone`, `isColimit_desc_cechMapCocone` | Maps of covered spaces and forced agreement with the ordinary induced functor |
| `SimplyConnected.lean`: `ContinuousMap.pathClass`, `pathClass_eq_mk`, `pathClass_comp_pathClass`, `map_pathClass` | Choice-free path classes inside the contractible tube members/components |

Using `Glue` directly avoids importing the larger Čech interface if the
proof is organized through the displayed strict local functors. The
fundamental-**group** file `VanKampen/Presentation/Cover.lean` is not suitable
for this tube cover: its theorem requires path connected triple
intersections, including repeated indices, while an adjacent pair already
has two components. The groupoid theorem has the correct hypotheses.

GitHub API checked during this task: TauCeti `main` was
`130523811f55c80f533e6024e190b945755f93c5`; the `Cech/Colimit.lean` blob
was `7bb9fc69947c9d34e1b34134c4e41a442fe15d79`, exactly matching the pinned
local file. This is source identity, not compiled acceptance.

The available `openai/math` source at
`/tmp/artin-landmark2-search/openai-math/lean/OAI/Topology/ArtinGroups`
was searched for arrangement/complement/fundamental-groupoid comparison
and its `Model.lean` definition read. `SalvettiCover M` there is the
realization of a nerve of ordinary Artin lifted cells. It does not mention
`J`, our actual relative flat or the complexified complement. The local
snapshot is not a git checkout, so I do not assign it an independently
verified revision. Current GitHub metadata was checked separately:
`openai/math main = 4eaee87548250b2682affda7d05d947c05554bae`, with
`Model.lean` blob `900a65a88e5b5c0d94507813b1d96d310730b794`.
No usable relative-complement comparison was located in that bounded
search; this is not a claim to have reviewed every upstream file or branch.
Ordinary Coxeter Salvetti statements cannot be instantiated by declaring
this restricted arrangement to be a Coxeter arrangement.

## First independently authorable obligations

The following small source obligations have concrete conclusions and no
desired-comparison premise. They can be completed before the large functor
assembly:

1. Generic finite nonzero functionals: one-parameter positive real
   perturbation and finite partial-sign chamber regions, with convexity,
   openness and connected-component identification.
2. Actual chamber tubes: `isOpen_tube`, `exists_mem_tube`, and explicit
   `ContractibleSpace` proofs for a member and each nonempty finite-overlap
   sign piece. This is elementary linear topology independent of ribbons.
3. Dominant orbit uniqueness by length descent, then the unique minimal
   chamber-label theorem using the existing dominant/stabilizer suppliers.
4. Finite arrangement gallery existence in convex partial-sign regions,
   sign-distance characterization, and overlap connector cancellation.
5. Actual longest-element wall formula and geometric weighted-length
   criterion. Only after these are proved consume `AtomicCoxeter` for
   pair-lcm relation lifting.

Items 1–2 and the dominant uniqueness part of item 3 are small initial code
units; no new Garside theory or contractibility of a universal cover is
needed. The full comparison still genuinely needs all the later gallery,
wall and descent proofs above. Importing the Čech theorem by itself does
not discharge them.

## Degenerate cases and conventions

* `J=∅`: this specializes to the ordinary reflection complement and
  Artin group. Both positive edge directions remain necessary.
* `J=Set.univ`: the flat is zero, there are no retained hyperplanes, `X`
  is a singleton, there is one chamber, no wall arrows and trivial ribbon
  vertex group and normalizer quotient. The tube proof uses the empty
  conjunction; it must not assume a retained root or a positive dimension.
* Empty index type/rank zero is included in the preceding case. A generic
  finite arrangement with no hyperplanes has one chamber equal to its
  ambient space; no generic-segment construction should demand a wall.
* Finite `M.Group` implies finite `I` by the existing `finite_index`; no
  crystallographic assumption, irreducibility or rank lower bound is
  permitted. Arbitrary `J` is supported.
* Ribbons `β:X→Y` compose by the actual product `β*γ` in path order;
  their convention is `β⁻¹ A_X β=A_Y`. Consequently chamber labels advance
  by right multiplication `x↦x·projection(β)`. The contragredient action
  evaluates using `w⁻¹`, as in the parent API.
* Category endomorphism multiplication reverses categorical composition.
  Landmark 2 already exposes opposite-group transports, while landmark 1
  raw endpoint monodromy targets `Nᵐᵒᵖ`. Keep categorical and path-order
  equations explicit here; resolving their final identity-on-`N` comparison
  belongs to landmark 4.

No original-article mathematical error was established in this investigation.
The missing suppliers described here are formal authoring obligations,
not defects in the cited statements.
