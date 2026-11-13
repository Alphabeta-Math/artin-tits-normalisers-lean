# Landmark 2: positive Artin and ribbon supplier search

Research date: 2026-11-14. Scope: read-only pinned-source investigation for
the actual reduced ribbon normalizer identification in Theorem 5.6 and
the positive lcm/weak-order inputs behind (5.8) and Lemma 5.9 of
arXiv:2509.21915v3. Only this report was edited. No proof, configuration,
vendor file, review receipt, provenance or shared cache was changed.

## Decision

**Positive Artin prerequisites are present as concrete source candidates.**
The inspected openai/revised development defines the positive monoid by its
actual braid presentation, constructs its canonical map to the actual
presented Artin group, and proves spherical embedding, cancellation,
fractions, left/right gcd existence and left lcm existence. It also proves
the precise positive-lift divisibility/weak-order correspondence used in
Lemma 5.9 and identifies divisors of the fundamental element with reduced
Coxeter lifts.

**No reduced ribbon groupoid, its complete relations, or Theorem 5.6
normalizer decomposition was found.** These positive results do not by
themselves prove the requested landmark. They are candidates for filling
prerequisites, not a replacement definition of the ribbon groupoid or an
assumption of the normalizer conclusion.

Nothing is accepted as formally verified by this search. No candidate was
compiled, transitively axiom-audited, or kernel-replayed here. Source
inspection, absence of textual holes and repository claims do not replace
those acceptance steps.

## Article requirements checked

Read the full article's §5 in the workflow source `article.txt`, together
with the corresponding PDF text. In spherical type:

- Definition 5.1 has actual Artin elements as arrows, satisfying
  `A_I⁺ β = β A_K⁺`, and multiplication in `A` as rightward composition.
- Equations (5.2)–(5.4) define positive elementary ribbons from parabolic
  fundamental elements; Definition 5.5 generates the reduced subgroupoid
  using these particular arrows.
- Theorem 5.6 asserts the actual normalizer decomposition
  `Norm_A(A_J) ≅ A_J ⋊ R_J`, hence the quotient identification.
- Remark 5.7/(5.8) uses the positive left lcm and its two generating-ribbon
  expressions; the cited completeness of these relations is an additional
  theorem, not a consequence of ordinary Matsumoto.
- Lemma 5.9 uses the order isomorphism between positive reduced Coxeter
  lifts and weak left divisibility, as well as the actual ribbon/lcm
  structure, to identify these expressions with the Coxeter standard ones.

An abstract groupoid whose vertex group is defined to be the normalizer
quotient would omit these statements. No such construction is recommended.

## Pins and local source evidence

Fresh GitHub core-API HEAD checks returned the same commits already inspected:

| Repository | Commit |
| --- | --- |
| <https://github.com/openai/math> | `4eaee87548250b2682affda7d05d947c05554bae` |
| <https://github.com/mathcommunity/oai-math-revised> | `d25fae85c2f5ce5aadac40fb2b4c2d332b393d1c` |

The relevant complete `lean/OAI/Topology/ArtinGroups` tree is identical,
`0b8f7c175022e4696404bb2bbabf12746f899d14` (891 entries including
directories). Toolchain: Lean `v4.34.1`. Manifest mathlib:
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Root LICENSE is Apache-2.0.
The Lake file pins other external projects, but the selected local OAI
closure below imports only OAI modules and mathlib.

The immutable source bytes came from the existing downloaded checkout under
`/tmp/lemma28-full-search/openai-math`; selected copies, closure lists and
fresh remote-check records are under `/tmp/artin-landmark2-search/`.
`openai-positive-source-inventory.json` records each selected module's path,
line count and SHA256. These temporary files are search artifacts, not build
or acceptance certificates.

## Exact positive definitions

All following names are in `OAI.HarmonicArtin`, except the `WeakPrefix`
definition in its nested `CoxeterExchange` namespace.

Read the complete
[`Coxeter/PositiveBraidRelations.lean`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Topology/ArtinGroups/Coxeter/PositiveBraidRelations.lean):

```lean
def positiveBraidRelations (u v : FreeMonoid S) : Prop :=
  ∃ s t : S, u = FreeMonoid.ofList (altList s t (M s t)) ∧
    v = FreeMonoid.ofList (altList t s (M s t))

abbrev PositiveArtin := PresentedMonoid (positiveBraidRelations M)
```

`positiveGenerator` and `wordPositive` are the canonical presented-monoid
generators and their products. `positiveToArtin : PositiveArtin M →* Artin M`
is built by `PresentedMonoid.lift`, using the actual braid equations proved
in the presented group. It maps each positive generator to `generator M s`.
Here `Artin M := PresentedGroup (braidRelators M)` from `Model.lean`.

Thus embedding is not true by a definition identifying the positive monoid
with a subset of a group. It is an actual injectivity obligation and has a
separate source proof. Zero/infinite entries give empty braid words and
diagonal entries give identical one-letter words; neither adds a square
relation to the Artin group.

`Harmonic/PositiveDegreeHom.lean` proves an additive nonnegative word degree,
with degree zero iff identity, and defines
`positiveToCoxeter : PositiveArtin M →* M.Group`.
`positiveSimpleLift M w` evaluates a chosen reduced expression in the
positive monoid, and its Coxeter image is proved to be `w`.

`Harmonic/PositivePrefix.lean` defines actual left divisibility by
`PositivePrefix M a b := ∃ c, b = a * c`; its antisymmetry follows from
degree. This is not an arbitrary ordered structure assumed to be a Garside
monoid. Right divisibility is `PositiveSuffix M a b := ∃ c, b = c * a`
in `PositiveReverseHom.lean`.

## Directly relevant source declarations

| Module | Exact useful declaration/content | Hypotheses and limits |
| --- | --- | --- |
| `Harmonic/ProbePositiveWordMonoid.lean` | `spherical_positive_words_reflect`: equality of ambient positive word evaluations implies equality in the restricted presented positive monoid. `spherical_positiveToAmbient_injective`: injectivity of `(restrictedArtinHom M T).comp (positiveToArtin (restrictedMatrix M T))`. | Ambient `S : Type`, `[Fintype S] [LinearOrder S]`, `T : Set S`, `hT : IsSpherical M T`. Neither embedding nor cancellation is a premise. The proof uses a constructed quiver/probe action over `ℚ` and induction; its large closure requires verification. |
| `Cancellation/SphericalPositiveCancelMonoid.lean` | `sphericalPositiveCancelMonoid` constructs `CancelMonoid` using the proved injective ambient map. `spherical_positiveToArtin_injective` proves the restricted positive monoid embeds in its own presented Artin group. `spherical_positive_monoid_fractions` proves both `a b⁻¹` and `c⁻¹ d` positive fraction forms. | Same finite/ordered ambient type and spherical subset. The fractions theorem omits the ambient `LinearOrder` instance. No target normalizer statement is assumed. |
| `Cancellation/SphericalPositiveCancelLeft.lean` | `spherical_positive_cancel_left`, `spherical_positive_head`, `spherical_positive_gcd_left`, `spherical_positive_gcd_right`. The gcd conclusions quantify over all common divisors and prove their universal property. | Same ambient hypotheses and spherical `T`; cancellation is derived at these endpoints. Lower generic helpers sometimes take cancellation as an explicit premise, so use the spherical endpoints rather than silently discharging that premise. |
| `Harmonic/SphericalPositiveCommonMultiple.lean` | `spherical_positive_common_multiple` proves existence of common right multiples. `spherical_positive_lcm_left` proves `∃ c`, both inputs left-divide `c`, and `c` left-divides every common right multiple. | Same ambient hypotheses and spherical `T`. The existential is a genuine lcm universal property; it is not yet a chosen lcm operation or a ribbon-expression theorem. |
| `Harmonic/PositiveSimpleLiftMul.lean` | `positiveSimpleLift_mul` proves multiplication of reduced lifts under length additivity. `positive_simple_factors` proves both factors of a reduced lift are reduced lifts. `positive_fundamental_left_divisor_iff` and `positive_fundamental_right_divisor_iff` identify the divisors of the lift of a longest element with all `positiveSimpleLift M w`. | `[Fintype S]`; a supplied `z : M.Group` and proof that all Coxeter lengths are at most `length z` where a longest element is needed. No cancellation or embedding premise in these divisor statements. |
| `Harmonic/PositivePrefix.lean` | `positivePrefix_simple_iff u v`: `PositivePrefix M (positiveSimpleLift M u) (positiveSimpleLift M v) ↔ WeakPrefix M.toCoxeterSystem u v`. | `[Fintype S]`, no finite-group or embedding premise. `WeakPrefix cs u v` is exactly `length v = length u + length (u⁻¹*v)`. This is the order correspondence needed by the first paragraph of Lemma 5.9, not the missing ribbon comparison itself. |
| `Harmonic/PositiveLiftSimple.lean` | `positiveLift_longest_conjugate` lifts the action of a longest Coxeter element on simple generators. `positiveLift_longest_square_central` proves the square of its group lift commutes with every Artin element. `positive_fraction_longest` and `finiteArtin_positive_fraction` give positive word fraction forms. | `[Fintype S]`; explicit longest-element hypothesis, or finite `M.Group` for the finite endpoint. Useful Delta algebra, but no elementary-ribbon conjugation/generation theorem. |
| `Harmonic/RestrictedArtinHom.lean` and `RestrictedArtinHomSpherical.lean` | Canonical restricted-presentation homomorphism, generator/word formulas, range equal to the subgroup generated by the selected Artin generators; `restrictedArtinHom_spherical_injective`. | The range formula is general; injectivity has finite ordered ambient type and spherical subset. This is a faithful actual parabolic embedding candidate. |

Read these endpoint modules fully, together with `PositiveDegreeHom`,
`WeakPrefix`, `PositiveReverseHom`, and the actual model/alternation
definitions. Inspected the source proof of positive-word reflection and its
use of the proved probe action, rather than treating a theorem name as
evidence. I did not independently review every imported categorical/quiver
proof.

## Source closures and verification workload

Actual local import traversal, including apostrophes in module identifiers,
gave these OAI closures. All referenced OAI sources are present; the static
graphs have no import cycle. Remaining imports are mathlib.

| Endpoint module under `OAI.Topology.ArtinGroups` | OAI modules | Source lines |
| --- | ---: | ---: |
| `Coxeter.PositiveBraidRelations` | 14 | 1,628 |
| `Harmonic.PositiveSimpleLiftMul` | 27 | 2,786 |
| `Harmonic.PositivePrefix` | 30 | 3,094 |
| `Harmonic.ProbePositiveWordMonoid` | 342 | 34,280 |
| `Cancellation.SphericalPositiveCancelMonoid` | 344 | 34,344 |
| `Cancellation.SphericalPositiveCancelLeft` | 356 | 35,528 |
| `Harmonic.SphericalPositiveCommonMultiple` | 358 | 35,631 |
| `Harmonic.RestrictedArtinHomSpherical` | 340 | 34,007 |

The union of the lcm and restricted-parabolic-injectivity closures has
359 modules/35,668 lines. These exact unchanged source copies and their
hash inventory are in the task's temporary candidate directory. A source
screen of that union found no `sorry`, `admit`, `sorryAx`, `native_decide`,
`implemented_by`, or custom `axiom`/`unsafe def`/`unsafe theorem`/`opaque`
declaration. This is only a screen. It does not establish successful
elaboration, compatibility with the parent mathlib pin, transitive axiom
purity, or valid kernel replay.

In particular, the large embedding proof is a different trust/porting task
from the small reduced-lift/divisor closure. No package update or build
attempt was made merely to support a suitability claim.

At root's request, the unchanged 30-module `PositivePrefix`/
`PositiveSimpleLiftMul` closure was also staged separately at
`/tmp/artin-landmark2-search/pilot-source/OAI/`. Its
`source-provenance.json` binds all source hashes, the complete dependency
graph, topological order, upstream license and pins, and the proposed
parent-toolchain target; `topological-order.txt` gives the compilation
order. This staging is not repository vendoring or a successful
compatibility result. The exact useful names are
`OAI.HarmonicArtin.positiveSimpleLift_mul`,
`OAI.HarmonicArtin.positive_fundamental_left_divisor_iff`,
`OAI.HarmonicArtin.positive_fundamental_right_divisor_iff` in
`Harmonic.PositiveSimpleLiftMul`, and
`OAI.HarmonicArtin.positivePrefix_simple_iff` in
`Harmonic.PositivePrefix`.

## Compatibility with the existing parent Artin model

The parent aliases `TauCeti.ArtinGroup M`; it must remain the actual target
group. The OAI Artin group is a second presented-group definition, **not
definitionally equal** to that alias. A canonical comparison would need
actual proofs of the following bridges:

1. Translate OAI's `altList s t n`, which starts at `s`, to mathlib/TauCeti's
   `alternatingWord s t n`, which uses its established ending convention.
   OAI proves `altList s t n = (alternatingWord t s n).reverse`;
   TauCeti proves the parity-dependent reversal identity. Hence the two
   families impose the same braid equations, possibly with their two
   sides swapped. They are not syntactically the same relator set.
2. Construct generator-preserving homomorphisms in both directions by the
   two presentation universal properties, prove both inverse laws by
   generator extensionality, and track the actual Coxeter projection.
3. Prove this isomorphism carries OAI `artinParabolic` to the existing
   parent subgroup closure. Identify the positive embedding's range with
   the submonoid generated by the actual parent Artin generators, as used
   for `A_I⁺` in Definition 5.1.
4. Transport positive reduced lifts, Delta elements, restricted-matrix
   inclusions and left/right divisibility through these actual maps.
   Positive lifts chosen by different reduced words agree by the proved
   monoid Matsumoto result; this still needs to be expressed in Lean.

The spherical embedding endpoints use a universe-zero finite ordered
ambient type and a restricted matrix on `T`. Applying `T = Set.univ` still
produces a presentation indexed by a subtype. The parent theorem permits
arbitrary indexing universes; a finite reindexing through `Fin n` and its
generator-preserving presentation equivalences must be proved if needed.
Choosing a finite order is not a new mathematical hypothesis, but it is
not a definitional transport either. No scope reduction is proposed.

The external Lean/mathlib pins also differ from the dedicated package's
mathlib `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; no compatibility is
inferred from source inspection or from the fact that a newer Lean exists.

## What remains missing

The complete inspected ArtinGroups tree has no `ribbon` or `Garside` term,
no elementary-ribbon groupoid, and no semidirect-product normalizer
decomposition. Its normalizer hits concern unrelated parabolic-intersection
stabilizer tests. Searches for Delta also return an unrelated indicator
function in the Coxeter inversion proof; that is not a fundamental element.

Still required for the whole landmark:

- actual elementary ribbon definitions and their positive-parabolic
  conjugation identities, including sources, targets and composition;
- generation of every required monoid-preserving conjugator by ribbons
  together with its parabolic factor, with the required uniqueness;
- the actual normalizer semidirect decomposition and the induced quotient
  isomorphism, with Coxeter projection tracked;
- the two elementary-ribbon expressions of their lcm, completeness of
  the necessary ribbon relations, and their identification with the
  Coxeter standard expressions in Lemma 5.9;
- any additional groupoid composition/opposite conventions needed when
  passing to the vertex group.

The positive lcm and order correspondence are directly relevant to some
of these proofs, but none of the missing assertions is declared proved
because those prerequisites exist. In particular, a generic abstract
Garside interface assuming the normalizer decomposition would not fill
this gap.

## Search limits and source attribution

Used fresh core-API commit checks, the already complete immutable tree,
local source search and actual import traversal. No broad GitHub search
or rate-limit-dependent absence claim was used. This report covers the
openai/revised ArtinGroups development, not every file in those repositories
or every external formalization. Related sources already assessed in
`docs/full/external-prerequisites.md` were not relabeled as new suppliers.

The article's Theorem 5.6 and ribbon relations cite independent published
inputs; absence of a reusable Lean supplier is an outstanding formalization
obligation, not an open mathematical problem or a defect in the article.
No mathematical error was established in any inspected source. All
acceptance, compilation, axiom and replay limits above remain explicit.
