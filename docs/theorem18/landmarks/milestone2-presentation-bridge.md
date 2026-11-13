# Milestone 2: canonical presentation and positive-image bridge

Status: source inspection and a derived implementation plan, 2026-11-14.
No OAI source, bridge Lean module, configuration, vendor record or dependency
cache was changed for this investigation. The signatures below are proposed
proof obligations, not claims of compiled declarations. The completed parent
Lemma 2.8 and Landmark 1 remain unchanged.

## Actual objects inspected

The inspected snapshot is
`/tmp/lemma28-full-search/openai-math/lean/OAI/Topology/ArtinGroups/`.
Its `lean-toolchain` says `leanprover/lean4:v4.34.1`. The parent uses
`v4.36.0-rc2` and mathlib revision
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. The snapshot directory has no
accessible Git metadata, so this investigation does not invent its repository
revision. The root's acquisition/provenance record must identify the upstream
snapshot. Selected inspected-file hashes are recorded below.

The OAI namespace is **`OAI.HarmonicArtin`**, not `OAI.Artin`. In
`Model.lean`:

```lean
alternating i j 0 = 1
alternating i j (n + 1) = FreeGroup.of i * alternating j i n
braidRelators M = Set.range (fun ij : I × I =>
  alternating ij.1 ij.2 (M ij.1 ij.2) *
    (alternating ij.2 ij.1 (M ij.1 ij.2))⁻¹)
Artin M = PresentedGroup (braidRelators M)
generator M i = PresentedGroup.of i
```

The parent `ArtinNormalisers.Artin.Group M` is the alias for
`TauCeti.ArtinGroup M = PresentedGroup (TauCeti.artinRelationsSet M)`.
Tau Ceti's relator is the product of its two free alternating words, with the
second inverted; its words are mathlib's `CoxeterSystem.braidWord M i j`.
Both presentations have arbitrary index type, arbitrary Coxeter matrix,
ordinary group multiplication, and no imposed generator involutions.
Zero entries contribute the identity relator; diagonal entries do too.

`Coxeter/PositiveBraidRelations.lean` defines the actual positive presentation:

```lean
positiveBraidRelations M u v := ∃ i j,
  u = FreeMonoid.ofList (altList i j (M i j)) ∧
  v = FreeMonoid.ofList (altList j i (M i j))
PositiveArtin M := PresentedMonoid (positiveBraidRelations M)
positiveGenerator M i := PresentedMonoid.of (positiveBraidRelations M) i
wordPositive M w := (w.map (positiveGenerator M)).prod
positiveToArtin M : PositiveArtin M →* OAI.HarmonicArtin.Artin M
```

The last map is defined by `PresentedMonoid.lift` on the actual OAI group
generators. Its generator and word formulas are proved in that file.

## Exact orientation calculation

OAI's `CoxeterExchange.altList i j n` **starts at `i`**. Mathlib's
`alternatingWord i j n` **ends at `j`**. These are compatible through

```text
altList i j n =
  if Even n then alternatingWord i j n
  else alternatingWord j i n.
```

For `n=0,1,2,3` the OAI lists are respectively `[]`, `[i]`, `[i,j]`,
`[i,j,i]`, which verifies the orientation of the displayed formula.
Its general proof is a list induction using `altList_succ`,
`alternatingWord_succ'`, and the parity change at a successor.
Also, by an elementary induction,

```text
alternating i j n = ((altList i j n).map FreeGroup.of).prod.
```

The source already proves
`altList i j n = (alternatingWord j i n).reverse` in `Coxeter/AltList.lean`.
This is useful corroboration, but **word reversal is not a group
homomorphism on a noncommutative group**. The bridge should use the parity
calculation, so every standard generator maps to the same standard generator,
without inversion, opposition, or reversed multiplication.

Let `δ(i,j)=(i,j)` when `Even (M i j)`, and `δ(i,j)=(j,i)` otherwise.
The two preceding identities and `M.symmetric` give the exact free-group
identity

```text
OAI-relator(i,j) = TauCeti.artinRelation M (δ(i,j)).1 (δ(i,j)).2.
```

Symmetry of `M` makes `δ` an involution. Therefore its range is all pairs,
and **the two relator sets themselves are equal**, not merely their normal
closures:

```lean
braidRelators_eq (M : CoxeterMatrix I) :
  OAI.HarmonicArtin.braidRelators M = TauCeti.artinRelationsSet M
```

Odd entries exchange the ordered pair; even entries leave it unchanged.
This also handles zero, diagonal, reducible and noncrystallographic cases.

## Generator-defined canonical group equivalence

The recommended public result is

```lean
presentationEquiv (M : CoxeterMatrix I) :
  OAI.HarmonicArtin.Artin M ≃* ArtinNormalisers.Artin.Group M
```

Construct the forward homomorphism with `PresentedGroup.toGroup`, sending
`OAI.HarmonicArtin.generator M i` to `Artin.generator M i`. Relator-set
equality proves its relations vanish by `PresentedGroup.one_of_mem`.
Construct the reverse homomorphism in the same way, or with
`TauCeti.ArtinGroup.lift` and the parity-converted OAI braid relation.
`PresentedGroup.toGroup.of` gives the two generator formulas.
`PresentedGroup.ext` proves both composites equal the identity. These are
actual maps with proved inverse laws; no equivalence is stored as an assumed
structure field.

The immediate compatibility statements should be:

```lean
presentationEquiv_generator :
  presentationEquiv M (OAI.HarmonicArtin.generator M i) = Artin.generator M i

presentationEquiv_word :
  presentationEquiv M (OAI.HarmonicArtin.wordArtin M w) = Artin.wordProd M w

presentationEquiv_parabolic :
  (OAI.HarmonicArtin.artinParabolic M J).map
      (presentationEquiv M).toMonoidHom = Artin.parabolic M J
```

The word formula follows by mapping a list product. The parabolic formula
follows from `MonoidHom.map_closure`, the image-of-image rule, and the generator
formula. OAI's `coxeterParabolic M J` and the parent's
`Artin.coxeterParabolic M J` already have the same defining expression
`Subgroup.closure (M.simple '' J)`.

Define the OAI-to-Coxeter map locally as
`(Artin.projection M).comp (presentationEquiv M).toMonoidHom`.
This sends its generator exactly to `M.simple i`. If the existing OAI
`artinCoxeter M` is later imported, `PresentedGroup.ext` and
`artinCoxeter_generator` prove equality to that map. Thus projection
compatibility fixes the actual Coxeter projection, with no automorphism of
the target group.

## Positive monoid image, and what it does not prove

Define the actual monoid homomorphism

```lean
positiveToParent (M : CoxeterMatrix I) :
  OAI.HarmonicArtin.PositiveArtin M →* Artin.Group M :=
  (presentationEquiv M).toMonoidHom.comp
    (OAI.HarmonicArtin.positiveToArtin M)
```

Its generator and word formulas follow from the source's
`positiveToArtin_generator`, `positiveToArtin_word`, and the group bridge.
For arbitrary `I` and `M`, without finite type or positive injectivity, prove

```lean
positiveToParent_mrange :
  (positiveToParent M).mrange =
    Submonoid.closure (Set.range (Artin.generator M))
```

The source's `positive_word_surjective` says every positive element is
`wordPositive M w`. It is a two-line consequence of
`PresentedMonoid.surjective_mk` and `wordPositive_mk`. Consequently the image
set is exactly the image set of `FreeMonoid.lift (Artin.generator M)`;
mathlib's `FreeMonoid.mrange_lift` identifies its monoid range with the
displayed closure. Alternatively prove the two containments by word
induction and closure induction. The analogous selected-generator image
identity follows directly from `MonoidHom.map_mclosure`.

This image theorem is **not** an embedding theorem. The 14–30-module core
does not prove `Function.Injective (positiveToArtin M)` for arbitrary positive
elements. It does provide degree, Coxeter projection, simple lifts, simple
factorization and prefix results inside the presented monoid. None should be
silently interpreted as cancellation or injectivity into the Artin group.

`positiveSimpleLift M w` is defined in `Harmonic/PositiveDegreeHom.lean` by
evaluating a chosen reduced expression in the positive monoid. Its composite
with `positiveToArtin M` is definitionally/propositionally the OAI
`positiveLift M w`; the short proof appears as
`positiveToArtin_simpleLift` in `Harmonic/SphericalLongest.lean`. Reprove that
short formula locally rather than importing its large unrelated closure.
After applying the bridge, its image is exactly
`Artin.wordProd M (OAI.HarmonicArtin.reducedExpression M w)`.
Tau Ceti's compiled Matsumoto theorem gives independence from the choice of
reduced expression, with no finite-rank restriction. There is no need to
replace the parent Artin group or assume a new positive-lift identification.

## Verified source dependency sizes and import traps

These counts were computed from transitive `import OAI.…` lines in the
inspected snapshot. They include the named module, exclude mathlib's closure,
and are source inventory counts, not build or axiom-audit results.

| Root module under `OAI.Topology.ArtinGroups` | OAI files | Source lines |
| --- | ---: | ---: |
| `Model` | 1 | 59 |
| `Coxeter.PositiveBraidRelations` | 14 | 1,628 |
| `Harmonic.PositiveDegreeHom` | 15 | 1,728 |
| `Harmonic.PositiveSimpleLiftMul` | 27 | 2,786 |
| `Harmonic.PositivePrefix` | 30 | 3,094 |
| `Coxeter.AlternatingLiftProd` | 167 | 18,267 |
| `Harmonic.ProbePositiveWordMonoid` | 342 | 34,280 |
| `Cancellation.SphericalPositiveCancelMonoid` | 344 | 34,344 |
| `Coxeter.ArtinCoxeter` | 373 | 37,642 |

In particular, importing `AlternatingLiftProd` for its elementary
`alternating_lift_prod` lemma pulls a fusion-packet development. Its displayed
proof is just induction and can be authored independently in the bridge.
Similarly, the existing `ArtinCoxeter` imports `FullSphericalCell`, even though
the desired projection follows directly from the presentation bridge.

The 342-file root proves
`spherical_positiveToAmbient_injective M T hT`, with exact conclusion

```lean
Function.Injective
  ((restrictedArtinHom M T).comp
    (positiveToArtin (restrictedMatrix M T)))
```

Its declared parameters are `S : Type`, `[Fintype S]`, `[LinearOrder S]`,
and `hT : IsSpherical M T`. The 344-file root derives injectivity for
`positiveToArtin (restrictedMatrix M T)` itself. These are genuine candidate
embedding theorems, but require their actual large proof closures to compile
and pass semantic/axiom review before use. The order instance is selectable
for finite indices; the `Type` universe restriction must also be handled,
for example by a proved reindexing equivalence with a finite `Fin n` model.
It must not become an undisclosed restriction on the requested arbitrary
finite Coxeter datum.

Every inspected positive-core file begins with `import Mathlib`. The old
toolchain, broad mathlib imports, and API drift require actual compilation
against the pinned parent environment. No compatibility result, kernel replay,
embedding theorem or ribbon-normalizer identification is asserted here.
The presentation/image bridge is a necessary supplier for that identification;
it is not the whole second landmark.

## Selected inspected source hashes

| Source | SHA256 |
| --- | --- |
| OAI `Model.lean` | `cb4f2e3fd5e75ca0b8783a477be79d7c89a643f2b108f39544b662c4b194595b` |
| OAI `Coxeter/AltList.lean` | `3e4fc0a5342ad41faa4adfea16ed4b77096fe55c06e079a9c52c603a628add78` |
| OAI `Harmonic/ReducedExpression.lean` | `5e404074ee09844e26d571b2ae2a55018e5633b2dab73938ccdf211a7e9f49a3` |
| OAI `Coxeter/PositiveBraidRelations.lean` | `0c208561919944d62482c7aa1275c1ae2496d37cdd79ea46b619207e0c9ab4ca` |
| OAI `Harmonic/PositiveDegreeHom.lean` | `f980380ceb24443786523b8b36f625b3728579943a55a9a6c03453d255c5ec5d` |
| OAI `Harmonic/PositiveSimpleLiftMul.lean` | `5a2f5b71e61549bc0b6fe4a705e857595c97cdd09ae18d481d14ad2545eb2a57` |
| OAI `Harmonic/PositivePrefix.lean` | `e2daec12467fd31a7a82a24125a01e95e4f9c1f93cda6c2a701476cd7ca74423` |
| Parent `ArtinNormalisers/Artin/Basic.lean` | `b9160bf44e7ae7aca86f7757158f742d5ca33c1eec527215e8238bd38a47c1da` |
| Parent `vendor/TauCeti/GroupTheory/Coxeter/Artin.lean` | `de27e110c9ec1e87cbb9c97cd8a07be3cf0d00ceb36d1cb874ae358b7706fad1` |

No mathematical error in the inspected source claims was established in this
bounded investigation. Large import closures and missing local compilation
are implementation/provenance obligations, not evidence of a false theorem.
