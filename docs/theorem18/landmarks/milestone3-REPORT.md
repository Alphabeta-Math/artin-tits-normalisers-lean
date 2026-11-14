# Landmark 3: actual equivariant geometric comparison

## Status and scope

The scientific proof is complete and compiled: all 42 scientific modules in
`chambers/ArtinChambers/` and the aggregate `ArtinChambers` have built.
The complete source-bound local technical build/audit/replay battery passed.
Both final independent statement reviews accepted the exact development, and
the root mathematical acceptance is recorded. Final-mode verification and
fresh clean Landmark 3 CI remain pending; no CI success is claimed here.

The final theorem is
[`ArtinNormalisers.Chamber3.landmark_3`](../../../chambers/ArtinChambers/Landmark3.lean).
For arbitrary `I`, `M : CoxeterMatrix I`, `[Finite M.Group]` and `J : Set I`,
it proves the actual geometric/ribbon comparison and covering square described
below. No independent finite-rank, irreducibility, crystallographic or
nonempty-parabolic hypothesis is imposed. Rank zero and empty/full `J` are
included. The algebraic Lemma 2.8 and accepted Landmarks 1 and 2 are preserved.

**Landmarks 4 and 5, and therefore full Theorem 1.8, remain unproved.** The
current result does not assert the compatible based fundamental-group exact
sequences or either asphericity conclusion.

## Exact geometric and algebraic objects

`Complement M J` is the existing actual relative complement. Its real flat
`Θ_J` is a submodule of `Module.Dual ℝ (I →₀ ℝ)`, annihilating the simple
roots indexed by `J`. Retained roots are actual geometric roots whose
evaluation is nonzero somewhere on this flat. The complement consists of
pairs in `Θ_J × Θ_J` which do not simultaneously vanish on any retained
root, with the inherited topology. Repeated root/hyperplane labels are allowed;
the formal arrangement does not require a chosen irredundant list.

`actualForms M J` is this same family of continuous linear evaluations, and
`actualComplementHomeomorph` identifies its real-pair complement with the
existing `Complement M J` by the actual two coordinates. Chambers are nonempty
strict sign cells, proved to be the connected components of the actual real
regular locus. This is not a replacement by an abstract classifying space.

Let `D` be `IntervalGroupoid (actualForms M J)`. Its objects are the actual
chambers, through explicit wrappers. Its positive generators `[C,D]` range
over **all ordered chamber pairs**, with relations

```text
[C,C] = 1
[C,F] = [C,D] ≫ [D,F]   if ChamberBetween C D F.
```

Here `ChamberBetween C D F` says that whenever `C` and `F` have the same
sign on a form, `D` has that sign too. The construction is a free groupoid
quotient by precisely these relations and their category congruence; it has
the proved extension/uniqueness property for arbitrary groupoid targets.
Opposite positive arrows are distinct generators, not defined as inverses.

This interval presentation is the implemented alternative to the article's
literal adjacent-gallery presentation. No theorem identifying those two
presentations is asserted. Instead, the interval model itself is compared
directly with the actual complement and the independently defined actual
reduced ribbons, which suffices for the comparison proved here.

Let `R = AssociateReducedRibbonObject M J`, the full `J`-associate component
of the Milestone 2 reduced ribbon groupoid. Its arrows retain their actual
Artin-group values and the proved complete chosen-lcm signed presentation;
it is not defined to be an orbit quotient of `D`. Finally, let
`Q = Artin.coxeterNormalizerQuotient M J = N_W(W_J)/W_J` and
`Y = OrbitSpace M J` for the existing actual action.

## Proved comparison and proof route

The development proves:

1. `actualIntervalForward : D ⥤ FundamentalGroupoid (Complement M J)` is an
   equivalence and is strictly equivariant for the actual `Q` actions.
2. `componentRibbonFunctor : D ⥤ R` is a covering functor, literally
   surjective on objects, with object fibers exactly the actual `Q` orbits.
3. The actual orbit projection induces the covering functor
   `orbitFundamentalGroupoidFunctor` on genuine fundamental groupoids.
4. `actualRibbonOrbitEquivalence : R ≌ FundamentalGroupoid Y` is an actual
   equivalence, with the strict equality

   ```text
   componentRibbonFunctor ⋙ actualRibbonOrbitEquivalence.functor
     = actualIntervalForward ⋙ orbitFundamentalGroupoidFunctor.
   ```

5. Both specified orbit cocones are colimits in ordinary `Grpd`.

The scientific dependency chain is as follows.

| Stage | What is proved on the actual objects |
| --- | --- |
| Geometry | Sign cells are the real components. Chamber tubes form an open cover. Each tube is contracted first by moving the imaginary coordinate to a chosen chamber point at fixed real coordinate, then by moving the real coordinate with that regular imaginary coordinate fixed. Overlap components are explicit sign pieces with contractions. A simultaneous straight-line contraction is not used. |
| Groupoid van Kampen | The actual open subspaces supply a Čech cocone in genuine fundamental groupoids. The accepted open-cover theorem proves its colimit and map naturality. Tube connectors and gluing give the interval/complement functors and both natural isomorphisms. |
| Coxeter transport | Actual regularity/stabilizer criteria and facet labels identify the chambers. Minimal transporter and root-inversion arguments turn Between relations into positive ribbon composition; ambient Coxeter length is not identified with the number of restricted walls. |
| Signed ribbon lifting | The complete Milestone 2 chosen-lcm relations extend to arbitrary groupoid targets, including actual chamber families. They produce lifts of every signed ribbon arrow. Recovery and uniqueness give inverse maps on the entire outgoing arrow sums, including literal endpoints. This proves the actual signed ribbon covering. |
| Actual actions and fibers | Canonical chamber points are chosen equivariantly. Strict equivariance holds on all arrows. For both actual covers, literal object surjectivity, invariance and orbit fibers are proved, rather than a transitivity hypothesis on all chambers being assumed. |
| Descent and comparison | Generic covering descent constructs the unique strict descent of any invariant functor. The actual upstairs equivalence, its object-injectivity and the two actual covers give a fully faithful, essentially surjective downstairs functor and the strict square. |

The generic `CoverOrbitData` fields contain only covering, literal object
surjectivity, strict invariance and orbit-fiber conditions. All are supplied by
proved statements for these actual models. Descent, the downstairs equivalence
and the orbit universal properties are conclusions, not input fields. The two
ordinary `Grpd` colimits are established separately from descent. In
particular, the argument does not transport a 1-colimit through an equivalence
as though that equivalence were an isomorphism in `Grpd`.

## The same quotient and every signed endpoint

[`RibbonDeckLabels.lean`](../../../chambers/ArtinChambers/RibbonDeckLabels.lean)
proves `ribbonLiftingFunctor_index_projection` and
`ribbonLiftEndpoint_projection` for every signed ribbon arrow. Thus the index
transport and literal lifted endpoint are those of its actual Coxeter
projection, not just of its positive generators.

At `standardActualChamber M J`,
`ribbonLiftEndpoint_reducedLoop` identifies the endpoint of every actual
reduced ribbon loop with

```text
reducedRibbonCoxeterProjection M ⟨J⟩ r • standardActualChamber M J.
```

`ribbonLiftEndpoint_loopArrow` gives the corresponding formula for every
signed loop arrow. The action is by the same actual `N_W(W_J)/W_J` appearing
in the algebraic normalizer sequence and actual topological cover. There is
no unspecified automorphism of the quotient in this result. Passing to based
fundamental groups, resolving mathlib's opposite-group path convention and
proving both compatible exact-sequence squares remain Landmark 4; this report
does not infer them from the endpoint formula alone.

## Pinned proof inputs and provenance

The central [GitHub proof-source register](../../provenance/GITHUB-PROOF-SOURCES.md)
separates accepted imports, inspected candidates and uninspected search hits.
The package inherits Lean `leanprover/lean4:v4.36.0-rc2` and mathlib
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`, requiring the unchanged
`ribbons/` and `landmarks/` path packages. Earlier accepted suppliers include
the parent TauCeti inputs, the two Landmark 1 sign modules, and the
359-module OpenAI positive-Artin closure recorded in the
[Milestone 2 report](milestone2-REPORT.md). They are reused as accepted
dependencies, not claimed to have been freshly replayed in full here.

The additional geometric supplier is TauCetiProject/TauCeti at
`62bbc0596dc3539d488232e4e924a338548ea0a9` (Apache-2.0). The required Čech
closure has twelve modules: three are reused unchanged from the parent and
**nine are new**, totaling 1,849 source lines, **232 canonical declarations
and 232 physical occurrences**. The new files cover TopCat Čech diagrams,
refinement and maps, fundamental-groupoid cover generation/gluing and Čech
colimits/maps, and the needed metric Lebesgue lemma.

Only imports are relocated to `ArtinChamberVendor`; declaration namespaces
remain TauCeti. No proof body, statement or hypothesis port was needed.
Original bytes, full patches, hashes, import edges and license are preserved in
[`chambers/vendor/`](../../../chambers/vendor/README.md). Upstream used the
same Lean rc2 and mathlib `e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`;
the accepted checks compiled against this development's exact mathlib pin.

The [separate supplier acceptance record](../../provenance/acceptance-landmark3-cech.json)
binds two independent supplier reviews, all nine builds, the 232-declaration
standard-axiom audit and nine exact-module kernel replays. It also records the
metadata transition between initial build and audit/replay; mathematical
supplier/configuration inputs were unchanged. This record accepts the supplier
cohort only. The previously accepted declaration-reference graph through
Milestone 2 is not represented as a final graph of this new development.

## Verification checkpoint and reproduction

The complete [technical receipt](../../../chambers/evidence/landmark3-technical-20261114T074500Z/verification.json)
has SHA-256
`0fd1675ebba198731bfd2ffe99232ee94d2fc92c1ec08b9b2bc75686e54464fb`.
It records **132 successful commands and 52 exact-module kernel replays**:
43 project modules (42 scientific files plus aggregate), 1,071 project
declarations with zero duplicates, and the nine new provider modules with
232 declarations. Only the three permitted standard axioms occur. The 855
older context inputs remain byte-for-byte unchanged.

The complete merged dependency export records 2,375 distinct project names
and 2,377 physical occurrences. The generated theorem
`ArtinNormalisers.Ribbon2.elementaryMu.congr_simp` occurs with identical
type, proof and universe parameters in `CofinalRibbons`, `RibbonWords` and
`PositiveTransport`. Canonical ownership depends on import order: the M3
audit owns it in `PositiveTransport`, while the full dependency observer
owns it in `CofinalRibbons`. Thus the earlier 1,305 project roots plus the
M3 audit's 1,071 names share one name: 2,375 distinct names, with two
additional identical physical occurrences. Both contexts and all occurrences
are retained; these are not three independent results. See the
[source register](../../provenance/GITHUB-PROOF-SOURCES.md) for exact records.

The frozen [source inventory](../../../chambers/source-inventory.json)
has SHA-256
`607626167363747853289eaafd4e6a96e32dbb7d9af88f975c0637818f71d5f5`.
It retains its historical candidate status unchanged. The subsequent
[root acceptance receipt](milestone3-root-acceptance.json) records mathematical
acceptance after validating both final review bindings, all 43 project sources,
the 855 preserved context inputs and the exact audit/technical evidence.
The independent final receipts are
[A](../../../chambers/reviews/landmark3-a.json) and
[B](../../../chambers/reviews/landmark3-b.json), with separate prose reviews
[A](../../../chambers/reviews/landmark3-a.md) and
[B](../../../chambers/reviews/landmark3-b.md).

| Check | Status at this report checkpoint |
| --- | --- |
| Scientific sources and full `ArtinChambers` aggregate compilation | Passed; 42 scientific modules frozen |
| New nine-module supplier build/audit/replay and two supplier reviews | Passed; supplier-only acceptance recorded |
| Complete source-bound local technical build/audit/replay battery | Passed; receipt and scope above |
| Both final independent main statement reviews and root mathematical acceptance | Passed; exact-source receipts above |
| Final-mode verification receipt | Pending |
| Fresh Landmark 3 GitHub CI | Pending |
| Full Theorem 1.8 | Unproved: Landmarks 4 and 5 outstanding |

From the repository root, with the pinned `lake` on `PATH`:

```sh
python3 chambers/scripts/cache_prerequisites.py --plan
python3 chambers/scripts/verify.py --plan
python3 chambers/scripts/cache_prerequisites.py
python3 chambers/scripts/verify.py --execute --mode technical --output chambers/evidence/reproduction-technical
python3 chambers/scripts/verify.py --execute --mode final --output chambers/evidence/reproduction-final
```

Output directories must be new. The cache helper checks the inherited pins and
protected configurations before fetching prerequisites; it does not update the
dependencies. The verifier cleans only the new `artin-chambers` package. Its
scientific scope is the 42 modules plus aggregate, together with the nine new
suppliers. It binds the actual sources, configurations, tooling, review/context
inputs and compiled outputs; checks canonical declarations and physical
occurrences including private/generated declarations and duplicate equality;
rejects proof holes through the transitive axiom audit; and replays each exact new module in
a fresh kernel process. Permitted axioms are `propext`, `Classical.choice` and
`Quot.sound`, not `sorryAx`, custom axioms or native decision axioms.

Technical mode never claims semantic acceptance. Final mode additionally
requires the root-owned `chambers/source-inventory.json` and two matching
`accept-landmark3` receipts. Both reviews and root acceptance are now recorded;
a final-mode execution result is not yet claimed. For ordinary compilation,
`lake build ArtinChambers` from `chambers/` is sufficient, but it does not
replace these checks.

Replay uses the pinned Lean kernel and exact-module checker algorithm relative
to imported mathlib and accepted older dependencies. It is neither a separate
kernel implementation nor a fresh replay of every old supplier or mathlib
declaration. Earlier Landmark 1/2 CI receipts remain historical evidence for
those landmarks, not new Milestone 3 CI.

## Consulted-source findings retained

The independent [Lemma 3.5 source note](milestone3-source-findings-a.md)
examines arXiv:2509.21915v3, PDF p.8, including the complete proof and its
closed-chamber notation. Its disposition is **unresolved attribution/severity
of a boundary-representative proof clarification**, not a confirmed substantive
article defect or a false lemma. In rank one, an arbitrary closed-chamber
representative can give a negative transformed root with zero evaluation and
can have nontrivial `w` while all simple evaluations are nonnegative. The first
example fails the proof paragraph's additional interior-hyperplane hypothesis;
the second permits a better witness or an early boundary case. No
counterexample to the lemma was found. The note gives a valid ordinary
mathematical finite-inversion-image argument using only the needed one-way
implication, explicitly not a Lean-verified proof from that note.

The present finite-`W` formal proof obtains finiteness of the actual root and
restricted-form families directly. It does not consume Lemma 3.5's induction
or require an unproved repair of that passage. The note retains exact PDF
hashes, reading limits and the dismissed scope of the first counterexample.
No original-article defect is claimed by this report.

The earlier prerequisite findings remain recorded in the
[Milestone 2 report](milestone2-REPORT.md#consulted-source-findings-retained)
and [normalizer route](milestone2-normalizer-route.md):

| Inspected source | Retained finding and effect |
| --- | --- |
| Godelle, arXiv:math/0202174v1, PDF p.7, proof of Proposition 2.1 | Confirmed exponent-sign error in the displayed positive-clearing line: a negative generator excludes `g=hΔ_S^(2n)` with positive `h`; use exponent `-2n`. |
| Same preprint, PDF p.12, proof of Proposition 4.4 | Confirmed overapplication of an indecomposable stripping lemma to arbitrary reducible `X`; the commuting rank-two example invalidates that reduction, not the splitting conclusion. The formal route strips arbitrary positive parabolic factors. |
| Godelle, arXiv:0811.0751v1, PDF p.28, proof of Theorem 4.25(ii) | Confirmed local conjugation-direction typo. The compatible conclusion is `r₁⁻¹ A_X⁺ r₁=A_Z⁺`; the recorded `B₃` calculation checks the orientation. |

These concern the exact inspected prerequisite preprints, not defects
attributed to the original article or unchecked journal versions. The prior
records also retain unproved literal-presentation dictionaries and actual
source hypotheses without treating a missing local proof or unsuccessful
search as an open problem or literature error.
