# Full Theorem 1.8: final scientific report

The complete scientific endpoint in `deligne/`—35 leaf proof modules and the
import-only aggregate—has [root mathematical acceptance](milestone5-root-acceptance.json).
Both independent GPT-6.1 Sol/high reviewers accepted the exact frozen
statements and proofs: [A](../../../deligne/reviews/theorem18-a.json),
[B](../../../deligne/reviews/theorem18-b.json). The [final local battery](../../../deligne/evidence/theorem18-local-final/verification.json)
passed all 159 commands, including a real clean/rebuild (19,433 jobs) and
64 fresh exact-module kernel replays. Complete canonical/physical auditing
covered 1,391 project and 475 new supplier declarations (1,866 total), with
zero duplicates, standard axioms only and unsafe/partial exclusions. All
1,781 bound inputs, including 1,264 accepted historical inputs, remained
unchanged. Clean GitHub CI is pending separately. Older accepted checkpoint
reports remain unchanged historical records.

## Original statement and exact formal endpoint

The source is Garnier–Heng–Licata–Yacobi,
[arXiv:2509.21915v3](https://arxiv.org/abs/2509.21915v3): Theorem 1.8 on PDF
p.3, Theorem 6.7 and Remark 6.12 on pp.26–27, and Corollary 6.14 with its
proof on p.27. Theorem 1.8 asks for the compatible algebraic/geometric short
exact sequences and both original-space K(π,1) conclusions. Corollary 6.14
supplies the quotient K(π,1) clause using arrangement asphericity and the
normal covering. The new endpoint retains all these conclusions.

In namespace `ArtinNormalisers.Deligne5`,
[`theorem_1_8`](../../../deligne/ArtinDeligne/Theorem18.lean) states, under
`M : CoxeterMatrix I`, `[Finite M.Group]`, `J : Set I`, for every
`x : Theorem18.Complement M J`:

```lean
actualNormalizerDiagrams M J x ∧
  TauCeti.IsEilenbergMacLaneSpaceOne (Artin.pureNormalizerImage M J)
    (Theorem18.Complement M J) x ∧
  TauCeti.IsEilenbergMacLaneSpaceOne (Artin.normalizerQuotient M J)
    (Theorem18.OrbitSpace M J) (Theorem18.orbitProjection M J x)
```

`theorem_1_8_all_basepoints` additionally states the quotient conclusion for
every actual orbit point. `corollary_6_14` is the named all-orbit-basepoints
K(`Artin.normalizerQuotient M J`,1) result. There is no assumption of a
comparison, asphericity, supplied simpliciality, nonempty index type,
irreducibility or crystallographic type. Arbitrary index universes, all
subsets, reducible groups, rank zero and empty/full parabolics are retained.
Finiteness of the actual Coxeter group implies the finite-index facts used
internally.

The frozen endpoint sources are:

| Source | SHA-256 |
| --- | --- |
| [`Theorem18.lean`](../../../deligne/ArtinDeligne/Theorem18.lean) | `6153e9ce05812013faae0917ee312192d6afc478c378c5819a9568a12ae118f8` |
| [`UniversalCoverComparison.lean`](../../../deligne/ArtinDeligne/UniversalCoverComparison.lean) | `70a04c0618870c1610b27c3e751f348a104c5f3995b682ad58b4d3ec15ec5f0d` |

## Actual spaces, groups and conventions

`Theorem18.Complement M J` is the original inherited-topology subset of
`relativeSubspace J × relativeSubspace J`. The flat consists of actual dual
vectors vanishing on the selected simple roots. The removed hyperplanes are
the actual root kernels whose restrictions to this flat are proper; a point
`(x,y)` is retained exactly when no retained root vanishes on both coordinates.
The finite-type interpretation of (3.26), its original contragredient action
and its original orbit topology were fixed in the earlier milestones.
`actualComplementHomeomorph` is identity on the real coordinates, rather
than a replacement space carrying desired properties.

`Theorem18.OrbitSpace M J` is the actual quotient by
`Artin.coxeterNormalizerQuotient M J`. The Artin group is the existing
standard braid-presentation group. `Artin.normalizerQuotient M J` is its
actual parabolic normalizer modulo its generated parabolic;
`Artin.pureNormalizerImage M J` is the image of the intersection with the
pure subgroup. None is defined as a fundamental group.

`actualNormalizerDiagrams` preserves both complete M4 exact diagrams,
including their actual induced maps and identity on the same Coxeter
quotient. The normalized comparisons are
`Sequence4.pureFundamentalGroupEquiv` and
`Sequence4.normalizerFundamentalGroupEquiv`; their inverses are exactly the
fundamental-group witnesses used in the two K(G,1) predicates. Ordinary
mathlib fundamental-group multiplication reverses traversal, so the raw
endpoint monodromy takes values in `Qᵐᵒᵖ` and sends the normalizer comparison
of `a` to `op ((Artin.normalizerQuotientMap M J a)⁻¹)`. Normalization applies
`op q ↦ q⁻¹`. The separate positive formulation uses opposite fundamental
groups and retains the labelled-path formula from Remark 6.12. No convention
is silently discarded when bundling the K(G,1) clauses.

The literal accepted TauCeti definitions are:

```lean
IsAspherical X x :=
  PathConnectedSpace X ∧ ∀ n : ℕ, Subsingleton (π_ (n + 2) X x)
IsEilenbergMacLaneSpaceOne G X x :=
  IsAspherical X x ∧ Nonempty (FundamentalGroup X x ≃* G)
```

The groups `π_ n` are actual based finite-cube generalized-loop homotopy
groups. This establishes every dimension at least two, with the actual
boundary/basepoint conditions. The predicate does not include a CW model,
a universal principal-bundle classification, or contractibility of a chosen
universal cover. Those stronger conclusions are not claimed here.

## Proof architecture

The earlier accepted M1–M4 results provide actual point-stabilizer/freeness
geometry and the normal quotient covering, the standard-presentation ribbon
normalizer identification, actual chamber/interval/fundamental-groupoid
comparisons, and every-basepoint exact-diagram compatibility. The existing
simpliciality and homotopy prerequisite packets remain inputs, not substitutes
for the new higher-topological comparison. This packet completes that bridge
by local constructions:

1. **Actual Garside model and based vanishing.**
   [`IncomingOrder`](../../../deligne/ArtinDeligne/IncomingOrder.lean),
   [`IncomingJoins`](../../../deligne/ArtinDeligne/IncomingJoins.lean) and
   [`IncomingMeets`](../../../deligne/ArtinDeligne/IncomingMeets.lean) construct
   the order/lattice on actual signed incoming reduced ribbons from positive
   generation and actual ribbon lcm/gcd. `GarsideWeights` uses the genuine
   weak finite-simplex topology with hereditary simple-chain support.
   `FiniteAncestry`, `GarsideFolds`, `GarsideShifts` and `GarsideTopology`
   prove finite contractible carrier factorization for actual compact maps.
   [`garside_genLoop_class_eq_const`](../../../deligne/ArtinDeligne/GlobalNullity.lean)
   includes the basepoint as a separate compact-domain summand and uses an
   injective unshifted carrier inclusion to retain every boundary condition.
   `garside_isAspherical` proves actual model asphericity; it is not inferred
   merely from free cube nullhomotopies or the model's fundamental groupoid.

2. **Original universal-cover charts and classifier.**
   `LiftedTubes` uses the existing based-path universal cover and genuine
   sheet sections. `LiftedTubeLabels` identifies their original path-class
   gauges with actual incoming ribbon labels. `CanonicalCells` and
   `CanonicalCarriers` construct a finite cover indexed by realized four-sign
   choices, with actual selected centers. `LiftedCanonicalCover` and
   `LiftedPartition` construct the actual lifted open cover and subordinate
   locally finite partition of unity. `NumerableWeights` and
   `universalCoverWeightsClassifier` in `CanonicalCoverWeights` give a continuous
   classifier from the original total space, without imposing a new metric
   or topology on it.

3. **Genuine geometric carriers and return.**
   `SheetIntervals` identifies the actual sheets through any point with an
   actual simple incoming interval. `LiftedTubeComponents` identifies each
   realized component of an arbitrary nonempty sheet intersection with its
   original contractible base sign piece. `GarsideTubeCarriers` proves that
   actual vertex points are connected inside all relevant simple-upper
   sheets, constructs monotone contractible finite-chain carriers, and
   descends `actualGarsideReturn` into the original universal cover.
   `CanonicalGarsideMap` gives the forward weighted-model map using the
   actual meet/join intervals. `CanonicalPacketCarriers` and
   `canonicalGarsideMap_return_carried` in `PacketCarrierCompatibility` prove
   that actual packet carriers contain both the common geometric points
   and the returned model points. The real-sign argument on disagreeing
   upper chambers is explicit; no arbitrary meet/common-sign principle is
   assumed.

4. **Constructed coherent homotopy and transfer.**
   `ContractibleExtension`, `ParametricExtension`, `ParametricFaceGluing`,
   `AcyclicCarrierFamilies` and `CarrierDescent` construct simplex maps and
   all-dimensional coherent parameterized homotopies from proved carrier
   contractibility and face monotonicity. `HereditaryWeights` supplies actual
   subspace/product finality; coordinate continuity alone is not used as a
   replacement for the weak topology. `NumerableCarrierHomotopy` glues the
   resulting tracks with the genuine partition of unity. Thus
   [`actualUniversalCoverComparisonHomotopy`](../../../deligne/ArtinDeligne/UniversalCoverComparison.lean)
   proves `actualGarsideReturn ∘ actualGarsideForward ≃ id`.
   Accepted `Homotopy5.isAspherical_of_dominated_by_aspherical` yields
   `actualUniversalCover_isAspherical`. Actual surjective covering transfer
   gives `actualComplement_isAspherical` and `actualOrbit_isAspherical`.
   Finally the unchanged M4 group comparisons give both literal K(G,1)
   clauses and the complete theorem bundle.

The article invokes Deligne's finite central simplicial-arrangement theorem
in Corollary 6.14. This formal proof supplies the required actual
higher-homotopy conclusion through the constructed ribbon model and
geometric domination. It does not assume a general Deligne theorem or
replace the relative restriction by a Coxeter arrangement for a new matrix.
Only the one composite homotopy needed for domination is asserted; a
two-sided nerve equivalence and contractibility of the whole cover are not
proved or needed by this endpoint.

## GitHub proof reuse and complete source records

The source inventory comprises **464 scientific supplier units from three
repositories**: 436 in the accepted historical cohorts and 28 new modules
for this packet. Mathlib, Lean and transitive build tooling are counted
separately. All three selected scientific repositories use Apache-2.0.

| Repository and exact commit | Historical/new units | Direct mathematical use |
| --- | ---: | --- |
| [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti/tree/62bbc0596dc3539d488232e4e924a338548ea0a9) `62bbc0596dc3539d488232e4e924a338548ea0a9` | 56 / 0 | Coxeter/Artin presentations, roots/parabolics, topology/Čech tools, genuine universal cover and K(G,1)/higher-homotopy transfer. |
| [openai/math](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae) `4eaee87548250b2682affda7d05d947c05554bae` | 359 / 12 | Earlier positive Artin embedding/calculus; new actual order weights, finite-carrier compactness, finite-chain charts, inclusions and nerve/weights homeomorphism. |
| [kangxyz/colib](https://github.com/kangxyz/colib/tree/bac5cab53eb6526e366e861d289253ec81aa89f0) `bac5cab53eb6526e366e861d289253ec81aa89f0` | 21 / 16 | Earlier numerable realization tools; new actual simplex-boundary HEP, cylinder-boundary pushouts and compatible face-track gluing. |

The [central ledger](../../provenance/GITHUB-PROOF-SOURCES.md) and its
[machine record](../../provenance/GITHUB-PROOF-SOURCES.json) preserve the
historical cohorts and complete linked search records. New exact source
records are [weights provenance](../../../deligne/vendor/provenance-weights.json)
and [carrier provenance](../../../deligne/vendor/provenance-carriers.json):
every upstream/local module path, original source hash, active hash, patch,
license and reused import is recorded. The complete new closures contain
12 OAI and 16 Colib modules; reused older modules are not counted again.
The weights cohort includes one explicit Lean-version continuity-tactic
port in `ConeWeights`, with unchanged statement/hypotheses. The Colib cohort
changes imports only. Preserved original files and explicit patches prevent
these relocated/ported modules being mislabeled byte-identical upstream.
Colib's comments retain indirect implementation lineage to
`kangxyz/quillen-k-theory` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`;
no additional source from that repository is counted as directly copied.

The [carrier search](milestone5-carrier-search.md),
[OAI search](milestone5-search-openai.md),
[other-repository search](milestone5-search-other.md) and
[TauCeti/mathlib search](milestone5-search-tauceti-mathlib.md) retain exact
candidate files/declarations, commits, query results and reading limits in
linked machine inventories. A query hit is not a source inspection, a read
proof is not a successful port, and an ordinary Coxeter Salvetti contraction
does not identify this restricted complement. Rejected/unselected leads
remain separate from the used proofs. These bounded searches make no claim
of worldwide absence of another suitable formalization.

## Consulted literature and source findings

No newly confirmed literature defect is asserted by this final packet.
This does not erase earlier qualified findings. The retained
[M2 findings table](milestone2-REPORT.md#consulted-source-findings-retained)
records: a sign error in the positive-central-power expression in Godelle's
`math/0202174v1`, PDF p.7; an invalid single-Δ factor-stripping reduction for
reducible subsets in the same preprint, p.12; and a local conjugation-direction
typo in `0811.0751v1`, p.28. The corrections, verified examples, precise
proof-line scope and absence of a journal-version comparison remain in the
[normalizer-route record](milestone2-normalizer-route.md). They are findings
about those prerequisite preprints, not defects attributed to the 2025
article or counterexamples to the normalizer splitting.

The original article's [Lemma 3.5 boundary-choice note](milestone3-source-findings-a.md)
retains its unresolved attribution/severity and local-hypothesis limitations.
It does not establish a false lemma or a new substantive article error. The
finite-W route here does not consume that boundary induction. The
[earlier M5 report](milestone5-REPORT.md) retains the original Deligne reading
record: §§1–3 and selected page images, archived PDF/text hashes, an HTTP403
on the fresh IAS fetch, and no reading claim for unrelated §4 applications.
That historical report's then-missing comparison is now addressed by the
new modules above; its historical status and reading limits remain intact.

## Reproduction and verification limits

Lean is pinned to `v4.36.0-rc2` and mathlib to
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. Transitive pins are committed in
the Lake manifests. From `deligne/`, the final verifier interface is:

```bash
python3 scripts/cache_prerequisites.py --plan
python3 scripts/cache_prerequisites.py
lake build ArtinDeligne
python3 scripts/verify.py --plan
python3 scripts/verify.py --execute --mode final --output evidence/theorem18-ci
```

Use a fresh output directory for each run. The cache helper fetches whole
pinned mathlib, as required by retained OAI imports, and performs no
`lake update` or manifest rewrite. The review-gated final battery cleans
only `artin-deligne`, explicitly builds **64 exact targets** (36 project,
28 new supplier), checks literal endpoint statement guards, exhaustive
private/generated/physical declaration coverage, standard transitive axioms
and unsafe/partial exclusions, then invokes the bundled kernel in 64 fresh
Lean processes through the previously accepted exact-module replay runner.
The runner uses the pinned official `LeanChecker.replayFromImports` algorithm
and checks each replay's physical declaration count. This avoids the official
CLI's prefix selector, which would also select descendants of the aggregate.
The allowed transitive axioms are only `propext`, `Classical.choice` and
`Quot.sound`; no `sorryAx` or native-evaluation premise is allowed.

These checks are relative to imported pinned mathlib and the accepted 436
older supplier units. They do not freshly replay all mathlib or every older
supplier and are not a second independently implemented kernel. Imported
compiled evidence, independent statement correspondence, source-bound final
reviews, clean final-mode execution, GitHub CI and publication binding are
distinct obligations. The actual local final record is
[`deligne/evidence/theorem18-local-final/verification.json`](../../../deligne/evidence/theorem18-local-final/verification.json),
SHA256 `38924ff028d9cf900ec491beba65f937c282734559ac6a0669525793f92be042`.
The [frozen inventory](../../../deligne/source-inventory.json), SHA256
`5b9c1f58867085b8f4d798c235d40a4221c3c8221e45eb3d1d6d4e0c7fecac3f`,
and [root acceptance](milestone5-root-acceptance.json), SHA256
`3ddaa380ad25e5f417e74c6e3f49b0d31709bfb80fc234e8b3b16c25977e1445`,
bind both final review receipts and all 24 source/context/tooling keys. The
[complete graph validation](../../provenance/deligne/validation-20261114T132100Z.json)
preserves all older roots, proof dependencies and physical occurrences.
The local clean pass and mathematical acceptance are completed; clean
GitHub CI and the source-publication binding remain pending at this science
checkpoint. No CI success, two-sided nerve equivalence or actual universal-cover
contractibility is inferred from the local result.
