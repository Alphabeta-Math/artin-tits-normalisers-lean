# Landmark 5 prerequisites: compiled geometry, covers and local topology

**Full landmark 5, actual arrangement asphericity and full Theorem 1.8 are
not proved.** This report concerns a prerequisite checkpoint only. Seven
scientific modules plus the aggregate compile. The full prerequisite
technical battery and both independent final main A/B reviews passed.
Root accepted this prerequisite checkpoint and [clean final-mode CI passed](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43579352641).
The separate
eleven-module topology supplier cohort is already independently reviewed,
technically verified and root-accepted.

The [plan](milestone5-PLAN.md) and independent [contract A](milestone5-contract-a.md)
and [contract B](milestone5-contract-b.md) preserve the full target: actual
asphericity and K(π,1) conclusions for both `Theorem18.Complement M J` and
its actual `OrbitSpace M J`, at every basepoint, under finite actual
`M.Group`. There is no substitute classifying space, rank bound,
crystallographic restriction, or restriction on `J`. The accepted M4
fundamental-group identifications, both exact rows, both commuting squares
and the same actual Coxeter quotient remain unchanged.

The eventual K(π,1) group labels remain `Artin.pureNormalizerImage M J`
for the complement and `Artin.normalizerQuotient M J` for its orbit space,
using the actual M4 equivalences.

## What the compiled prerequisites prove

All modules are in the independent
[`asphericity/`](../../../asphericity/README.md) package, requiring
`sequences/` with the inherited pinned context. They reuse the original
dual flat, actual retained root kernels, complement topology and M3 chambers.

| Module | Actual conclusion and its boundary |
| --- | --- |
| [`FlatCoordinates`](../../../asphericity/ArtinAsphericity/FlatCoordinates.lean) | `relativeSubspace K ≃L[ℝ] ({i // i∉K}→ℝ)` by simple-root evaluation and zero extension. This chart needs no finiteness; finite rank gives a genuine basis and exact finrank. The standard facet is exactly the strict positive orthant. |
| [`Simpliciality`](../../../asphericity/ArtinAsphericity/Simpliciality.lean) | Every actual chamber is a strict finite-basis orthant, using the proved actual facet classification and continuous linear transport. Its closure is exactly the finite-basis pointed-cone hull and that cone satisfies native `IsSimplicial`. |
| [`FiniteArrangement`](../../../asphericity/ArtinAsphericity/FiniteArrangement.lean) | The distinct actual restricted kernels are finite, central, closed, proper and codimension one. `actual_arrangement_simplicial_hypotheses` bundles these with the actual basis/chamber statement; it does not assume an asphericity conclusion. |
| [`ConvexCover`](../../../asphericity/ArtinAsphericity/ConvexCover.lean) | A finite open cover of the original complement uses one of four strict real/imaginary sign conditions per retained form. Every nonempty intersection of a nonempty family is homeomorphic to an actual convex subspace and contractible. |
| [`UniversalCoverGeometry`](../../../asphericity/ArtinAsphericity/UniversalCoverGeometry.lean) | The original complement is strongly locally contractible, locally path connected and semilocally simply connected. Its actual endpoint/path-class universal cover has a surjective covering projection and path-connected, simply connected total space. Higher-homotopy projection isomorphisms and an asphericity iff are reductions, not vanishing proofs. |
| [`DirectedCover`](../../../asphericity/ArtinAsphericity/DirectedCover.lean) | A generic directed open cover by genuine contractible subspaces forces trivial actual cube homotopy groups: compact loop image and basepoint fit in one cover member. No such filtration of the actual universal cover is constructed or postulated. |
| [`Prerequisites`](../../../asphericity/ArtinAsphericity/Prerequisites.lean) | `actual_universal_cover_and_good_cover` bundles the proved actual covering, total-space connectivity and finite open good-cover facts. It has no actual-asphericity clause. |

Finite index type is derived from finite actual Coxeter group where needed.
Arbitrary index universes, reducible/noncrystallographic finite types, empty
rank and full/empty `J` remain included. In dimension zero the basis is
empty; no positive-dimensional assumption silently excludes that case.
The relative arrangement is not replaced by a new Coxeter reflection
arrangement.

The nonempty-family restriction in the cover theorem is essential. An empty
family intersects to the whole complement, whose contractibility is not
known or asserted. Cover members and their intersections may be empty;
contractibility is asserted only after nonemptiness is supplied. This is a
genuine good cover, but a good cover alone does not prove asphericity:
its nerve still needs an actual higher-topological comparison and an
appropriate contraction or higher-homotopy argument.

## The precise unproved core

One sufficient remaining statement is

```text
∀ z : ComplementUniversalCover M J, ∀ n : ℕ,
  Subsingleton (π_(n+2) (ComplementUniversalCover M J) z).
```

A genuine contraction of that actual space would also suffice. Direct
all-degree higher-homotopy vanishing for the original complement is another
valid route. None has been proved here. TauCeti's actual asphericity
predicate requires path connectedness and trivial genuine based cube
homotopy groups in every degree at least two. Simple connectedness of the
universal cover does not supply those higher groups, and weak
contractibility does not assert a contraction without an appropriate
additional theorem and its hypotheses.

The generic `DirectedCover` criterion retains genuine open coverage,
directedness and contractibility hypotheses. Applying it would require
constructing and proving those facts for actual subsets of the actual cover;
algebraic directedness of ribbon labels is insufficient. Likewise M3's
fundamental-groupoid equivalences control the one-type, not the higher
homotopy of the complement. No desired contraction, Deligne theorem or
model comparison is stored as a field that supposedly closes the target.

The remaining source-faithful chain includes positive/facet-local gallery
data, the capped chamber complex and its topology, contractible filtration
attachments, signed exhaustion, actual lifted-cover gluing, localized
intersection contractions and a genuine nerve/homotopy comparison. A
different construction from the new convex cover is possible only after
its actual comparison and the lifted nerve's higher topology are proved.
These are established mathematical obligations to formalize, not new open
problems or evidence against the article. Once actual complement
asphericity is proved, the accepted surjective orbit-cover transfer and
the inverse M4 group equivalences yield both intended K(π,1) conclusions.

## Selected topology proofs and verification checkpoint

The new supplier cohort is eleven **complete** TauCeti source modules at
`62bbc0596dc3539d488232e4e924a338548ea0a9`, covering universal-cover/local
topology and homotopy invariance/contractible-space homotopy groups. Their
union closure has sixteen already accepted unchanged TauCeti dependencies.
Only selected-cohort import paths are relocated to `ArtinAsphericityVendor`;
definitions, theorem statements and proof bodies are unchanged. Full original
bytes, Apache-2.0 license/headers, import-only diffs, deterministic assembly
recipe and exact applications are retained in
[`vendor/provenance.json`](../../../asphericity/vendor/provenance.json) and
[`source inspection`](../../../asphericity/evidence/providers/source-inspection.json).
This is full-module reuse, distinct from M4's two-proof extraction.

The [provider technical record](../../../asphericity/evidence/providers/verification.json)
binds successful builds, an exhaustive census of **310 canonical declarations
and 310 physical occurrences, with zero duplicates**, allowed transitive
axioms and eleven separate exact-module kernel replays. Both independent
supplier reviews and the later
[root acceptance](../../provenance/acceptance-landmark5-topology.json) bind
that exact cohort and its actual applications. Earlier pending-status fields
in the technical snapshot remain authentic historical fields. Supplier
acceptance is not acceptance of the whole prerequisite frontier, full M5,
or actual arrangement asphericity.

The complete [technical record](../../../asphericity/evidence/prerequisites-technical-20261114T090200Z/verification.json)
passed all **67 commands**, with **138 canonical project declarations and
138 physical occurrences**, zero project duplicates in this audit context,
and **19 fresh exact-module kernel replays**: eight project modules and eleven
suppliers. Root inspection checked every command's successful exit and log
digest, the coverage digest and all 1,280 frozen source/record input hashes.
The 996 inherited accepted inputs remain byte-identical. Both independent
GPT-6.1 Sol/high final reviews ([A](../../../asphericity/reviews/asphericity-prerequisites-a.md),
[B](../../../asphericity/reviews/asphericity-prerequisites-b.md)) accept these
exact statements and bindings. [Root acceptance](milestone5-prerequisites-root-acceptance.json)
records local prerequisite acceptance. The later
[closeout](milestone5-prerequisites-closeout.json) binds the actual successful
clean CI at source commit `3165671b648d24521a78d71aac47bd61d0500251`.
All scopes retain `full_landmark_5_proved=false`,
`actual_arrangement_asphericity_proved=false` and
`full_theorem_1_8_proved=false`, including after a prerequisite-only closeout.

The [permanent archive](github-evidence/run-43579352641/README.md) preserves
the original artifact ZIP, complete compressed Actions log, run/job/artifact
metadata, inventory and both reviews. Its
[validation](github-evidence/run-43579352641/archive-verification.json)
checked the GitHub artifact digest, all **67 successful command logs**,
**1,117 current repository source/record inputs**, the **996 unchanged
historical inputs**, all fifteen review-binding keys, the complete
138-project/310-provider physical coverage and all nineteen exact-module
replay results. Runner-specific compiled/toolchain hashes are recorded,
not compared to unrelated local binaries. Historical pending acceptance,
export and publication records remain unchanged.

From `asphericity/`, reproduction is:

```bash
python3 scripts/cache_prerequisites.py
python3 scripts/providers/assemble.py --check
python3 scripts/verify.py --plan
python3 scripts/verify.py --execute --mode final --output evidence/reproduction
```

Final mode requires the frozen prerequisite inventory and two accepted
`accept-asphericity-prerequisites` receipts. Technical mode performs checks
without that acceptance claim. Logs preserve actual commands, exits,
durations and source/context/artifact bindings. Only `propext`,
`Classical.choice`, `Quot.sound` are permitted. Official kernel replay is
relative to imported foundations; it is neither a second kernel nor a fresh
replay of all mathlib or all prior landmarks.

## Search, primary sources and retained findings

Three bounded GitHub investigations retain full commits, exact types,
dependencies, licenses, reading limits and dispositions:

- [OpenAI search](milestone5-search-openai.md), with
  [machine inventory](../../provenance/searches/m5-openai-inventory.json):
  ordinary Coxeter Salvetti contractions and generic order-realization
  tools do not provide the missing actual restricted-complement comparison.
  Machine screening of source bodies is distinguished from manual proof
  reading; the larger topology closure was not accepted wholesale.
- [TauCeti/mathlib search](milestone5-search-tauceti-mathlib.md), with
  [machine inventory](../../provenance/searches/m5-tauceti-inventory.json):
  genuine universal-cover and higher-homotopy tools were separated from
  conditional recognition theorems and non-topological name matches.
  Subsequent full-proof inspection and acceptance concern only the selected
  eleven new modules and recorded reused context.
- [Other-source search](milestone5-search-other.md), with
  [machine inventory](../../provenance/searches/m5-other-inventory.json):
  Colib/Quillen groupoid realizations, cover-nerve domination and filtered
  realization tools are genuine candidates, but do not establish this
  arrangement-specific comparison or contraction. They were not imported.

These searches do not establish worldwide absence of a useful theorem. The
[central proof-source register](../../provenance/GITHUB-PROOF-SOURCES.md)
preserves accepted uses separately from candidates and historical records.

The independent [contract A](milestone5-contract-a.md) records reading the
archived original Deligne, *Les immeubles des groupes de tresses généralisés*,
Invent. Math. 17 (1972), 273–302. Relevant locators are hypothesis 1.8 and
restriction Remark 1.9.1(ii), p.277; positive contraction 2.9, pp.288–289;
signed exhaustion/contractibility 2.14–2.15, pp.290–291; and the actual
cover/nerve/localization proof 3.7, pp.293–296. The source record read the
general proof in §§1–3 and visually checked selected pages; it did not read
the unrelated §4 applications or formally verify the prose proof.

The archived [IAS URL](https://publications.ias.edu/sites/default/files/Number18.pdf)
returned HTTP 403 on the contract's fresh fetch attempt, so no fresh-download
comparison is claimed. The archived PDF SHA256 is
`1905043232e1dadd97696372252bb5f91c202ea1b72379e77a9fecbfe9eed4bc`;
the extracted text SHA256 is
`ab83dc523206dc8484b36a93a5eb6012f6882a47a1b9e3161eae33e13ab98e9c`.
These are the contract's recorded reading limits, not a new primary-source
reading claim by this documentation task.

No new confirmed error in Deligne's theorem or the original article is
asserted. The qualified [Lemma 3.5 boundary-choice observation](milestone3-source-findings-a.md)
retains unresolved attribution and its local-hypothesis limits. The separate
[Godelle preprint findings](milestone2-normalizer-route.md) retain their
verified examples, corrections and journal-version limits; they are not
new defects attributed to the 2025 article. The missing higher-topological
bridge remains visible and blocks full landmark 5 and Theorem 1.8.
