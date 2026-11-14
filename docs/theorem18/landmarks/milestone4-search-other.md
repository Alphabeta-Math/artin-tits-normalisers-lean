# Landmark 4: exact vertex-group and basepoint prerequisites

Research date: 2026-11-14. Baseline repository:
`1aa55a9ee5f13c9e3a8e64b4aec4675c0435a9c0`. Read the complete
[`milestone4-PLAN.md`](milestone4-PLAN.md), the current main landmark plan,
and the actual M1/M2/M3 map APIs before proposing reuse. No earlier scientific,
configuration or review source was changed by this search.

## Selected result and present verification status

Root selected **exactly two TauCeti declarations**, extracted verbatim into
`ArtinSequenceVendor.FundamentalGroup.BasepointChange`, from
`TauCetiProject/TauCeti` at `62bbc0596dc3539d488232e4e924a338548ea0a9`:

- `FundamentalGroup.fundamentalGroupMulEquivOfPath_apply`, original lines
  129–148 including its documentation and local namespace opening.
- `FundamentalGroup.map_fundamentalGroupMulEquivOfPath`, original lines
  196–212 including its documentation and local namespace opening.

The complete original 651-line file, Apache-2.0 license, original copyright
header, selected-block hashes, full mechanical diff and deterministic assembly
recipe are preserved in [`sequences/vendor/`](../../../sequences/vendor/README.md).
The original namespace and both declaration/proof blocks remain unchanged;
the new wrapper imports only two existing pinned mathlib modules. The full
upstream BasepointChange file and its unrelated dependencies are not imported.

The actual selected module passed explicit Lake compilation, exhaustive
canonical/physical transitive axiom audit and fresh exact-module official
`leanchecker` replay. Coverage measured **2 canonical declarations, 2 physical
occurrences, no duplicates**, with only `propext`, `Classical.choice` and
`Quot.sound`. The measured replay took 5.87 seconds. Inputs were unchanged
through audit and replay. Raw commands/logs/hashes, displayed elaborated
statements and environment bindings are in
[`sequences/evidence/providers/verification.json`](../../../sequences/evidence/providers/verification.json).
Replay is relative to imported pinned mathlib, not a new replay of all mathlib
or an independent kernel implementation.

**The technical record predates independent acceptance.** Both independent
supplier review receipts are now available in `sequences/reviews/providers-a.json`
and `providers-b.json`, with verdict `accept-supplier-cohort`; their hashes are
recorded in the inventory. Root mathematical acceptance is not asserted here.
Technical success is not reported as completion of landmark 4. The generic alternatives below remain
source-inspected candidates; they were not compiled, audited or replayed by
this search. No new FormalFrontier, Oka, sphere-six or other source was imported.

## Directly usable existing APIs

The project uses Lean `v4.36.0-rc2` and mathlib
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. These are the actual inspected
local sources, not assumptions based on current online documentation.

| Need | Exact API and type/application |
| --- | --- |
| Take vertex groups of the M3 equivalences | `CategoryTheory.Functor.FullyFaithful.mulEquivEnd (hf : FullyFaithful F) (X : C) : End X ≃* End (F.obj X)`, in `Mathlib/CategoryTheory/Endomorphism.lean:217`. Apply an M3 equivalence's `.fullyFaithfulFunctor`. This uses the actual functor, preserving its map on arrows. |
| Induced homomorphism on vertex groups | `CategoryTheory.Functor.mapEnd` in the same file: `End X →* End (F.obj X)`. Restrict the already proved strict M3 functor square, using its object equality and `eqToIso` where necessary. |
| Actual fundamental-group model | `FundamentalGroup X x` is literally `End (FundamentalGroupoid.mk x)`. `FundamentalGroup.mul_def` is `.of (q.asHom.trans p.asHom)` for `p * q`: categorical/loop multiplication order must be tracked. Source: `Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`. |
| Continuous-map homomorphism | `FundamentalGroup.map (f : C(X,Y)) (x : X)` maps to the group at `f x`. `mapOfEq f (h : f x = y)` maps to the group at the specified `y`. `mapOfEq_apply` gives the path-class map followed by endpoint casts using `h.symm` twice. |
| Actual basepoint transport | `FundamentalGroup.fundamentalGroupMulEquivOfPath (θ : Path x₀ x₁) : FundamentalGroup X x₀ ≃* FundamentalGroup X x₁`. It is `Iso.conj` of the actual path class, not a separately chosen abstract group equivalence. |
| Map/basepoint naturality foundation | `CategoryTheory.Functor.map_conj` in `Mathlib/CategoryTheory/Conj.lean` maps `α.conj f` to `(F.mapIso α).conj (F.mapEnd X f)`, on underlying arrows. This is the exact existing supplier used by the selected TauCeti naturality proof. |
| Evaluate actual endpoint monodromy | `IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_mk_eq`, in `Mathlib/Topology/Homotopy/Lifting.lean:664`, takes a loop `γ`, a continuous lift `Γ`, `p ∘ Γ = γ`, `Γ 0 = e`, and `Γ 1 = g • e`, and concludes the raw monodromy is `MulOpposite.op g`. |
| Evaluate using a path class rather than a representative | `fundamentalGroupToMulOpposite_apply_eq_iff` states that raw label `g : Gᵐᵒᵖ` is equivalent to `g.unop • e = monodromy γ.asHom e`. `IsCoveringMap.monodromy_eq_of_map_eq`, `monodromy_map`, `map_liftPathQuotient`, and `monodromy_trans_apply` supply the lift/class and concatenation calculations. |
| Move the selected lift within a fiber | `IsQuotientCoveringMap.fundamentalGroupToMulOpposite_toPermFiber` gives raw label `op (g * oldLabel.unop * g⁻¹)` after moving the lift by `g`. This is a conjugation law, not basepoint independence for a noncommutative quotient. |
| Normalize the opposite convention honestly | `MulEquiv.inv' G : G ≃* Gᵐᵒᵖ` in `Mathlib/Algebra/Group/Equiv/Opposite.lean:71`. Its inverse sends `op g` to `g⁻¹`. Plain `op`/`unop`, or inversion within a noncommutative group, is not silently used as a homomorphism. |

The literal selected statements, with arbitrary topological spaces and no
connectivity/covering hypotheses, are:

```lean
FundamentalGroup.fundamentalGroupMulEquivOfPath γ g =
  .of ((Path.Homotopic.Quotient.mk γ).symm.trans
    (g.asHom.trans (Path.Homotopic.Quotient.mk γ)))

FundamentalGroup.map f x₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) =
  FundamentalGroup.fundamentalGroupMulEquivOfPath (γ.map f.continuous)
    (FundamentalGroup.map f x₀ g)
```

The second formula is exactly the covering-induced-map/basepoint square.
For landmark 4 choose one actual upstairs path `θ` and **its image under the
actual orbit projection** downstairs. The first formula, mathlib's monodromy
concatenation law and `monodromy_toPermFiber` compute raw endpoint monodromy
under that paired transport. Independent downstairs path choices would
introduce conjugation, so path-connectedness alone does not prove the desired
identity on the same Coxeter quotient.

## Existing actual M1/M2/M3 suppliers and application limits

- `ArtinNormalisers.Landmark1.orbitFundamentalGroupMap`, `orbitMonodromy` and
  `orbitFundamentalGroup_shortExact`, in `landmarks/ArtinLandmarks/Covering.lean`,
  are the actual orbit-map homomorphism, raw monodromy into the **opposite**
  actual Coxeter normalizer quotient, and their short exactness at every
  actual complement basepoint.
- `Ribbon2.reducedRibbonNormalizerQuotientEquiv` in
  `ribbons/ArtinRibbons/NormalizerSplitting.lean` is the actual canonical
  reduced-loop-label quotient map proved bijective in M2. The larger ribbon
  group's `endEquivRibbonLoopsOpposite` in `RibbonGroupoid.lean` is useful for
  recognizing the convention, but is not the reduced associate-component
  vertex identification needed by M4.
- `Chamber3.actualIntervalComplementEquivalence`,
  `actualRibbonOrbitEquivalence` and `actualComparison_square` are actual M3
  equivalences and the strictly commuting covering square. Taking `End` and
  transporting the literal object equalities yields the middle comparison;
  it does not by itself identify the canonical Coxeter label.
- `chambers/ArtinChambers/RibbonDeckLabels.lean` supplies the already proved
  signed endpoint projection. Combine that formula with the actual M3 lifted
  path class and mathlib's endpoint evaluation before normalizing `Qᵐᵒᵖ→Q`.
  This avoids treating two unrelated isomorphisms as a commuting diagram.

These earlier accepted sources were read as prerequisite context, not modified
or re-certified. The new M4 `BasepointTransport.lean` source actually references
both selected declarations: naturality for the covering-map square and the
explicit path formula for raw endpoint-label transport. Its author reported
a successful build; its final project-level review/audit/replay belongs to the
M4 closeout, not this supplier record.

## Complete source-inspected repository inventory

The durable machine inventory is
[`docs/provenance/searches/m4-other-inventory.json`](../../provenance/searches/m4-other-inventory.json).
It records all eight repositories below with exact commits, source hashes,
literal relevant theorem types, licenses, reading limits, dispositions,
recursive closure inventories, and technical flags. It separately records
76 repositories returned as bounded search hits; those hits are not called
source reading, proof use or accepted suppliers.

| Repository / full commit | Pins and license | Exact inspected sources / disposition |
| --- | --- | --- |
| `lazyinspirit/artin-tits-normalisers-lean` / `1aa55a9ee5f13c9e3a8e64b4aec4675c0435a9c0` | Lean `v4.36.0-rc2`, mathlib `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; Apache-2.0 and retained upstream headers | Actual files named in the preceding section; accepted baseline context, with no old-file changes. |
| `leanprover-community/mathlib4` / `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9` | Lean `v4.36.0-rc2`; Apache-2.0 | `CategoryTheory/{Endomorphism,Conj}.lean`, `AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`, `Topology/Homotopy/Lifting.lean`, `Algebra/Group/Equiv/Opposite.lean`. Exact useful definitions/proof portions read; entire `Conj` and fundamental-group file read. Existing dependency. |
| `TauCetiProject/TauCeti` / `62bbc0596dc3539d488232e4e924a338548ea0a9` | Lean `v4.36.0-rc2`, upstream mathlib `e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`; Apache-2.0 | `AlgebraicTopology/FundamentalGroup/BasepointChange.lean`: exact selected blocks/proofs and surrounding relevant API read. `Topology/Homotopy/Monodromy/{BasepointChange,Functoriality,Basic}.lean`: full first file, relevant full base-map proof passages and declaration inventory of others. Only the selected two blocks were imported and checked against target pins. |
| `FormalFrontier/fundamental-groupoids` / `ce38a38faef1a147e75b68b78b02bbfd6ad82948` | Lean `v4.34.0-rc2`, mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`; Apache-2.0 | `FundamentalGroupoids/Topology/Covering/{Monodromy,DeckMonodromy}.lean`, `FundamentalGroupoids/FundamentalGroup.lean`. Exact general monodromy/basepoint naturality proofs read; deck file declaration inventory only. Genuine relevant alternative, not selected or verified. |
| `FormalFrontier/group-theory` / `da81dc691eabf38306f427465ea8a4af350f0aef` | Same Lean/mathlib as preceding row; Apache-2.0 | `GroupTheory/GroupAction/Quotient.lean`, `GroupTheory/Topology/LocallyConstant.lean`: import/header/dependency inspection only. Unselected dependency of preceding candidate, not a directly required M4 proof. |
| `deancureton/sphere-six-complex` / `b783b990d46c5f5ce02a4ecbbb2c02408b452cde` | Lean `v4.35.0-rc3`, mathlib `6b7abb3c7686292736be2955bd3eb9ebf63b456a`; Apache-2.0 | Entire `SphereSixComplex/Prerequisites/Topology/Covering/MonodromyTransport.lean` and `ForMathlib/Geometry/Manifold/Quotient/DeckFundamentalGroup.lean`. Genuine endpoint/basepoint formulas, but unrelated affine/punctured-plane imports and older API make full-file reuse disproportionate. Not selected. |
| `qinz1yang/differential-geometry` / `13c41a632efb8fbf93101c8a20f2a9214ab33240` | Lean `v4.35.0-rc3`, mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`; Apache-2.0 | Entire `Topology/FundamentalGroup/BasepointChange.lean` under `DifferentialGeometry/`; declarations in `Topology/Covering/FundamentalGroup/{CoveringSquareInjective,CoveringSquareConsumers}.lean`. Reverse-direction basepoint change duplicates mathlib; connector-change bookkeeping does not automatically give the paired transport required here. Not selected. |
| `chrisflav/oka` / `9a9fc315498d58484ac1abc9668548212eb7c1ff` | Lean `v4.32.0`, mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`; Apache-2.0 | Entire `Oka/Topology/Covering/Monodromy.lean`. `IsCoveringMap.monodromy_comp` is genuine naturality for a continuous map of covers over the **same** base; a short useful alternative, but M4 changes base and already has the selected minimal route. Not selected. |

Source code was inspected, not merely README theorem claims or badges.
Recursive import scans establish paths and sizes, not proof correctness.
No consulted mathematical error was established; rejection as unnecessary,
inapplicable or costly is not an allegation of false mathematics.

## Closest alternatives: literal hypotheses and closure costs

**TauCeti full-file alternatives.** `Monodromy/Functoriality.lean` has
`IsCoveringMap.coe_monodromy_mapOfEq` for an arbitrary commuting continuous
cover square `q ∘ g = f ∘ p`, a target equality `h : f x = y`, and compatible
lifts `g e = e'`. It concludes
`(hq.monodromy (FundamentalGroup.mapOfEq f h γ).asHom e' : F) =
g (hp.monodromy γ.asHom e)`. It does not require simple connectivity.
Its complete non-mathlib closure is only two new modules,
`Topology/Homotopy/Monodromy/Functoriality.lean` and `Logic/Function/Fiber.lean`:
428 lines / 20,159 bytes. This was proposed promptly, but root selected the
still smaller exact extraction and existing mathlib endpoint laws.

The full TauCeti fundamental-group `BasepointChange.lean` closure has ten
modules, 3,420 lines / 168,961 bytes, including five already vendored modules.
Five new modules would add 1,969 lines / 94,421 bytes; the extra homeomorphism,
conjugation and normalizer-quotient bookkeeping is not needed by the selected
two proofs. `Monodromy/BasepointChange.lean` would bring thirteen modules,
4,100 lines / 205,855 bytes, seven new. These full closures are not imported.

**FormalFrontier exact quotient naturality.** Its
`IsQuotientCoveringMap.fundamentalGroupToMulOpposite_naturality` assumes two
actual quotient coverings, a homomorphism `ρ : G →* H`, continuous total/base
maps `F,f`, `q ∘ F = f ∘ p`, and pointwise equivariance
`F (g • e) = ρ g • F e`. It proves equality of homomorphisms
`newMonodromy.comp (FundamentalGroup.map f x) =
(MonoidHom.op ρ).comp oldMonodromy`. The proof constructs monodromy naturality
from actual lifted path classes; no desired commutation is assumed as a field.
Its full closure is three new modules, 1,078 lines / 51,736 bytes, across the
two FormalFrontier repositories listed above. Its basepoint file also proves
`FundamentalGroup.mapOfEq_comp_fundamentalGroupMulEquivOfPath`, including the
correct endpoint casts; its full closure is two modules, 1,948 lines /
90,065 bytes. These are real candidates, but none was selected or compiled.

**Sphere-six endpoint transport.** The exact declaration
`SphereSixComplex.fundamentalGroupToMulOpposite_transport_endpoint` takes
`hp : IsQuotientCoveringMap p G`, `W : Path x y`, `ex : p ⁻¹' {x}` and
`γ : FundamentalGroup X x`, and asserts

```text
hp.fundamentalGroupToMulOpposite (hp.isCoveringMap.monodromy ⟦W⟧ ex)
  (FundamentalGroup.fundamentalGroupMulEquivOfPath W γ)
= hp.fundamentalGroupToMulOpposite ex γ.
```

This is exactly the compatible-lift transport shape, with no simply-connected
total-space assumption. The same file proves quotient-cover naturality from
a `QuotientCoverMapData` containing actual continuous maps, deck homomorphism,
commuting square and pointwise equivariance; the conclusion is not a field.
Its full imported affine/punctured-plane development was not audited or built,
so no full-closure reuse was proposed. The selected short path formula plus
existing mathlib monodromy laws supports the local M4 derivation directly.

## Reproduction and bounded search limits

The selected extraction is checked read-only from `sequences/` by
`python3 scripts/providers/assemble.py --check`. The actual verification
commands, each with retained raw output and exit status, were:

```bash
python3 scripts/providers/run_checks.py build
python3 scripts/providers/run_checks.py audit
python3 scripts/providers/run_checks.py replay
python3 scripts/providers/summarize.py
```

The replay invocation is the supported official
`lake env leanchecker --verbose ArtinSequenceVendor.FundamentalGroup.BasepointChange`.
No shared cache/dependency update or competing toolchain installation occurred.
Only the selected provider, its audit/tooling/evidence, and this task's
search documents/inventory were authored after root expanded the task scope.

The bounded GitHub code queries were `fundamentalGroupToMulOpposite`,
`fundamentalGroupMulEquivOfPath`, `monodromy naturality`, `mulEquivEnd`, and
`monodromy basepoint`, with `.lean` filtering and up to 100 indexed hits per
query. Results included mathlib/OpenAI duplicates; these were filtered during
candidate assessment, not mistaken for new suppliers. Query counts and all
indexed repository/commit/path results are retained in the durable inventory.
The search cannot establish absence of another useful theorem in unindexed
branches or repositories. A hit, source appearance, `#check`, claimed no-`sorry`
status or successful build alone is never recorded as proof acceptance.
