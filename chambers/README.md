# Actual equivariant geometric groupoid comparison

This independent Lake package contains the compiled proof of **Landmark 3**
for Theorem 1.8 of Garnier–Heng–Licata–Yacobi, arXiv:2509.21915v3.
All 42 scientific modules and the aggregate compile, and the complete local
technical build/audit/replay battery passed. Current independent-review,
final-verification and CI status is maintained in the
[Milestone 3 report](../docs/theorem18/landmarks/milestone3-REPORT.md).
Landmarks 4 and 5, and therefore full Theorem 1.8, remain unproved.

The final statement is
[`ArtinNormalisers.Chamber3.landmark_3`](ArtinChambers/Landmark3.lean).
It applies to every `M : CoxeterMatrix I` with `[Finite M.Group]` and every
`J : Set I`, in arbitrary index universes. There is no separate finite-rank,
irreducibility or crystallographic hypothesis. Empty and full parabolics and
rank zero are included.

## Actual objects and comparisons

Write `X = Complement M J` for the inherited-topology complement in
`Θ_J × Θ_J`, where `Θ_J` is the annihilator of the selected simple roots in
the actual dual geometric representation. The excluded pairs simultaneously
vanish on a retained root: a root whose evaluation is not identically zero on
`Θ_J`. Write `Q = N_W(W_J)/W_J` for the existing Coxeter normalizer quotient,
`Y = OrbitSpace M J`, `D` for the interval groupoid on the actual real
restricted chambers, and `R` for the actual reduced ribbon groupoid restricted
to the `J`-associate component.

The proved square is

```text
D  ── actualIntervalForward ──→  FundamentalGroupoid X
│                               │
│ componentRibbonFunctor        │ orbitFundamentalGroupoidFunctor
↓                               ↓
R  ── actualRibbonOrbitEquivalence.functor ──→ FundamentalGroupoid Y
```

Both horizontal functors are equivalences; both vertical functors are actual
groupoid coverings. The square commutes as a strict equality of functors.
The upper equivalence is strictly equivariant for the same actual `Q` on both
sides. Both lower targets, with their specified action cocones, satisfy the
ordinary groupoid orbit-colimit universal property. These colimit statements
are proved separately by covering descent; an equivalence is not treated as
an isomorphism of objects of `Grpd`.

`D` uses a positive generator `[C,D]` for **every ordered pair** of chambers.
Its defining relations are `[C,C]=1` and
`[C,F]=[C,D] ≫ [D,F]` when every form on which `C` and `F` agree has that same
sign on `D` (`ChamberBetween`). This is a proved geometric interval
alternative. A dictionary with the article's literal adjacent-gallery
presentation is not asserted. Opposite positive generators are separate;
signed inverses are the groupoid inverses.

[`RibbonDeckLabels.lean`](ArtinChambers/RibbonDeckLabels.lean) additionally
proves the Coxeter projection formula for every signed ribbon arrow. At the
standard chamber, the endpoint of every reduced ribbon loop is its actual
Coxeter quotient projection acting on that chamber. This fixes the same `Q`,
not an unspecified automorphism of it. The based fundamental-group maps,
opposite-group convention and compatible exact sequences are still Landmark 4.

## Proof and source records

The route uses actual sign chambers, explicitly contracted chamber tubes and
their overlap components, genuine open-cover groupoid van Kampen, an actual
interval/complement equivalence, signed ribbon lifting, and covering descent.
No desired geometric comparison, ribbon identification or orbit universal
property is assumed as a field of the final inputs.

The [report](../docs/theorem18/landmarks/milestone3-REPORT.md) describes the
proof boundaries and retained literature findings. The
[plan](../docs/theorem18/landmarks/milestone3-PLAN.md) tracks closeout.
All GitHub proof inputs are recorded in the central
[source register](../docs/provenance/GITHUB-PROOF-SOURCES.md).

Lean is pinned to `leanprover/lean4:v4.36.0-rc2`, mathlib to
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. The path dependencies
`../ribbons` and `../landmarks` preserve their accepted inputs. Nine additional
TauCeti Čech modules, pinned at
`62bbc0596dc3539d488232e4e924a338548ea0a9`, contribute 232 canonical
declarations and 232 physical occurrences. Their only source changes relocate
imports; original bytes, patches and license are in [vendor/](vendor/README.md).
Their build, standard-axiom audit and nine exact-module kernel replays passed,
and the [supplier cohort was separately accepted](../docs/provenance/acceptance-landmark3-cech.json).
This acceptance concerns the supplier cohort; the report records the separate
main-statement review and verification results.

## Reproduction and verification

The [technical receipt](evidence/landmark3-technical-20261114T074500Z/verification.json)
records 132 successful commands, 52 exact-module replays, all 43 project
modules (42 scientific files plus aggregate), 1,071 project declarations with
zero duplicates, the nine suppliers' 232 declarations, standard axioms only,
and 855 unchanged older context inputs. The report links the main reviews,
final-mode evidence and fresh CI when available.

From the repository root, with the pinned `lake` available:

```sh
python3 chambers/scripts/cache_prerequisites.py --plan
python3 chambers/scripts/verify.py --plan
python3 chambers/scripts/cache_prerequisites.py
python3 chambers/scripts/verify.py --execute --mode technical --output chambers/evidence/reproduction-technical
python3 chambers/scripts/verify.py --execute --mode final --output chambers/evidence/reproduction-final
```

Use fresh output directories. The cache script preserves the exact dependency
pins; the verifier cleans only this new package's outputs. Technical mode
builds, audits and replays the bound scientific modules and new suppliers but
never asserts semantic acceptance. Final mode additionally requires the
root-owned source inventory and two matching `accept-landmark3` receipts.

For an ordinary compilation check, run `lake build ArtinChambers` from
`chambers/`. This alone does not replace the source-bound verification battery.
Kernel replay uses Lean's pinned kernel relative to imported mathlib and
accepted dependencies; it is not an independent kernel implementation or a
fresh replay of all older dependencies.
