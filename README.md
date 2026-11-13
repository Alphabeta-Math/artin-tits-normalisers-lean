# Artin–Tits normalisers: Lean formalization

Public repository for formalizing results from Garnier, Heng, Licata and Yacobi,
*Normalisers of parabolic subgroups of Artin–Tits groups and Tits cone intersections*,
arXiv:2509.21915v3. The completed result currently covered is the full algebraic
Lemma 2.8.

## Lemma 2.8: the full algebraic normalizer exact sequence

This standalone Lake package proves the full algebraic statement of Lemma 2.8
on PDF page 6 of Garnier–Heng–Licata–Yacobi,
[arXiv:2509.21915v3](https://arxiv.org/abs/2509.21915v3):

```text
1 → N(P,J) → N(A,J) → N(W,J) → 1.
```

The final theorem is `ArtinNormalisers.Artin.lemma_2_8` in
[`Artin/ExactSequence.lean`](ArtinNormalisers/Artin/ExactSequence.lean).
For every index type `I`, every `M : CoxeterMatrix I` and every `J : Set I`, it
proves injectivity of the first arrow, equality of its range with the kernel of
the second, and surjectivity of the second. It assumes no finiteness,
sphericality, or normalizer-lifting premise.

## Actual groups and exact scope

`ArtinNormalisers.Artin.Group M` is an alias for TauCeti's actual
`PresentedGroup` with the standard Artin braid relators. Its generators are
not made involutions. Diagonal entries and zero entries (infinite Coxeter
labels) contribute only trivial relators. `M.Group` is mathlib's actual Coxeter
presentation. `projection M` sends each Artin generator to the corresponding
simple reflection.

`parabolic M J` and `coxeterParabolic M J` are closures of the actual selected
generators. `map_parabolic` proves their image identification. The two quotient
groups really are their normalizers modulo those subgroups. The pure subgroup
is the kernel of `projection`; `pureNormalizerImage` is the quotient image of
its intersection with the Artin normalizer, as in equation (1.7). The first
arrow is inclusion of that image subgroup, not inclusion of the whole pure group.

The article first describes the Artin group topologically and then states its
standard presentation. This package proves the full **algebraic** lemma for that
standard presentation model. The equivalence of the topological fundamental-group
model with the presentation is not formalized here, nor used as an axiom.
The source-to-formal reviews explicitly distinguish these claims.

## Proof and reused formal prerequisites

The initial kernel proof is preserved in `ArtinNormalisers/Kernel.lean`.
The remaining normalizer-lifting argument is now proved:

1. Adjust a Coxeter normalizer element by a parabolic element to a minimal
   representative `d`.
2. Prove `d⁻¹` is also minimal. Parabolic length additivity implies conjugating a
   selected simple generator by `d` gives a length-one parabolic element,
   hence another selected simple generator. Apply the same reasoning to `d⁻¹`
   for the reverse direction; no finite-set argument is used.
3. Choose a reduced word for `d`. Matsumoto's theorem evaluates the corresponding
   two reduced expressions in the actual Artin group and proves both generator
   conjugation directions for its positive lift.
4. Correct by a proved Artin-parabolic preimage of the remaining Coxeter
   parabolic factor. This yields an Artin normalizer element projecting to
   exactly the original Coxeter element, proving even normalizer-level
   surjectivity.
5. Descend to the quotient, combine surjectivity with the kernel theorem, and
   use the injective subgroup inclusion to obtain the short exact sequence.

Ten unchanged TauCeti modules are vendored at the exact revision recorded in
[`vendor/provenance.json`](vendor/provenance.json). They supply the concrete
Artin presentation, Matsumoto, standard parabolic minima/lengths and their
proof prerequisites. Their source hashes, Apache-2.0 license and original
copyright headers are retained. They have been rebuilt against the project's
pinned mathlib, audited for transitive axioms, and replayed through the kernel.
They are not accepted merely from a README or CI badge. See
[`vendor/README.md`](vendor/README.md) and the
[external-source search](docs/full/external-prerequisites.md).

Lean is pinned to `v4.36.0-rc2`; mathlib is pinned to
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. All transitive dependency revisions
are recorded in `lake-manifest.json`. No whole third-party repository or
precompiled third-party mathematics is needed to reproduce the local sources.

## Reproduce the verification

Install [elan](https://lean-lang.org/install/manual/) and Python 3. From this
directory run:

```bash
python3 scripts/cache_prerequisites.py
python3 scripts/verify.py --output evidence/full-reproduction
```

The first script fetches only the actual mathlib import closure. The verifier
checks accepted independent GPT-6.1 Sol/high review receipts against all nine
project proof/root source files and the ten upstream supplier files; then it
cleans only this package's outputs, builds `ArtinNormalisersFull`, runs
`FullAudit.lean` and `ProviderAudit.lean`, and kernel-replays every scientific
module sequentially. Source/input hashes, real commands, exit statuses,
durations and unmodified diagnostic logs are retained. It fails on changed
inputs or review receipts, a missing supplier, or any failed tool command.

The audits select declarations by their defining module, so supplier extensions
to `CoxeterSystem` and private project helpers are included. Only transitive
axioms from `propext`, `Classical.choice`, `Quot.sound` are allowed. An empty
audit is rejected; `sorryAx` and added mathematical/native-evaluation axioms
are forbidden. Compiled proof checking and statement correspondence are
separate obligations; both are recorded.

The bundled rc2 checker's aggregate-prefix invocation crashes locally. Supported
single-module invocations succeed and are used instead, with failed development
attempts retained. Replay checks project and supplier declarations relative to
their imported mathlib environments. It is not a fresh replay of all mathlib
or a second independent kernel implementation.

## Records and historical pilot

- [Full-lemma implementation plan](docs/full/PLAN.md)
- [Full-lemma independent reviews](docs/full/reviews/)
- [Full-lemma verification report](docs/full/REPORT.md)
- [Original end-to-end plan and kernel milestone](docs/PLAN.md)

Historical `evidence/local/`, `docs/reviews/` and their archived
GitHub run describe the earlier kernel-only milestone and remain authentic.
Their input hashes refer to that earlier version, not the enlarged package.
Full-lemma evidence is stored separately. This package does not alter the
published Research portal. See [MIGRATION.md](MIGRATION.md) for the original repository and preserved proof hashes.
