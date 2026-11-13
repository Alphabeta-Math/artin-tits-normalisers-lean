# Full algebraic Lemma 2.8 formalization

The Lean theorem `ArtinNormalisers.Artin.lemma_2_8` proves the full normalizer
short exact sequence of arXiv:2509.21915v3, PDF p. 6:

`1 → N(P,J) → N(A,J) → N(W,J) → 1`.

It quantifies over an arbitrary type of indices, an arbitrary Coxeter matrix
and any subset of indices. It assumes no finiteness, sphericality, positive-lift
theorem or normalizer surjectivity. The maps and groups are the actual standard
Artin braid presentation, Coxeter presentation, generated standard parabolics,
canonical projection and normalizer quotients. The left group is the quotient
image of the intersection of the pure kernel with the Artin normalizer.

The source initially describes the Artin group topologically and states its
standard presentation. This development proves the full **algebraic** lemma in
the standard presentation model; the topology-to-presentation equivalence is
not itself Lean-formalized or inserted as an axiom. Both independent reviews
explicitly accept this interpretation and record that limit.

## What was added beyond the kernel milestone

- Actual Artin group/projection wrappers and a proof that the Artin parabolic's
  image is the Coxeter parabolic.
- Minimal normalizer representatives, inverse minimality and simple-generator
  conjugation for arbitrary subsets, using parabolic length additivity.
- A genuine normalizing Artin lift, constructed by evaluating a reduced word
  and applying monoid-valued Matsumoto in both generator directions. A
  parabolic correction gives an exact preimage of every Coxeter normalizer
  element, proving more than just quotient-level surjectivity.
- The actual quotient homomorphism, its evaluation formula and kernel, the
  injective pure-image inclusion, range/kernel equality and surjectivity, and
  the final conjunction expressing short exactness.

No assumption of the missing result replaces any of these steps. The existing
kernel proof and its historical evidence remain unchanged.

## Verified external reuse and independent review

Ten exact source modules from TauCeti commit
`62bbc0596dc3539d488232e4e924a338548ea0a9` supply the standard Artin presentation,
Matsumoto theorem, parabolic machinery and their local proof dependencies.
All original byte hashes, copyright headers and Apache-2.0 license are retained.
They compiled unchanged against the project's existing mathlib pin, passed
transitive axiom checks, and were individually replayed by the official checker.
No third-party proof was accepted from a README claim or a CI badge.

Two independent GPT-6.1 Sol/high reviewers accepted every one of the 51 explicit
project definitions/theorems across nine source/root files, including the
private helper and all transport/lifting statements. They bound their reviews
to independently recomputed project and supplier source hashes and checked
supplier-critical definitions/conclusions against the intended mathematics.
Reviewer A also independently ran the full aggregate build and project axiom
audit; reviewer B accurately records semantic/source/hash review without
claiming compilation. Their final reports/JSON receipts are in `reviews/`.

## Final local verification

`formalizations/artin-normalisers/evidence/full-local/verification.json`
records **24 commands, all exit 0**, and matches both accepted review receipts.
The final harness:

1. Confirms the exact reviewed project source, all ten original supplier hashes,
   vendor provenance and pinned mathlib revision.
2. Cleans only this package, then builds `ArtinNormalisersFull` from project and
   supplier sources while retaining the pinned mathlib dependency cache.
3. Audits 69 project declarations and 171 supplier declarations by their defining
   modules, including private/generated declarations and provider extensions
   outside the TauCeti namespace. Allowed transitive axioms are only
   `propext`, `Classical.choice`, `Quot.sound`.
4. Runs official kernel replay sequentially on all seven scientific project
   modules and all ten suppliers. Each real command succeeds.
5. Rechecks that all checked input hashes and independent review receipts remain
   unchanged. Its 32 input-file hashes, commands, durations, diagnostics and log
   hashes are retained.

Replay is relative to imported mathlib environments, not a fresh recheck of the
entire mathlib library or a second independent kernel implementation. Sequential
single-module commands avoid the documented bundled rc2 checker's aggregate
replay crash. All actual development failures remain separately labeled under
`evidence/full-development/`, including an audit-import harness repair which
did not change mathematical source.

Lean is pinned to `v4.36.0-rc2`, mathlib to
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`, and the Lake manifest binds every
transitive package revision. The local record's starting Git HEAD predates this
implementation; its exact input hashes bind the checked working tree instead.
The fresh GitHub run
[43484468188](https://github.com/lazyinspirit/workflow-engines/actions/runs/43484468188)
passed in 7m59s against commit `b41b7634c78cd3927dd2216246203535ad93d248`.
All 24 command exits are zero; its 32 input hashes and all downloaded log hashes
match the committed origin package. The run metadata, complete compressed log
and artifact are archived in `full/github-evidence/run-43484468188/`.

## Reproduce and archive

From `formalizations/artin-normalisers/`:

```bash
python3 scripts/cache_prerequisites.py
python3 scripts/verify.py --output evidence/full-reproduction
```

The scoped GitHub workflow runs those commands on a fresh runner, with review
and source/provenance checks mandatory. Its successful records are durably
archived under `full/github-evidence/`. The owner subsequently requested the
dedicated public repository
[artin-tits-normalisers-lean](https://github.com/lazyinspirit/artin-tits-normalisers-lean);
its unchanged mathematical source and adapted standalone packaging have their
own verification records. No unrelated engine or serving content was changed.
