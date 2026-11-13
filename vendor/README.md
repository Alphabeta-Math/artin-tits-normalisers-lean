# Directly used, source-vendored formal prerequisites

The ten algebraic suppliers bound in `provenance.json` are byte-for-byte copies from
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) at commit
`62bbc0596dc3539d488232e4e924a338548ea0a9`. `provenance.json` binds their complete
module list and original SHA-256 values. `LICENSE.TauCeti` is the original
Apache-2.0 license; copyright/author headers remain in every source file.
`TauCeti.lean` is a locally authored import-only aggregate, not an upstream file.

For the algebraic Lemma 2.8, only the local import closure of Artin, Matsumoto
and Parabolic was copied.
Artin supplies the actual braid presentation and canonical Coxeter projection;
Parabolic supplies minimal representatives and length additivity; Matsumoto
supplies monoid-valued reduced-word invariance. The remaining files prove their
exchange, rank-two and geometric/trigonometric prerequisites. No unrelated
TauCeti mathematics, source modifications, opaque replacement axioms, or
precompiled TauCeti artifacts were imported.

Upstream pins Lean 4.36.0-rc2 and mathlib
`e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`. This package uses the same Lean but
retains its existing mathlib pin
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. Every supplier source compiled
unchanged against this pin. The actual compiled supplier declarations passed a
transitive standard-axiom allowlist and sequential official kernel replay.
The full verification harness repeats these checks from a clean package build
and enforces the source hashes and independent supplier-review bindings.

`ProviderAudit.lean` selects declarations by defining module, rather than by
namespace: the suppliers also add declarations to `CoxeterSystem` and `Real`.
It rejects `sorryAx`, custom mathematical axioms and native-evaluation axioms.
Kernel replay covers these exact ten supplier modules using their imported
library environments; it does not claim a fresh replay of all mathlib.

## Additional Theorem 1.8 prerequisites

`theorem18-provenance.json` separately binds 23 further unchanged modules from
the same revision: the exact whole-module import closure for the
`IsAspherical`/`IsEilenbergMacLaneSpaceOne` predicates and higher-homotopy
covering-transfer results. All original license and source headers are retained.
These generic results are directly useful after the actual arrangement's
covering and asphericity have been proved; they do not supply either missing
proof or the arrangement's Artin-normalizer fundamental-group comparison.

This library uses upstream's `autoImplicit = true` convention, scoped to the
`TauCeti` Lake library. Project proofs retain `autoImplicit = false`.
In particular, the source basepoint inferred in three trivial-source-π₁
lemmas remains a genuine quantified point with an explicit subsingleton
source-fundamental-group hypothesis. The audit prints their elaborated types.

The separate `Theorem18Audit.lean` directly imports all 33 supplier modules,
audits declarations by defining module, and prints every new project type.
`scripts/verify_theorem18.py` binds independent statement reviews and supplier
hashes, builds `ArtinTheorem18`, performs this transitive audit, and kernel
replays each of the 23 new modules and each new project module individually.
Its records explicitly say that **Theorem 1.8 remains unproved**. Supplier
provenance by itself is not evidence of successful verification; consult the
actual hash-bound records under `evidence/theorem18-local/` or CI artifacts.
