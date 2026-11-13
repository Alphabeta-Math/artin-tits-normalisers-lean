# Directly used, source-vendored formal prerequisites

The ten files under `TauCeti/` are byte-for-byte copies from
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) at commit
`62bbc0596dc3539d488232e4e924a338548ea0a9`. `provenance.json` binds their complete
module list and original SHA-256 values. `LICENSE.TauCeti` is the original
Apache-2.0 license; copyright/author headers remain in every source file.
`TauCeti.lean` is a locally authored import-only aggregate, not an upstream file.

Only the local import closure of Artin, Matsumoto and Parabolic was copied.
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
