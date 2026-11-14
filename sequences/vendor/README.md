# Two exact basepoint-change proofs from TauCeti

This cohort contains exactly two declarations from
`TauCeti/AlgebraicTopology/FundamentalGroup/BasepointChange.lean` at
`62bbc0596dc3539d488232e4e924a338548ea0a9`, licensed under the retained
Apache-2.0 license. The complete original file is preserved under
`upstream-original/`; selected lines 129–148 and 196–212 retain their
declaration statements, attributes, comments and proof bodies byte for byte.

The new module `ArtinSequenceVendor.FundamentalGroup.BasepointChange` retains
the namespace `FundamentalGroup` and imports only the two existing mathlib
fundamental-group/groupoid modules used by these proofs. The original
upstream file's unrelated subgroup/normalizer and homotopy bookkeeping is not
imported. The changed wrapper and omitted blocks are recorded in the complete
unified patch and deterministic assembly recipe.

From `sequences/`, reproduce or check the assembly with:

```bash
python3 scripts/providers/assemble.py
python3 scripts/providers/assemble.py --check
```

The check is read-only. `vendor/provenance.json` binds original, active,
selected-block, license, patch, recipe and assembly-script hashes, the exact
upstream/toolchain/mathlib pins, and the two concrete applications. Both
statements retain arbitrary topological spaces and actual paths; no
connectivity, covering, finite-type or equivariance premise is added.

Technical records are separate from mathematical acceptance. The new module
must pass explicit compilation, exhaustive canonical/physical transitive
axiom audit and exact-module kernel replay; independent reviews and root
acceptance remain required. This supplier cohort does not prove landmark 4
or the full article theorem.
