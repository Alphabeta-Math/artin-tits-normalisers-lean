# Independent M4 basepoint supplier review B

Reviewer: **GPT-6.1 Sol/high** (`gpt-6.1-sol`, reasoning effort `high`). Verdict: **accept-supplier-cohort**, for **exactly two selected declaration/proof blocks** in the one frozen module `ArtinSequenceVendor.FundamentalGroup.BasepointChange`. **Landmark 4 and full Theorem 1.8 are not accepted or proved by this receipt.** The retained 651-line original is context, not an accepted whole-file supplier or recursively imported proof closure.

I independently read both complete selected statements/proofs, their active wrapper, upstream source context through line 220, the full extraction recipe and assembly script, complete byte-level unified diff, license/provenance, audit/verification scripts and actual retained evidence. I also read the actual `BasepointTransport.lean` consumer for direct applicability. I did not consult review A or edit any proof, configuration, supplier, cache or evidence file. I wrote only this review/JSON receipt. My own execution consisted of read-only source/hash/Git-blob/diff/evidence checks and the reviewed assembler’s `--check`; no Lean build, axiom audit or kernel replay was run by me.

## Exact mathematical statements and proof meanings

`FundamentalGroup.fundamentalGroupMulEquivOfPath_apply` has arbitrary `X : Type u`, its actual `TopologicalSpace`, actual points x₀,x₁, an actual continuous path γ:x₀→x₁, and an actual mathlib fundamental-group element g at x₀. It computes the already defined multiplicative basepoint-change equivalence as the actual path-homotopy class

```
γ.symm ⋆ g.asHom ⋆ γ.
```

This is the correct direction for changing the basepoint to x₁ under mathlib’s End convention. Its proof names the actual quotient path γq and corresponding fundamental-groupoid isomorphism α, unfolds the standard `α.conj` transport and applies the actual `Iso.conj_apply_asHom` computation. It does not define a new fundamental group or a transport chosen to make the desired formula true. The `[simp]` attribute and the full declaration/proof block are unchanged.

`FundamentalGroup.map_fundamentalGroupMulEquivOfPath` has arbitrary independent universes/topological spaces X,Y, an actual continuous map `f:C(X,Y)`, an actual γ:x₀→x₁ and g in the actual fundamental group at x₀. Its conclusion is exactly

```
map f x₁ (Tγ g) = T(γ.map f.continuous) (map f x₀ g).
```

Its proof identifies the image of the actual path isomorphism with the isomorphism of the actual mapped path, uses genuine `Functor.map_conj`, then unfolds mathlib’s actual `Functor.mapEnd`/basepoint definitions. It assumes no comparison isomorphism, chosen desired square or target path equality. The base path is precisely the image of the supplied path, not an arbitrary path between the image endpoints.

Neither theorem needs connectedness, local connectedness, Hausdorffness, a covering, freeness, finite Coxeter type, rank, irreducibility, commutativity or equivariance. All data and hypotheses are explicit in both selected source and actual elaborated types in the audit log. Supplier-only `autoImplicit=true` does not hide a desired comparison premise in either type; project `autoImplicit=false` remains unchanged.

## Direct use in M4 and limits

The actual consumer `sequences/ArtinSequences/BasepointTransport.lean` uses the second theorem to prove the covering-induced fundamental-group square along one total-space path and **exactly its projected path**, including `mapOfEq` and homomorphism-equality formulations. A covering hypothesis there supplies continuity; the supplier statement itself is more general.

The consumer uses the first computation to expand path conjugation in its raw-monodromy transport proof. The remaining local proof follows the actual lift of the reverse path, the actual loop lift, then the translated projected-path lift, using mathlib’s real monodromy composition/equivariance. Thus its intended output keeps the same raw `Qᵐᵒᵖ` label, without inserting an unexplained Q conjugation. These two supplier theorems are directly useful to the paired-basepoint contract; they are not an ordinary Salvetti or abstract classification surrogate.

The extracted supplier does **not** prove raw-monodromy invariance by itself, the inverse-opposite normalizer comparison, either pure/middle group isomorphism, either full exact-sequence comparison square, all-basepoint M4 assembly, or asphericity. I read the consumer to check application rather than issue a final M4 proof acceptance; no active main-M4 proof hashes are bound here. Final concrete M,J instances and the complete exact-sequence/opposite convention remain subject to their later independent frozen-source review.

## Upstream provenance and exact extraction

The scientific source is [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/FundamentalGroup/BasepointChange.lean), pinned at `62bbc0596dc3539d488232e4e924a338548ea0a9`, under the retained Apache-2.0 license. I independently compared the full original `.lean.txt` bytes with `git show` of that exact path/SHA in the existing local upstream checkout. I also compared the entire license bytes with the upstream pinned `LICENSE`; all hashes match.

| Selected declaration | Original lines | Exact bytes | Block SHA256 |
| --- | --- | ---: | --- |
| `FundamentalGroup.fundamentalGroupMulEquivOfPath_apply` | 129–148 | 1,134 | `8414d978ee933fc8345ef2c57737a2d050eb8ed0358e533db46ca279f05fbc63` |
| `FundamentalGroup.map_fundamentalGroupMulEquivOfPath` | 196–212 | 1,163 | `0a7c0a3dc68b8face62da69fe5bdce30395b2fd5d09708f3470ed928587515ba` |

I independently sliced the exact original ranges, checked the bytes/hashes and one occurrence of each unchanged block in the active source, reconstructed the complete documented active wrapper and compared it byte-for-byte, and regenerated the **whole** unified diff in memory and checked exact equality. I then ran the inspected `assemble.py --check`, which completed successfully without writing files. The active hash is `a08b1f392653c11ac4599c226029bf90b8f13ab51024ad4e74916b93bbbb820d`; the full original hash is `87851dc988d7b53b32c35841a90f22aae58f3cd0eb6a4f3e232e78fc69b3bc43`.

Only the module path, minimal Mathlib imports, extraction notice and omission of unrelated blocks change. Both statements, attributes, namespace, comments and proof bodies remain byte-for-byte intact. Source context places these explicit declarations in the retained `FundamentalGroup` namespace; no implicit section variable, preceding hypothesis or unimported helper is removed from a selected proof. The active file imports **only two existing Mathlib modules**; none of the unselected TauCeti normalizer/homeomorphism/homotopy bookkeeping is imported. This acceptance therefore covers two proofs, not the original file’s other theorems or its recursive dependencies.

Upstream uses Lean 4.36.0-rc2/mathlib `e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`; target uses Lean 4.36.0-rc2/mathlib `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. The recorded target compilation/audit/replay are actual compatibility evidence, rather than an assumption that pins match. The new package’s three configuration files are hash-bound; it requires the existing `../chambers` package with inherited accepted pins. Both selected types remain fully generic under the upstream supplier implicit convention.

## Observed technical evidence

I read the combined provider verification/coverage/environment records and their **selected latest successful** build, audit and replay phase records. I checked all six recorded commands’ zero exits and exact raw-log hashes: each phase first checks the deterministic extraction, then runs its actual Lake target, declaration audit or one exact official `leanchecker --verbose ArtinSequenceVendor.FundamentalGroup.BasepointChange` process. The build log reports successful completion. The audit’s printed elaborated types are exactly the two types discussed above. Its raw canonical and physical names are exactly the selected two, with **2 unique declarations = 2 physical occurrences**, no aliases or duplicates, and only `propext`, `Classical.choice`, `Quot.sound` collected transitively.

The harness scans constants by the actual defining module and compares each physical serialized constant’s name, type, proof/value and universe parameters against its canonical imported constant, checks array lengths and both directions of physical/canonical name coverage, and would reject any extra selected-module axiom or unaccounted overlap. The observed run has no overlap, so theorem-alias exceptions are not used. A fresh process replays that exact provider module, rather than an aggregate-prefix match. Its retained log contains the exact module replay header; it does not itself print every proof name, which is why the separate physical/canonical audit matters.

I independently recomputed the provenance, active/original/selection/recipe/patch/license/assembler/harness/configuration and evidence hashes. Every before/after snapshot is identical in its run and matches current bytes: **26 bound inputs for build**, **32 for audit**, **32 for replay**; audit/replay snapshots are identical. The additional six audit/replay inputs are the provider’s compiled module parts/hash sidecars. I also checked the actual current resolved Leanchecker binary against the environment’s recorded binary hash. There is no earlier-build/current-metadata transition in these selected successful records. Earlier exploratory records are not substituted for the selected records, and no historical failure is relabeled as a successful run.

These are **root/team Lean executions**, not mine. Replay uses Lean’s bundled kernel relative to imported pinned Mathlib; it is not an independent kernel implementation or fresh replay of every imported Mathlib theorem. I did not read all unselected proofs in the retained original or reconstruct imported Mathlib’s full proof closure. The exact reading and execution limits are also recorded in the receipt.

## Binding and disposition

`providers-b.json` binds repo-relative maps for the active file, complete original, patch, assembler/recipe, selected blocks, license, provenance, audit, three new configuration files, all selected immutable phase records/logs/snapshots and environment/coverage, and tooling/context hashes. It inventories exactly the two accepted declaration names. No changing main M4 mathematics is bound. The central GitHub proof ledger owner has been informed of this cohort and its required schema; these records preserve the exact repository/pin/proofs used, without inventing a new independent source.

**Accept this supplier cohort only.** No false statement, strengthened selected hypothesis, missing selected dependency or proof-body change was found. Final landmark 4, fresh full-frontier verification/CI and the remaining Theorem 1.8 asphericity conclusion remain separate obligations.
