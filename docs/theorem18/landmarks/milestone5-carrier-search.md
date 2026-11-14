# Landmark 5: topological carrier and cell-extension search

This bounded search found a small, genuine topological cell-extension cohort in [kangxyz/colib](https://github.com/kangxyz/colib/tree/bac5cab53eb6526e366e861d289253ec81aa89f0). It does **not** supply the general monotone contractible-carrier theorem or asphericity of the actual arrangement complement. The selected tools let a local client derive prescribed boundary/cylinder extensions into a contractible target; the all-dimensional carrier induction and its application remain separate obligations.

The complete six GitHub commands, returned hits, all 17 encountered repositories and resolved result commits, inspected-file hashes, exact reading limits, and selected import graph are in [m5-carrier-inventory.json](../../provenance/searches/m5-carrier-inventory.json). Query-only hits have no inferred proof, license, build, or acceptance status. No search here establishes worldwide absence of a formal theorem.

## Selected source and literal domain

The selected source commit is `bac5cab53eb6526e366e861d289253ec81aa89f0`, Apache-2.0, upstream Lean `v4.35.0` and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The target is Lean `v4.36.0-rc2` with mathlib `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`. All 16 new source files and complete proof bodies were read. The exact Colib closure has 19 modules / 2626 source lines: 16 new modules / 2182 lines and three already accepted modules reused by import (`Boundary`, `BoundaryRetraction`, `Util.References`). Namespaces and declarations stay unchanged; only import prefixes change.

The active modules, originals, Git blob IDs, SHA256 hashes, explicit patches, DAG, license, assembly recipe and reused-context hashes are in [provenance-carriers.json](../../../deligne/vendor/provenance-carriers.json). Colib itself preserves implementation-origin citations to **kangxyz/quillen-k-theory**, commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, for HEP, cylinders, collars, and pushout tools. Those citations and copyright notices remain in exact original and active source. This is an indirect implementation origin; our direct source bytes and compiled proof bodies come from the pinned Colib cohort.

`Convexity.StdSimplex.simplexBoundary_homotopy_extension` takes actual continuous maps

```
f : C(X × StdSimplex ℝ (Fin (n+1)), Y)
H : C((X × boundary n) × I, Y)
h : ∀ x b, H ((x,b),0) = f (x,b.val)
```

and produces `K : C((X × StdSimplex ℝ (Fin (n+1))) × I,Y)` with the prescribed initial map and exact boundary homotopy. Source/target universes are independent; `n=0` is included. Its proof constructs actual radial retractions and uses closed gluing.

`TopCat.HomotopyExtensionProperty i` means that for every actual target `Z`, map `f : B ⟶ Z`, and `H : A ⊗ I ⟶ Z` satisfying the initial endpoint equation, an actual `K : B ⊗ I ⟶ Z` extends both. `homotopyExtensionProperty_continuous` converts this to ordinary `C(I × B,Z)` coordinates. `homotopyExtensionProperty_simplexBoundary X n` proves it for the literal inclusion `X × boundary n → X × StdSimplex_n`; pushout stability is proved using the actual cylinder compact-open adjunction.

`TopCat.CylinderBoundary i` is the actual topological pushout of the side cylinder `A × I` and the two caps `B ⊕ B` along `A ⊕ A`. `TopCat.CylinderBoundary.cylinderBoundaryMap i` sends the side to `(i a,t)` and the caps to `(b,0)` and `(b,1)`. Its theorem

```
TopCat.CylinderBoundary.homotopyExtensionProperty_cylinderBoundaryMap
  (hi : TopCat.HomotopyExtensionProperty i) :
  TopCat.HomotopyExtensionProperty
    (TopCat.CylinderBoundary.cylinderBoundaryMap i)
```

assumes HEP of `i`, not an interior filler or an already coherent homotopy. It does not assume the target contractible. A local client can glue prescribed side homotopy and endpoint maps on this genuine pushout, contract that boundary map in the target, apply this HEP, and take a slice. This additional argument is local project mathematics, not a supplier conclusion.

`Convexity.StdSimplex.exists_simplex_boundary_track_of_faces` glues actual continuous face tracks on `StdSimplex × I` under their explicit double-face equations. Its proof establishes common geometric preimages and descends an actual finite compact Hausdorff quotient. It is a gluing tool, not a structure with desired coherence assumed as a field.

## Verification scope

Every new module was explicitly built, including modules whose declarations are not retained by one final root. No mathematical compatibility port was needed. The provider audit covers all 201 canonical declarations, including private/generated constants, and all 201 physically serialized occurrences across the 16 modules, with no duplicate names. Each physical declaration's type, value/proof and universe parameters equals its imported audited declaration. Every transitive axiom is among `propext`, `Classical.choice`, `Quot.sound`.

Evidence lives in [deligne/evidence/providers/carriers](../../../deligne/evidence/providers/carriers). The first audit failure is retained: two endpoint `#check` commands omitted the `CylinderBoundary` namespace; this affected only the audit harness, not supplier sources. Later successful audit records do not overwrite that failure. Exact single-module official Lean checker runs are relative to pinned imported Mathlib and the accepted supplier context; they are not a second independently implemented kernel. All 16 exact-module checks passed sequentially in 99.15 seconds with unchanged source and artifact snapshots. [technical-summary.json](../../../deligne/evidence/providers/carriers/technical-summary.json) binds the successful build, audit and replay records; the audit-to-replay snapshots are identical. Independent A/B review and parent acceptance remain separate and pending at this handoff.

## Other inspected candidates and limits

| Repository / exact revision | Actual inspected domain | Decision and limits |
|---|---|---|
| `cadamcat/homotopy-hypothesis-lean4` / `6766fc567cfbf82a49843c698826c0d6aa47f7b5` | `carrierHomotopyStatement_proof` produces actual `HomotopicRel` between realization maps into a **finite target simplicial complex**, provided every source simplex factors through one common target simplex. | Genuine topology, but its common-simplex factorization is stronger and different from arbitrary monotone contractible target subspaces. Full 205-line proof and 34-line statement read; another 145-line pointwise file fetched only. No import closure, compile, audit, replay or reuse. |
| `AxiomMath/BondalThomsen` / `9a2bdcdcf6b25710459f7f476c9c62de3039b7bb` | `IntegralAcyclicCarrier` has target `ChainComplex AddCommGrpCat`, exactness and chain maps. | Chain homotopies do not supply `ContinuousMap.Homotopy`. Definition and declaration inventory inspected; the 656-line proof closure was not read or accepted. |
| `Vilin97/homotopy-groups-lean` / `c66523531ff172d7f41913d94e56921e790a1b47` | Finite affine simplicial elementary-collapse deformation maps, with explicit barycentric min-coordinate formula. | No arbitrary contractible-target cell-extension endpoint established in the inspected first 100 lines and later declaration signatures. Full 1175 lines and closure not reviewed; no build or reuse. |
| `openai/math` / `4eaee87548250b2682affda7d05d947c05554bae` | Selected Thomason relative contiguity and simplicial approximation declarations involve finite-poset affine/nerve models or `SSet.Homotopy`. | Bounded declaration/context inspection of three fetched files; no arbitrary topological carrier endpoint established and no new source selected here. This is distinct from the other owner's OAI12 weights supplier. |
| `lowrank/gromov-filling-lower-bound` / `d63b2618df02cb9c8bee04d6612b5241079949c9` | Carrier occurrences in normal-form complementary surface arcs and parity obstruction. | Term/declaration search only in a fetched 2092-line file; no generic topological carrier theorem established or source reused. |

At the pinned current mathlib revision, bounded source searches found actual nonsingular simplicial-set realization colimits (`NonsingularColimit`, already used in the accepted realization context). `ContinuousMap.Homotopy.extend` extends the **time coordinate** from the unit interval to the real line; it does not fill a simplex or sphere. No generic arbitrary-contractible-carrier endpoint was located by this bounded search. Remaining query-only repositories, every returned file and full commit, are retained in the machine inventory without promoting a name match to a proof assessment.
