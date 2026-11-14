# Full Theorem 1.8 and the actual Deligne comparison

The complete scientific endpoint
[`ArtinNormalisers.Deligne5.theorem_1_8`](ArtinDeligne/Theorem18.lean) has
[root mathematical acceptance](../docs/theorem18/landmarks/milestone5-root-acceptance.json).
Both independent GPT-6.1 Sol/high reviews accepted its exact frozen scope:
[A](reviews/theorem18-a.json), [B](reviews/theorem18-b.json). The
[final local battery](evidence/theorem18-local-final/verification.json) passed
159 commands, a real clean/rebuild (19,433 jobs), and 64 fresh exact-module
replays. Complete canonical/physical auditing covered 1,391 project and 475
new supplier declarations, with zero duplicates and only the three standard
axioms. All 1,781 bound inputs, including 1,264 accepted historical inputs,
stayed unchanged. Clean GitHub CI remains pending separately.

For arbitrary `I`, `M : CoxeterMatrix I` with finite actual `M.Group`, and
any `J : Set I`, the theorem identifies the actual algebraic and covering
short exact sequences and proves the original relative complement and its
original normalizer quotient space are K(π,1) spaces for their stated
normalizer groups. There is no additional crystallographic, irreducibility,
positive-rank, chosen-simpliciality or asphericity hypothesis. Rank zero and
empty/full subsets are included.

The main exports in [`Theorem18.lean`](ArtinDeligne/Theorem18.lean) are:

| Declaration in `ArtinNormalisers.Deligne5` | Conclusion |
| --- | --- |
| `actualUniversalCover_isAspherical` in [`UniversalCoverComparison.lean`](ArtinDeligne/UniversalCoverComparison.lean) | Higher-homotopy vanishing of the original based-path universal cover. |
| `actualComplement_isAspherical`, `actualOrbit_isAspherical` | Asphericity of the original complement and quotient at every point. |
| `actualComplement_isKpi1`, `corollary_6_14` | Literal TauCeti K(G,1) predicates for the pure normalizer image and normalizer quotient. |
| `theorem_1_8`, `theorem_1_8_all_basepoints` | Both K(G,1) conclusions together with the complete actual M4 diagrams and all-basepoint coverage. |

Here `TauCeti.IsAspherical X x` means path connectedness and trivial actual
based homotopy groups in every dimension at least two.
`TauCeti.IsEilenbergMacLaneSpaceOne G X x` additionally exhibits
`FundamentalGroup X x ≃* G`. The group witnesses are precisely the inverses
of the existing M4 comparison isomorphisms. The actual Artin group still has
its standard braid presentation, and the spaces retain their original
subspace/orbit topologies.

The proof constructs a weighted simple-chain Garside model from actual
incoming reduced ribbons. Compact maps land in proved finite contractible
carriers; this proves the model's based higher-homotopy vanishing. Actual
lifted canonical cells and a subordinate partition of unity produce a
continuous map from the original universal cover to that model. Actual
sheet-intersection components provide monotone contractible carriers for a
continuous return. A parameterized carrier construction proves the return
composite homotopic to the identity. Higher-homotopy transfer and the actual
surjective coverings finish the K(G,1) conclusions. No comparison map,
coherent homotopy or Deligne conclusion is supplied as a mathematical premise.
The [full report](../docs/theorem18/landmarks/milestone5-final-report.md)
connects these steps to exact files and to Theorem 1.8/Corollary 6.14.

## Rebuild and verification

Use the committed Lean `v4.36.0-rc2` and mathlib
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9` pins. From this directory:

```bash
python3 scripts/cache_prerequisites.py --plan
python3 scripts/cache_prerequisites.py
lake build ArtinDeligne
python3 scripts/verify.py --plan
python3 scripts/verify.py --execute --mode final --output evidence/theorem18-ci
```

Choose a fresh output directory for a new verification run. The cache helper
fetches whole pinned mathlib because the retained OAI imports require it;
it performs no `lake update` or manifest rewrite. The final verifier is
review-gated: it cleans only `artin-deligne`, explicitly builds all 36 project
modules and 28 new suppliers, audits their complete scientific declarations
and physical serialized occurrences, then runs 64 exact-module kernel replays
in fresh Lean processes using the accepted runner for the official kernel
algorithm. A plan or ordinary build is not a successful final
verification record. Final commands may be rejected until their frozen
review receipts are present.

Only `propext`, `Classical.choice` and `Quot.sound` are permitted transitive
axioms. Replay is relative to imported pinned mathlib and the accepted older
supplier context: it is not a fresh replay of every older dependency or a
second independent kernel implementation. No two-sided nerve homotopy
equivalence, contractibility of the entire universal cover, finite CW model
or universal-bundle classification is asserted by this packet.

## Source records

The scientific supplier inventory comprises 464 units from three repositories:
436 historical units plus 12 new OAI weighted-realization modules and 16 new
Colib extension/gluing modules. These counts exclude mathlib, Lean and build
tooling. Exact upstream/local hashes, original source, patches, licenses and
reuse edges are in [weights provenance](vendor/provenance-weights.json),
[carrier provenance](vendor/provenance-carriers.json) and the
[complete central ledger](../docs/provenance/GITHUB-PROOF-SOURCES.md).
All selected repositories use Apache-2.0. The OAI weights cohort includes
one explicitly recorded continuity-tactic compatibility change; the Colib
cohort changes only imports. Neither cohort is described as byte-identical
upstream source. Consulted-only candidates and reading/verification limits
remain separate in the linked search inventories.
