# Full compiled M3 proof dependency record

The separate [M3 execution](m3/run-20261114T065009Z/execution.json) passed with unchanged source/object inputs and unchanged historical baseline. Its [complete graph](m3/run-20261114T065009Z/graph.json.gz) contains 2,375 project roots, 42,408 reachable declarations, 966,795 references and 1,655 defining modules. All physical private/generated project parts are included; raw exports and annotated graph remain immutable.

The accounting is `1305 + 1071 − 1 = 2375` distinct root names, and `2375 + 2 = 2377` physical occurrences. The shared generated theorem is `ArtinNormalisers.Ribbon2.elementaryMu.congr_simp`, physically present in `ArtinRibbons.CofinalRibbons`, `ArtinRibbons.RibbonWords` and `ArtinChambers.PositiveTransport`. Joint export canonically owns it in `CofinalRibbons`. The technical M3 audit uses another import order and correctly reports 1,071 canonical/physical declarations with zero duplicates in that context; these are not 1,071 globally new names. Both aliases have exactly identical type, proof and universe parameters. Every old root and every old dependency edge is retained.

[Source-attribution metadata](m3/source-attribution.json) corrects the original child-directory Git-tree query without rewriting graph/execution bytes: 37 project modules have exact committed bytes at observed HEAD; 42 new modules are precommit source snapshots. Their exact hashes are authoritative. No GitHub blob link is asserted for uncommitted files. A later immutable source commit can be attached separately.

The [root acceptance](../theorem18/landmarks/milestone3-root-acceptance.json) records mathematical acceptance and both final independent reviews; clean GitHub CI remains pending. Graph export is an observation, not another proof acceptance or kernel implementation. Supplier physical duplicates retain their separate accepted inventory records.

To create a new observation after root confirms compiled readiness:

```bash
python3 docs/provenance/run_m3_export.py --execute --technical-record chambers/evidence/landmark3-technical-20261114T074500Z/verification.json
python3 docs/provenance/refresh_ledger.py
python3 docs/provenance/validate_ledger.py
```

Each export uses a new directory. The historical through-M2 graphs, raw exports, execution records and observer sources are read-only. No Lake configuration changes are required. New graph source/configuration/tooling hashes are bound independently; editing documentation or an observer does not change frozen mathematical proof inputs. Do not rerun the historical baseline writer over its archived outputs.
