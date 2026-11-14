# Full compiled M4 dependency and source-publication record

The separate [M4 observation](m4/run-20261114T080416Z/execution.json) and [graph integrity validation](m4/validation.json) pass. The [complete graph](m4/run-20261114T080416Z/graph.json.gz) records 2,526 project roots, 42,603 reachable declarations, 973,914 references and 1,670 defining modules, including all private/generated project parts.

`2375 + 151 = 2526` distinct project roots. The 2,528 physical occurrences include the two inherited aliases of `ArtinNormalisers.Ribbon2.elementaryMu.congr_simp` in `RibbonWords` and `PositiveTransport`, canonically owned by `CofinalRibbons`. The new M4 audit has 151 canonical/physical declarations and zero duplicates; no new M4 name overlaps an older root. Every M3 root and dependency edge is retained. All immutable M2/M3 graphs, observers, raw executions and prior publication records remain byte-identical.

All 91 project defining modules have exact published source bytes at `e7703926f3e486c0fca3a0fe292ab56d6411c248`, checked using Git's full tree and actual blobs. The [source-publication binding](publications/e7703926f3e486c0fca3a0fe292ab56d6411c248/binding.json) maps 1,014 source/configuration/provider/review/record hashes, including all 13 M4 project files, to that actual clean-CI code commit. [Independent publication validation](publications/e7703926f3e486c0fca3a0fe292ab56d6411c248/validation.json) checks preserved Git tree/batch output and Git object identities. No frozen proof/configuration/provider/review differs from publication.

Two observer-only files were written after the code commit: `ExportM4Dependencies.lean` and `run_m4_export.py`. Their exact snapshot bytes are retained under the publication record's `observer-sources/`; they are explicitly classified as post-publication metadata, with no false Git-blob link to the earlier CI code commit. External foundations retain their own pins and are not claimed as source blobs in this project.

The accepted suppliers remain two scientific repositories: 403 prior modules plus one importable TauCeti fragment containing exactly two unchanged proof blocks. Its complete original is preserved for provenance, without accepting unrelated declarations. Exact original/active/block/assembly/patch/license/review and actual verification records are in the central ledger. New M4 search records distinguish eight source-inspected repositories from 76 query-hit repositories; search results are not proof use or acceptance.

Root mathematical acceptance and both final independent reviews are recorded in [the M4 acceptance](../theorem18/landmarks/milestone4-root-acceptance.json). Clean [CI43573814974](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43573814974) remains in progress; no successful CI result is asserted. Full Theorem 1.8 and asphericity remain unproved.

Metadata reproduction uses unused output paths:

```bash
python3 docs/provenance/validate_m4_export.py --output /tmp/m4-graph-validation-e770392.json
python3 docs/provenance/validate_m4_publication.py --binding docs/provenance/publications/e7703926f3e486c0fca3a0fe292ab56d6411c248/binding.json --output /tmp/m4-publication-validation-e770392.json
```

No build, axiom audit or kernel replay is performed by these checks. New observations, when root authorizes them, use a new `m4/run-*` directory; historical exports and publication records are never overwritten. No Lake configuration changes are required for the read-only observer.
