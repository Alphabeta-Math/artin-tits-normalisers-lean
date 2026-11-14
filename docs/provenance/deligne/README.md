# Complete Deligne dependency observation

The [actual complete export](run-20261114T132100Z/execution.json) and [metadata validation](validation-20261114T132100Z.json) passed. Both complete raw graphs are identical. The annotated [graph](run-20261114T132100Z/graph.json.gz) retains 4,294 project roots, 51,405 reachable declarations, 1,215,678 references and 1,989 defining modules. All earlier roots and dependency rows survive unchanged, along with all 4,296 physical project occurrences and three inherited exact theorem aliases. No raw node, edge, occurrence or alias was deleted during annotation/compression.

The actual source attribution checks identify 108 defining project modules matching Git HEAD and 35 newly authored defining modules retained as exact uncommitted snapshots, with no fabricated blob URLs. All 36 new project sources, including the import-only aggregate, match the frozen technical inventory. Source publication is deliberately a later binding to an actual science commit. Root mathematical acceptance, final exact replay battery and clean CI remain separately controlled records.

[Actual supplier use](run-20261114T132100Z/supplier-use.json) accounts for all 464 accepted units: 242 have reachable compiled declarations; the other selected closure units are explicitly marked as having no reachable declaration in this observation. This is distinct from import reachability, whole-module acceptance and complete per-cohort physical audits.

This directory is new metadata infrastructure. It preserves all previous graph/export/publication records. The central current ledger is not updated until explicit root approval after final mathematical acceptance and the actual local battery.

`reuse-inventory.json` retains every prior accepted cohort intact and records the accepted 12 OAI weight modules and 16 Colib carrier modules: 436 + 28 = 464 source units from three scientific repositories. The three already accepted Colib closure modules are identified and counted once. Original/local sources, declared ports, licenses, provider reviews, exact source inventories, upstream metadata and actual application logs remain bound. Foundation and tooling pins remain separate.

`ExportDependencies.lean` imports the actual final aggregate plus every older project aggregate. It observes every canonical and physical project declaration, including private/generated names, and checks equal types, proof values and universe parameters for every repeated physical theorem. Alias rows remain explicit; canonical term nodes do not erase occurrences. Ordinary/server/private parts and the imported module closure are recorded. Type/value/inductive/constructor/recursor references are traversed recursively, including opaque proof values.

`run_export.py` is read-only, defaulting to a plan. One execution performs two identical complete observer passes while binding source/object inputs before and after. It does not build, run another axiom audit, replay the kernel, accept mathematics or infer CI success. Every old root, reachable declaration dependency row, physical occurrence and alias must survive. `supplier-use.json` identifies actual reachable compiled supplier declarations and separately identifies selected closure units with no reachable declaration.

After the final source inventory and single technical observation are ready:

```sh
python3 docs/provenance/deligne/run_export.py --execute \
  --technical-record deligne/evidence/theorem18-observation/verification.json \
  --output docs/provenance/deligne/NEW-RUN
python3 docs/provenance/deligne/validate_export.py \
  --run docs/provenance/deligne/NEW-RUN \
  --output docs/provenance/deligne/NEW-VALIDATION.json
```

Use unique output paths; no historical output may be overwritten. Mathematical acceptance comes only from the root receipt and both statement reviews. Source publication is a later actual Git blob binding via `bind_publication.py` / `validate_publication.py` after the exact science commit exists. `promote_ledger.py` only prepares a plan unless explicitly executed following root approval, and preserves the old cohort/graph/publication history while updating current summaries. The current scientific entrypoint will be `THEOREM18.md`.
