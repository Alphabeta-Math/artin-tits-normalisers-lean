# Navigation metadata tools

These tools organize the already verified source at commit `3c389334729dbd37d26bdf52dd808e540aae6d37`. They do not rerun the mathematical build, axiom audit or kernel replay. Proof reproduction belongs to that exact science commit and its archived verification records.

The source census uses actual compiled `.ilean` declaration/name ranges and frozen source hashes. It identifies 2,295 written declaration commands and 1,999 generated artifacts. A range inherited by a generated declaration does not make it an article lemma. All 4,294 compiled roots and their exact direct type/value/structural dependencies remain indexed.

`ExportStatements.lean` is a metadata-only observer importing the same complete aggregate context as the dependency graph. Its output retains all universe parameters and every `Expr`, `Level`, `Name`, syntax and source-info field. Readable types are rendered views, not independently compilable declarations: routine proof terms may appear as `⋯`, explicitly flagged. The structural types and exact source/context links are authoritative.

The original complete JSON is retained losslessly in [statements.raw.json.gz](../data/statements.raw.json.gz), with its original uncompressed SHA256 in [the compaction receipt](../data/compaction-receipt.json). [The shared type table](../data/type-expressions.json.gz) factors repeated JSON strings and trees without dropping any field. Every one of the 4,294 types has been reconstructed and checked against its original structural SHA256.

```sh
python3 docs/navigation/tools/compact_types.py \
  --input docs/navigation/data/statements.json --check
python3 docs/navigation/tools/show_type.py \
  --name ArtinNormalisers.Artin.lemma_2_8
```

`show_type.py` prints the exact reconstructed structural type; `--rendered` prints only its labeled readable view.

The curated catalog is configured in [important-projects.json](important-projects.json): twenty important topics, with their selected Lean declarations. Regenerate only this focused navigation with:

```bash
python3 docs/navigation/tools/generate_important_projects.py
python3 docs/navigation/tools/validate_navigation.py
```

The validator checks the twenty-page limit, exact source/statement/proof locations, original citation fields, direct dependency records, evidence links, pinned scientific hashes and Markdown navigation. It performs documentation metadata checks only. Mathematical verification remains bound to the verified source tag and CI archive.

The exhaustive machine-readable source census and structural types remain provenance. They are not expanded into thousands of human navigation pages.
