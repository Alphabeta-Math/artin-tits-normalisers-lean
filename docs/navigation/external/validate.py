#!/usr/bin/env python3
"""Validate source-catalog structure, input/output hashes, and local Markdown links."""
import gzip
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
metadata = json.loads((HERE / 'metadata.json').read_text())
raw = gzip.decompress((HERE / 'catalog.json.gz').read_bytes())
catalog = json.loads(raw)
assert hashlib.sha256(raw).hexdigest() == metadata['uncompressed_catalog_sha256']
for path, record in catalog['inputs'].items():
    assert sha(ROOT / path) == record['sha256'], path
for name, record in metadata['outputs'].items():
    assert sha(HERE / name) == record['sha256'], name
assert sha(ROOT / metadata['generator']['path']) == metadata['generator']['sha256']
assert len(catalog['declarations']) == 47111
assert len(catalog['modules']) == 1845
assert len(catalog['repositories']) == 13
assert len(catalog['selected_supplier_units']) == 464
assert len(catalog['external_canonical_project_root_aliases']) == 1
assert sum(r['reachable']['declarations'] for r in catalog['repositories'].values()) == 47111
assert sum(r['reachable']['declarations'] > 0 for r in catalog['repositories'].values()) == 7
assert sum(r['lake_package'] is not None for r in catalog['repositories'].values()) == 9
for name, declaration in catalog['declarations'].items():
    module = catalog['modules'][declaration['module']]
    assert name in module['reachable_declaration_names'], name
    assert declaration['github_source_url'] == module['github_source_url'], name
    assert declaration['repository'] == module['repository'], name
    assert module['revision'] == catalog['repositories'][module['repository']]['revision']
for unit in catalog['selected_supplier_units'].values():
    assert unit['reachable_count'] == len(unit['reachable_declarations'])
    assert unit['upstream_source_url']
    for name in unit['reachable_declarations']:
        assert catalog['declarations'][name]['module'] == unit['module'], name
assert sum(u['reachable_count'] > 0 for u in catalog['selected_supplier_units'].values()) == 242
local_links = []
for document in HERE.glob('*.md'):
    # README-table.md is deliberately a fragment for the repository-root README.
    base = ROOT if document.name == 'README-table.md' else document.parent
    for link in re.findall(r'\]\(([^)]+)\)', document.read_text()):
        if '://' in link or link.startswith('#'):
            continue
        target = link.split('#', 1)[0]
        assert (base / target).exists(), (document.name, target)
        local_links.append((document.name, target))
assert catalog['verified_release']['full_theorem_1_8_proved']
assert catalog['verified_release']['clean_github_ci'] == 'passed'
assert not catalog['verified_release']['actual_universal_cover_contractible_proved']
assert not catalog['verified_release']['two_sided_nerve_homotopy_equivalence_proved']
print(f'Validated 47,111 declarations, 1,845 modules, 464 supplier units, 13 repositories, '
      f'input/output hashes, and {len(local_links)} local Markdown links.')
