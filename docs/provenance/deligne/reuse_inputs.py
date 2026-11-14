#!/usr/bin/env python3
"""Read-only supplier consolidation for the Deligne observation; never rewrites the central ledger."""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path

BASE = Path(__file__).resolve().parents[3]
OUT = BASE / 'docs/provenance'

def read(p): return json.loads(Path(p).read_text())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok, msg):
    if not ok: raise RuntimeError(msg)
def ref(p):
    p = Path(p)
    return {'path': str(p.relative_to(BASE)), 'sha256': sha(p)}
def check_map(m):
    for p, h in m.items():
        require(sha(BASE / p) == h, 'Changed bound input: ' + p)

def build():
    ledger_path = OUT / 'GITHUB-PROOF-SOURCES.json'
    ledger = read(ledger_path)
    old = ledger['accepted_cohorts']
    require(sum(len(c['files']) for c in old) == 436, 'Expected frozen prior 436 supplier units')
    cohorts = list(old)  # Preserve each old cohort record intact, not a lossy projection.
    by_module = {f['module']: (c, f) for c in old for f in c['files']}
    require(len(by_module) == 436, 'Old supplier module overlap requires explicit handling')
    inputs = {str(ledger_path.relative_to(BASE)): sha(ledger_path)}
    for c in old:
        for f in c['files']:
            for k in ['active_path', 'original_path']:
                inputs[f[k]] = sha(BASE / f[k])
            require(inputs[f['active_path']] == f['active_sha256'], 'Old active source changed')
            require(inputs[f['original_path']] == f['upstream_sha256'], 'Old original source changed')
    reused = []
    for name, count in [('weights', 12), ('carriers', 16)]:
        p = BASE / f'deligne/vendor/provenance-{name}.json'
        a = BASE / f'docs/provenance/acceptance-deligne-{name}.json'
        d, acceptance = read(p), read(a)
        require(acceptance['accepted'] is True and acceptance['modules'] == count,
                'Missing exact supplier root acceptance: ' + name)
        require(len(d['files']) == count, 'Supplier module count changed')
        for key, value in acceptance['provider_bindings'].items():
            if isinstance(value, dict):
                check_map(value)
                inputs.update(value)
        check_map(acceptance['independent_reviews_sha256'])
        inputs.update(acceptance['independent_reviews_sha256'])
        inputs.update({str(p.relative_to(BASE)): sha(p), str(a.relative_to(BASE)): sha(a)})
        files, patches = [], []
        for f in d['files']:
            active = 'deligne/vendor/' + f['path']
            original = 'deligne/vendor/' + f['original_path']
            patch = 'deligne/vendor/' + f['patch_path']
            require(sha(BASE / active) == f['active_sha256'], 'New active source changed')
            require(sha(BASE / original) == f['upstream_sha256'], 'New original source changed')
            require(sha(BASE / patch) == f['patch_sha256'], 'New patch changed')
            require(f['module'] not in by_module, 'New supplier counted twice')
            files.append({**f, 'active_path': active, 'original_path': original,
                          'patch_path': patch, 'scope': f.get('selection', f.get('modifications')),
                          'upstream_blob_url': d['repository'] + '/blob/' + d['upstream_sha'] + '/' + f['upstream_path']})
            patches.append({'module': f['module'], 'patch': ref(BASE / patch),
                            'scope': f.get('selection', f.get('modifications'))})
            inputs.update({active: sha(BASE / active), original: sha(BASE / original), patch: sha(BASE / patch)})
        lp = 'deligne/vendor/' + (d['license']['path'] if name == 'weights' else d['license_path'])
        expected_license = d['license']['sha256'] if name == 'weights' else d['license_sha256']
        require(sha(BASE / lp) == expected_license, 'License changed')
        applications_path = BASE / f'deligne/evidence/providers/{name}/applications.json'
        applications = read(applications_path)
        c = {'id': 'deligne-' + name + '-supplier', 'repository': d['repository'],
             'revision': d['upstream_sha'], 'module_count': count, 'files': files,
             'provenance': ref(p), 'root_acceptance': ref(a), 'root_acceptance_snapshot': acceptance,
             'license_files': [ref(BASE / lp)], 'license_identifier': 'Apache-2.0',
             'patches': patches, 'actual_applications': {'record': ref(applications_path), 'contents': applications},
             'disposition': 'Accepted supplier cohort only; full-project mathematical acceptance is separate.',
             'upstream_toolchain': d.get('upstream_lean_toolchain', d.get('upstream_toolchain')),
             'upstream_mathlib': d.get('upstream_mathlib_revision', d.get('upstream_mathlib')),
             'target_toolchain': d.get('lean_toolchain', d.get('target_toolchain')),
             'target_mathlib': d.get('project_mathlib_revision', d.get('target_mathlib')),
             'independent_reviews_sha256': acceptance['independent_reviews_sha256'],
             'verification_ok': True, 'fresh_exact_module_kernel_replays': acceptance['fresh_exact_module_kernel_replays']}
        for field in ['assembly_script', 'assembly_recipe', 'recipe']:
            if field in d:
                q = BASE / 'deligne' / d[field]
                if not q.is_file(): q = BASE / 'deligne/vendor' / d[field]
                c[field] = ref(q)
        for parent in [BASE / f'deligne/evidence/providers/{name}', BASE / 'deligne/reviews']:
            for q in parent.rglob('*'):
                if q.is_file() and (parent.name != 'reviews' or q.name.startswith(name + '-')):
                    inputs[str(q.relative_to(BASE))] = sha(q)
        for f in d.get('upstream_metadata', []):
            q = BASE / ('deligne/vendor/' + f['path'])
            require(sha(q) == f['sha256'], 'Upstream metadata changed')
            inputs[str(q.relative_to(BASE))] = sha(q)
        for f in d.get('reused_accepted_modules', []):
            require(f['module'] in by_module, 'Reused module absent from accepted old register')
            old_cohort, old_file = by_module[f['module']]
            require(old_file['active_sha256'] == f['active_sha256'], 'Reused active hash differs')
            require(old_file['upstream_sha256'] == f['original_sha256'], 'Reused original hash differs')
            reused.append({**f, 'prior_cohort': old_cohort['id'], 'counted_again': False,
                           'actual_active_path': old_file['active_path'], 'actual_original_path': old_file['original_path']})
        cohorts.append(c)
    require(len(reused) == 3, 'Expected three explicitly reused Colib units')
    all_modules = [f['module'] for c in cohorts for f in c['files']]
    require(len(all_modules) == len(set(all_modules)) == 464, 'Combined supplier unit count differs')
    require(len({c['repository'] for c in cohorts}) == 3, 'Scientific repository count differs')
    return {'kind': 'source-bound-deligne-combined-github-reuse-snapshot',
            'scope': 'Exact accepted supplier source units, not a claim that every declaration in every module is reachable.',
            'central_ledger_before_promotion': ref(ledger_path), 'accepted_cohorts': cohorts,
            'old_accepted_supplier_units': 436, 'new_accepted_supplier_units': 28,
            'accepted_supplier_units': 464, 'accepted_scientific_repository_count': 3,
            'reused_prior_modules': reused, 'input_sha256': dict(sorted(inputs.items())),
            'pinned_foundations': {'lean': ledger['lean_foundation'], 'lake_git_dependencies': ledger['lake_git_dependencies']},
            'central_ledger_updated': False, 'Lean_build_audit_or_replay_executed': False,
            'full_project_acceptance_inferred_from_supplier_acceptance': False}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = build()
    if args.output:
        require(not args.output.exists(), 'Refuse to overwrite immutable reuse snapshot')
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        print(json.dumps({'ok': True, 'output': str(args.output), 'units': 464, 'repositories': 3}))
    else:
        print(json.dumps({'ok': True, 'units': 464, 'repositories': 3, 'execute': False}))
if __name__ == '__main__': main()
