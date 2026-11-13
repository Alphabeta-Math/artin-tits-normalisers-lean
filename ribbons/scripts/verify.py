#!/usr/bin/env python3
"""Verify source-bound landmark 2; actual normalizers and chosen-lcm presentation only."""
import argparse
import datetime as dt
import difflib
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT.parent

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def aggregate(mapping):
    return hashlib.sha256(json.dumps(mapping, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def require(test, message):
    if not test:
        raise RuntimeError(message)

def source_map():
    return {str(p.relative_to(BASE)): sha(p) for p in
            [ROOT / 'ArtinRibbons.lean', *sorted(ROOT.glob('ArtinRibbons/**/*.lean'))]}

def check_bindings():
    inv = read(ROOT / 'source-inventory.json')
    require(inv['landmark_2_proved'] is True and inv['full_theorem_1_8_proved'] is False, 'Wrong scope')
    require(inv['project_source_sha256'] == source_map(), 'Changed/missing/extra project sources')
    config = {str((ROOT / p).relative_to(BASE)): sha(ROOT / p) for p in
              ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']}
    require(inv['configuration_sha256'] == config, 'Changed configuration')
    provenance = ROOT / 'vendor/provenance.json'
    require(sha(provenance) == inv['vendor_provenance_sha256'], 'Changed provider provenance')
    provider = read(provenance)
    modules = provider['modules']
    require(len(modules) == provider['module_count'] == 359 and
            len({m['module'] for m in modules}) == 359, 'Provider coverage mismatch')
    require(set(provider['topological_order']) == {m['module'] for m in modules}, 'Provider order mismatch')
    require(provider['upstream_sha'] == '4eaee87548250b2682affda7d05d947c05554bae', 'Changed upstream source pin')
    active = {'ribbons/vendor/' + m['path']: sha(ROOT / 'vendor' / m['path']) for m in modules}
    original = {'ribbons/vendor/upstream-original/' + m['path']:
                sha(ROOT / 'vendor/upstream-original' / m['path']) for m in modules}
    require(active == inv['provider_active_source_sha256'] and
            original == inv['provider_original_source_sha256'], 'Changed provider sources')
    require(aggregate(active) == inv['provider_active_aggregate_sha256'] and
            aggregate(original) == inv['provider_original_aggregate_sha256'], 'Provider aggregate hash mismatch')
    require(set(active) == {str(p.relative_to(BASE)) for p in ROOT.glob('vendor/OAI/**/*.lean')},
            'Extra/missing active provider module')
    require(set(original) == {str(p.relative_to(BASE)) for p in ROOT.glob('vendor/upstream-original/**/*.lean')},
            'Extra/missing original provider module')
    patch_map = {str(p.relative_to(BASE)): sha(p) for p in ROOT.glob('vendor/compatibility-patches/*.patch')}
    require(patch_map == inv['provider_compatibility_patch_sha256'], 'Changed compatibility patches')
    ports = {p['path']: p for p in provider['compatibility_ports']}
    require(len(ports) == len(patch_map) == 7, 'Expected exactly seven compatibility ports')
    changed = set()
    for m in modules:
        p = m['path']
        require(p == m['module'].replace('.', '/') + '.lean', 'Provider module/path mismatch')
        require(active['ribbons/vendor/' + p] == m['active_sha256'] and
                original['ribbons/vendor/upstream-original/' + p] == m['upstream_sha256'],
                'Provider manifest hash mismatch: ' + p)
        original_bytes = (ROOT / 'vendor/upstream-original' / p).read_bytes()
        active_bytes = (ROOT / 'vendor' / p).read_bytes()
        if original_bytes != active_bytes:
            changed.add(p)
            require(p in ports, 'Undeclared provider modification: ' + p)
            diff = ''.join(difflib.unified_diff(original_bytes.decode().splitlines(keepends=True),
                active_bytes.decode().splitlines(keepends=True), fromfile='upstream-original/' + p, tofile=p))
            patch = ROOT / 'vendor/compatibility-patches' / (Path(p).name + '.patch')
            require(patch.read_text() == diff, 'Compatibility patch differs from actual changes: ' + p)
            require(ports[p]['active_sha256'] == m['active_sha256'] and
                    ports[p]['original_sha256'] == m['upstream_sha256'], 'Port hash mismatch')
    require(changed == set(ports), 'Unexpected compatibility port inventory')
    parent_path = BASE / inv['parent_verification_path']
    require(sha(parent_path) == inv['parent_verification_sha256'], 'Changed historical parent verification')
    parent = read(parent_path)
    require(parent['ok'] is True and parent['full_theorem_1_8_proved'] is False, 'Parent verification failed')
    require(aggregate(parent['input_sha256']) == inv['parent_input_aggregate_sha256'], 'Parent input digest mismatch')
    for p, digest in parent['input_sha256'].items():
        require(sha(BASE / p) == digest, 'Changed accepted parent input: ' + p)
    for review in parent['independent_reviews']:
        p = BASE / 'docs/theorem18/reviews' / ('foundations-' + review['reviewer'] + '.json')
        require(sha(p) == review['json_sha256'] and sha(p.with_suffix('.md')) == review['markdown_sha256'],
                'Historical parent review changed')
    manifest, base_manifest = read(ROOT / 'lake-manifest.json'), read(BASE / 'lake-manifest.json')
    pins = {p['name']: p['rev'] for p in manifest['packages'] if p['type'] == 'git'}
    require(pins == {p['name']: p['rev'] for p in base_manifest['packages'] if p['type'] == 'git'},
            'Dependencies differ from accepted parent pins')
    require(pins['mathlib'] == provider['pilot_target_mathlib'] == '65d730f7150f21fdfa32f3e73a3f549c1f96a0e9',
            'Wrong mathlib pin')
    require((ROOT / 'lean-toolchain').read_bytes() == (BASE / 'lean-toolchain').read_bytes(), 'Toolchain differs')
    path_packages = [p for p in manifest['packages'] if p['type'] == 'path']
    require(len(path_packages) == 1 and path_packages[0]['dir'] == '..', 'Unexpected path dependency')
    reviews = []
    keys = ['project_source_sha256', 'configuration_sha256', 'vendor_provenance_sha256',
            'provider_active_aggregate_sha256', 'provider_original_aggregate_sha256',
            'provider_compatibility_patch_sha256', 'parent_verification_sha256', 'parent_input_aggregate_sha256']
    for label in ['a', 'b']:
        p = ROOT / 'reviews' / ('landmark2-' + label + '.json')
        review = read(p)
        require(review['verdict'] == 'accept-landmark2' and review['landmark_2_proved'] is True and
                review['full_theorem_1_8_proved'] is False, 'Unaccepted or incorrect review scope: ' + label)
        require(review['model'] == 'gpt-6.1-sol' and review['reasoning_effort'] == 'high', 'Wrong reviewer configuration')
        for key in keys:
            require(review[key] == inv[key], 'Stale review binding: ' + label + ':' + key)
        reviews.append({'reviewer': label, 'json_sha256': sha(p), 'markdown_sha256': sha(p.with_suffix('.md'))})
    return inv, provider, parent, reviews

def inputs(parent):
    paths = [*ROOT.glob('*.lean'), *ROOT.glob('ArtinRibbons/**/*.lean'), *ROOT.glob('scripts/*.py'),
             *ROOT.glob('vendor/OAI/**/*.lean'), *ROOT.glob('vendor/upstream-original/**/*.lean'),
             *ROOT.glob('vendor/compatibility-patches/*.patch'), *ROOT.glob('reviews/landmark2-*')]
    paths += [ROOT / p for p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'README.md',
              'source-inventory.json', 'vendor/provenance.json', 'vendor/LICENSE.openai-math',
              'vendor/README.md', 'vendor/ENDPOINTS.md']]
    paths += [BASE / '.github/workflows/ribbons.yml']
    return {**parent['input_sha256'], **{str(p.relative_to(BASE)): sha(p) for p in sorted(set(paths))}}

def verify_provider_certificate(path, provider, env):
    cert = read(path)
    require(cert['ok'] is True and cert['inputs_unchanged'] is True and cert['completed_module_count'] == 359,
            'Provider replay incomplete or failed')
    expected = {m['module']: m for m in provider['modules']}
    require(set(cert['modules']) == set(expected) and len(cert['commands']) == 359 and
            {c['module'] for c in cert['commands']} == set(expected), 'Provider replay module coverage mismatch')
    manifest = path.parent / cert['source_inputs_file']
    require(sha(manifest) == cert['source_inputs_sha256'], 'Changed replay input manifest')
    # Certificate reuse accepts exactly the same bytes, including compiled artifacts
    # and the toolchain binaries. Historical stat/absolute paths remain in the raw record.
    required = {}
    def bind(p, role):
        required[str(p.absolute())] = role
    bind(ROOT / 'scripts/replay_providers.py', 'verification script')
    bind(ROOT / 'vendor/provenance.json', 'provider provenance')
    bind(ROOT / 'vendor/LICENSE.openai-math', 'upstream license')
    for name in ['README.md', 'ENDPOINTS.md']:
        bind(ROOT / 'vendor' / name, 'provider source notes')
    for p in ROOT.glob('vendor/compatibility-patches/*.patch'):
        bind(p, 'compatibility patch')
    for directory, role in [(ROOT, 'ribbons configuration'), (BASE, 'parent configuration baseline')]:
        for name in ['lakefile.toml', 'lean-toolchain', 'lake-manifest.json']:
            bind(directory / name, role)
    artifact_count = 0
    for m in provider['modules']:
        bind(ROOT / 'vendor' / m['path'], 'active provider source')
        bind(ROOT / 'vendor/upstream-original' / m['path'], 'original upstream source')
        stem = ROOT / '.lake/build/lib/lean' / Path(*m['module'].split('.'))
        require(stem.with_suffix('.olean').is_file(), 'Missing current provider artifact')
        for p in sorted(stem.parent.glob(stem.name + '.olean*')):
            if p.is_file() and not p.name.endswith('.hash'):
                bind(p, 'frozen provider compiled artifact')
                artifact_count += 1
    mathlib = ROOT / '.lake/packages/mathlib'
    for name in ['lean-toolchain', 'lake-manifest.json']:
        bind(mathlib / name, 'pinned mathlib metadata')
    bind(mathlib / '.lake/build/lib/lean/Mathlib.olean', 'imported mathlib root artifact')
    for binary in ['lean', 'leanchecker', 'lake']:
        p = Path(subprocess.check_output(['lake', 'env', 'which', binary], cwd=ROOT, env=env, text=True).strip())
        bind(p, 'toolchain executable')
    bound = read(manifest)['files']
    require(len(bound) == len(required) == cert['input_count'] and
            {i['path']: i['role'] for i in bound} == required,
            'Incomplete or unexpected provider replay input coverage')
    require(cert['provider_compiled_artifact_count'] == artifact_count,
            'Incomplete provider compiled artifact coverage')
    for item in bound:
        require(str(Path(item['path']).resolve()) == item['resolved_path'], 'Replayed input resolves elsewhere')
        require(sha(Path(item['path'])) == item['sha256'], 'Replayed provider input bytes changed: ' + item['path'])
    for c in cert['commands']:
        require(c['exit_code'] == 0 and c['command'] == ['lake', 'env', 'leanchecker', '--verbose', c['module']],
                'Unexpected provider replay command or failure')
        require(c['active_source_sha256'] == expected[c['module']]['active_sha256'] and
                c['upstream_original_sha256'] == expected[c['module']]['upstream_sha256'], 'Replay source mismatch')
        require(sha(path.parent / c['raw_log']) == c['raw_log_sha256'], 'Changed provider replay log')
        require(c['all_input_hashes_ref'] == cert['source_inputs_sha256'], 'Replay command input binding mismatch')
        require((path.parent / c['raw_log']).read_text().splitlines()[0] == 'replaying ' + c['module'],
                'Replay log belongs to another module')
    require(cert['actual_mathlib_revision'] == provider['pilot_target_mathlib'], 'Replayed wrong mathlib pin')
    return {'verification': str(path), 'verification_sha256': sha(path),
            'input_manifest_sha256': sha(manifest), 'module_count': 359,
            'reuse_policy': 'Exact source, compiled artifact, dependency root and executable hashes rechecked; no fresh replay implied by reuse'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--fresh-provider-replay', action='store_true')
    parser.add_argument('--provider-workers', type=int, choices=(1, 2, 4), default=2)
    parser.add_argument('--provider-record', type=Path,
                        help='Reuse a completed local certificate only after checking every current bound input byte')
    args = parser.parse_args()
    out = (args.output or ROOT / 'evidence' /
           dt.datetime.now(dt.timezone.utc).strftime('landmark2-%Y%m%dT%H%M%SZ')).resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + env.get('PATH', '')
    env['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
    env.setdefault('LEAN_NUM_THREADS', '2')
    record = {'kind': 'theorem18-landmark2-verification', 'ok': False,
              'landmark_2_proved': True, 'full_theorem_1_8_proved': False,
              'scope': 'Actual reduced ribbon normalizers and complete fixed lcm groupoid presentation',
              'started_at': dt.datetime.now(dt.timezone.utc).isoformat(), 'commands': [],
              'repository_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=BASE, text=True).strip(),
              'limitations': ['Bundled Lean kernel, not an independent kernel implementation.',
                  'Mathlib is imported at the pinned revision, not freshly kernel-replayed in its entirety.',
                  'Parent 65 accepted inputs checked unchanged against previous CI.',
                  'No geometric comparison, literal full standard-path classification, or asphericity claim.']}
    def save():
        (out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    def run(label, argv):
        log = out / (label + '.log')
        print('Running:', ' '.join(argv), flush=True)
        start = time.monotonic()
        with log.open('w') as stream:
            result = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
        record['commands'].append({'argv': argv, 'exit_code': result.returncode, 'log': log.name,
                                   'log_sha256': sha(log), 'elapsed_seconds': round(time.monotonic() - start, 3)})
        save()
        require(result.returncode == 0, label + ' failed; see ' + str(log))
        return log
    save()
    try:
        inv, provider, parent, reviews = check_bindings()
        record['independent_reviews'] = reviews
        record['parent_verified_input_sha256'] = parent['input_sha256']
        record['parent_verification_sha256'] = inv['parent_verification_sha256']
        record['input_sha256'] = inputs(parent)
        run('lean-version', ['lake', 'env', 'lean', '--version'])
        revision = run('mathlib-revision', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'])
        require(revision.read_text().strip() == provider['pilot_target_mathlib'], 'Actual mathlib revision differs')
        status = run('mathlib-tracked-status', ['git', '-C', '.lake/packages/mathlib', 'status', '--porcelain', '--untracked-files=no'])
        require(not status.read_text().strip(), 'Mathlib checkout has tracked changes')
        run('project-verification', ['python3', 'scripts/verify_project.py', '--output', str(out / 'project')])
        project = read(out / 'project/verification.json')
        require(project['ok'] is True, 'Project build/audit/replay failed')
        record['project_verification_sha256'] = sha(out / 'project/verification.json')
        log = run('provider-axiom-audit', ['lake', 'env', 'lean', 'ProviderAudit.lean'])
        seen = {line.split()[1] for line in log.read_text().splitlines() if line.startswith('RIBBON_PROVIDER_AXIOMS ')}
        require(seen == {m['module'] for m in provider['modules']}, 'Incomplete provider axiom module coverage')
        record['provider_axiom_module_count'] = len(seen)
        record['provider_axiom_declaration_count'] = sum(line.startswith('RIBBON_PROVIDER_AXIOMS ') for line in log.read_text().splitlines())
        semantic_names = {line.split()[2].removesuffix(':') for line in log.read_text().splitlines()
                          if line.startswith('RIBBON_PROVIDER_AXIOMS ')}
        physical_log = run('provider-physical-coverage', ['lake', 'env', 'lean', 'ProviderPhysicalAudit.lean'])
        def rows(prefix):
            return [json.loads(line[len(prefix):]) for line in physical_log.read_text().splitlines()
                    if line.startswith(prefix)]
        physical_modules = rows('PROVIDER_PHYSICAL_MODULE_JSON ')
        require(len(physical_modules) == 359 and {r['module'] for r in physical_modules} == seen,
                'Incomplete physical provider module coverage')
        for row in physical_modules:
            require(row['declarations'] == len(row['names']) == len(set(row['names'])) > 0,
                    'Malformed physical provider declaration inventory')
        require({name for r in physical_modules for name in r['names']} == semantic_names,
                'Physical provider declarations differ from the axiom-audited names')
        summaries = rows('PROVIDER_PHYSICAL_SUMMARY_JSON ')
        require(len(summaries) == 1, 'Missing or duplicate provider physical summary')
        summary = summaries[0]
        require(summary['modules'] == 359 and summary['canonical_declarations'] == len(semantic_names) and
                summary['distinct_physical_names'] == len(semantic_names) and
                summary['physical_occurrences'] == sum(r['declarations'] for r in physical_modules) and
                summary['canonical_axioms_checked'] is True and
                summary['all_physical_type_value_universe_parameters_identical'] is True,
                'Provider physical/canonical declaration coverage mismatch')
        duplicate_rows = rows('PROVIDER_PHYSICAL_DUPLICATE_JSON ')
        require(len(duplicate_rows) == summary['identical_theorem_duplicates'] and
                summary['physical_occurrences'] == len(semantic_names) + len(duplicate_rows),
                'Unaccounted provider physical occurrences')
        require(all(all(r[k] is True for k in ['same_type', 'same_proof',
                    'same_universe_parameters', 'theorem_in_both']) for r in duplicate_rows),
                'Unverified provider declaration overlap')
        record['provider_physical_summary'] = summary
        record['provider_identical_theorem_duplicates'] = duplicate_rows
        fresh_provider = args.fresh_provider_replay or args.provider_record is None
        if fresh_provider:
            cert_path = out / 'providers/verification.json'
            run('provider-kernel-replays', ['python3', 'scripts/replay_providers.py', '--workers',
                str(args.provider_workers), '--output', str(out / 'providers')])
        else:
            cert_path = args.provider_record.resolve()
        record['provider_replay'] = verify_provider_certificate(cert_path, provider, env)
        record['fresh_provider_replay'] = fresh_provider
        require(inputs(parent) == record['input_sha256'], 'Inputs changed during verification')
        require(check_bindings()[3] == reviews, 'Review receipts changed during verification')
        record['ok'] = True
    except BaseException as exc:
        record['error'] = str(exc)
        raise
    finally:
        record['finished_at'] = dt.datetime.now(dt.timezone.utc).isoformat()
        save()
    print('Landmark 2 verified. Full Theorem 1.8 remains unproved.', flush=True)

if __name__ == '__main__':
    main()
