#!/usr/bin/env python3
"""Download and validate a successful landmark-2 GitHub Actions evidence archive."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile

BASE = Path(__file__).resolve().parents[4]
REPO = 'lazyinspirit/artin-tits-normalisers-lean'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def require(test, message):
    if not test:
        raise RuntimeError(message)

def gh(*args):
    return subprocess.check_output(['gh', *args], cwd=BASE)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('run_id', type=int)
    args = parser.parse_args()
    output = BASE / 'docs/theorem18/landmarks/github-evidence' / ('run-' + str(args.run_id))
    output.mkdir(parents=True, exist_ok=False)
    def metadata(name, endpoint):
        raw = gh('api', endpoint)
        (output / name).write_bytes(raw)
        return json.loads(raw)
    run = metadata('run.json', f'/repos/{REPO}/actions/runs/{args.run_id}')
    require(run['status'] == 'completed' and run['conclusion'] == 'success', 'CI is not successful and complete')
    require(run['path'] == '.github/workflows/ribbons.yml', 'Unexpected workflow')
    jobs = metadata('jobs.json', f'/repos/{REPO}/actions/runs/{args.run_id}/jobs')
    require(jobs['total_count'] == 1 and all(j['conclusion'] == 'success' for j in jobs['jobs']), 'Unexpected job status')
    artifacts = metadata('artifacts.json', f'/repos/{REPO}/actions/runs/{args.run_id}/artifacts')
    selected = [a for a in artifacts['artifacts'] if a['name'] == 'lean-landmark2-verification']
    require(len(selected) == 1 and not selected[0]['expired'], 'Missing/ambiguous/expired evidence artifact')
    artifact = selected[0]
    zip_path = output / 'landmark2-verification.zip'
    with zip_path.open('wb') as stream:
        subprocess.run(['gh', 'api', f'/repos/{REPO}/actions/artifacts/{artifact["id"]}/zip'],
                       cwd=BASE, stdout=stream, check=True)
    zip_sha = sha(zip_path.read_bytes())
    require(artifact['digest'] == 'sha256:' + zip_sha, 'ZIP does not match GitHub artifact digest')
    log = gh('run', 'view', str(args.run_id), '--log')
    with gzip.GzipFile(filename=str(output / 'actions.log.gz'), mode='wb', mtime=0) as stream:
        stream.write(log)
    checked_logs = []
    with zipfile.ZipFile(zip_path) as archive:
        def data(path):
            return archive.read(path)
        def record(path):
            return json.loads(data(path))
        def logs(prefix, commands, path_key='log', hash_key='log_sha256'):
            for command in commands:
                require(command['exit_code'] == 0, 'Archived command failed')
                p = prefix + command[path_key]
                require(sha(data(p)) == command[hash_key], 'Changed archived command log: ' + p)
                checked_logs.append(p)
        result = record('verification.json')
        require(result['ok'] is True and result['landmark_2_proved'] is True and
                result['full_theorem_1_8_proved'] is False, 'Wrong result/scope')
        require(result['repository_head'] == run['head_sha'] and result['fresh_provider_replay'] is True,
                'Wrong source commit or no fresh provider replay')
        for path, expected in result['input_sha256'].items():
            require(sha((BASE / path).read_bytes()) == expected, 'Current source differs from successful CI: ' + path)
        for review in result['independent_reviews']:
            p = BASE / 'ribbons/reviews' / ('landmark2-' + review['reviewer'] + '.json')
            require(sha(p.read_bytes()) == review['json_sha256'] and
                    sha(p.with_suffix('.md').read_bytes()) == review['markdown_sha256'], 'Review receipt changed')
        require(len(result['parent_verified_input_sha256']) == 65, 'Wrong parent context coverage')
        logs('', result['commands'])
        project = record('project/verification.json')
        require(sha(data('project/verification.json')) == result['project_verification_sha256'] and
                project['ok'] is True and project['inputs_unchanged'] is True, 'Project certificate mismatch')
        inv = json.loads((BASE / 'ribbons/source-inventory.json').read_text())
        modules = set(inv['compiled_declaration_occurrences_by_module'])
        replays = project['exact_replays']
        require(len(replays) == 24 and {r['module'] for r in replays} == modules and all(r['ok'] for r in replays),
                'Project replay coverage mismatch')
        require(project['audited_declaration_count'] == 999 and
                project['compiled_declaration_occurrence_count'] == 1000, 'Project declaration counts differ')
        require(project['compiled_duplicate_equivalences'] == inv['compiled_duplicate_equivalences'],
                'Generated duplicate coverage differs')
        require(sha(data('project/inputs.json')) == project['inputs_sha256'], 'Project input manifest changed')
        logs('project/', project['commands'])
        providers = record('providers/verification.json')
        require(sha(data('providers/verification.json')) == result['provider_replay']['verification_sha256'] and
                providers['ok'] is True and providers['inputs_unchanged'] is True, 'Provider certificate mismatch')
        require(sha(data('providers/inputs.json')) == providers['source_inputs_sha256'], 'Provider input manifest changed')
        provenance = json.loads((BASE / 'ribbons/vendor/provenance.json').read_text())
        provider_modules = {m['module'] for m in provenance['modules']}
        require(len(providers['commands']) == 359 and {c['module'] for c in providers['commands']} == provider_modules,
                'Provider replay coverage mismatch')
        logs('providers/', providers['commands'], 'raw_log', 'raw_log_sha256')
        for c in providers['commands']:
            require(data('providers/' + c['raw_log']).decode().splitlines()[0] == 'replaying ' + c['module'],
                    'Provider replay header mismatch')
        require(result['provider_axiom_module_count'] == 359 and result['provider_axiom_declaration_count'] == 6133,
                'Provider axiom coverage mismatch')
        (output / 'verification.json').write_bytes(data('verification.json'))
        report = {'ok': True, 'run_id': args.run_id, 'run_url': run['html_url'], 'source_commit': run['head_sha'],
                  'landmark_2_proved': True, 'full_theorem_1_8_proved': False,
                  'artifact_sha256': zip_sha, 'github_artifact_digest_matches': True,
                  'current_source_input_count': len(result['input_sha256']), 'parent_input_count': 65,
                  'independent_review_count': len(result['independent_reviews']),
                  'project_unique_declarations': 999, 'project_physical_occurrences': 1000,
                  'project_exact_replays': 24, 'provider_modules': 359, 'provider_unique_declarations': 6133,
                  'provider_exact_replays': 359, 'checked_raw_log_count': len(checked_logs),
                  'limitations': ['Compiled CI artifact hashes remain recorded, not rechecked against local compiled binaries.',
                      'Bundled Lean kernel relative to imported environments; not a second kernel or fresh full-mathlib replay.']}
        (output / 'archive-verification.json').write_text(json.dumps(report, indent=2) + '\n')
    (output / 'README.md').write_text(
        '# Landmark 2: successful fresh CI and permanent proof records\n\n'
        'Actual reduced ribbon normalizer quotient, semidirect splitting and complete chosen-lcm positive/signed '
        'groupoid presentation. **Full Theorem 1.8 remains unproved.**\n\n'
        f'- Run: <{run["html_url"]}>\n- Source commit: `{run["head_sha"]}`.\n'
        '- All 24 new exact-module replays and 359 fresh provider replays passed.\n'
        '- Axiom audit covers 999 unique project declarations (1,000 physical occurrences with one checked '
        'identical generated theorem duplicate), and 6,133 provider declarations.\n'
        '- Both independent review receipts, current proof inputs, 65 unchanged parent inputs and all '
        'archived command-log hashes were checked. The ZIP digest matches GitHub metadata.\n\n'
        'The original ZIP and complete compressed Actions log are retained with run/job/artifact metadata. '
        'The direct verification JSON is included for reading. The archive does not copy every compiled '
        'binary or freshly replay mathlib; actual CI artifact hashes and their unchanged checks are recorded. '
        'No geometric comparison, asphericity or literal full standard-path classification is claimed.\n')
    sums = ''.join(sha(p.read_bytes()) + '  ' + p.name + '\n' for p in sorted(output.iterdir())
                   if p.name != 'SHA256SUMS')
    (output / 'SHA256SUMS').write_text(sums)
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
