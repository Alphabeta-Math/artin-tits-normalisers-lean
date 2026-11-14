#!/usr/bin/env python3
"""Prepare, or explicitly publish after root approval, the mutable current ledger.

Historical cohorts and graph/publication records remain intact. This tool does
not build Lean, accept mathematics, or infer CI success. Root acceptance and a
passing final local battery must already exist. Default prints a plan only.
"""
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path
BASE=Path(__file__).resolve().parents[3]
OUT=BASE/'docs/provenance'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def require(b,m):
    if not b:raise RuntimeError(m)
def ref(p):
    p=Path(p).resolve();return {'path':str(p.relative_to(BASE)),'sha256':sha(p)}
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--execute',action='store_true')
    p.add_argument('--run',type=Path,required=True)
    p.add_argument('--validation',type=Path,required=True)
    p.add_argument('--root-acceptance',type=Path,required=True)
    p.add_argument('--technical-record',type=Path,required=True)
    p.add_argument('--publication-binding',type=Path)
    p.add_argument('--publication-validation',type=Path)
    a=p.parse_args()
    e=read(a.run/'execution.json');v=read(a.validation);r=read(a.root_acceptance);t=read(a.technical_record)
    reuse=read(OUT/'deligne/reuse-inventory.json')
    require(e['ok'] and v['ok'] and t['ok'] and t['inputs_unchanged'],'Incomplete graph/metadata/local battery')
    require(len(t['exact_replays'])==64,'Expected actual local exact replay of 36 project +28 new supplier units')
    require(r['full_theorem_1_8_proved'] is True,'Requires explicit root acceptance of full Theorem1.8')
    require((BASE/'THEOREM18.md').is_file(),'Current THEOREM18.md entrypoint must exist')
    for path,h in r['independent_reviews_sha256'].items():require(sha(BASE/path)==h,'Final review changed')
    require(v['run_execution_sha256']==sha(a.run/'execution.json'),'Validation is for another graph')
    ledger=read(OUT/'GITHUB-PROOF-SOURCES.json')
    old=reuse['accepted_cohorts'][:8]
    require(ledger['accepted_cohorts'][:8]==old,'Old accepted cohort records changed')
    require(len(ledger['accepted_cohorts']) in [8,10],'Unexpected current cohort frontier')
    if len(ledger['accepted_cohorts'])==10:
        require(ledger['accepted_cohorts']==reuse['accepted_cohorts'],'Already-promoted cohorts differ')
    else:require(sha(OUT/'GITHUB-PROOF-SOURCES.json')==reuse['central_ledger_before_promotion']['sha256'],
                 'Current ledger changed since consolidation; reconcile before publication')
    current={'root_acceptance':ref(a.root_acceptance),'technical_verification':ref(a.technical_record),
      'source_inventory':ref(BASE/'deligne/source-inventory.json'),'dependency_export':ref(a.run/'execution.json'),
      'dependency_validation':ref(a.validation),'supplier_reuse_inventory':ref(OUT/'deligne/reuse-inventory.json'),
      'entrypoint':'THEOREM18.md','full_theorem_1_8_proved':True,
      'scope':'The exact full actual-space Theorem1.8 statements bound by the root receipt, both final reviews and actual local battery.',
      'clean_github_CI':'No new success inferred; root-owned final CI closeout remains separate.'}
    if a.publication_binding:
        require(a.publication_validation is not None,'Provide actual publication validation')
        b=read(a.publication_binding);bv=read(a.publication_validation)
        require(b['ok'] and bv['ok'],'Publication binding/validation failed')
        current['source_publication']={'binding':ref(a.publication_binding),'validation':ref(a.publication_validation),
            'commit':b['commit'],'exact_repository_source_bindings':b['exact_source_binding_count']}
    else:current['source_publication']={'status':'pending exact science commit; no Git blob binding fabricated'}
    ledger['accepted_cohorts']=reuse['accepted_cohorts']
    ledger['accepted_scientific_repositories']=sorted({c['repository'] for c in ledger['accepted_cohorts']})
    ledger['accepted_scientific_repository_count']=3
    ledger['accepted_vendor_unit_count']=464
    manifest_path='deligne/lake-manifest.json'
    manifest=read(BASE/manifest_path)
    if not any(m['path']==manifest_path for m in ledger['manifest_records']):
        ledger['manifest_records'].append(ref(BASE/manifest_path))
    for package in manifest['packages']:
        if package['type']!='git':continue
        matching=[d for d in ledger['lake_git_dependencies'] if d['lake_package']==package['name'] and d['revision']==package['rev']]
        require(len(matching)==1,'New/changed foundation dependency requires explicit attribution')
        if manifest_path not in matching[0]['manifests']:matching[0]['manifests'].append(manifest_path)
    milestone={'milestone':'full-Theorem1.8','mathematical_acceptance':True,
        'full_theorem_1_8_proved':True,'root_acceptance':ref(a.root_acceptance),
        'technical_verification':ref(a.technical_record),
        'independent_reviews_sha256':r['independent_reviews_sha256'],
        'scope':current['scope'],'clean_github_ci_status':'separate root-owned closeout; no new result inferred'}
    previous=[m for m in ledger['accepted_local_milestones'] if m.get('milestone')=='full-Theorem1.8']
    if previous:require(previous==[milestone],'Existing full-Theorem1.8 acceptance entry differs')
    else:ledger['accepted_local_milestones'].append(milestone)
    if a.publication_binding:
        pub={**current['source_publication'],'milestone_project_source_files':36,
            'observation_policy':'Append-only actual Git blob binding; original source observation and all older records remain immutable.'}
        previous=[p for p in ledger['source_publication_bindings'] if p.get('commit')==pub['commit']]
        if previous:require(previous==[pub],'Existing source publication differs')
        else:ledger['source_publication_bindings'].append(pub)
    ledger['current_full_theorem_1_8']=current
    ledger['compiled_deligne_dependency_graph']={'execution':ref(a.run/'execution.json'),
        'validation':ref(a.validation),'graph':e['annotated_graph'],'counts':e['counts'],
        'historical_roots_and_dependency_edges_preserved':True,'all_physical_project_occurrences_retained':True}
    ledger['generation_script']=ref(Path(__file__))
    ledger['maintenance']='Current full-Theorem1.8 registry is maintained by docs/provenance/deligne/promote_ledger.py after explicit root approval. Earlier refresh_ledger.py remains historical and must not overwrite this current frontier. Historical proof/provenance/review/graph/publication records are immutable.'
    md=(OUT/'GITHUB-PROOF-SOURCES.md').read_text()
    md=md.replace('**3 repositories, 436 vendored modules**','**3 repositories, 464 vendored modules**',1)
    marker='| homotopy-colib-domination-supplier |'
    if '| deligne-weights-supplier |' not in md:
        rows=[]
        for c in reuse['accepted_cohorts'][8:]:
            repo=c['repository'].removeprefix('https://github.com/')
            rows.append(f"| {c['id']} | [{repo}]({c['repository']}/tree/{c['revision']}) `{c['revision']}` | {c['module_count']} | [root acceptance](../../{c['root_acceptance']['path']}); [exact original/local/patch/license/application inventory](deligne/reuse-inventory.json) |")
        lines=md.splitlines();i=next(i for i,line in enumerate(lines) if line.startswith(marker))
        lines[i+1:i+1]=rows;md='\n'.join(lines)+'\n'
    begin='<!-- CURRENT-FULL-THEOREM18:BEGIN -->';end='<!-- CURRENT-FULL-THEOREM18:END -->'
    section=f'''{begin}
## Current full Theorem 1.8

[THEOREM18.md](../../THEOREM18.md) is the current entrypoint. The [root acceptance](../../{ref(a.root_acceptance)['path']}), final independent reviews and [actual local battery](../../{ref(a.technical_record)['path']}) bind the full actual-space result. The [combined graph](../../{e['annotated_graph']['path']}) records {e['counts']['project_roots']} project roots, {e['counts']['reachable_declarations']} reachable declarations and {e['counts']['references']} references, with every prior root/edge and physical project occurrence preserved. [Metadata validation](../../{ref(a.validation)['path']}) adds no mathematics.

The [exact supplier inventory](deligne/reuse-inventory.json) retains the prior 436 accepted units and adds 12 OAI weight modules plus 16 Colib carrier modules: 464 units from the same three scientific repositories. Three previously accepted Colib closure modules are reused without recounting. [Actual compiled supplier use](../../{e['supplier_use']['path']}) distinguishes term dependencies from selected modules with no reachable declaration. Original pins, sources, ports, licenses, upstream metadata and real application evidence are retained. Mathlib and Lean remain separately pinned foundations. Historical sections below describe their own earlier frontiers; their pending/unproved statements are not the current status.

Source publication: {('exact Git source binding at `'+current['source_publication']['commit']+'`' if a.publication_binding else 'pending the exact science commit; no source-commit binding is fabricated')}. Final clean CI is a separate root-owned record; this registry makes no new CI-success claim.
{end}
'''
    if begin in md:md=re.sub(re.escape(begin)+'.*?'+re.escape(end),section.strip(),md,flags=re.S)
    else:
        first=md.index('\n\n')
        md=md[:first+2]+section+'\n'+md[first+2:]
    if not a.execute:
        print(json.dumps({'execute':False,'ready':True,'supplier_units':464,'project_roots':e['counts']['project_roots'],
                          'central_files_unchanged':True,'requires_explicit_root_go_before_execute':True}));return
    (OUT/'GITHUB-PROOF-SOURCES.json').write_text(json.dumps(ledger,indent=2,sort_keys=True)+'\n')
    (OUT/'GITHUB-PROOF-SOURCES.md').write_text(md)
    print(json.dumps({'ok':True,'supplier_units':464,'full_theorem_1_8_proved':True,'publication_bound':bool(a.publication_binding)}))
if __name__=='__main__':main()
