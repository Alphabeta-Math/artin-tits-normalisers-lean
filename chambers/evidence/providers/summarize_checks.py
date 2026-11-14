#!/usr/bin/env python3
"""Validate and combine the retained actual provider run records."""
import pathlib,json,hashlib,re,datetime
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/providers';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();p=json.loads((R/'vendor/provenance.json').read_text());modules=p['topological_order'];records={}
for phase in ['build','audit','replay']:
 path=sorted(E.glob(phase+'-*/verification.json'))[-1];rec=json.loads(path.read_text());assert rec['ok'] and rec['inputs_unchanged'];assert rec['modules']==modules
 for c in rec['commands']:
  assert c['exit_code']==0 and H(path.parent/c['log'])==c['log_sha256']
 records[phase]={'record':str(path.relative_to(R)),'sha256':H(path),'data':rec}
assert records['build']['data']['commands'][0]['command']==['lake','build',*modules]
rep=records['replay'];assert len(rep['data']['commands'])==9
for m,c in zip(modules,rep['data']['commands']):
 assert c['command']==['lake','env','leanchecker','--verbose',m]
 log=(R/rep['record']).parent/c['log'];assert log.read_text().splitlines()[0]=='replaying '+m
ar=records['audit'];text=((R/ar['record']).parent/ar['data']['commands'][0]['log']).read_text();parse=lambda pre:[json.loads(l.split(pre,1)[1]) for l in text.splitlines() if pre in l]
decls=parse('CHAMBER_PROVIDER_DECL_JSON ');rows=parse('CHAMBER_PROVIDER_PHYSICAL_MODULE_JSON ');summary=parse('CHAMBER_PROVIDER_PHYSICAL_SUMMARY_JSON ');dups=parse('CHAMBER_PROVIDER_PHYSICAL_DUPLICATE_JSON ')
assert len(rows)==9 and {x['module'] for x in rows}==set(modules);assert len({x['name'] for x in decls})==len(decls)==232;names={n for row in rows for n in row['names']};assert names=={x['name'] for x in decls};assert sum(x['declarations'] for x in rows)==232 and not dups
for d in decls:assert set(d['axioms'])<={'propext','Classical.choice','Quot.sound'}
assert summary==[{'all_physical_type_value_universe_parameters_identical':True,'canonical_axioms_checked':True,'canonical_declarations':232,'distinct_physical_names':232,'identical_theorem_duplicates':0,'modules':9,'physical_occurrences':232}]
for f in p['files']:
 assert H(R/'vendor'/f['path'])==f['active_sha256'];assert H(R/'vendor'/f['original_path'])==f['upstream_sha256'];assert H(R/'vendor'/f['patch_path'])==f['patch_sha256']
 # Removing import lines must recover identical declaration text byte for byte.
 strip=lambda s:re.sub(rb'^\s*(?:public\s+)?import[^\n]*\n',b'',s,flags=re.M)
 assert strip((R/'vendor'/f['path']).read_bytes())==strip((R/'vendor'/f['original_path']).read_bytes())
for f in p['reused_unchanged_parent_modules']:assert H(R/f['path'])==f['sha256']
before=json.loads(((R/ar['record']).parent/'inputs-before.json').read_text());after=json.loads(((R/rep['record']).parent/'inputs-after.json').read_text());assert before==after
coverage={'declarations':decls,'physical_modules':rows,'duplicates':dups,'summary':summary[0]};(E/'coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
record={'ok':True,'created_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'repository':p['repository'],'upstream_sha':p['upstream_sha'],'provenance':'vendor/provenance.json','provenance_sha256':H(R/'vendor/provenance.json'),'harness':'ProviderAudit.lean','harness_sha256':H(R/'ProviderAudit.lean'),'module_count':9,'canonical_declarations':232,'physical_occurrences':232,'identical_duplicates':0,'axioms_allowed':['propext','Classical.choice','Quot.sound'],'audit_through_replay_inputs_identical':True,'kernel_replay_workers':1,'replay_mode':'one exact module per official leanchecker process, sequential','kernel_replay_relative_to_imports':True,'independent_kernel_implementation':False,'independent_statement_reviews_pending':True,'full_landmark_3_proved':False,'full_theorem_1_8_proved':False,'coverage_file':'evidence/providers/coverage.json','coverage_sha256':H(E/'coverage.json'),'environment_file':'evidence/providers/environment.json','environment_sha256':H(E/'environment.json'),'records':{k:{x:y for x,y in v.items() if x!='data'} for k,v in records.items()},'replay_duration_seconds':sum(x['duration_seconds'] for x in rep['data']['commands']),'source_ports':'Mechanical import relocation only; no declaration/hypothesis/proof-body change.'}
(E/'verification.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
