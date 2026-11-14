#!/usr/bin/env python3
"""Source-bound full Theorem 1.8 verification. Default is read-only planning.

--write-audit refreshes the explicit full new-module observer before freeze.
--observe --output DIR builds and audits once to prepare physical inventory;
 it does not replay kernels or assert mathematical acceptance.
--write-inventory --coverage DIR/coverage.json freezes common review bindings.
--execute --mode final requires both final receipts; it cleans only artin-deligne,
 builds every new module, audits every physical declaration, then runs one fresh
 exact-module bundled-kernel replay process per science/provider module.
"""
from __future__ import annotations
import argparse,ast,datetime as dt,json,os,re,subprocess,sys,time
from pathlib import Path
from audit_support import require,read,sha,aggregate,write,utc,validate_project_audit,audit_text,aggregate_import_closure

ROOT=Path(__file__).resolve().parents[1];BASE=ROOT.parent
ALLOW={'propext','Classical.choice','Quot.sound'}
BASELINE_ARCHIVE='docs/theorem18/landmarks/github-evidence/run-43590812660/archive-verification.json'
BASELINE_ARCHIVE_SHA256='8b1a28b845c65d2006a1252149ade2ed453f485270c88b521950b89e04139f9a'
BASELINE_VERIFICATION='docs/theorem18/landmarks/github-evidence/run-43590812660/verification.json'
BASELINE_VERIFICATION_SHA256='b2e5ed0715a52ff165bd3f5ee51f1299c4d4a3914e1bbf9ffd86d4ce7a3c4f9b'
CLAIMS={'full_landmark_5_proved':True,'actual_arrangement_asphericity_proved':True,
 'full_theorem_1_8_proved':True,'two_sided_nerve_homotopy_equivalence_proved':False,
 'actual_universal_cover_contractible_proved':False}
CRITICAL=['ArtinNormalisers.Deligne5.'+x for x in [
 'actualUniversalCoverComparisonHomotopy','actualUniversalCover_isAspherical',
 'actualComplement_isAspherical','actualOrbit_isAspherical','actualComplement_isKpi1',
 'actualOrbit_isKpi1_at_projection','corollary_6_14','theorem_1_8','theorem_1_8_all_basepoints']]
REVIEW_KEYS=['project_source_sha256','configuration_sha256','vendor_provenance_sha256',
 'provider_active_source_sha256','provider_original_source_sha256','provider_import_patch_sha256',
 'provider_assembly_sha256','provider_license_sha256','provider_audit_sha256',
 'provider_verification_source_sha256','provider_statement_reviews_sha256','provider_reused_source_sha256',
 'provider_evidence_sha256','provider_upstream_metadata_sha256','provider_cohort_bindings_sha256',
 'provider_acceptance_sha256','provider_source_inspection_sha256','provider_application_inspection_sha256',
 'provider_application_source_sha256','accepted_context_input_sha256',
 'accepted_context_input_aggregate_sha256','accepted_context_verification_sha256',
 'historical_reviews_sha256','verification_source_sha256']
COVERAGE_KEYS=['audited_declarations_by_module','compiled_declaration_occurrences_by_module',
 'compiled_duplicate_equivalences','external_canonical_declarations']

def rel(p):return str(Path(p).resolve().relative_to(BASE.resolve()))
def mapping(paths):return {rel(p):sha(p) for p in sorted(paths)}
def sources():return mapping([ROOT/'ArtinDeligne.lean',*sorted(ROOT.glob('ArtinDeligne/**/*.lean'))])
def modules():return ['ArtinDeligne']+[str(p.relative_to(ROOT)).removesuffix('.lean').replace('/','.') for p in sorted(ROOT.glob('ArtinDeligne/**/*.lean'))]
def configs():return mapping([ROOT/n for n in ['lakefile.toml','lean-toolchain','lake-manifest.json']])
def checked(mapping_,label):
 for p,h in mapping_.items():require((BASE/p).is_file() and sha(BASE/p)==h,label+': '+p)

def accepted_context():
 require(sha(BASE/BASELINE_ARCHIVE)==BASELINE_ARCHIVE_SHA256,'Changed accepted1264 archive')
 require(sha(BASE/BASELINE_VERIFICATION)==BASELINE_VERIFICATION_SHA256,'Changed accepted1264 final record')
 a=read(BASE/BASELINE_ARCHIVE);v=read(BASE/BASELINE_VERIFICATION)
 require(a['ok'] is True and v['ok'] is True and v['mode']=='final','Accepted context unsuccessful')
 require(a['source_commit']==v['repository_head']=='9dacc8befce702eed601430c776da385cab07343','Wrong accepted source commit')
 require(a['accepted_homotopy_prerequisites'] is True and not a['clean_skipped'],'Wrong accepted scope/clean')
 c=a['checked_source_sha256'];require(len(c)==a['current_source_input_count']==1264,'Wrong accepted input count');checked(c,'Changed accepted input')
 reviews={}
 for k in ['historical_reviews_sha256','provider_statement_reviews_sha256','project_statement_reviews_sha256']:
  for p,h in v[k].items():require(p not in reviews or reviews[p]==h,'Conflicting accepted review');reviews[p]=h
 checked(reviews,'Changed accepted review')
 return c,{BASELINE_ARCHIVE:BASELINE_ARCHIVE_SHA256,BASELINE_VERIFICATION:BASELINE_VERIFICATION_SHA256},reviews

def cohort_bindings():
 result={k:{} for k in REVIEW_KEYS if k.startswith('provider_') or k=='vendor_provenance_sha256'}
 providers=[];physical={};cohorts={}
 for label,count in [('weights',12),('carriers',16)]:
  pp=ROOT/f'vendor/provenance-{label}.json';p=read(pp);providers+=p['topological_order']
  require(len(p['files'])==len(p['topological_order'])==count and {f['module'] for f in p['files']}==set(p['topological_order']),'Wrong cohort modules: '+label)
  bp=ROOT/f'evidence/providers/{label}/review-bindings.json';b=read(bp)
  ap=BASE/f'docs/provenance/acceptance-deligne-{label}.json';acceptance=read(ap)
  require(acceptance['accepted'] is True and acceptance['modules']==count,'Root supplier acceptance absent')
  require(acceptance['review_bindings_sha256']==sha(bp),'Changed root-reviewed binding file')
  require(all(acceptance[k] is False for k in CLAIMS),'Supplier acceptance overstates scope')
  normative=list(acceptance['provider_bindings']);require(len(normative)==18,'Wrong supplier review schema')
  require(acceptance['provider_bindings']=={k:b[k] for k in normative},'Root supplier bindings differ')
  for k in normative:
   val=b[k]
   if isinstance(val,dict):checked(val,'Changed supplier '+label+':'+k)
  require(b['configuration_sha256']==configs(),'Changed supplier-reviewed config')
  require(b['vendor_provenance_sha256']==sha(pp),'Changed supplier provenance')
  expected_active=mapping([ROOT/'vendor'/f['path'] for f in p['files']])
  expected_original=mapping([ROOT/'vendor'/f['original_path'] for f in p['files']])
  expected_patches=mapping([ROOT/'vendor'/f['patch_path'] for f in p['files']])
  require(b['provider_source_sha256']==expected_active and b['provider_original_source_sha256']==expected_original and b['provider_import_patch_sha256']==expected_patches,'Supplier source coverage differs')
  require(sha(ROOT/f'evidence/providers/{label}/source-inspection.json')==b['source_inspection_sha256'],'Source inspection changed')
  require(sha(ROOT/f'evidence/providers/{label}/applications.json')==b['application_inspection_sha256'],'Application inspection changed')
  scalar_paths={'provider_audit_sha256':ROOT/('WeightsProviderAudit.lean' if label=='weights' else 'CarrierProviderAudit.lean')}
  for k,path in scalar_paths.items():require(sha(path)==b[k],'Changed supplier observer')
  refs={};scope_observations={}
  for who in ['a','b']:
   rp=ROOT/f'reviews/{label}-providers-{who}.json';r=read(rp)
   require(r['verdict']=='accept-supplier-cohort' and r['model']=='gpt-6.1-sol' and r['reasoning_effort']=='high','Supplier reviewer not accepted')
   require(r.get('review_bindings_sha256',r.get('review_input_binding_sha256'))==sha(bp),'Stale supplier review binding')
   require(all(r[k]==b[k] for k in normative),'Stale supplier review fields')
   require(all(r[k] is False for k in CLAIMS if k!='actual_universal_cover_contractible_proved'),'Supplier reviewer overstates scope')
   contract_keys=[k for k in ['actual_universal_cover_contractible_proved','actual_universal_cover_contraction_proved','full_actual_universal_cover_contraction_proved'] if k in r]
   if contract_keys:
    require(all(r[k] is False for k in contract_keys),'Supplier reviewer claims universal-cover contraction')
    scope_observations[who]={'observed_receipt_keys':contract_keys,'all_values_false':True,'source':'explicit historical supplier receipt fields'}
   else:
    require(who=='a' and r['actual_acyclic_carrier_theorem_proved'] is False and acceptance['actual_universal_cover_contractible_proved'] is False,'Missing explicit supplier-scope limit')
    scope_observations[who]={'observed_receipt_keys':[],'receipt_specific_contractibility_key_absent':True,'source':'root supplier acceptance canonical false; historical A did not examine a specific universal-cover contractibility claim'}
   refs.update(mapping([rp,rp.with_suffix('.md')]))
  require(acceptance['independent_reviews_sha256']==refs,'Root supplier review refs differ')
  for k,oldkey in [('provider_active_source_sha256','provider_source_sha256'),('provider_original_source_sha256','provider_original_source_sha256'),('provider_import_patch_sha256','provider_import_patch_sha256'),('provider_assembly_sha256','provider_assembly_sha256'),('provider_license_sha256','provider_license_sha256'),('provider_verification_source_sha256','verification_scripts_sha256'),('provider_reused_source_sha256','provider_reused_source_sha256'),('provider_upstream_metadata_sha256','provider_upstream_metadata_sha256'),('provider_application_source_sha256','application_source_sha256')]:
   for path,h in b[oldkey].items():require(path not in result[k] or result[k][path]==h,'Conflicting supplier binding');result[k][path]=h
  result['vendor_provenance_sha256'].update(mapping([pp]));result['provider_audit_sha256'].update(mapping(list(scalar_paths.values())))
  result['provider_cohort_bindings_sha256'].update(mapping([bp]));result['provider_acceptance_sha256'].update(mapping([ap]));result['provider_statement_reviews_sha256'].update(refs)
  result['provider_source_inspection_sha256'].update(mapping([ROOT/f'evidence/providers/{label}/source-inspection.json']))
  result['provider_application_inspection_sha256'].update(mapping([ROOT/f'evidence/providers/{label}/applications.json']))
  result['provider_evidence_sha256'].update(b['evidence_sha256'])
  technical=BASE/acceptance['technical_summary_file'];require(sha(technical)==acceptance['technical_summary_sha256'],'Changed accepted supplier technical summary')
  result['provider_evidence_sha256'].update(mapping([technical]))
  if label=='weights':
   coverage=read(ROOT/'evidence/providers/weights/coverage.json');physical.update({r['module']:sorted(r['names']) for r in coverage['physical_modules']})
  else:
   technical_data=read(technical);record=ROOT/technical_data['successful_records']['audit']['path'];d=read(record)
   log=(record.parent/d['commands'][1]['log']).read_text()
   for line in log.splitlines():
    if line.startswith('CARRIER_PROVIDER_PHYSICAL_MODULE_JSON '):
     row=json.loads(line.split(' ',1)[1]);physical[row['module']]=sorted(row['names'])
  p['historical_review_scope_normalization']=scope_observations
  cohorts[label]=p
 require(len(providers)==len(set(providers))==28,'New provider sets overlap')
 require(set(result['provider_active_source_sha256'])==set(mapping(ROOT.glob('vendor/ArtinDeligneVendor/**/*.lean'))),'Extra/missing provider source')
 require(set(physical)==set(providers),'Missing reviewed supplier physical modules')
 return result,providers,physical,cohorts

def known_modules(context):
 out=set()
 prefixes=['homotopy/vendor/','homotopy/','asphericity/vendor/','asphericity/','sequences/vendor/','sequences/','chambers/vendor/','chambers/','ribbons/vendor/','ribbons/','landmarks/vendor/','landmarks/','vendor/','']
 for p in context:
  if not p.endswith('.lean'):continue
  for prefix in prefixes:
   if p.startswith(prefix):
    module=p[len(prefix):].removesuffix('.lean').replace('/','.')
    if module.startswith(('Artin','TauCeti.','OAI.')) and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*",module):out.add(module)
    break
 return sorted(out)

def bindings():
 c,records,history=accepted_context();p,pm,physical,cohorts=cohort_bindings()
 tooling=[*ROOT.glob('scripts/*.py'),ROOT/'ProjectAudit.lean',ROOT/'StatementAudit.lean',BASE/'.github/workflows/deligne.yml']
 archive=BASE/'docs/theorem18/landmarks/scripts/archive_deligne_ci.py'
 if archive.exists():tooling.append(archive)
 b={**p,'project_source_sha256':sources(),'configuration_sha256':configs(),'accepted_context_input_sha256':c,'accepted_context_input_aggregate_sha256':aggregate(c),'accepted_context_verification_sha256':records,'historical_reviews_sha256':history,'verification_source_sha256':mapping(tooling)}
 require(set(b)==set(REVIEW_KEYS),'Internal review schema differs')
 return b,pm,physical,known_modules(c),cohorts

def final_reviews(inv,b):
 require(all(inv[k]==b[k] for k in REVIEW_KEYS),'Stale frozen source inventory')
 require(inv['scope_claims']==CLAIMS and inv['critical_declarations']==CRITICAL,'Inventory scope/endpoints differ')
 require(inv['coverage_observed'] is True,'Inventory declaration coverage pending')
 refs={}
 for who in ['a','b']:
  path=ROOT/f'reviews/theorem18-{who}.json';r=read(path)
  require(r['verdict']=='accept-theorem-1-8' and r['model']=='gpt-6.1-sol' and r['reasoning_effort']=='high','Final mathematical review not accepted')
  require(r['source_inventory_sha256']==sha(ROOT/'source-inventory.json'),'Stale final inventory review')
  require(all(r[k]==b[k] for k in REVIEW_KEYS),'Stale final reviewer binding')
  require(all(r[k] is value for k,value in CLAIMS.items()),'Final review claim scope differs')
  require(r['critical_declarations']==CRITICAL,'Final review endpoint set differs')
  for key in [*COVERAGE_KEYS,'coverage_record_sha256','technical_verification_sha256']:require(r[key]==inv[key],'Final review declaration/evidence coverage differs')
  refs.update(mapping([path,path.with_suffix('.md')]))
 return refs

def exact_replay_source():
    # Reuse the already accepted exact-module implementation of the pinned official
    # checker algorithm; extract its literal without executing the old Python script.
    tree = ast.parse((BASE / "ribbons/scripts/verify_project.py").read_text())
    return next(
        ast.literal_eval(n.value)
        for n in tree.body
        if isinstance(n, ast.Assign)
        and any(isinstance(t, ast.Name) and t.id == "EXACT_REPLAY" for t in n.targets)
    )

def provider_reproduction_commands():return [('weights-extraction',['python3','scripts/providers/weights/assemble.py','--check']),('carriers-extraction',['python3','scripts/providers/carriers/verify_source.py'])]

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--plan',action='store_true');parser.add_argument('--write-audit',action='store_true');parser.add_argument('--write-inventory',action='store_true');parser.add_argument('--coverage',type=Path);parser.add_argument('--observe',action='store_true');parser.add_argument('--execute',action='store_true');parser.add_argument('--mode',choices=['technical','final'],default='technical');parser.add_argument('--skip-clean',action='store_true');parser.add_argument('--output',type=Path)
 args=parser.parse_args();require(sum([args.plan,args.write_audit,args.write_inventory,args.observe,args.execute])<=1,'Choose one operation');require(not args.skip_clean or args.mode=='technical','Final cannot skip clean')
 b,provider,reviewedphysical,known,cohorts=bindings();science=modules();allmodules=science+provider
 expected=audit_text(allmodules,known)
 if args.write_audit:(ROOT/'ProjectAudit.lean').write_text(expected);print('Wrote exact audit imports: '+str(len(allmodules)));return 0
 closure=aggregate_import_closure(science)
 plan={'kind':'theorem18-verification-plan','project_modules':science,'new_provider_modules':provider,'explicit_build_targets':allmodules,'aggregate_import_closure':closure,'aggregate_imports_all_project_modules':set(closure)==set(science),'expected_audit_is_current':(ROOT/'ProjectAudit.lean').read_text()==expected,'accepted_context_input_count':1264,'accepted_context_input_aggregate_sha256':b['accepted_context_input_aggregate_sha256'],'kernel_replay_scope':'Fresh Lean process executing the accepted official replayFromImports kernel algorithm for one exact new module, relative to pinned imported Mathlib and accepted436suppliers; not the prefix-matching leanchecker CLI, independent kernel or old supplier replay.','requested_scope_claims':CLAIMS,'final_review_keys':REVIEW_KEYS,'supplier_review_scope_normalization':{k:v['historical_review_scope_normalization'] for k,v in cohorts.items()}}
 if args.write_inventory:
  require(args.coverage is not None,'Provide actual coverage observation');coverage=read(args.coverage)
  require(coverage['source_bindings']==b,'Coverage source bindings stale');require(coverage['all_new_modules']==allmodules,'Coverage module set stale')
  observation=args.coverage.parent/'verification.json';observed=read(observation)
  require(observed['ok'] is True and observed['inputs_unchanged'] is True and observed['mode']=='observation','Actual observation not successful')
  require(observed['source_bindings']==b and observed['coverage_sha256']==sha(args.coverage),'Observation source/coverage binding differs')
  inv={**b,'technical_verification_sha256':{rel(observation):sha(observation)},'schema_version':1,'scope_claims':CLAIMS,'critical_declarations':CRITICAL,'project_modules':science,'new_provider_modules':provider,'all_new_modules':allmodules,'coverage_observed':True,'coverage_record_sha256':{rel(args.coverage):sha(args.coverage)},**{k:coverage[k] for k in COVERAGE_KEYS},'coverage_summary':coverage['summary']}
  write(ROOT/'source-inventory.json',inv);print('Frozen source inventory '+sha(ROOT/'source-inventory.json'));return 0
 if not(args.execute or args.observe):print(json.dumps(plan,indent=2));return 0
 require(plan['expected_audit_is_current'],'Run --write-audit before freeze');require(plan['aggregate_imports_all_project_modules'],'Aggregate misses science modules')
 inventory=None;reviews={}
 if args.execute and args.mode=='final':inventory=read(ROOT/'source-inventory.json');reviews=final_reviews(inventory,b)
 output=(args.output or ROOT/'evidence'/('theorem18-'+dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))).resolve();output.mkdir(parents=True,exist_ok=False);(output/'logs').mkdir()
 env=dict(os.environ);env['PATH']=str(Path.home()/'.elan/bin')+os.pathsep+env.get('PATH','');env['MATHLIB_NO_CACHE_ON_UPDATE']='1';env.setdefault('LEAN_NUM_THREADS','2')
 record={**plan,'kind':'source-bound-theorem18-verification','ok':False,'mode':'observation' if args.observe else args.mode,'started_at':utc(),'commands':[],'exact_replays':[],'source_bindings':b,'semantic_acceptance_claimed':False,'clean_skipped':bool(args.observe or args.skip_clean),'repository_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=BASE,text=True).strip(),**{k:False for k in CLAIMS},'accepted_context_input_sha256':b['accepted_context_input_sha256'],'accepted_context_verification_sha256':b['accepted_context_verification_sha256'],'project_statement_reviews_sha256':reviews}
 frozen={};compiled={}
 def bind(path):
  path=Path(path).resolve();h=sha(path);require(str(path) not in frozen or frozen[str(path)]==h,'Changed binding');frozen[str(path)]=h
 def unchanged():
  for path,h in frozen.items():require(sha(path)==h,'Input changed during verification: '+path)
 def save():write(output/'verification.json',record)
 def run(label,argv):
  log=output/'logs'/(label+'.log');t=time.monotonic();print('Running: '+label,flush=True)
  with log.open('wb') as f:result=subprocess.run(argv,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
  row={'label':label,'argv':argv,'cwd':str(ROOT),'exit_code':result.returncode,'log':str(log.relative_to(output)),'log_sha256':sha(log),'elapsed_seconds':round(time.monotonic()-t,3)};record['commands'].append(row);save();require(result.returncode==0,label+' failed: '+str(log));return log.read_text()
 save()
 try:
  for value in b.values():
   if isinstance(value,dict):
    for path,h in value.items():require(sha(BASE/path)==h,'Changed source input');bind(BASE/path)
  if inventory:
   bind(ROOT/'source-inventory.json')
   for key in ['coverage_record_sha256','technical_verification_sha256']:
    for path,h in inventory[key].items():require(sha(BASE/path)==h,'Changed reviewed observation');bind(BASE/path)
   for path in reviews:bind(BASE/path)
  run('lean-version',['lake','env','lean','--version']);run('lake-version',['lake','--version'])
  require(run('mathlib-revision',['git','-C','.lake/packages/mathlib','rev-parse','HEAD']).strip()=='65d730f7150f21fdfa32f3e73a3f549c1f96a0e9','Wrong Mathlib pin')
  manifest=read(ROOT/'lake-manifest.json')
  for package in manifest['packages']:
   if package['type']!='git':continue
   name=package['name'].strip('«»');directory='.lake/packages/'+name
   require(run('pin-'+name,['git','-C',directory,'rev-parse','HEAD']).strip()==package['rev'],'Wrong dependency pin')
   require(not run('tracked-status-'+name,['git','-C',directory,'status','--porcelain','--untracked-files=no']).strip(),'Modified dependency')
  for label,command in provider_reproduction_commands():run(label,command)
  if not(args.observe or args.skip_clean):run('clean-new-package',['lake','clean','artin-deligne'])
  run('build-exact-frontier',['lake','build',*allmodules]);unchanged()
  coverage=validate_project_audit(run('project-statements-axioms-physical',['lake','env','lean','ProjectAudit.lean']),allmodules,known)
  require(all(name in {n for ns in coverage['audited_declarations_by_module'].values() for n in ns} for name in CRITICAL),'Critical theorem absent from audited declarations')
  for module,names in reviewedphysical.items():require(coverage['compiled_declaration_occurrences_by_module'][module]==names,'Supplier physical inventory changed')
  run('literal-theorem-endpoints',['lake','env','lean','StatementAudit.lean']);unchanged()
  coverage.update(source_bindings=b,all_new_modules=allmodules,project_modules=science,new_provider_modules=provider)
  write(output/'coverage.json',coverage);record['coverage_sha256']=sha(output/'coverage.json');record['coverage_file']='coverage.json';record['project_summary']=coverage['summary'];save()
  if inventory:
   for key in COVERAGE_KEYS:require(coverage[key]==inventory[key],'Frozen declaration inventory differs: '+key)
  for i,module in enumerate(allmodules):
   source=ROOT/(('vendor/' if module in provider else '')+module.replace('.','/')+'.lean')
   deps=run(f'deps-{i:03d}',['lake','env','lean','--deps',str(source)])
   paths=[Path(line) for line in deps.splitlines() if line.endswith('.olean')]
   paths.append(ROOT/'.lake/build/lib/lean'/(module.replace('.','/')+'.olean'))
   for path in paths:
    if not path.is_absolute():path=ROOT/path
    for part in [path,Path(str(path)+'.server'),Path(str(path)+'.private')]:
     if part.is_file():bind(part);compiled[str(part.resolve())]=sha(part)
  for tool in ['lean','lake','leanchecker']:bind(Path(run('resolve-'+tool,['lake','env','which',tool]).strip()))
  prefix=run('toolchain-prefix',['lake','env','lean','--print-prefix']).strip();checker_source=Path(prefix)/'src/lean/LeanChecker.lean';bind(checker_source)
  runner=output/'ExactReplay.lean';runner.write_text(exact_replay_source());bind(runner)
  record['exact_replay_source_sha256']=sha(runner);record['official_checker_source_sha256']=sha(checker_source);record['exact_replay_runner']='ExactReplay.lean';record['official_checker_source_path']=str(checker_source)
  write(output/'inputs.json',{'source_and_records_sha256':frozen,'compiled_parts_sha256':compiled});record['inputs_sha256']=sha(output/'inputs.json');record['bound_input_count']=len(frozen);save();unchanged()
  if not args.observe:
   for i,module in enumerate(allmodules):
    label=f'replay-{i:03d}-{module}';text=run(label,['lake','env','lean','--run',str(runner),module])
    rows=[json.loads(line.split(' ',1)[1]) for line in text.splitlines() if line.startswith('EXACT_REPLAY_JSON ')]
    expected_count=len(coverage['compiled_declaration_occurrences_by_module'][module])
    require(len(rows)==1 and rows[0]['module']==module and rows[0]['exact'] is True and rows[0]['kernel_replay_passed'] is True and rows[0]['declarations']==expected_count,'Exact replay module or physical declaration count differs')
    record['exact_replays'].append({'module':module,'physical_declarations_expected':expected_count,'official_kernel_replay':True,'official_algorithm':True,'result':rows[0],'command_label':label});save();unchanged()
  unchanged();require(bindings()[0]==b,'Final input frontier changed');require(modules()==science,'Scientific module set changed')
  if inventory:require(final_reviews(inventory,b)==reviews,'Final reviews changed')
  record.update(ok=True,inputs_unchanged=True,finished_at=utc())
  if inventory:record.update(CLAIMS);record['semantic_acceptance_claimed']=True
 except BaseException as error:record['error']=f'{type(error).__name__}: {error}';print(record['error'],file=sys.stderr)
 finally:record['finished_at']=utc();save()
 return 0 if record['ok'] else 1

if __name__=='__main__':raise SystemExit(main())
