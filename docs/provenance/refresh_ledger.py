#!/usr/bin/env python3
"""Rebuild the central source ledger from preserved provenance and search records.
No proof/config/review file is written. Network is never used.
"""
from __future__ import annotations
import datetime as dt, gzip, hashlib, json, re, shutil, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
LAKE=shutil.which('lake') or str(Path.home()/'.elan/bin/lake')
SYSROOT=Path(subprocess.check_output([LAKE,'env','lean','--print-prefix'],cwd=ROOT/'chambers',text=True).strip())

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads((ROOT/p).read_text())
def ref(p):
 p=Path(p); return {'path':str(p),'sha256':sha(ROOT/p)}
def save(p,x): (OUT/p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')

def main():
 search=(OUT/'searches'); search.mkdir(exist_ok=True)
 promoted=[]
 for src,report in [
 ('/tmp/artin-landmark3-search/m3-openai-candidate-register.json','docs/theorem18/landmarks/milestone3-search-openai.md'),
 ('/tmp/artin-landmark3-search/tauceti-cech-closure.json','docs/theorem18/landmarks/milestone3-search-openai.md'),
 ('/tmp/artin-landmark3-search/m3-openai-salvetti-closure.json','docs/theorem18/landmarks/milestone3-search-openai.md'),
 ('/tmp/artin-landmark3-search/oai-salvetti-closure.json','docs/theorem18/landmarks/milestone3-search-openai.md'),
 ('/tmp/m3-other-inventory.json','docs/theorem18/landmarks/milestone3-search-other.md'),
 ('/tmp/m3-qinz-fullgroupoid-closure.json','docs/theorem18/landmarks/milestone3-search-other.md')]:
  p=Path(src)
  dest=search/p.name
  if p.exists() or dest.exists():
   if p.exists() and dest.exists() and dest.read_bytes()!=p.read_bytes():
    raise RuntimeError(f'Promoted input changed: {src}; preserve old version before refresh')
   if not dest.exists(): shutil.copyfile(p,dest)
   promoted.append({'original_path':src,'durable_path':str(dest.relative_to(ROOT)), 'sha256':sha(dest), 'report':ref(report),'copy':'Exact bytes preserved at initial promotion; durable committed copy remains authoritative if the original temporary path no longer exists. Search artifact, not proof acceptance.'})
 reports=sorted(set([p for p in ROOT.glob('docs/**/*search*.md')]+[ROOT/'docs/full/external-prerequisites.md',ROOT/'docs/external-prerequisites.md']))
 records=[]
 # Repository identities come from GitHub URLs, machine inventories, or an
 # explicit first-column repository+commit table cell, never arbitrary paths.
 explicit_repositories={repo for p in reports for repo in re.findall(r'https://github.com/([\w.-]+/[\w.-]+)',p.read_text())}
 file_origins={
  'Cancellation/SphericalPositiveCancelLeft.lean':('openai/math','4eaee87548250b2682affda7d05d947c05554bae','lean/OAI/Topology/ArtinGroups/Cancellation/SphericalPositiveCancelLeft.lean'),
  'Cancellation/SphericalPositiveCancelMonoid.lean':('openai/math','4eaee87548250b2682affda7d05d947c05554bae','lean/OAI/Topology/ArtinGroups/Cancellation/SphericalPositiveCancelMonoid.lean'),
  'ChenRanks/ArrangementObjects.lean':('DongzheZheng/Suciu-s-Chen-ranks-conjecture','3a84cf4619f2c17e55f2e05214e9638e8d3b7634','ChenRanks/ArrangementObjects.lean'),
  'CoxeterWord/Basic.lean':('slashbade/coxeter_word','172f58a4010214de9f5695560a852925849e0e79','CoxeterWord/Basic.lean'),
  'OrlikSolomon/MainTheorem.lean':('adamtopaz/OrlikSolomon','1568c3994d24e53d39471ffe810cb076cfbccc8c','OrlikSolomon/MainTheorem.lean'),
  'Topology/ArtinGroups':('openai/math','4eaee87548250b2682affda7d05d947c05554bae','lean/OAI/Topology/ArtinGroups'),
  'Structures/CombinatorialTwoComplex.lean':('siddhartha-gadgil/Polylean','b2379c538307b2ce4a9f9969587232f9d94dd438','Complexes/Structures/CombinatorialTwoComplex.lean')}
 for p in reports:
  text=p.read_text();lines=text.splitlines();mentions=[];locators=[]
  for i,line in enumerate(lines):
   urls=re.findall(r'https://github.com/([\w.-]+/[\w.-]+)(?:/(?:tree|blob)/([0-9a-f]{40})(?:/([^\s)>`]+))?)?',line)
   bounded=[]
   for token in (re.findall(r'`([\w.-]+/[\w.-]+)`',line) if '|' in line else []):
    is_file=token.rsplit('/',1)[1].endswith(('.lean','.md','.json','.txt','.py','.toml','.yml','.yaml'))
    first_cell=bool(re.match(r'^\|\s*`'+re.escape(token)+r'`\s*(?:,\s*|\|\s*)`[0-9a-f]{40}`',line))
    if not is_file and token.split('/')[0] not in {'Mathlib','TauCeti','Topology','GroupTheory','Coxeter','Analysis','AlgebraicTopology','Geometry','Realizations','Harmonic','Cech','Interface','Complexes','LinearAlgebra','Weyl','RootSystem','Structures','ChenRanks','OrlikSolomon','Cancellation','CoxeterWord'} and (token in explicit_repositories or first_cell):bounded.append((token,'',''))
    else:
     row={'raw_locator':token,'line':i+1,'exact_source_line':line,'kind':'file locator or unclassified path; never a repository identity'}
     if token in file_origins:
      repo,rev,path=file_origins[token];row.update(repository='https://github.com/'+repo,revision=rev,upstream_path=path,kind='source file locator under actual repository')
     locators.append(row)
   for repo,rev,path in urls+bounded:
    if not rev:
     found=re.findall(r'\b[0-9a-f]{40}\b',line)
     if found and ('|' in line or 'commit' in line.lower() or 'sha' in line.lower()):rev=found[0]
    mentions.append({'repository':'https://github.com/'+repo,'revision':rev or None,'file':path or None,'line':i+1,'exact_source_line':line,'meaning':'Report mention only; semantic/reading/execution limits are those of this source report.'})
  records.append({'report':ref(p.relative_to(ROOT)),'full_report_text':text,'repository_mentions':mentions,'file_locators':locators})

 # Accepted source cohorts: original/active bytes and patches remain in existing contexts.
 cohorts=[]
 specs=[('lemma28-algebra','vendor/provenance.json','docs/full/source-inventory.json','vendor', 'docs/full/github-evidence/run-43486289665/verification.json'),
 ('theorem18-topology','vendor/theorem18-provenance.json','docs/theorem18/source-inventory.json','vendor','docs/theorem18/github-evidence/run-43492004104/lean-theorem18-foundations-verification.json'),
 ('landmark1-sign','landmarks/vendor/provenance.json','landmarks/source-inventory.json','landmarks/vendor','docs/theorem18/landmarks/github-evidence/run-43498322108/verification.json'),
 ('landmark2-positive','ribbons/vendor/provenance.json','ribbons/source-inventory.json','ribbons/vendor','docs/theorem18/landmarks/github-evidence/run-43516856592/verification.json')]
 for ident,prov,inv,base,ver in specs:
  d=load(prov); inventory=load(inv); v=load(ver); files=[]
  if ident=='landmark2-positive':
   for row in d['modules']:
    active=f'{base}/{row["path"]}'; original=f'{base}/upstream-original/{row["path"]}'
    files.append({'module':row['module'],'upstream_path':'lean/'+row['path'],'active_path':active,'original_path':original,
      'upstream_sha256':row['upstream_sha256'],'active_sha256':row['active_sha256'],'actual_active_sha256':sha(ROOT/active),'actual_original_sha256':sha(ROOT/original),'imports':row['imports']})
   patches=[dict(p,patch_files=[ref(str(pth.relative_to(ROOT))) for pth in sorted((ROOT/base/'compatibility-patches').glob('*')) if Path(p['path']).stem in pth.name]) for p in d['compatibility_ports']]
  else:
   for path,h in d['files_sha256'].items():
    local=f'{base}/{path}'; mod=next((m for m in d['modules'] if m.replace('.','/')+'.lean'==path),path[:-5].replace('/','.'))
    source=d.get('module_sources_and_imports',{}).get(mod,{})
    upstream=source.get('upstream_path',path)
    orig=f'{base}/{source["preserved_upstream_bytes"]}' if 'preserved_upstream_bytes' in source else local
    files.append({'module':mod,'upstream_path':upstream,'active_path':local,'original_path':orig,
      'upstream_sha256':source.get('upstream_sha256',h),'active_sha256':h,'actual_active_sha256':sha(ROOT/local),'actual_original_sha256':sha(ROOT/orig),'imports':source.get('imports'), 'imports_inventory_note':'See provenance; null means not re-extracted by this ledger.'})
   patches=d.get('modifications',[])
  for row in files:
   if row['active_sha256']!=row['actual_active_sha256'] or row['upstream_sha256']!=row['actual_original_sha256']: raise RuntimeError(f'Byte mismatch {row}')
  licenses=[]
  for path in [ROOT/base/'LICENSE.TauCeti',ROOT/base/'LICENSE',ROOT/base/'LICENSE.openai-math',ROOT/'vendor/LICENSE.TauCeti']:
   if path.is_file() and (ident!='landmark2-positive' or 'TauCeti' not in path.name): licenses.append(ref(path.relative_to(ROOT)))
  archives=[ref(str(p.relative_to(ROOT))) for p in sorted((ROOT/Path(ver).parent).glob('README.md'))]
  command_status=v.get('commands',[])
  endpoints=inventory.get('declarations',d.get('selected_declarations',[]))
  if ident=='landmark2-positive': endpoints=[{'module':m,'declarations':names} for m,names in inventory['audited_declarations_by_module'].items()]
  cohorts.append({'id':ident,'repository':d['repository'],'revision':d.get('revision',d.get('upstream_sha')),'disposition':'accepted for the exact recorded scope by later verification and reviews, not by historical provenance alone',
    'module_count':len(files),'provenance':ref(prov),'source_inventory':ref(inv),'verification':ref(ver),'verification_ok':v.get('ok'),'verification_repository_head':v.get('repository_head'), 'verification_commands':command_status,'verification_limits':v.get('limitations',v.get('limits')),
    'license_identifier':'Apache-2.0','license_files':licenses,'files':files,'patches':patches,'exact_project_or_supplier_declaration_inventory':endpoints,'archive_records':archives})

 # Explicit root acceptance promotes only the reviewed supplier cohort, never M3 project mathematics.
 acceptance_path=OUT/'acceptance-landmark3-cech.json'
 if acceptance_path.exists():
  acceptance=json.loads(acceptance_path.read_text());d=load('chambers/vendor/provenance.json')
  verification=load('chambers/evidence/providers/verification.json');coverage=load('chambers/evidence/providers/coverage.json')
  assert acceptance['root_disposition']=='accept-supplier-cohort' and verification['ok']
  reviews=[]
  for r in acceptance['independent_reviews']:
   assert sha(ROOT/r['path'])==r['sha256'] and sha(ROOT/r['prose_path'])==r['prose_sha256']
   receipt=load(r['path']);assert receipt['verdict']=='accept-supplier-cohort'
   for field in ['provider_source_sha256','provider_original_source_sha256','provider_import_patch_sha256','provider_patch_sha256','configuration_sha256','reused_parent_source_sha256','parent_source_context_sha256','parent_context_sha256','evidence_sha256','verification_scripts_sha256']:
    for path,h in receipt.get(field,{}).items():
     assert (ROOT/path).is_file() and sha(ROOT/path)==h,(field,path)
   reviews.append({'receipt':ref(r['path']),'prose':ref(r['prose_path']),'verdict':receipt['verdict'],'model':receipt['model'],'reasoning_effort':receipt['reasoning_effort'],'reading_and_execution_limits':receipt.get('reading_limits',receipt.get('source_reading')),'independent_lean_execution':False})
  files=[];patches=[]
  for f in d['files']:
   active='chambers/vendor/'+f['path'];original='chambers/vendor/'+f['original_path'];patch='chambers/vendor/'+f['patch_path']
   assert sha(ROOT/active)==f['active_sha256'] and sha(ROOT/original)==f['upstream_sha256'] and sha(ROOT/patch)==f['patch_sha256']
   files.append({'module':f['module'],'upstream_module':f['upstream_module'],'upstream_path':f['upstream_path'],'active_path':active,'original_path':original,'upstream_sha256':f['upstream_sha256'],'active_sha256':f['active_sha256'],'actual_active_sha256':sha(ROOT/active),'actual_original_sha256':sha(ROOT/original),'imports':f['active_imports']})
   patches.append({'module':f['module'],'patch':ref(patch),'scope':f['port']})
  commands=[];phase_records=[]
  for phase,row in verification['records'].items():
   path='chambers/'+row['record'];assert sha(ROOT/path)==row['sha256'];record=load(path)
   phase_records.append({'phase':phase,'record':ref(path),'data':record})
   commands.extend(record.get('commands',[record]) if isinstance(record.get('commands',[record]),list) else [])
  cohorts.append({'id':'landmark3-cech-supplier','repository':d['repository'],'revision':d['upstream_sha'],'disposition':'accepted supplier cohort by explicit root acceptance after both independent GPT-6.1 Sol/high receipts; active main M3 remains unaccepted','module_count':len(files),'provenance':ref('chambers/vendor/provenance.json'),'source_inventory':ref('chambers/evidence/providers/coverage.json'),'verification':ref('chambers/evidence/providers/verification.json'),'verification_ok':verification['ok'],'verification_commands':commands,'verification_phase_records':phase_records,'verification_limits':{'kernel_relative_to_imports':True,'independent_kernel_implementation':False,'main_landmark_3_proved':False,'build_to_audit_transition':acceptance['build_to_audit_metadata_transition']},'license_identifier':d['upstream_license'],'license_files':[ref('chambers/vendor/'+d['license_path'])],'files':files,'patches':patches,'exact_project_or_supplier_declaration_inventory':coverage['declarations'],'intended_direct_endpoints':d['intended_direct_endpoints'],'archive_records':[],'independent_reviews':reviews,'root_acceptance':ref('docs/provenance/acceptance-landmark3-cech.json'),'included_in_throughM2_dependency_graph':False})
 manifests=[]; dependencies={}
 for p in [Path('lake-manifest.json'),Path('landmarks/lake-manifest.json'),Path('ribbons/lake-manifest.json'),Path('chambers/lake-manifest.json')]:
  if not (ROOT/p).exists():continue
  d=load(p); manifests.append(ref(p))
  for pkg in d['packages']:
   if pkg['type']=='git':
    key=(pkg['url'].removesuffix('.git'),pkg['rev'])
    dependencies.setdefault(key,{'repository':key[0],'revision':key[1],'lake_package':pkg['name'],'manifests':[], 'role':'foundation library' if pkg['name']=='mathlib' else 'transitive Lake dependency; build/tooling and possibly term-level suppliers distinguished by compiled graph'})['manifests'].append(str(p))
 # Bind dependency licenses without copying third-party package trees.
 for dep in dependencies.values():
  package=dep['lake_package']
  root=ROOT/'chambers/.lake/packages'/package
  dep['license_records']=[]
  for leaf in ['LICENSE','LICENSE.md','LICENSE.txt']:
   p=root/leaf
   if p.is_file():dep['license_records'].append({'package_path':leaf,'sha256':sha(p),'repository_revision':dep['revision']})
 # Merge detailed current search registers, preserving their exact per-file limits.
 machine_searches=[]
 for row in promoted:
  p=ROOT/row['durable_path']
  if 'candidate-register' in p.name or p.name=='m3-other-inventory.json': machine_searches.append({'inventory':ref(p.relative_to(ROOT)), 'records':json.loads(p.read_text())})

 repo_index={}
 def repo_entry(repo):
  repo=repo.removesuffix('.git')
  return repo_index.setdefault(repo,{'roles':set(),'exact_revisions':set(),'source_reports':[]})
 for c in cohorts:
  r=repo_entry(c['repository']);r['roles'].add('accepted scientific supplier');r['exact_revisions'].add(c['revision'])
 for dep in dependencies.values():
  r=repo_entry(dep['repository']);r['roles'].add(dep['role']);r['exact_revisions'].add(dep['revision'])
 for record in records:
  for m in record['repository_mentions']:
   r=repo_entry(m['repository']);r['roles'].add('search-report mention; read/use/disposition bounded by exact report')
   if m['revision']:r['exact_revisions'].add(m['revision'])
   r['source_reports'].append({'path':record['report']['path'],'line':m['line']})
 for record in machine_searches:
  data=record['records']
  if 'source_inspected_repositories' in data:
   for item in data['source_inspected_repositories']:
    r=repo_entry(item['repository']);r['roles'].add('source inspected only; not accepted by search');r['exact_revisions'].add(item['commit'])
   for item in data.get('search_hit_repositories_not_equated_with_use',[]):
    r=repo_entry(item['repository']);r['roles'].add('search hit only; not equated with source reading/use');r['exact_revisions'].update(item['indexed_commits'])
  else:
   for key,item in data.items():
    r=repo_entry('https://github.com/'+key);r['roles'].add('M3 machine search inventory; exact reading/disposition retained in records');r['exact_revisions'].update(item.get('revisions',{}))
 tooling=[]
 for workflow in sorted((ROOT/'.github/workflows').glob('*.yml')):
  for line_no,line in enumerate(workflow.read_text().splitlines(),1):
   hit=re.search(r'\buses:\s*([\w.-]+/[\w.-]+)@([0-9a-f]{40})\b',line)
   if hit:
    repository='https://github.com/'+hit[1];revision=hit[2]
    tooling.append({'repository':repository,'revision':revision,'role':'GitHub Actions tooling only; no scientific proof supplied','workflow':ref(workflow.relative_to(ROOT)),'line':line_no,'source_reading_limit':'Exact uses entry inspected; action implementation/dependencies not manually audited by this register.'})
    entry=repo_entry(repository);entry['roles'].add('GitHub Actions tooling only');entry['exact_revisions'].add(revision)
 project_repository='https://github.com/lazyinspirit/artin-tits-normalisers-lean'
 repo_entry(project_repository)['roles'].add('locally authored project; precommit source hashes and base Git revision, later immutable commit binding separate')
 repo_entry(project_repository)['exact_revisions'].add(subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip())
 if (OUT/'m3/run-20261114T065009Z/execution.json').exists():
  repo_entry(project_repository)['exact_revisions'].add(json.loads((OUT/'m3/run-20261114T065009Z/execution.json').read_text())['observed_git_head'])
 for published in sorted((OUT/'publications').glob('*/binding.json')):
  publication=json.loads(published.read_text())
  if publication.get('ok'):repo_entry(project_repository)['exact_revisions'].add(publication['commit'])

 repo_entry('https://github.com/leanprover/lean4')['roles'].add('kernel and builtin foundation')
 repo_entry('https://github.com/leanprover/lean4')['exact_revisions'].add('b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a')
 for item in repo_index.values():
  item['roles']=sorted(item['roles']);item['exact_revisions']=sorted(item['exact_revisions'])
 ledger={'schema_version':1,'generation_script':ref('docs/provenance/refresh_ledger.py'),'kind':'github-proof-source-ledger','base_repository_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
   'policy':{'all_used_sources':'Accepted cohorts list every vendored scientific source file, original/active hashes, patches, licenses and original inventories. Compiled dependency graph records actual term suppliers including foundations. Search reports register inspected/rejected/uninspected leads separately.','manual_reading_limit':'This consolidation reads inventories and source reports; it does not claim independent manual inspection of every supplier proof body.','verification_limit':'Existing verification records are preserved and referenced, not rerun or relabeled by this ledger. Mathlib/Lean remain pinned imported foundations; no fresh replay of all mathlib is claimed.','mirror_limit':'mathcommunity/oai-math-revised is byte-identical in the inspected OAI subtree, not independent proof or review.','new_proof_acceptance':False,'full_theorem_1_8_proved':False},
   'repository_index':repo_index,'github_actions_tooling':tooling,'repository_extraction_policy':'Explicit GitHub URLs and exact machine register repository fields; bounded first-cell repository+40-character commit tokens only. File locators stay attached to report/source repository and are never converted into GitHub repositories.','accepted_scientific_repository_count':2,'accepted_scientific_repositories':sorted({c['repository'] for c in cohorts}), 'accepted_cohorts':cohorts,
   'lean_foundation':{'repository':'https://github.com/leanprover/lean4','tag':'v4.36.0-rc2','revision':'b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a','role':'bundled Lean kernel/Init/Lean/Lake and proof language','toolchain_file':ref('lean-toolchain'),'whole_library_fresh_replayed':False,'license_path':'LICENSE','license_sha256':sha((SYSROOT/'src/lean/LICENSE')) if (SYSROOT/'src/lean/LICENSE').exists() else None},
   'lake_git_dependencies':list(dependencies.values()),'manifest_records':manifests,
   'mirror':{'repository':'https://github.com/mathcommunity/oai-math-revised','revision':'d25fae85c2f5ce5aadac40fb2b4c2d332b393d1c','identical_to':'https://github.com/openai/math','upstream_revision':'4eaee87548250b2682affda7d05d947c05554bae','ArtinGroups_tree':'0b8f7c175022e4696404bb2bbabf12746f899d14','disposition':'identical inspected source; not independently accepted proof'},
   'search_report_register':records,'promoted_search_inventories':promoted,'detailed_machine_search_records':machine_searches,
   'compiled_dependency_graph':{'status':'pending observer run','observer':ref('docs/provenance/ExportDependencies.lean')},
   'maintenance':'Rerun docs/provenance/refresh_ledger.py after new search reports or accepted source inventories. Do not mutate old proof/provenance/review records. New supplier acceptance requires its own existing gates.'}
 # Through-M2 export is an immutable historical observation. A refresh must not
 # rehash current objects or relabel its source context with a newer Git HEAD.
 baseline_graph=OUT/'dependency-graph.json.gz'
 if baseline_graph.exists():
  data=gzip.decompress(baseline_graph.read_bytes());g=json.loads(data)
  bymodule=g['modules_to_sources'];nodes=g['nodes'];mods=set(bymodule)
  unmapped=[m for m,rows in bymodule.items() if any(r['repository']=='UNMAPPED' for r in rows)]
  ledger['compiled_dependency_graph']={'status':'actual exported graph throughM2; immutable historical observation, not new mathematical verification','scope':'throughM2: accepted project roots preceding M3; excludes the newly accepted232-declaration Cech cohort and later ArtinChambers mathematics','observer':ref('docs/provenance/ExportDependencies.lean'),'graph':ref('docs/provenance/dependency-graph.json.gz'),'roots':len(g['roots']),'declarations':len(nodes),'edge_count':g['edge_count'],'reachable_module_count':len(mods),'unmapped_modules':unmapped,'source_module_records':bymodule,'actual_used_modules_by_repository':dict(__import__('collections').Counter(s['repository'] for rows in bymodule.values() for s in rows)),'uncompressed_graph_sha256':hashlib.sha256(data).hexdigest(),'raw_export':ref('docs/provenance/dependency-graph.raw.json.gz'),'execution_record':ref('docs/provenance/export-execution.json'),'refresh_policy':'Read archival bytes only. Later M3 exports use distinct versioned directories; baseline graph, raw export and execution records are never rewritten.'}
 staged_path=ROOT/'chambers/vendor/provenance.json'
 if staged_path.exists() and not acceptance_path.exists():
  staged=json.loads(staged_path.read_text())
  for f in staged['files']:
   for key,pathkey in [('active_sha256','path'),('upstream_sha256','original_path'),('patch_sha256','patch_path')]:
    if sha(ROOT/'chambers/vendor'/f[pathkey]) != f[key]:raise RuntimeError(f'Staged supplier byte mismatch: {f[pathkey]}')
  ledger['staged_supplier_cohorts']=[{'repository':staged['repository'],'revision':staged['upstream_sha'],'module_count':staged['module_count'],'status':'technically verified, independent statement/diff review and root acceptance pending; excluded from accepted root graph','provenance':ref('chambers/vendor/provenance.json'),'complete_file_patch_license_and_endpoint_inventory':staged,'technical_verification':ref('chambers/evidence/providers/verification.json') if (ROOT/'chambers/evidence/providers/verification.json').exists() else None,'accepted_by_this_ledger':False}]
 # Continually maintained, source-level record for active M3 files. This is not a compiled-term audit.
 development_file=OUT/'development-sources.json'
 prior_development=json.loads(development_file.read_text()) if development_file.exists() else {'files':[]}
 previous={r['path']:r for r in prior_development['files']}
 observed_at=dt.datetime.now(dt.timezone.utc).isoformat();development_rows=[];events=[]
 for path in sorted((ROOT/'chambers/ArtinChambers').glob('*.lean'))+([ROOT/'chambers/ArtinChambers.lean'] if (ROOT/'chambers/ArtinChambers.lean').exists() else []):
  before=path.stat();content=path.read_bytes();after=path.stat()
  stable=(before.st_size,before.st_mtime_ns,before.st_ctime_ns)==(after.st_size,after.st_mtime_ns,after.st_ctime_ns)
  text=content.decode();imports=[];headers=[]
  for line_no,line in enumerate(text.splitlines(),1):
   m=re.match(r'^(?:(?:public|meta)\s+)?import(?:\s+all)?\s+(.+)$',line.strip())
   if m:
    for module in m.group(1).split():
     if module.startswith('--'):break
     if module.startswith('Mathlib'):origin={'repository':'https://github.com/leanprover-community/mathlib4','revision':'65d730f7150f21fdfa32f3e73a3f549c1f96a0e9','role':'pinned foundation'}
     elif module.startswith('ArtinChamberVendor.'):origin={'repository':'https://github.com/TauCetiProject/TauCeti','revision':'62bbc0596dc3539d488232e4e924a338548ea0a9','role':'accepted nine-module Cech supplier cohort'}
     elif module.startswith(('TauCeti.','ArtinLandmarkVendor.')):origin={'repository':'https://github.com/TauCetiProject/TauCeti','revision':'62bbc0596dc3539d488232e4e924a338548ea0a9','role':'previously accepted parent/sign supplier'}
     elif module.startswith(('ArtinChambers','ArtinNormalisers','ArtinLandmarks','ArtinRibbons')):origin={'repository':'https://github.com/lazyinspirit/artin-tits-normalisers-lean','role':'locally authored project module; M3 files remain under development'}
     else:origin={'role':'unclassified direct import; investigate before acceptance'}
     imports.append({'module':module,'source_line':line_no,'origin':origin})
   if re.match(r'^(?:(?:private|protected|noncomputable)\s+)*(?:def|theorem|lemma|instance|abbrev|structure|inductive|class)\s',line.strip()):headers.append({'line':line_no,'text':line.strip()})
  rel=str(path.relative_to(ROOT));digest=hashlib.sha256(content).hexdigest()
  row={'path':rel,'sha256':digest,'bytes':len(content),'stable_during_read':stable,'status':'locally authored active M3 source; main M3 not accepted','proof_origin':'Local authoring authorized by root; direct source imports recorded, no additional external repository is inferred from a search lead. Exact term-level origins await the finalized M3 graph.','imports':imports,'source_declaration_headers':headers,'header_limits':'Lexical index only; not complete compiler declaration/signature coverage.','compiled_object_present':(ROOT/'chambers/.lake/build/lib/lean'/Path(rel).relative_to('chambers').with_suffix('.olean')).is_file(),'compilation_limit':'No build/audit/replay is executed by this source observation; object presence does not certify this exact current source version.'}
  development_rows.append(row)
  if previous.get(rel,{}).get('sha256')!=digest:events.append({'recorded_at':observed_at,'path':rel,'previous_sha256':previous.get(rel,{}).get('sha256'),'observed_source':row})
 for path,row in previous.items():
  if path not in {r['path'] for r in development_rows}:events.append({'recorded_at':observed_at,'path':path,'previous_sha256':row['sha256'],'status':'no longer present in current source observation; historical record preserved'})
 history=OUT/'development-history.jsonl'
 if events:
  with history.open('a') as stream:
   for event in events:stream.write(json.dumps(event,sort_keys=True)+'\n')
 save('development-sources.json',{'kind':'active-M3-source-observation','observed_at':observed_at,'full_landmark_3_proved':False,'accepted':False,'files':development_rows,'history':'docs/provenance/development-history.jsonl','limits':'Per-file stable reads, not a globally frozen source set; live authors may continue editing. Refresh after changes; final M3 verification and exact term graph remain separate.'})
 ledger['current_m3_development']={'inventory':ref('docs/provenance/development-sources.json'),'change_history':ref('docs/provenance/development-history.jsonl'),'file_count':len(development_rows),'accepted':False,'complete_term_dependency_graph':'pending finalized root aggregate and explicit root direction','additional_external_repositories_used':'None identified beyond pinned Mathlib/old providers and the accepted nine Cech modules; direct import classification retained per file.'}
 root_acceptance=ROOT/'docs/theorem18/landmarks/milestone3-root-acceptance.json'
 if root_acceptance.exists():
  accepted=json.loads(root_acceptance.read_text());assert accepted['mathematical_acceptance'] is True
  for field,mapping in accepted['source_bindings'].items():
   if isinstance(mapping,dict):
    for path,digest in mapping.items():assert sha(ROOT/path)==digest,(field,path)
  for path,digest in accepted['independent_reviews_sha256'].items():assert sha(ROOT/path)==digest
  ledger['accepted_local_milestones']=[{'milestone':'M3','root_acceptance':ref(root_acceptance.relative_to(ROOT)),'scope':accepted['scope'],'mathematical_acceptance':True,'clean_github_ci_status':accepted['clean_github_ci_status'],'source_inventory':ref('chambers/source-inventory.json'),'technical_verification':ref('chambers/evidence/landmark3-technical-20261114T074500Z/verification.json'),'independent_reviews_sha256':accepted['independent_reviews_sha256'],'full_theorem_1_8_proved':False}]
  development=json.loads((OUT/'development-sources.json').read_text());development['accepted']=True;development['full_landmark_3_proved']=True;development['acceptance_scope']=accepted['scope'];development['clean_github_ci_status']=accepted['clean_github_ci_status']
  for row in development['files']:
   row['status']='Root mathematically accepted exact frozen M3 source; clean GitHub CI pending'
   row['proof_origin']='Locally authored exact M3 source; full compiled dependency origins are recorded in the separate M3 graph.'
   row['compilation_limit']='Exact source version has passing source-bound technical verification and root mathematical acceptance. Clean GitHub CI is separate and pending.'
  development['limits']='Historical development observations remain in the append-only history; this current snapshot is the frozen root-accepted M3 source set.'
  save('development-sources.json',development);ledger['current_m3_development']['inventory']=ref('docs/provenance/development-sources.json');ledger['current_m3_development']['accepted']=True;ledger['current_m3_development']['clean_github_ci_status']=accepted['clean_github_ci_status']
 m3=OUT/'m3/run-20261114T065009Z/execution.json'
 if m3.exists():
  execution=json.loads(m3.read_text());assert execution['ok'] and execution['baseline_unchanged'] and execution['old_roots_and_dependency_edges_preserved']
  ledger['compiled_m3_dependency_graph']={'scope':'All canonical/physical project declarations through M3, private/generated included; canonical-name sharing represented once with explicit physical aliases','execution':ref(m3.relative_to(ROOT)),'graph':execution['annotated_graph'],'counts':execution['counts'],'raw_graphs':execution['raw_graphs'],'baseline_unchanged':True,'old_roots_and_edges_preserved':True,'source_attribution_supplement':ref('docs/provenance/m3/source-attribution.json'),'root_count_accounting':'1305 old roots +1071 technical M3 canonical declarations -1 shared generated name =2375 unique roots;2377 physical occurrences =2375+2 aliases. The same elementaryMu.congr_simp name occurs in CofinalRibbons,RibbonWords,PositiveTransport; joint export canonical owner CofinalRibbons. Technical M3 audit has a different import order and reports1071/1071 with0duplicates in its own context.','source_commit_binding':'Exact precommit source hashes and observed base HEAD retained; later immutable source commit is appended separately without rewriting graphs.'}
 publication_records=[]
 for published in sorted((OUT/'publications').glob('*/binding.json')):
  publication=json.loads(published.read_text());assert publication['ok'] and publication['Lean_build_audit_or_kernel_replay_executed'] is False
  validation=published.parent/'validation.json'
  if validation.exists():
   validated=json.loads(validation.read_text());assert validated['ok'] and validated['binding_sha256']==sha(published)
  publication_records.append({'commit':publication['commit'],'binding':ref(published.relative_to(ROOT)),'validation':ref(validation.relative_to(ROOT)) if validation.exists() else None,'exact_repository_source_bindings':publication['exact_source_binding_count'],'M3_project_source_files':publication['M3_project_source_count'],'historical_non_scientific_metadata_differences':list(publication['non_scientific_historical_metadata_differences']),'clean_github_ci':publication['clean_github_ci'],'observation_policy':'Append-only publication binding; original precommit graphs/execution/attribution are not rewritten.'})
 ledger['source_publication_bindings']=publication_records
 if (OUT/'m3/validation.json').exists():
  validation=json.loads((OUT/'m3/validation.json').read_text());assert validation['ok']
  ledger['compiled_m3_dependency_graph']['integrity_validation']=ref('docs/provenance/m3/validation.json')
 closeout_path=ROOT/'docs/theorem18/landmarks/milestone3-closeout.json'
 if closeout_path.exists():
  closeout=json.loads(closeout_path.read_text());assert closeout['clean_ci_passed'] is True and closeout['full_landmark_3_proved'] is True and closeout['full_theorem_1_8_proved'] is False
  directory=Path(closeout['ci_archive_directory']);archive_path=directory/'archive-verification.json';verification_path=directory/'verification.json'
  assert sha(ROOT/archive_path)==closeout['ci_archive_sha256'][str(archive_path)]
  assert sha(ROOT/verification_path)==closeout['ci_archive_sha256'][str(verification_path)]
  archived=json.loads((ROOT/archive_path).read_text());verified=json.loads((ROOT/verification_path).read_text())
  assert archived['ok'] and verified['ok'] and verified['mode']=='final' and verified['inputs_unchanged'] and archived['source_commit']==closeout['source_commit']
  ledger['current_M3_clean_CI']={'status':'passed','source_commit':closeout['source_commit'],'run_url':closeout['github_run_url'],'closeout':ref(closeout_path.relative_to(ROOT)),'archive_verification':ref(archive_path),'final_verification':ref(verification_path),'artifact_sha256':archived['artifact_sha256'],'checked_current_inputs':archived['current_source_input_count'],'unchanged_old_inputs':archived['historical_input_count'],'checked_raw_logs':archived['checked_raw_log_count'],'project_exact_replays':archived['project_exact_replays'],'provider_exact_replays':archived['provider_exact_replays'],'provider_declarations':archived['provider_declarations'],'full_theorem_1_8_proved':False}
  for milestone in ledger.get('accepted_local_milestones',[]):
   if milestone['milestone']=='M3':milestone['clean_github_ci_status']='passed';milestone['clean_CI_closeout']=ref(closeout_path.relative_to(ROOT));milestone['archive_verification']=ref(archive_path)
  for publication in ledger.get('source_publication_bindings',[]):
   publication['clean_github_ci_at_binding_creation']=publication.pop('clean_github_ci')
   if publication['commit']==closeout['source_commit']:publication['current_clean_CI_closeout']=ref(closeout_path.relative_to(ROOT))
  ledger['current_m3_development']['clean_github_ci_status']='passed'
  current=json.loads((OUT/'development-sources.json').read_text());current['clean_github_ci_status']='passed';current['clean_CI_closeout']=ref(closeout_path.relative_to(ROOT))
  for row in current['files']:
   row['status']='Root mathematically accepted frozen M3 source; clean final-mode GitHub CI passed'
   row['compilation_limit']='Exact source has passing local technical verification, both independent final reviews, root acceptance and clean final-mode CI at the recorded source commit. Imported old suppliers and whole Mathlib were not freshly replayed.'
  save('development-sources.json',current);ledger['current_m3_development']['inventory']=ref('docs/provenance/development-sources.json')
 save('GITHUB-PROOF-SOURCES.json',ledger)
 # Human index stays compact; machine ledger contains the complete inventories.
 lines=['# GitHub proof source ledger','',f"Accepted scientific suppliers: **2 repositories, {sum(c['module_count'] for c in cohorts)} vendored modules** at the exact revisions below. Mathlib, Lean, transitive Lake dependencies and inspected-only leads are separate categories.",'','| Cohort | Repository and revision | Modules | Exact byte and proof record |','| --- | --- | ---: | --- |']
 for c in cohorts:lines.append(f"| {c['id']} | [{c['repository'].split('github.com/')[1]}]({c['repository']}/tree/{c['revision']}) `{c['revision']}` | {c['module_count']} | [{c['source_inventory']['path']}](../../{c['source_inventory']['path']}); [{c['verification']['path']}](../../{c['verification']['path']}) |")
 lines+=['','The [machine ledger](GITHUB-PROOF-SOURCES.json) records every accepted file’s upstream/local paths and SHA256, preserved originals, compatibility changes, licenses, exact declaration inventories, CI verification inputs and raw search-report locators. Original inventories remain authoritative; this consolidation does not replace or edit them. Seven OAI compatibility ports and the one relocated TauCeti Sign import are explicit. Historical provider provenance saying acceptance was pending is retained; later successful CI/reviews supply acceptance.','', 'Mathlib is pinned to `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; Lean is pinned to `v4.36.0-rc2`, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`. Every transitive Git dependency revision is recorded from all four Lake manifests. Imported proof terms and build tooling are distinguished by the actual dependency graph. No fresh replay of all mathlib or second independent kernel is claimed.','', 'The mathcommunity/oai-math-revised commit `d25fae85c2f5ce5aadac40fb2b4c2d332b393d1c` has the identical inspected ArtinGroups tree `0b8f7c175022e4696404bb2bbabf12746f899d14` as openai/math. It supplies the same source, not independent proof evidence.','', '## Actual compiled proof dependencies through M2','']
 if ledger['compiled_dependency_graph']['status'].startswith('actual'):
  z=ledger['compiled_dependency_graph'];lines +=[f"The **through-M2** [compressed graph](dependency-graph.json.gz) recursively records **{z['roots']} compiled project declarations, {z['declarations']} reachable declarations and {z['edge_count']} distinct-per-node references**, across {z['reachable_module_count']} source modules. Each node records its defining module, declaration kind, type/value/structural edges and repository mapping. Module source hashes and actual reachable compiled object hashes are bound. The graph is an observation of imported constants, not a new proof acceptance or a claim of manual reading. Unmapped modules: {len(z['unmapped_modules'])}."]
 else:lines +=['The read-only exporter is in development; no completed graph is claimed yet.']
 lines +=['','[ExportDependencies.lean](ExportDependencies.lean) uses the existing combined `chambers` environment and imports only the accepted `ArtinRibbons` and `ArtinLandmarks` targets. Its root selection includes defining modules `ArtinNormalisers.*`, `ArtinLandmarks.*` and `ArtinRibbons.*`; import-only aggregators contribute no scientific constants. It follows actual elaborated type/value references and inductive/recursor metadata, including opaque values. Private/generated declarations present in the legacy environment are included. Existing physical-coverage audits document identical theorem duplicates; canonical defining-module ownership in this graph is not a claim that duplicate physical occurrences do not exist.','', '## Inspected candidates and search leads','', 'Every existing source-search report is hash-bound in the JSON with exact repository mentions and original report lines. Source file paths are kept as file locators under their actual repository, never invented repository identities. GitHub Actions checkout, artifact upload and Lean action repositories are indexed at the exact workflow pins as tooling only, alongside this locally authored project. Complete M3 machine candidate and closure inventories are preserved byte-for-byte under [searches/](searches/), with their original temporary locations, SHA256 and author report references. Detailed machine records retain per-file hashes/declarations, dispositions and actual reading/execution limits. Search hits are not mislabeled as read proofs, copied sources, compiled suppliers or accepted mathematics.','', 'For earlier reports without a machine inventory, exact file/declaration names, hypotheses, reason for rejection and reading limits remain in the linked original report; the ledger’s extracted mention is an index into that record, not a fabricated complete manual inspection. Repository searches are bounded and negative results are not worldwide absence claims.','']
 for row in records:lines.append(f"- [{row['report']['path']}](../../{row['report']['path']})")
 lines +=['','The nine mechanically relocated TauCeti Čech supplier modules in `chambers/vendor/` are accepted as suppliers following both independent GPT-6.1 Sol/high receipts and explicit root acceptance. Their 232 canonical/physical declarations, nine successful individual replays, exact original/local/patch/license/endpoint inventory and [both](../../chambers/reviews/providers-a.json) [review bindings](../../chambers/reviews/providers-b.json) are recorded separately. Review B preserves the two changed metadata/runner hashes between build and audit: every mathematical source/configuration byte agrees, while the whole earlier build manifest is not relabeled identical. The immutable historical graph remains through M2; the separate full M3 graph records the later accepted mathematics and its actual supplier dependencies. Historical development observations are retained in [development-history.jsonl](development-history.jsonl). The current [frozen source inventory](development-sources.json) identifies the root-accepted M3 files; exact compiled term coverage is in the full M3 graph. Historical observations are not relabeled as verification certificates. M3 now has explicit root mathematical acceptance at its exact qualified scope, with both final independent reviews and the passing local technical record. Clean GitHub CI is pending. Full Theorem 1.8 remains unproved. The full compiled M3 graph and import-order accounting are documented in [M3-EXPORT.md](M3-EXPORT.md).','', 'Publication is bound separately to commit `59941e65aece274beb65a3f5c668616a69c0e292`: [970 exact source/configuration/provider/review/record bindings](publications/59941e65aece274beb65a3f5c668616a69c0e292/binding.json), including all 43 M3 project files, with [actual Git blob validation](publications/59941e65aece274beb65a3f5c668616a69c0e292/validation.json). The original graph remains an honest precommit observation. The sole historical mismatch is the mutable registry JSON snapshot, explicitly classified as metadata; no frozen proof/configuration/provider/review differs. Clean CI was pending when this binding was made and remains a separate root-owned archive. Regenerate the ledger offline with `python3 docs/provenance/refresh_ledger.py`. The historical `run_export.py` command is retained for its source-bound baseline and must not be rerun over those archival outputs. New M3 observations use the separate versioned command documented in `M3-EXPORT.md`, after root confirms compiled readiness. Then refresh the register and use the M3/publication validators documented in `M3-EXPORT.md` with previously unused output paths. The historical baseline validator/report remain archived; its default writer must not overwrite that report. Decode the complete raw export with `gzip -dc docs/provenance/dependency-graph.raw.json.gz`, or the annotated graph with `gzip -dc docs/provenance/dependency-graph.json.gz`; compressed and uncompressed SHA256 values are recorded. Raw export and annotated graph retain every node and edge. Compiled object references bind the exact proof terms without duplicating those binaries.']
 rendered='\n'.join(lines)+'\n'
 if closeout_path.exists():
  rendered=rendered.replace('Clean GitHub CI is pending.', 'Clean final-mode GitHub CI has passed at source `59941e65aece274beb65a3f5c668616a69c0e292`: [run 43568861942](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43568861942), [permanent archive verification](../theorem18/landmarks/github-evidence/run-43568861942/archive-verification.json) and [root closeout](../theorem18/landmarks/milestone3-closeout.json).')
  rendered=rendered.replace('Clean CI was pending when this binding was made and remains a separate root-owned archive.', 'CI was pending at the historical publication-binding timestamp; current clean CI has passed and is bound separately to the permanent archive and closeout. That historical pending record is unchanged.')
 (OUT/'GITHUB-PROOF-SOURCES.md').write_text(rendered)
 print(json.dumps({'accepted_repositories':2,'accepted_module_counts':{c['id']:c['module_count'] for c in cohorts},'search_reports':len(records),'promoted_inventories':len(promoted),'graph_status':ledger['compiled_dependency_graph']['status']}))

if __name__=='__main__': main()
