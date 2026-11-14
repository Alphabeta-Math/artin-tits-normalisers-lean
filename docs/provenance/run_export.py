#!/usr/bin/env python3
"""Observe accepted compiled roots, bind inputs, and retain complete dependency data.
Run after old accepted contexts have been built; does not build, clean, update,
replay, accept or mutate any scientific proof/configuration.
"""
from __future__ import annotations
import datetime as dt, gzip, hashlib, json, os, shutil, subprocess, time
from pathlib import Path
BASE=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
LAKE=shutil.which('lake') or str(Path.home()/'.elan/bin/lake')

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def utc():return dt.datetime.now(dt.timezone.utc).isoformat()
def dump(p,d):p.write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
def main():
 ledger=json.loads((OUT/'GITHUB-PROOF-SOURCES.json').read_text())
 paths=set()
 for c in ledger['accepted_cohorts']:
  for r in c['files']:paths.update([r['active_path'],r['original_path']])
  for field in ['provenance','source_inventory','verification']:paths.add(c[field]['path'])
  inv=json.loads((BASE/c['source_inventory']['path']).read_text())
  paths.update(inv.get('project_source_sha256',{}))
  paths.update(inv.get('configuration_sha256',{}))
  for p in c['license_files']:paths.add(p['path'])
  if c['id']=='landmark2-positive':paths.update(inv.get('provider_compatibility_patch_sha256',{}))
 for prefix in ['', 'landmarks/', 'ribbons/', 'chambers/']:
  for leaf in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
   if (BASE/(prefix+leaf)).exists():paths.add(prefix+leaf)
 paths.update(['docs/provenance/ExportDependencies.lean','docs/provenance/run_export.py'])
 source_before={p:sha(BASE/p) for p in sorted(paths)}
 # A prior observation supplies exactly the object paths to bind before rerun.
 raw=OUT/'dependency-graph.raw.json'
 if raw.exists():prior=json.loads(raw.read_text())
 else:prior=json.loads(gzip.decompress((OUT/'dependency-graph.raw.json.gz').read_bytes()))
 reachable={n['module'] for n in prior['nodes']}
 search_command=[LAKE,'env','printenv','LEAN_PATH']
 search_text=subprocess.check_output(search_command,cwd=BASE/'chambers',text=True).strip()
 search_paths=[Path(p) if Path(p).is_absolute() else BASE/'chambers'/p for p in search_text.split(os.pathsep)]
 objects={}
 for module in sorted(reachable):
  relative=module.replace('.','/')+'.olean'
  file=next((p/relative for p in search_paths if (p/relative).is_file()),None)
  if file is None:raise RuntimeError(f'Missing current compiled module: {module}')
  for p in [file,Path(str(file)+'.server'),Path(str(file)+'.private')]:
   if p.is_file():objects[str(p.resolve())]=sha(p)
 record={'kind':'read-only-compiled-proof-dependency-observation','started_at':utc(),'repository_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=BASE,text=True).strip(), 'source_configuration_and_record_sha256_before':source_before,'reachable_compiled_artifacts_sha256_before':objects,'current_lean_path_resolution':{'argv':search_command,'exit_code':0,'stdout':search_text},
  'lean_version':subprocess.check_output([LAKE,'env','lean','--version'],cwd=BASE/'chambers',text=True).strip(),'limitations':['Observes compiled expressions, not a new proof acceptance, statement review or kernel replay.','All accepted project roots selected by exact defining-module families; currently staged M3 sources are not imported.','No claim of manual reading of all suppliers or fresh rechecking of all mathlib.']}
 cmd=[LAKE,'env','lean','../docs/provenance/ExportDependencies.lean']
 t=time.monotonic()
 with (OUT/'export-final.log').open('wb') as stream:
  p=subprocess.run(cmd,cwd=BASE/'chambers',stdout=stream,stderr=subprocess.STDOUT,env={**os.environ,'GITHUB_PROOF_GRAPH_OUT':str(raw)})
 record['command']={'argv':cmd,'cwd':'chambers','exit_code':p.returncode,'elapsed_seconds':round(time.monotonic()-t,6),'log':'docs/provenance/export-final.log','log_sha256':sha(OUT/'export-final.log')}
 record['source_configuration_and_record_sha256_after']={p:sha(BASE/p) for p in sorted(paths)}
 record['reachable_compiled_artifacts_sha256_after']={p:sha(p) for p in objects}
 record['inputs_unchanged']=record['source_configuration_and_record_sha256_after']==source_before and record['reachable_compiled_artifacts_sha256_after']==objects
 record['ok']=p.returncode==0 and record['inputs_unchanged']
 record['finished_at']=utc()
 if p.returncode==0:
  b=raw.read_bytes(); gz=OUT/'dependency-graph.raw.json.gz'
  with gzip.GzipFile(filename=str(gz),mode='wb',mtime=0) as stream:stream.write(b)
  record['raw_graph']={'path':'docs/provenance/dependency-graph.raw.json.gz','compressed_sha256':sha(gz),'uncompressed_sha256':hashlib.sha256(b).hexdigest(),'uncompressed_bytes':len(b),'decoder':'gzip -dc docs/provenance/dependency-graph.raw.json.gz'}
 dump(OUT/'export-execution.json',record)
 print(json.dumps({'ok':record['ok'],'exit_code':p.returncode,'inputs_unchanged':record['inputs_unchanged'],'bound_source_inputs':len(paths),'bound_artifacts':len(objects)}))
 if not record['ok']:return 1
 return 0
if __name__=='__main__':raise SystemExit(main())
