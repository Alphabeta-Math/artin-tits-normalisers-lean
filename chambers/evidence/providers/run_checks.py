#!/usr/bin/env python3
"""Actual source-bound checks, without package/cache cleanup or updates."""
import datetime,hashlib,json,pathlib,subprocess,time,sys,os
ROOT=pathlib.Path(__file__).resolve().parents[2]
REPO=ROOT.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def snapshot(artifacts=False):
 paths=set(ROOT.glob('vendor/**/*'));paths={p for p in paths if p.is_file()}
 paths.add(ROOT/'ProviderAudit.lean');paths.add(pathlib.Path(__file__).resolve())
 for parent in [REPO,REPO/'ribbons',REPO/'landmarks',ROOT]:
  for n in ['lakefile.toml','lakefile.lean','lean-toolchain','lake-manifest.json']:
   p=parent/n
   if p.is_file():paths.add(p)
 for parent in [REPO/'vendor',REPO/'ribbons/vendor',REPO/'landmarks/vendor']:
  paths.update(p for p in parent.glob('**/*') if p.is_file())
 if artifacts:
  for base in [REPO,REPO/'ribbons',REPO/'landmarks',ROOT]:
   for p in (base/'.lake/build/lib/lean').glob('**/*.olean*'):
    if p.is_file() and any(part in {'TauCeti','OAI','ArtinChamberVendor'} for part in p.parts):paths.add(p)
 return {str(p.relative_to(REPO)):H(p) for p in sorted(paths)}
phase=sys.argv[1];run=ROOT/'evidence/providers'/(phase+'-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));run.mkdir()
p=json.loads((ROOT/'vendor/provenance.json').read_text());mods=p['topological_order'];before=snapshot(phase!='build');(run/'inputs-before.json').write_text(json.dumps(before,indent=2)+'\n')
record={'ok':False,'phase':phase,'cwd':str(ROOT),'started_at':now(),'modules':mods,'commands':[],'full_landmark_3_proved':False,'scope':'Nine newly relocated TauCeti provider modules; relative to imported Mathlib and accepted parent providers. No independent kernel implementation.'}
(run/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
commands=([['lake','build',*mods]] if phase=='build' else [['lake','env','lean','ProviderAudit.lean']] if phase=='audit' else [['lake','env','leanchecker','--verbose',m] for m in mods])
for i,cmd in enumerate(commands):
 log=run/(f'{i:02d}-'+phase+'.log');start=time.monotonic()
 with log.open('wb') as f:
  result=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
 row={'command':cmd,'cwd':str(ROOT),'exit_code':result.returncode,'duration_seconds':time.monotonic()-start,'log':log.name,'log_sha256':H(log)};record['commands'].append(row);(run/'verification.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(row),flush=True)
 if result.returncode:break
after=snapshot(phase!='build');(run/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n');record.update({'ended_at':now(),'inputs_unchanged':before==after,'inputs_before_sha256':H(run/'inputs-before.json'),'inputs_after_sha256':H(run/'inputs-after.json'),'ok':len(record['commands'])==len(commands) and all(x['exit_code']==0 for x in record['commands']) and before==after});(run/'verification.json').write_text(json.dumps(record,indent=2)+'\n');print(str(run),flush=True);sys.exit(0 if record['ok'] else 1)
