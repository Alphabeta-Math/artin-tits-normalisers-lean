#!/usr/bin/env python3
"""Run immutable, scoped carrier supplier checks with exact single-module replay."""
import datetime,hashlib,json,pathlib,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[3];REPO=ROOT.parent;V=ROOT/'vendor'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
P=json.loads((V/'provenance-carriers.json').read_text());MODS=P['topological_order']
def snapshot(artifacts):
 paths={ROOT/'CarrierProviderAudit.lean',V/'provenance-carriers.json',V/'recipe-carriers.json',V/'LICENSE.Colib'}
 paths.update((ROOT/'scripts/providers/carriers').glob('*.py'))
 for f in P['files']:
  paths.update(V/f[k] for k in ['path','original_path','patch_path'])
  if artifacts:
   stem=ROOT/'.lake/build/lib/lean'/f['path'][:-5]
   paths.update(stem.parent.glob(stem.name+'.olean*'))
 for pkg in ['', 'landmarks','ribbons','chambers','sequences','asphericity','homotopy','deligne']:
  base=REPO/pkg
  for n in ['lakefile.toml','lakefile.lean','lean-toolchain','lake-manifest.json']:
   if (base/n).is_file():paths.add(base/n)
  if pkg!='deligne':
   paths.update(p for p in (base/'vendor').rglob('*') if p.is_file())
   if artifacts:paths.update(p for p in (base/'.lake/build/lib/lean').rglob('*.olean*') if p.is_file() and ('Vendor' in str(p) or '/TauCeti/' in str(p)))
 return {str(p.relative_to(REPO)):digest(p) for p in sorted(paths)}
def main():
 phase=sys.argv[1];assert phase in ['build','audit','replay']
 run=ROOT/'evidence/providers/carriers'/(phase+'-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));run.mkdir(parents=True)
 before=snapshot(phase!='build');(run/'inputs-before.json').write_text(json.dumps(before,indent=2)+'\n')
 tools={}
 for name in ['lean','leanchecker']:
  path=pathlib.Path(subprocess.check_output(['lake','env','which',name],cwd=ROOT,text=True).strip());tools[name]={'path':str(path),'sha256':digest(path)}
 mathlib=ROOT/'.lake/packages/mathlib'
 revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip();assert revision==P['target_mathlib']
 record={'ok':False,'phase':phase,'cwd':str(ROOT),'started_at':now(),'modules':MODS,'commands':[],'actual_mathlib_revision':revision,'tools':tools,'concurrency':1,'kernel_scope':'Official exact-module leanchecker, relative to imported pinned Mathlib and accepted supplier contexts; not an independent kernel implementation.','independent_reviews_pending':True,'full_landmark_5_proved':False,'full_theorem_1_8_proved':False}
 commands=[['python3','scripts/providers/carriers/verify_source.py']]
 commands+=([['lake','build',*MODS]] if phase=='build' else [['lake','env','lean','CarrierProviderAudit.lean']] if phase=='audit' else [['lake','env','leanchecker','--verbose',m] for m in MODS])
 out=run/'verification.json';out.write_text(json.dumps(record,indent=2)+'\n')
 for i,cmd in enumerate(commands):
  log=run/f'{i:02d}-{phase}.log';t=time.monotonic()
  with log.open('wb') as stream:result=subprocess.run(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
  row={'command':cmd,'cwd':str(ROOT),'exit_code':result.returncode,'duration_seconds':time.monotonic()-t,'log':log.name,'log_sha256':digest(log)}
  record['commands'].append(row);out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(row),flush=True)
  if result.returncode:break
 after=snapshot(phase!='build');(run/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
 record.update(ended_at=now(),inputs_unchanged=before==after,inputs_before_sha256=digest(run/'inputs-before.json'),inputs_after_sha256=digest(run/'inputs-after.json'))
 record['ok']=len(record['commands'])==len(commands) and all(c['exit_code']==0 for c in record['commands']) and before==after
 out.write_text(json.dumps(record,indent=2)+'\n');print(str(run),flush=True);sys.exit(0 if record['ok'] else 1)
if __name__=='__main__':main()
