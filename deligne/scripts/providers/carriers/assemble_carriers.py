#!/usr/bin/env python3
"""Reproduce the approved import-only Colib carrier cohort from pinned originals."""
import argparse,pathlib,json,hashlib,re,difflib
ROOT=pathlib.Path(__file__).resolve().parents[3]
V=ROOT/'vendor';H=lambda b:hashlib.sha256(b).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--source',type=pathlib.Path,required=True);p.add_argument('--tree',type=pathlib.Path,required=True);p.add_argument('--closure',type=pathlib.Path,required=True);a=p.parse_args()
source=a.source;g=json.loads(a.closure.read_text());tree=json.loads(a.tree.read_text());blob={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
oldp=ROOT.parent/'homotopy/vendor/provenance.json';old=json.loads(oldp.read_text());oldmap={x['upstream_module']:x['module'] for x in old['files']};oldfiles={x['upstream_module']:x for x in old['files']}
new=set(g['new_modules']);mapping={m:m.replace('Colib.','ArtinDeligneVendor.',1) for m in new};mapping.update(oldmap);order=[];seen=set()
def topo(m):
 if m in seen:return
 seen.add(m)
 for d in g['files'][m]['imports']:
  if d in new:topo(d)
 order.append(m)
for root in g['roots']:topo(root)
assert len(order)==16
files=[]
for m in order:
 d=g['files'][m];rel=d['path'];b=(source/rel).read_bytes();assert H(b)==d['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob[rel]
 s=b.decode();out=re.sub(r'(^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)([\w.\x27]+)',lambda z:z[1]+mapping.get(z[2],z[2]),s,flags=re.M);active=out.encode();am=mapping[m];ar=am.replace('.','/')+'.lean';ap=V/ar;ap.parent.mkdir(parents=True,exist_ok=True);ap.write_bytes(active)
 orig='upstream-original/carriers/'+rel+'.txt';op=V/orig;op.parent.mkdir(parents=True,exist_ok=True);op.write_bytes(b)
 patch='patches/carriers/'+ar+'.patch';dp=V/patch;dp.parent.mkdir(parents=True,exist_ok=True);diff=''.join(difflib.unified_diff(s.splitlines(True),out.splitlines(True),fromfile='upstream/'+rel,tofile='active/'+ar));dp.write_text(diff)
 deps=re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.\x27]+)',out,re.M);assert not any(x.startswith('Colib.') for x in deps)
 files.append({'upstream_module':m,'upstream_path':rel,'module':am,'path':ar,'original_path':orig,'patch_path':patch,'upstream_git_blob_sha':blob[rel],'upstream_sha256':H(b),'active_sha256':H(active),'patch_sha256':H(diff.encode()),'lines':len(s.splitlines()),'original_imports':d['imports'],'imports':deps,'full_original_source_read':True,'modifications':'Only import prefixes; all declarations, hypotheses, bodies, namespaces and comments retained byte for byte outside imports.'})
reused=[]
for m in g['reused_modules']:
 f=oldfiles[m];active=ROOT.parent/'homotopy/vendor'/f['path'];orig=ROOT.parent/'homotopy/vendor'/f['original_path'];assert H(active.read_bytes())==f['active_sha256'];assert H(orig.read_bytes())==g['files'][m]['sha256'];reused.append({'upstream_module':m,'module':f['module'],'path_from_package_root':'../homotopy/vendor/'+f['path'],'active_sha256':H(active.read_bytes()),'original_sha256':H(orig.read_bytes()),'acceptance_record':'../docs/provenance/acceptance-homotopy-colib.json'})
license=(source/'LICENSE').read_bytes();(V/'LICENSE.Colib').write_bytes(license)
recipe={'schema':'artin-colib-carriers-import-relocation-v1','repository':'https://github.com/kangxyz/colib','upstream_sha':'bac5cab53eb6526e366e861d289253ec81aa89f0','roots':g['roots'],'module_mapping':{m:mapping[m] for m in g['files']},'new_topological_order':[mapping[m] for m in order],'operation':'Replace ONLY imports of selected new modules with ArtinDeligneVendor and accepted old modules with ArtinHomotopyVendor; namespaces/types/proofs unchanged.','files':files};(V/'recipe-carriers.json').write_text(json.dumps(recipe,indent=2)+'\n')
prov={'schema':'artin-colib-carriers-provider-v1','repository':'https://github.com/kangxyz/colib','upstream_sha':'bac5cab53eb6526e366e861d289253ec81aa89f0','upstream_license':'Apache-2.0','license_path':'LICENSE.Colib','license_sha256':H(license),'upstream_toolchain':'leanprover/lean4:v4.35.0','upstream_mathlib':'56a005855ea17e0b0958f73ec801ae140b0a1679','target_toolchain':'leanprover/lean4:v4.36.0-rc2','target_mathlib':'65d730f7150f21fdfa32f3e73a3f549c1f96a0e9','roots':[mapping[m] for m in g['roots']],'topological_order':[mapping[m] for m in order],'module_count':16,'source_lines':sum(x['lines'] for x in files),'complete_colib_closure_modules':19,'reused_accepted_modules':reused,'files':files,'assembly_script':'scripts/providers/carriers/assemble_carriers.py','assembly_script_sha256':H(pathlib.Path(__file__).read_bytes()),'recipe':'vendor/recipe-carriers.json','recipe_sha256':H((V/'recipe-carriers.json').read_bytes()),'selection_status':'Prospective cohort. Acceptance requires separate actual compilation, std3 axiom/physical coverage, exact module replay and independent semantic review.','source_ports':'Only mechanical import-prefix changes; no compatibility proof ports yet.','full_landmark_5_proved':False,'full_theorem_1_8_proved':False,'actual_acyclic_carrier_theorem_proved':False,'intended_applications':['Actual simplex-boundary HEP from explicit radial retraction','Actual side-and-two-caps cylinder boundary HEP','Continuous geometric boundary-track gluing from double-face equations','Local generic contractible-target extension/client carrier induction; no desired filler assumed']};(V/'provenance-carriers.json').write_text(json.dumps(prov,indent=2)+'\n');print('Staged',len(files),'modules',prov['source_lines'],'lines; reused',len(reused));print('\n'.join(prov['topological_order']))
