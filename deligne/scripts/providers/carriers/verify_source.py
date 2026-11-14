#!/usr/bin/env python3
"""Check exact preserved sources and the import-only relocation without mutation."""
import hashlib,json,pathlib,re,sys
ROOT=pathlib.Path(__file__).resolve().parents[3]
V=ROOT/'vendor'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((V/'provenance-carriers.json').read_text());r=json.loads((V/'recipe-carriers.json').read_text())
assert p['module_count']==len(p['files'])==len(set(p['topological_order']))==16
assert h(V/p['license_path'])==p['license_sha256']
assert h(V/'recipe-carriers.json')==p['recipe_sha256']
assert h(ROOT/p['assembly_script'])==p['assembly_script_sha256']
for f in p['files']:
 original=V/f['original_path'];active=V/f['path'];patch=V/f['patch_path']
 assert h(original)==f['upstream_sha256'];assert h(active)==f['active_sha256'];assert h(patch)==f['patch_sha256']
 b=original.read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==f['upstream_git_blob_sha']
 expected=re.sub(r'(^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)([\w.\x27]+)',lambda m:m[1]+r['module_mapping'].get(m[2],m[2]),b.decode(),flags=re.M)
 assert active.read_text()==expected,f['module']
for f in p['reused_accepted_modules']:
 assert h(ROOT/f['path_from_package_root'])==f['active_sha256']
print(json.dumps({'ok':True,'new_modules':16,'only_import_relocation':True,'reused_modules':3,'upstream_sha':p['upstream_sha']}))
