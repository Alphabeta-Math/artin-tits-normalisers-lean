#!/usr/bin/env python3
"""Reproduce upstream files with selected imports and explicit recorded compatibility blocks."""
import pathlib,json,re,difflib,sys,hashlib
ROOT=pathlib.Path(__file__).resolve().parents[3]
VENDOR=ROOT/'vendor'
def main():
 recipe=json.loads((VENDOR/'weights-recipe.json').read_text())
 for row in recipe['files']:
  original=(VENDOR/row['original_path']).read_text()
  def relocate(match):
   return match[1]+recipe['module_relocations'].get(match[2],match[2])+match[3]
  active=re.sub(r'(?m)^((?:(?:public|private) )?import[ \t]+)([^ \t\n]+)([^\n]*)$',relocate,original)
  for port in row.get('compatibility_replacements',[]):
   assert hashlib.sha256(port['old_text'].encode()).hexdigest()==port['old_sha256']
   assert hashlib.sha256(port['new_text'].encode()).hexdigest()==port['new_sha256']
   assert active.count(port['old_text'])==1, 'Compatibility source block mismatch'
   active=active.replace(port['old_text'],port['new_text'])
  patch=''.join(difflib.unified_diff(original.splitlines(keepends=True),active.splitlines(keepends=True),fromfile=row['upstream_path'],tofile=row['path']))
  for relative,content in [(row['path'],active),(row['patch_path'],patch)]:
   path=VENDOR/relative
   if '--check' in sys.argv:
    assert path.read_text()==content, 'Mechanical assembly mismatch: '+str(path)
   else:
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(content)
 print('Exact import/recorded-port assembly verified for '+str(len(recipe['files']))+' modules')
if __name__=='__main__':main()
