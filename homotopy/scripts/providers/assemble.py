#!/usr/bin/env python3
"""Reproduce exact upstream files with only selected import module relocations."""
import pathlib,json,re,difflib,sys,hashlib
ROOT=pathlib.Path(__file__).resolve().parents[2]
VENDOR=ROOT/'vendor'
def main():
 recipe=json.loads((VENDOR/'import-relocation-recipe.json').read_text())
 for row in recipe['files']:
  original=(VENDOR/row['original_path']).read_text()
  def relocate(match):
   return match[1]+recipe['module_relocations'].get(match[2],match[2])+match[3]
  active=re.sub(r'(?m)^((?:(?:public|private) )?import[ \t]+)([^ \t\n]+)([^\n]*)$',relocate,original)
  patch=''.join(difflib.unified_diff(original.splitlines(keepends=True),active.splitlines(keepends=True),fromfile=row['upstream_path'],tofile=row['path']))
  for relative,content in [(row['path'],active),('patches/'+row['path']+'.patch',patch)]:
   path=VENDOR/relative
   if '--check' in sys.argv:
    assert path.read_text()==content, 'Mechanical assembly mismatch: '+str(path)
   else:
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(content)
 print('Exact import-only assembly verified for '+str(len(recipe['files']))+' modules')
if __name__=='__main__':main()
