#!/usr/bin/env python3
"""Validate curated navigation and source identity, without running Lean."""
import gzip, hashlib, json, re, subprocess, urllib.parse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];NAV=ROOT/'docs/navigation'
def load(p):
 p=Path(p);return json.loads(gzip.decompress(p.read_bytes()) if p.suffix=='.gz' else p.read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
cfg=load(NAV/'tools/important-projects.json');topics=cfg['topics'];assert len(topics)==20
inv=load(NAV/'data/source-inventory.json');st={r['name']:r for r in load(NAV/'data/statements.json')['rows']}
g=load(ROOT/inv['graph_path']);nodes={r['name']:r for r in g['nodes']}
expected={NAV/'projects'/t['id']/'PROJECT.md' for t in topics}
assert set(NAV.rglob('PROJECT.md'))==expected,'Catalog must contain only twenty PROJECT.md files'
main=(ROOT/'README.md').read_text();diagram=(NAV/'important-dependencies.mmd').read_text()
assert diagram.strip() in main and len(re.findall(r'^  n\d+\[',diagram,re.M))==20
assert '2295' not in main and '2,295' not in main and 'FULL-SOURCE-MODULE-GRAPH' not in main
for r in inv['modules'].values():
 p=ROOT/r['source_path'];assert sha(p)==r['source_sha256']
 blob=subprocess.check_output(['git','cat-file','blob',cfg['proof_commit']+':'+r['source_path']],cwd=ROOT)
 assert hashlib.sha256(blob).hexdigest()==r['source_sha256']
formal=0;edges=0
for t in topics:
 p=NAV/'projects'/t['id']/'PROJECT.md';text=p.read_text();d=load(p.with_name('dependencies.json'));types=load(p.with_name('types.json'))['declarations'];ev=load(p.with_name('evidence.json'))
 assert 'Translation file | Proof / construction file' in text and 'Compilation and verification evidence' in text
 for n in t['declarations']:
  r=inv['source_written'][n];assert n in text and r['source_path'] in text and types[n]==st[n]
  assert r['module'] in ev
  for k in ['type_dependencies','value_dependencies','structural_dependencies']:
   assert [x['name'] for x in d[n][k]]==nodes[n][k];edges+=len(d[n][k])
  formal+=1
for who in ['a','b']:
 r=load(NAV/f'reviews/source-correspondence-{who}.json');assert r['verdict']=='accept-source-correspondence'
scoped={ROOT/'README.md',ROOT/'docs/history/README.md',NAV/'index.md',NAV/'important-dependencies.md',NAV/'tools/README.md',NAV/'external/modules.md',NAV/'external/README-table.md',*expected,*NAV.glob('source-notes/*.md')}
links=0
for p in scoped:
 base=ROOT if p.name=='README-table.md' else p.parent
 lines=[];fence=0
 for line in p.read_text().splitlines():
  m=re.match(r'^\s*(`{3,})',line)
  if m:
   q=len(m.group(1))
   if fence and q>=fence:fence=0
   elif not fence:fence=q
   continue
  if not fence:lines.append(line)
 for raw in re.findall(r'\]\(([^\s)]+)\)', '\n'.join(lines)):
  if re.match(r'^[A-Za-z][A-Za-z0-9+.-]*:',raw) or raw.startswith('#'):continue
  target=(base/urllib.parse.unquote(raw.split('#',1)[0])).resolve()
  assert target.exists(),f'Broken link: {p.relative_to(ROOT)} -> {raw}'
  if target.suffix=='.lean' and '#L' in raw:
   ln=int(raw.split('#L',1)[1].split('-')[0]);assert 1<=ln<=len(target.read_text().splitlines())
  links+=1
old=ROOT/'docs/history/README-before-navigation.md.txt';assert sha(old)==hashlib.sha256(subprocess.check_output(['git','cat-file','blob',cfg['proof_commit']+':README.md'],cwd=ROOT)).hexdigest()
record={'ok':True,'scope':'Curated documentation metadata validation; no Lean build/audit/replay','important_topics':20,'project_files':20,'key_formal_declarations':formal,'exact_direct_edge_occurrences':edges,'readme_graph_nodes':20,'local_links_checked':links,'unchanged_scientific_source_modules':len(inv['modules']),'proof_commit':cfg['proof_commit'],'generator_sha256':sha(NAV/'tools/generate_important_projects.py'),'generation_record_sha256':sha(NAV/'important-generation.json'),'readme_sha256':sha(ROOT/'README.md'),'independent_source_reviews_sha256':{str((NAV/f'reviews/source-correspondence-{w}.json').relative_to(ROOT)):sha(NAV/f'reviews/source-correspondence-{w}.json') for w in ['a','b']}}
out=ROOT/'docs/navigation-validation.json';out.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');print(json.dumps(record,indent=2))
