#!/usr/bin/env python3
"""Generate the user-requested twenty important dossiers; no Lean proof checks."""
import collections, gzip, hashlib, json, os, re, urllib.parse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'docs/navigation'
def load(p):
 p=Path(p);return json.loads(gzip.decompress(p.read_bytes()) if p.suffix=='.gz' else p.read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def link(page,target):return urllib.parse.quote(os.path.relpath(target,page.parent),safe='/._-')
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def fence(s,lang='text'):
 mark='`'*max(3,max([len(x) for x in re.findall(r'`+',s)]+[0])+1)
 return mark+lang+'\n'+s.rstrip()+'\n'+mark
cfg=load(OUT/'tools/important-projects.json');topics=cfg['topics'];assert len(topics)<=20
inv=load(OUT/'data/source-inventory.json');written=inv['source_written']
statements=load(OUT/'data/statements.json');types={r['name']:r for r in statements['rows']}
graph=load(ROOT/inv['graph_path']);nodes={r['name']:r for r in graph['nodes']}
atlas=load(OUT/'data/attribution/declaration-attribution.json')['declarations']
addendum=load(OUT/'data/important-source-addendum.json');extra={r['topic_id']:r for r in addendum['topics']}
evidence=load(OUT/'data/evidence-atlas.json')['modules']
owner={n:t['id'] for t in topics for n in t['declarations']};assert len(owner)==sum(len(t['declarations']) for t in topics)
paths={t['id']:OUT/'projects'/t['id']/'PROJECT.md' for t in topics}
titles={t['id']:t['title'] for t in topics}
# Collapse implementation helpers to paths between the selected important topics.
edges=set()
for t in topics:
 pending=list(t['declarations']);seen=set()
 while pending:
  n=pending.pop()
  if n in seen:continue
  seen.add(n)
  for d in nodes[n]['type_dependencies']+nodes[n]['value_dependencies']:
   if d in owner:
    if owner[d]!=t['id']:edges.add((owner[d],t['id']))
   elif nodes[d].get('is_project_root'):pending.append(d)
def reachable(a,b,skip=None):
 todo=[a];seen=set()
 while todo:
  n=todo.pop()
  for x,y in edges:
   if (x,y)==skip or x!=n:continue
   if y==b:return True
   if y not in seen:seen.add(y);todo.append(y)
 return False
assert not any(reachable(a,a) for a in paths),'Topic grouping produced a dependency cycle'
reduced={e for e in edges if not reachable(e[0],e[1],e)}
ids={t['id']:'n'+str(i+1) for i,t in enumerate(topics)}
mermaid=['flowchart TD']+[f'  {ids[t["id"]]}["{i+1}. {t["title"]}"]' for i,t in enumerate(topics)]
mermaid+=['  '+ids[a]+' --> '+ids[b] for a,b in sorted(reduced)]
write(OUT/'important-dependencies.mmd','\n'.join(mermaid)+'\n')
write(OUT/'important-dependencies.md','# Important dependencies\n\nTwenty important results and definitions. Arrows summarize checked prerequisite paths through omitted implementation helpers. Redundant transitive arrows are omitted; exact direct edges remain in each dossier’s `dependencies.json`.\n\n```mermaid\n'+'\n'.join(mermaid)+'\n```\n')
def original_sources(topic):
 rows=[]
 for n in topic['declarations']:
  m=atlas.get(n,{})
  if m.get('article') or m.get('alphabeta'):rows.append((n,m))
 if topic.get('source_addendum'):rows.append(('Definition context',extra[topic['source_addendum']]))
 return rows
def render_originals(topic,page):
 rows=original_sources(topic)
 s=['## Original statements','']
 if not rows:
  return '\n'.join(s+['No standalone article or Alphabeta statement is assigned to this local formalization result. It supports [Theorem 1.8, p. 3](https://arxiv.org/pdf/2509.21915v3#page=3) and the finite-arrangement argument in the [proof of Corollary 6.14, p. 27](https://arxiv.org/pdf/2509.21915v3#page=27). These are related target passages, not asserted original counterparts.',''])
 seen=set()
 for member,m in rows:
  s+=['### Source correspondence for `'+member+'`','',f'Relation: **{m.get("mapping_status","related-only")}**.','']
  for key in ['article','alphabeta']:
   sources=m.get(key) or []
   if isinstance(sources,dict):sources=[sources]
   for r in sources:
    signature=json.dumps([key,r],sort_keys=True)
    if signature in seen:continue
    seen.add(signature)
    if key=='article':
     assert r.get('original_label') and r.get('printed_page') and r.get('url')
     s+=['**Article:** ['+r['original_label']+', printed page '+str(r['printed_page'])+']('+r['url']+').','']
     if r.get('normalized_source_statement'):s+=['Normalized mathematical transcription:','',r['normalized_source_statement'],'']
     if r.get('source_excerpt'):s+=['<details><summary>Original article statement extraction</summary>','',fence(r['source_excerpt']),'','</details>','']
    else:
     assert '/item-' in r['url']
     s+=['**Alphabeta Math:** ['+r.get('original_label',r['item_id'])+']('+r['url']+').','']
     if r.get('source_excerpt'):s+=['Original statement Markdown:','',fence(r['source_excerpt'],'text'),'']
    s+=['Scope of this source link: **'+r.get('mapping_status',m.get('mapping_status','related-only'))+'**.','']
    for q in r.get('limits',[]):s+=['- '+q]
    s+=['']
  for k in ['differences','limits']:
   v=m.get(k,[])
   if isinstance(v,str):v=[v]
   s+=['- '+x for x in v]+['']
 return '\n'.join(s)
def evidence_paths(value):
 found=set()
 def walk(x):
  if isinstance(x,dict):
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
  elif isinstance(x,str) and len(x)<600:
   p=x.split('#',1)[0]
   if '/' in p and not Path(p).is_absolute() and '.lake' not in Path(p).parts and (ROOT/p).is_file() and (ROOT/p).stat().st_size<=100*1024*1024:found.add(p)
 walk(value);return found
for t in topics:
 page=paths[t['id']];selected=t['declarations']
 s=['# '+t['title'],'',t['summary'],'',f'Kind: **{t["kind"]}**. Verified source: `theorem-1.8-verified` (`{cfg["proof_commit"]}`).','', '[Important results index]('+link(page,OUT/'index.md')+').','',render_originals(t,page),'## Lean translation and proof files','', 'Statement and proof may share a `.lean` file. The links below identify the exact declaration range; the proof or construction body follows its statement there.','', '| Declaration | Translation file | Proof / construction file |','|---|---|---|']
 depdata={};record_paths=set();module_records={}
 for n in selected:
  r=written[n];src=ROOT/r['source_path'];start=r['source_range']['start'][0]+1;end=r['source_range']['end'][0]+1
  assert sha(src)==r['source_sha256']
  sl=link(page,src)+'#L'+str(start)
  s+=[f'| `{n}` | [`{r["source_path"]}:{start}`]({sl}) | [`{r["source_path"]}:{start}–{end}`]({sl}) |']
  module_records[r['module']]=evidence[r['module']];record_paths|=evidence_paths(evidence[r['module']])
  depdata[n]={}
  for kind in ['type_dependencies','value_dependencies','structural_dependencies']:
   depdata[n][kind]=[{'name':d,'module':nodes[d]['module'],'important_topic':owner.get(d),'project_root':nodes[d].get('is_project_root',False),'source':nodes[d].get('source',{})} for d in nodes[n][kind]]
 s+=['','Rendered checked statements are provided below. Routine implicit proof terms may be suppressed in this view; [exact structural types](types.json) retain the complete expression references, universes and ranges. The linked original Lean files provide the compilable context.','']
 for n in selected:
  r=written[n];s+=['<details><summary>'+n+'</summary>','',fence(types[n]['elaborated_type'],'lean'),'']
  if r['compiled_kind']!='theorem':s+=['Source definition/construction:','',fence(r['source_declaration'],'lean'),'']
  s+=['</details>','']
 prereqs=sorted({a for a,b in reduced if b==t['id']})
 s+=['## Immediate dependencies','', 'Important prerequisite paths:','']+(['- ['+titles[a]+']('+link(page,paths[a])+')' for a in prereqs] if prereqs else ['This entry is foundational within the selected twenty; its external and implementation dependencies remain in the exact record below.'])
 s+=['','[All exact immediate internal and external Lean dependencies](dependencies.json) are recorded separately for each declaration, including type, proof/construction and structural edges, exact source paths and pinned external URLs. The README graph hides implementation helpers and transitive arrows; this record preserves every direct edge.','','## Compilation and verification evidence','', 'The [evidence record](evidence.json) distinguishes historical module verification, final import/build scope and fresh exact-module replays.','']
 s+=['- [`'+p+'`]('+link(page,ROOT/p)+')' for p in sorted(record_paths)]
 s+=['','[Successful final CI](https://github.com/lazyinspirit/artin-tits-normalisers-lean/actions/runs/43599459363). [Source-correspondence review A]('+link(page,OUT/'reviews/source-correspondence-a.md')+') and [review B]('+link(page,OUT/'reviews/source-correspondence-b.md')+').','']
 write(page,'\n'.join(s));write(page.with_name('dependencies.json'),json.dumps(depdata,indent=2,ensure_ascii=False)+'\n')
 write(page.with_name('evidence.json'),json.dumps(module_records,indent=2,ensure_ascii=False)+'\n')
 write(page.with_name('types.json'),json.dumps({'shared_type_table':link(page,OUT/'data/type-expressions.json.gz'),'decoder':link(page,OUT/'tools/show_type.py'),'declarations':{n:types[n] for n in selected}},indent=2,ensure_ascii=False)+'\n')
index=['# Important results and definitions','', 'Twenty focused dossiers cover the mathematical setup, landmark prerequisites and main theorems. Implementation helpers remain in machine-readable provenance.','', '| # | Important result or definition | Role |','|---|---|---|']
index += [f'| {k+1} | [{t["title"]}]('+link(OUT/'index.md',paths[t['id']])+f') | {t["kind"]} |' for k,t in enumerate(topics)]
index+=['','[Dependency graph](important-dependencies.md). [External Lean proofs](external/modules.md). [Verified compilation evidence](data/evidence-atlas.json).','']
write(OUT/'index.md','\n'.join(index))
inputs=['tools/important-projects.json','data/source-inventory.json','data/statements.json','data/attribution/declaration-attribution.json','data/important-source-addendum.json','data/evidence-atlas.json']
record={'kind':'important-documentation-generation','topics':20,'selected_formal_declarations':len(owner),'project_files':[str(p.relative_to(ROOT)) for p in paths.values()],'proof_commit':cfg['proof_commit'],'important_dependency_paths':len(edges),'displayed_reduced_edges':len(reduced),'input_sha256':{p:sha(OUT/p) for p in inputs},'generator_sha256':sha(__file__),'mathematical_proof_changes':False}
write(OUT/'important-generation.json',json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps(record|{'input_sha256':'recorded in important-generation.json','project_files':'20 PROJECT.md files'},indent=2))
