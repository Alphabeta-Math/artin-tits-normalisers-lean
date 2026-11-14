#!/usr/bin/env python3
"""Source/compiled declaration classification. Reads the repository; writes only the explicit output."""
import argparse,collections,gzip,hashlib,json,re
from pathlib import Path

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def strip_comments_strings(s):
 out=list(s);i=0;depth=0;string=False;line=False
 while i<len(s):
  if line:
   if s[i]=='\n':line=False
   else:out[i]=' '
   i+=1;continue
  if depth:
   if s.startswith('/-',i):out[i:i+2]=[' ',' '];depth+=1;i+=2
   elif s.startswith('-/',i):out[i:i+2]=[' ',' '];depth-=1;i+=2
   else:
    if s[i]!='\n':out[i]=' '
    i+=1
   continue
  if string:
   if s[i]=='\\':
    out[i]=' ';i+=1
    if i<len(s):out[i]=' ';i+=1
   elif s[i]=='"':out[i]=' ';string=False;i+=1
   else:
    if s[i]!='\n':out[i]=' '
    i+=1
   continue
  if s.startswith('--',i):out[i:i+2]=[' ',' '];line=True;i+=2
  elif s.startswith('/-',i):out[i:i+2]=[' ',' '];depth=1;i+=2
  elif s[i]=='"':out[i]=' ';string=True;i+=1
  else:i+=1
 return ''.join(out)
def span(lines,a,b,c,d):
 return lines[a][b:d] if a==c else lines[a][b:]+''.join(lines[a+1:c])+lines[c][:d]
def module_path(base,m):
 for prefix,folder in [('ArtinDeligne','deligne'),('ArtinHomotopy','homotopy'),('ArtinAsphericity','asphericity'),('ArtinSequences','sequences'),('ArtinChambers','chambers'),('ArtinRibbons','ribbons'),('ArtinLandmarks','landmarks'),('ArtinNormalisers',''),('ArtinTheorem18','')]:
  if m==prefix or m.startswith(prefix+'.'):
   p=base/folder/(m.replace('.','/')+'.lean')
   if p.exists():return p
 if m=='ArtinNormalisersFull':return base/'ArtinNormalisersFull.lean'
 raise ValueError('Unmapped module '+m)
def extract(base,graphpath):
 g=json.loads(gzip.decompress(graphpath.read_bytes()))
 roots={n['name']:n for n in g['nodes'] if n['is_project_root']}
 physical={m['module']:m for m in g['physical_project_modules']}
 occurrences=collections.defaultdict(list)
 for m,row in physical.items():
  for n in row['names']:occurrences[n].append(m)
 sources={m:module_path(base,m) for m in physical}
 texts={m:p.read_text().splitlines(keepends=True) for m,p in sources.items()}
 clean={m:strip_comments_strings(''.join(t)).splitlines(keepends=True) for m,t in texts.items()}
 artifacts={a['module']:a for a in g['artifact_paths']}
 written={};modules={};inputs={}
 for m,row in physical.items():
  p=Path(next(q for q in artifacts[m]['object_paths'] if q.endswith('.olean')))
  if not p.is_absolute():p=base/'deligne'/p
  ilean=p.with_suffix('.ilean');data=json.loads(ilean.read_text());inputs[str(ilean)]=sha(ilean)
  modules[m]={'module':m,'source_path':str(sources[m].relative_to(base)),
    'source_sha256':sha(sources[m]),'physical_names':row['names'],
    'direct_imports':data['directImports'],'source_written':[],'generated_or_auxiliary':[]}
  for name,loc in data['decls'].items():
   if name not in roots:continue
   pref=span(clean[m],loc[0],loc[1],loc[4],loc[5])
   token=span(texts[m],loc[4],loc[5],loc[6],loc[7]);plain=token.replace('«','').replace('»','')
   commands=list(re.finditer(r'\b(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\b',pref))
   kind=commands[-1].group() if commands else None
   anonymous_instance=token=='instance' and (kind is None or kind=='instance')
   explicit=((name==plain or name.endswith('.'+plain)) and kind is not None) or anonymous_instance
   if not explicit:continue
   if anonymous_instance:kind='instance'
   private=name.startswith('_private.') or bool(re.search(r'\bprivate\b',pref))
   category=('private-helper' if private else 'theorem-lemma') if kind in ['theorem','lemma'] else (
    'instance' if kind=='instance' else 'structure-inductive' if kind in ['structure','class','inductive'] else 'definition-construction')
   written[name]={'name':name,'module':m,'canonical_module':roots[name]['module'],
    'source_path':str(sources[m].relative_to(base)),'source_sha256':sha(sources[m]),
    'source_keyword':kind,'source_spelling':token,'anonymous_instance':anonymous_instance,
    'private':private,'category':category,'compiled_kind':roots[name]['kind'],
    'source_range':{'basis':'zero-based line and codepoint column; .ilean exact declaration range',
     'start':loc[:2],'end':loc[2:4],'name_start':loc[4:6],'name_end':loc[6:8]},
    'source_declaration':span(texts[m],*loc[:4]),
    'physical_modules':occurrences[name],
    'type_dependencies':roots[name]['type_dependencies'],
    'value_dependencies':roots[name]['value_dependencies'],
    'structural_dependencies':roots[name]['structural_dependencies']}
   modules[m]['source_written'].append(name)
 generated={}
 for name,node in roots.items():
  if name in written:continue
  owners=occurrences[name]
  owner=node['module'] if node['module'] in physical else owners[0]
  generated[name]={'name':name,'module':owner,'canonical_module':node['module'],
    'compiled_kind':node['kind'],'physical_modules':owners,
    'type_dependencies':node['type_dependencies'],'value_dependencies':node['value_dependencies'],
    'structural_dependencies':node['structural_dependencies']}
  for m in owners:modules[m]['generated_or_auxiliary'].append(name)
 assert len(written)==2295 and len(generated)==1999 and set(written)|set(generated)==set(roots)
 counts=collections.Counter(r['category'] for r in written.values())
 family=collections.defaultdict(collections.Counter)
 for r in written.values():family[r['module'].split('.')[0]][r['category']]+=1
 internal_imports=[(m,im[0]) for m,d in modules.items() for im in d['direct_imports'] if im[0] in modules]
 return {'kind':'read-only-navigation-source-classification','graph_path':str(graphpath.relative_to(base)),
   'graph_sha256':sha(graphpath),'counts':{'roots':len(roots),'source_written':len(written),'generated':len(generated),
     'modules':len(modules),'source_categories':dict(counts),'internal_import_edges':len(internal_imports)},
   'counts_by_package':{k:dict(v) for k,v in family.items()},'source_written':written,
   'generated':generated,'modules':modules,'ilean_input_sha256':inputs,
   'classification_limit':'Source syntax categories, not article correspondence; exact semantic proposition flags await metadata reflection.'}
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
 a=p.parse_args();b=a.repo.resolve();result=extract(b,b/'docs/provenance/deligne/run-20261114T132100Z/graph.json.gz')
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 roots=a.output.with_name('roots.json');roots.write_text(json.dumps(sorted([*result['source_written'],*result['generated']]))+'\n')
 print(json.dumps({'counts':result['counts'],'counts_by_package':result['counts_by_package'],'output':str(a.output),'root_list':str(roots)}))
if __name__=='__main__':main()
