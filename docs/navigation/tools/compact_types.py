#!/usr/bin/env python3
"""Lossless shared JSON DAG for reflected types; retain byte-exact raw export gzip."""
import argparse,functools,gzip,hashlib,json,shutil
from pathlib import Path

def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def canonical_sha(v):
 h=hashlib.sha256()
 for part in json.JSONEncoder(ensure_ascii=False,sort_keys=True,separators=(',',':')).iterencode(v):h.update(part.encode())
 return h.hexdigest()
def write_json(p,v):
 with Path(p).open('w') as f:json.dump(v,f,ensure_ascii=False,sort_keys=True,separators=(',',':'));f.write('\n')
def gz(p,q):
 with Path(p).open('rb') as f,Path(q).open('wb') as dest,gzip.GzipFile(filename='',fileobj=dest,mode='wb',mtime=0) as z:shutil.copyfileobj(f,z)
def raw_sha(p):
 h=hashlib.sha256()
 with gzip.open(p,'rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def load(p):
 if str(p).endswith('.gz'):
  with gzip.open(p,'rt') as f:return json.load(f)
 with Path(p).open() as f:return json.load(f)
def expand_factory(table):
 @functools.lru_cache(None)
 def expand(ref):
  tag,data=table[ref]
  if tag=='a':return [expand(i) for i in data]
  if tag=='o':return {k:expand(i) for k,i in data}
  return data
 return expand

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--input',type=Path,required=True);p.add_argument('--check',action='store_true')
 a=p.parse_args();base=a.input.parent
 if a.check:
  data=load(a.input);info=data['type_expression_table'];table=load(base/info['path'])['nodes']
  assert sha(base/info['path'])==info['sha256']
  assert raw_sha(base/data['raw_export']['path'])==data['raw_export']['uncompressed_sha256']
  expand=expand_factory(table)
  for r in data['rows']:assert canonical_sha(expand(r['type_expression_ref']))==r['type_expression_sha256'],r['name']
  print(json.dumps({'ok':True,'lossless_type_ast_roundtrips':len(data['rows']),'shared_nodes':len(table),'raw_bytes_retained':data['raw_export']['uncompressed_bytes']}));return
 original_sha=sha(a.input);original_size=a.input.stat().st_size
 data=load(a.input);assert data['declaration_count']==len(data['rows'])==4294
 nodes=[];ids={}
 def intern(v):
  if isinstance(v,list):key=('a',tuple(intern(x) for x in v))
  elif isinstance(v,dict):key=('o',tuple((k,intern(v[k])) for k in sorted(v)))
  elif v is None:key=('n',None)
  elif isinstance(v,bool):key=('b',v)
  elif isinstance(v,int):key=('i',v)
  elif isinstance(v,float):key=('f',v)
  else:key=('s',v)
  if key in ids:return ids[key]
  n=len(nodes);ids[key]=n;nodes.append([key[0],key[1]]);return n
 for row in data['rows']:
  expr=row.pop('type_expression')
  row['type_expression_sha256']=canonical_sha(expr)
  row['type_expression_ref']=intern(expr)
  row['type_expression_format']='shared-json-dag-v1'
 table_path=base/'type-expressions.json';write_json(table_path,{'schema':'shared-json-dag-v1','nodes':nodes,
   'decoder':'a=list of child IDs; o=ordered key/child-ID pairs; n=null; b=bool; i=int; f=float; s=string. No expression, level, name, syntax or source-info field is discarded.'})
 compressed=Path(str(table_path)+'.gz');gz(table_path,compressed);table_path.unlink()
 raw=base/'statements.raw.json.gz';assert not raw.exists();gz(a.input,raw)
 assert raw_sha(raw)==original_sha
 data['raw_export']={'path':raw.name,'compressed_sha256':sha(raw),'uncompressed_sha256':original_sha,'uncompressed_bytes':original_size}
 data['type_expression_table']={'path':compressed.name,'sha256':sha(compressed),'format':'shared-json-dag-v1','nodes':len(nodes),
   'decoder_tool':'../tools/compact_types.py','lossless':True}
 write_json(a.input,data)
 write_json(base/'compaction-receipt.json',{'ok':True,'raw_export':data['raw_export'],'type_expression_table':data['type_expression_table'],
   'compact_statements_sha256':sha(a.input),'tool_sha256':sha(__file__),'mathematical_verification':False})
 print(json.dumps({'ok':True,'rows':len(data['rows']),'shared_nodes':len(nodes),'compact_statement_bytes':a.input.stat().st_size,
   'shared_table_gzip_bytes':compressed.stat().st_size,'raw_gzip_bytes':raw.stat().st_size,'original_uncompressed_sha256':original_sha}))
if __name__=='__main__':main()
