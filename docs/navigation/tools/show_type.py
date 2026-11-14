#!/usr/bin/env python3
"""Read one exact reflected type from the lossless shared table; no Lean execution."""
import argparse,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
from compact_types import load,expand_factory,canonical_sha,sha

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--name',required=True);p.add_argument('--rendered',action='store_true')
 a=p.parse_args();base=Path(__file__).resolve().parent.parent/'data';data=load(base/'statements.json')
 row=next((r for r in data['rows'] if r['name']==a.name),None)
 if row is None:raise SystemExit('Unknown compiled project root')
 if a.rendered:
  print('Rendered view only; not asserted independently compilable. Full structural type remains authoritative.\n'+row['elaborated_type']);return
 info=data['type_expression_table'];table_path=base/info['path']
 assert sha(table_path)==info['sha256']
 expr=expand_factory(load(table_path)['nodes'])(row['type_expression_ref'])
 assert canonical_sha(expr)==row['type_expression_sha256']
 print(json.dumps({'name':row['name'],'universe_parameters':row['universe_parameters'],
   'type_expression':expr,'declaration_ranges':row['declaration_ranges'],
   'type_expression_sha256':row['type_expression_sha256']},indent=2,ensure_ascii=False))
if __name__=='__main__':main()
