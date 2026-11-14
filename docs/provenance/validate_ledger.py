#!/usr/bin/env python3
"""Validate provenance hashes and the complete compiled dependency graph.
This checks record integrity and graph completeness, not mathematical statements.
"""
import gzip,hashlib,json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent

def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 ledger=json.loads((OUT/'GITHUB-PROOF-SOURCES.json').read_text())
 graph_record=ledger['compiled_dependency_graph']
 graph_file=ROOT/graph_record['graph']['path']
 assert sha(graph_file.read_bytes())==graph_record['graph']['sha256']
 data=gzip.decompress(graph_file.read_bytes())
 assert sha(data)==graph_record['uncompressed_graph_sha256']
 g=json.loads(data);nodes={n['name']:n for n in g['nodes']}
 assert len(nodes)==len(g['nodes'])==graph_record['declarations']
 assert len(set(g['roots']))==len(g['roots'])==graph_record['roots']
 assert all(n in nodes and nodes[n]['is_project_root'] for n in g['roots'])
 assert sum(n['is_project_root'] for n in nodes.values())==len(g['roots'])
 total=0
 for node in nodes.values():
  refs=set(node['type_dependencies']+node['value_dependencies']+node['structural_dependencies'])
  assert refs<=nodes.keys(),(node['name'],refs-nodes.keys())
  total+=len(refs)
  assert node['source'] and all(s['repository']!='UNMAPPED' for s in node['source'])
  assert not node['module'].startswith(('ArtinChambers.','ArtinChamberVendor.'))
 assert total==g['edge_count']==graph_record['edge_count']
 assert not graph_record['unmapped_modules']
 execution=json.loads((OUT/'export-execution.json').read_text())
 assert execution['ok'] and execution['inputs_unchanged'] and execution['command']['exit_code']==0
 assert execution['source_configuration_and_record_sha256_before']==execution['source_configuration_and_record_sha256_after']
 assert execution['reachable_compiled_artifacts_sha256_before']==execution['reachable_compiled_artifacts_sha256_after']
 for path,h in execution['source_configuration_and_record_sha256_after'].items():
  assert sha((ROOT/path).read_bytes())==h,path
 raw_record=execution['raw_graph'];raw_file=ROOT/raw_record['path']
 assert sha(raw_file.read_bytes())==raw_record['compressed_sha256']
 raw=gzip.decompress(raw_file.read_bytes());assert sha(raw)==raw_record['uncompressed_sha256']
 original=json.loads(raw)
 for key in ['roots','nodes','declaration_count','edge_count']:
  if key=='nodes':
   # The annotated graph adds only source attribution to otherwise exact nodes.
   stripped=[{k:v for k,v in n.items() if k!='source'} for n in g['nodes']]
   assert original[key]==stripped
  else:assert original[key]==g[key]
 assert sum(c['module_count'] for c in ledger['accepted_cohorts'])==403
 for c in ledger['accepted_cohorts']:
  assert c['verification_ok'] is True
  assert all(r['exit_code']==0 for r in c['verification_commands'])
  for f in c['files']:
   assert sha((ROOT/f['active_path']).read_bytes())==f['active_sha256']
   assert sha((ROOT/f['original_path']).read_bytes())==f['upstream_sha256']
 assert graph_record['scope'].startswith('throughM2')
 cech=next(c for c in ledger['accepted_cohorts'] if c['id']=='landmark3-cech-supplier')
 assert cech['module_count']==9 and cech['included_in_throughM2_dependency_graph'] is False
 assert len(cech['exact_project_or_supplier_declaration_inventory'])==232
 for r in cech['independent_reviews']:
  for field in ['receipt','prose']:
   assert sha((ROOT/r[field]['path']).read_bytes())==r[field]['sha256']
  assert json.loads((ROOT/r['receipt']['path']).read_text())['verdict']=='accept-supplier-cohort'
 assert cech['verification_limits']['build_to_audit_transition']['all_actual_supplier_and_configuration_inputs_match'] is True
 assert len(cech['verification_limits']['build_to_audit_transition']['build_current_metadata_differences'])==2
 for row in ledger['promoted_search_inventories']:
  assert sha((ROOT/row['durable_path']).read_bytes())==row['sha256']
 for row in ledger['search_report_register']:
  b=(ROOT/row['report']['path']).read_bytes()
  assert sha(b)==row['report']['sha256'] and b.decode()==row['full_report_text']
 result={'ok':True,'kind':'provenance-and-graph-integrity-only','declarations':len(nodes),'roots':len(g['roots']),'references':total,'reachable_source_modules':len(graph_record['source_module_records']),'actual_used_modules_by_repository':graph_record['actual_used_modules_by_repository'],'graph_sha256':sha(graph_file.read_bytes()),'ledger_sha256':sha((OUT/'GITHUB-PROOF-SOURCES.json').read_bytes()),'execution_sha256':sha((OUT/'export-execution.json').read_bytes()),'validator_sha256':sha(Path(__file__).read_bytes()),'accepted_vendored_modules':403,'graph_scope':'throughM2 historical graph; current M3 mathematical acceptance and full graph recorded separately, clean CI pending','limits':'Checks hashes and complete graph edges, not mathematical validity, statement correspondence or fresh kernel replay.'}
 (OUT/'validation.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result))
if __name__=='__main__':main()
