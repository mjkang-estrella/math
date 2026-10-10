"""Create the one I151 seal from a successful read-only prevalidation on stdin.
Does not traverse the corpus, run any diagnostic, repair, or reseal.
"""
from pathlib import Path
import json,sys,hashlib,datetime
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i151_spatial_dynamical_percolation_continuation'
E='frontier/experiments/i151_spatial_dynamical_percolation_continuation'
REPORT='frontier/iterations/i151-spatial-dynamical-percolation-continuation.md'
p=ROOT/S/'seal.json'
assert not p.exists(),'one seal only'
r=json.load(sys.stdin)
assert r['preseal'] and r['evidence_status']=='PASS' and r['all_immutable_bytes_before_diagnostics'] and r['corpus_traversals']==1
rows=r['files'];paths=[x['path'] for x in rows]
actual={REPORT}
for root in (S,E):
 for q in (ROOT/root).rglob('*'):
  assert not q.is_symlink()
  if q.is_file():actual.add(str(q.relative_to(ROOT)))
assert paths==sorted(set(paths)) and set(paths)==actual
for x in rows:
 b=(ROOT/x['path']).read_bytes();assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256'],x['path']
digest=hashlib.sha256(json.dumps(rows,sort_keys=True,separators=(',',':')).encode()).hexdigest()
assert digest==r['validated_inventory_sha256']
seal={'schema':'i151-exact-owned-v1','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','roots':[REPORT,S+'/',E+'/'],'files':rows,'validated_inventory_sha256':digest,'task_status':r['task_status'],'original_I149_task_status':'INCOMPLETE','original_I149_evidence_status':'PASS','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'prevalidation':{k:v for k,v in r.items() if k!='files'},'scope':r['certifies']}
b=(json.dumps(seal,ensure_ascii=False,sort_keys=True,indent=2)+'\n').encode()
with p.open('xb') as f:f.write(b)
assert p.read_bytes()==b
print(json.dumps({'seal_sha256':hashlib.sha256(b).hexdigest(),'owned_files_excluding_seal':len(rows),'validated_inventory_sha256':digest,'seal_created_once':True,'post_prevalidation_owned_bytes_unchanged':True,'corpus_not_retraversed_by_sealer':True},sort_keys=True))
