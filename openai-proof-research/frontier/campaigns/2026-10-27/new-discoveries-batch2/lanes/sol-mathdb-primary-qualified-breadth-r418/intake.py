from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent;I=L/'root-mathdb-breadth-intake-r417'
r=json.loads((I/'reserved-ids.json').read_text());ids=set(map(str,r['ids']));other=set(map(str,r['other_active_reservations']));old=set(json.loads((I/'coverage-delta.json').read_text()));queue=json.loads((I/'queue.json').read_text())
assert len(ids)==50 and len(other)==50 and len(old)==1833
assert ids=={str(x['mathdb_id']) for x in queue}
assert not ids&(other|old|{'372627','372628','368940'})
found={}
C=L/'pi-mathdb-full-corpus-inventory-r301'
for e in json.loads((C/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 with (C/e['path']).open() as f:
  for line in f:
   x=json.loads(line);n=str(x['mathdb_id'])
   if n in ids:
    assert n not in found;found[n]=x
assert set(found)==ids
(R/'assignment-check.json').write_text(json.dumps({'assigned_ids':sorted(ids),'assigned_count':50,'other_reserved_count':50,'reviewed_count':1833,'exact_queue_match':True,'disjoint':True,'forbidden_ids':['372627','372628','368940'],'other_reserved_statements_inspected':False},indent=2)+'\n')
# Assigned record extraction only; no corpus/history copies.
(R/'selected-records.json').write_text(json.dumps([found[str(x['mathdb_id'])] for x in queue],ensure_ascii=False,indent=2)+'\n')
for x in queue:
 z=found[str(x['mathdb_id'])];print(json.dumps(z,ensure_ascii=False))
