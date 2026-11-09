from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent; B=O.parent;R=B/'root-mathdb-breadth-intake-r397'
def load(p):return json.loads(p.read_text())
a=load(R/'reserved-ids.json');cov=load(R/'coverage-delta.json');q=load(R/'queue.json');ids=set(a['ids']);assert len(ids)==50 and a['lane']==O.name
assert not ids&set(a['other_active_reservations']);assert not ids&{372627,372628,368940};assert len(cov)==1333;assert not ids&set(map(int,cov));assert set(int(x['id']) for x in q)==ids
print('ASSIGNMENT VERIFIED; reviewed disjointness 1333; active 50; special IDs 3')
print('queue first',json.dumps(q[0],ensure_ascii=False))
rows=[]
for p in sorted((B/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for line in p.open():
  d=json.loads(line)
  if int(d['id']) in ids:rows.append(d)
assert len(rows)==50
(O/'statements.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('record keys',list(rows[0]));print('first record',json.dumps(rows[0],ensure_ascii=False))
print('r304 schemas')
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 d=load(B/'root-mathdb-accepted-exclusions-r304'/n);print(n,type(d).__name__,list(d)[:8])
print('cayley disposition', (B/'root-mathdb-cayley-review-intake-r363/disposition.json').read_text())
print('intake decision', (R/'DECISION.md').read_text())
