from pathlib import Path
import json,hashlib
D=Path(__file__).parent;B=D.parent.parent;L=D.parent;C=L/'pi-mathdb-full-corpus-inventory-r301';R=B.parents[3]
paths=[R/'sources/upstream.json',R/'sources/CONTENTS.md',B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',C/'frozen/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',C/'frozen/root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'sol-mathdb-primary-qualified-breadth-r696/failures.json']
a=[]
for p in paths:
 b=p.read_bytes();a.append({'path':str(p.resolve()),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(D/'context-bindings.json').write_text(json.dumps(a,indent=2)+'\n')
ids={str(x['record']['mathdb_id']) for x in json.loads((D/'literal-records.json').read_text())}
for p in paths:
 if p.name in ['accepted-exclusions.json','historical-dispositions.json']:
  obj=json.loads(p.read_text());print(p.name,'top keys',list(obj)[:15])
  def walk(v):
   if isinstance(v,dict):
    if str(v.get('mathdb_id',v.get('id',''))) in ids: print('ASSIGNED MATCH',json.dumps(v))
    else:
     for k,w in v.items():
      if k in ids: print('ASSIGNED MATCH',k,json.dumps(w))
      else: walk(w)
   elif isinstance(v,list):
    for w in v: walk(w)
  walk(obj)
 elif p.name=='upstream.json': print(p.read_text())
 elif p.name=='failures.json': print(p.read_text())
 elif p.name=='ledger.json':
  obj=json.loads(p.read_text()); print('ledger keys',list(obj)[:15]);print('ledger count',len(obj) if isinstance(obj,list) else '')
 elif p.name=='prior-campaign-context.json':
  obj=json.loads(p.read_text());print('prior context keys',list(obj)[:15])
print('No unrelated historical entries displayed; Cayley decision read separately; no accepted-match inferred from tags.')
