import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parents[1]
(L/'context').mkdir(exist_ok=True)
out=[]
for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
 b=(B/n).read_bytes();(L/'context'/n).write_bytes(b)
 out.append(dict(name=n,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),role='mutable continuation context excluded from scientific freeze' if n=='NEXT.md' else 'as-read campaign context'))
 if n.endswith('.json'):
  j=json.loads(b)
  for key in ['accepted','excluded','held_candidates','candidates']:
   if key in j:
    print(n,key)
    for x in j[key]:print(json.dumps({k:x[k] for k in ['number','id','title','name','status'] if k in x},ensure_ascii=False))
(L/'context-reading.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),receipts=out),indent=2)+'\n')
