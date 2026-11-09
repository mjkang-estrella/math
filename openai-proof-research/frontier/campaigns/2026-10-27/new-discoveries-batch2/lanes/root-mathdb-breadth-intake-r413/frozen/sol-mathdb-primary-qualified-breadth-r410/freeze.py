from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent; B=L.parent; R=B.parents[4]
I=B/'root-mathdb-breadth-intake-r409'
def ref(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
paths=list(I.rglob('*'))
refs=[ref(p) for p in paths if p.is_file()]
extra=[B/'pi-mathdb-full-corpus-inventory-r301/manifest.json',B/'root-mathdb-cayley-review-intake-r363/disposition.json']
refs += [ref(p) for p in extra]
(L/'bindings-initial.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'refs':refs,'policy':'flat refs only; upstream read-only; no upstream receipt writer'},indent=2)+'\n')
print('Frozen',len(refs),'files before scientific content')
for n in ['bindings.json','manifest.json','reserved-ids.json','queue.json']:
 d=json.loads((I/n).read_text());print(n,json.dumps(d)[:14000])
print('r301 manifest', (extra[0]).read_text()[:5000])
