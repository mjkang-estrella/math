from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r517';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,e):
 a=entry(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
def out(n,x):(P/n).write_text(json.dumps(x,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
# Persist binding before content inspection.
paths=[I/'manifest.json',I/'verification-receipt.json']+[I/e['path'] for e in j(I/'manifest.json')['files']]
refs=[B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'root-mathdb-cayley-review-intake-r363/disposition.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']
out('flat-bindings.json',[entry(p) for p in paths+refs])
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:check(I/e['path'],e)
for e in j(I/'bindings.json'):
 for k in ('original','copy'):check(Path(e[k]),e)
cm=j(C/'manifest.json');check(C/'manifest.json',next(e for e in m['files'] if e['path']=='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'))
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
out('flat-bindings.json',j(P/'flat-bindings.json')+[entry(C/'manifest.json')]+[entry(C/e['path']) for e in chunks+cm['frozen_inputs']]+[entry(Path(e[k])) for e in j(I/'bindings.json') for k in ('original','copy')])
cov=j(I/'coverage-delta.json');assert len(cov)==3983
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
res=j(I/'reserved-ids.json');ids=set(res['ids']);q=j(I/'queue.json');assert ids=={r['mathdb_id'] for r in q} and len(ids)==50
found=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:found.append(dict(mathdb_id=r['mathdb_id'],corpus_chunk=str(p),corpus_line=n,record=r,statement=r['statement'],statement_utf8_sha256=hashlib.sha256(r['statement'].encode()).hexdigest(),canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
assert len(found)==50
out('assigned-records.json',found)
out('initial-verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),intake_payload=True,direct_pairs=len(j(I/'bindings.json')),chunks=20,frozen_inputs=8,baseline=3983,reservation_disjointness=True))
print(json.dumps(dict(records=50,queue_example=q[0],record_example=found[0]),ensure_ascii=False))
