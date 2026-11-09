import pathlib,json,hashlib,datetime
O=pathlib.Path(__file__).resolve().parent;L=O.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r587';C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def rec(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,e):
 r=rec(p);assert r['size']==e.get('size',e.get('bytes')) and r['sha256']==e['sha256'],str(p);return r
flat=load(O/'initial-bindings.json')['files'][:]
for e in load(I/'manifest.json')['files']:flat.append(check(I/e['path'],e))
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in load(I/'manifest.json')['files']}|{'manifest.json','verification-receipt.json'}
for e in load(I/'bindings.json'):
 for k in ['original','copy']:flat.append(check(pathlib.Path(e[k]),e))
m=load(C/'manifest.json');chunks=[e for e in m['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(m['frozen_inputs'])==8
for e in chunks+m['frozen_inputs']:flat.append(check(C/e['path'],e))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'sol-mathdb-primary-qualified-breadth-r578/failures.json',L/'sol-mathdb-primary-qualified-breadth-r542/failures.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 flat.append(rec(p))
(O/'flat-bindings.json').write_text(json.dumps(list({r['path']:r for r in flat}.values()),indent=2)+'\n')
ids=set(load(I/'reserved-ids.json')['ids']);cov=load(I/'coverage-delta.json');assert len(cov)==5633
assert ids=={r['mathdb_id'] for r in load(I/'queue.json')} and len(ids)==50
sets=[]
for r in load(I/'active-breadth-reservations.json'):
 s=set(r['ids']);assert len(s)==50 and not s&set(map(int,cov)) and not s&set(r['protected_ids']);assert all(not s&t for t in sets);sets.append(s)
rows=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('id',r.get('mathdb_id')) in ids:
   rows.append(dict(corpus_chunk=str(p),line=n,record=r,canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
assert len(rows)==50
(O/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(O/'binding-receipt.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),original_chunks_checked=20,frozen_inputs_checked=8,baseline=5633,assignment=50,active_disjoint_sets=3,intake_exact_payload=True,direct_pairs_checked=len(load(I/'bindings.json'))),indent=2)+'\n')
print('BOUND; record keys:',rows[0]['record'].keys())
print('PRIOR CONTEXT')
for p in [I/'adjudications.json',I/'hypothesis-queue.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'sol-mathdb-primary-qualified-breadth-r578/failures.json',L/'sol-mathdb-primary-qualified-breadth-r542/failures.md']:
 print(p.name,p.read_text())
print('LEDGER', (B/'ledger.json').read_text()[:1500]);print('PRIOR',(B/'prior-campaign-context.json').read_text()[:2000])
