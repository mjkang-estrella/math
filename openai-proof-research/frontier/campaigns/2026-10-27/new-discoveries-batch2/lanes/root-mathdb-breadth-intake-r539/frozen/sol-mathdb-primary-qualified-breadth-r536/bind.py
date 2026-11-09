import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r535';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def ent(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,e):
 a=ent(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p);return a
refs={}
def add(p,e=None):
 p=p.resolve();a=check(p,e) if e else ent(p);refs[str(p)]=a
# Bind before reading nested references.
add(I/'manifest.json');m=j(I/'manifest.json')
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:add(I/e['path'],e)
add(I/'verification-receipt.json')
for e in j(I/'bindings.json'):
 for k in ['original','copy']:add(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json')
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:add(C/e['path'],e)
for n in ['ledger.json','prior-campaign-context.json']:add(B/n)
for n in ['accepted-exclusions.json','historical-dispositions.json']:add(L/'root-mathdb-accepted-exclusions-r304'/n)
add(L/'root-mathdb-cayley-review-intake-r363/DECISION.md')
# Flat immutable references from the reconciled child; no recursive expansion.
for e in j(L/'sol-mathdb-primary-qualified-breadth-r532/flat-bindings.json'):add(pathlib.Path(e['path']),e)
add(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
cov=j(I/'coverage-delta.json');assert len(cov)==4333
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
ids=set(j(I/'reserved-ids.json')['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue.json')} and len(ids)==50
rows=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:rows.append(dict(mathdb_id=r['mathdb_id'],corpus_chunk=str(p),corpus_line_1based=n,statement=r['statement'],statement_utf8_sha256=hashlib.sha256(r['statement'].encode()).hexdigest(),canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),record=r))
assert len(rows)==50
rows.sort(key=lambda r:j(I/'reserved-ids.json')['ids'].index(r['mathdb_id']))
(P/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(P/'reading.txt').write_text('\n\n'.join(str(r['mathdb_id'])+' '+r['record']['title']+'\n'+r['statement']+'\nSOURCE '+json.dumps({k:v for k,v in r['record'].items() if k not in ['statement','title']},ensure_ascii=False) for r in rows))
print(json.dumps(dict(bindings=len(refs),chunks=20,frozen_inputs=8,records=len(rows),disjoint=True)))
