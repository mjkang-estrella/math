import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent; L=P.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r589'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def binding(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
refs={}
def bind(p,sha=None,size=None):
 e=binding(p);assert sha is None or e['sha256']==sha,str(p);assert size is None or e['size']==size,str(p);refs[str(p)]=e
bind(I/'manifest.json','f113bfb809c174de3bf97a7101fde67845574bcfcfb4f8d70b4f75d40300ecbd',10560)
m=load(I/'manifest.json'); actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}
assert actual=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:bind(I/e['path'],e['sha256'],e['size'])
bind(I/'verification-receipt.json','16cb7794f2223514daf6d69eacf7c73f0ac32cf7f2fecaed2957f3afb6cdbc62',509)
for e in load(I/'bindings.json'):
 for k in ['original','copy']:bind(pathlib.Path(e[k]),e['sha256'],e['size'])
inv=load(C/'manifest.json')
chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
assert len(inv['frozen_inputs'])==8
for e in chunks+inv['frozen_inputs']:bind(C/e['path'],e['sha256'],e['bytes'])
# Flat additional context references: bind before reading.
contexts=[B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'sol-mathdb-primary-qualified-breadth-r578/failures.json']
contexts+=list(L.glob('*r363/DECISION.md'))
contexts+=[L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']
for p in contexts:bind(p)
r=load(I/'reserved-ids.json');q=load(I/'queue.json');covered=load(I/'coverage-delta.json');active=load(I/'active-breadth-reservations.json')
assert len(covered)==5683
assigned=set(r['ids']);assert len(assigned)==50 and assigned=={x['mathdb_id'] for x in q}
sets=[set(x['ids']) for x in active if set(x['ids'])!=assigned]+[assigned]
for i,s in enumerate(sets):
 assert not s.intersection(map(int,covered));assert not s.intersection(r['protected_ids'])
 for t in sets[:i]:
  assert not s&t
assert set(r['other_active_reservations'])==set().union(*sets[:-1])
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'binding-receipt.json').write_text(json.dumps(dict(intake_exact_payload=True,direct_original_copy_pairs=len(load(I/'bindings.json')),chunks_in_place=20,frozen_inputs_in_place=8,baseline_record_reviews=5683,assigned=50,all_reservations_disjoint=True,context_paths=[str(p) for p in contexts]),indent=2)+'\n')
print('BOUND',len(refs),'files; 20 chunks, 8 inputs, 50 assigned')
# Read assigned literal records only now.
rows=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  o=json.loads(line)
  if o.get('mathdb_id',o.get('id')) in assigned:
   rows.append(dict(chunk=str(p),line=n,record=o,canonical_record_sha256=hashlib.sha256(json.dumps(o,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
assert len(rows)==50
(P/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('RECORD KEYS',rows[0]['record'].keys())
