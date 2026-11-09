import json,hashlib,pathlib
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent; I=L.parent/'root-mathdb-breadth-intake-r595'; refs={}
def bind(p,expected=None):
 p=pathlib.Path(p); b=p.read_bytes(); r={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
 if expected: assert all(r[k]==expected[k] for k in ('sha256','size')),str(p)
 refs[str(p)]=r; return r
def load(p): return json.loads(pathlib.Path(p).read_text())
for n in ['manifest.json','bindings.json','coverage-delta.json','queue.json','reserved-ids.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','active-breadth-reservations.json']:bind(I/n)
m=load(I/'manifest.json'); expected={r['path'] for r in m['files']}; actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']); assert actual==expected
for r in m['files']:bind(I/r['path'],r)
for r in load(I/'bindings.json'):
 bind(r['original'],r);bind(r['copy'],r);assert pathlib.Path(r['original']).read_bytes()==pathlib.Path(r['copy']).read_bytes()
# Bind inventory itself first, then inspect schema only.
R=L.parent/'pi-mathdb-full-corpus-inventory-r301'; inv=load(R/'manifest.json')
print('INVENTORY KEYS',list(inv)); print(json.dumps(inv,ensure_ascii=False)[:5500])
(L/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
print('QUEUE SCHEMA',str(load(I/'queue.json'))[:1500]);print('RESERVATIONS',str(load(I/'reserved-ids.json'))[:3000])
chunks=[r for r in inv['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
for r in chunks+inv['frozen_inputs']:bind(R/r['path'],{'sha256':r['sha256'],'size':r['bytes']})
for n in ['ledger.json','prior-campaign-context.json']:bind(B/n)
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md','sol-mathdb-primary-qualified-breadth-r578/failures.json','sol-mathdb-primary-qualified-breadth-r542/failures.md'] :bind(L.parent/rel)
res=load(I/'reserved-ids.json');ids=set(res['ids']);cov=load(I/'coverage-delta.json');assert len(cov)==5833 and len(ids)==50
sets=[set(r['ids']) for r in load(I/'active-breadth-reservations.json')]
assert len(sets)==3
for j,s in enumerate(sets):
 assert len(s)==50 and not s&set(map(int,cov)) and not s&set(res['protected_ids'])
 for t in sets[:j]:assert not s&t
assert ids in sets and not ids&set(res['other_active_reservations'])
assert [r['mathdb_id'] for r in load(I/'queue.json')]==res['ids']
(L/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
records=[]
for c in chunks:
 p=R/c['path']
 for line,b in enumerate(p.open(),1):
  r= json.loads(b)
  if int(r.get('id',r.get('mathdb_id',-1))) in ids:
   records.append({'corpus_path':str(p),'line':line,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(records)==50
records.sort(key=lambda r:res['ids'].index(int(r['record'].get('id',r['record'].get('mathdb_id')))))
(L/'literal-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
print('VERIFIED 20 CHUNKS,8 INPUTS,50 ASSIGNED; record schema:',str(records[0])[:12000])
