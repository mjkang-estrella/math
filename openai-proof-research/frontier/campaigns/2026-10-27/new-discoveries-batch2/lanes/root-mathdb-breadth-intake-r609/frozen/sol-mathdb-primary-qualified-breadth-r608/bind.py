import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent; L=P.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r605'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def binding(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 a=binding(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),(str(p),a,e);return a
out=[]
assert binding(I/'manifest.json')['sha256']=='d2910a960ea63a6ff6d9d7f8f241abb2a541c124b94d073b135190d824b37849'
for n in ['manifest.json','verification-receipt.json']:out.append(binding(I/n))
m=load(I/'manifest.json'); listed={e['path'] for e in m['files']};actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert listed==actual
for e in m['files']:out.append(check(I/e['path'],e))
for e in load(I/'bindings.json'):
 out.append(check(pathlib.Path(e['original']),e));out.append(check(pathlib.Path(e['copy']),e));assert pathlib.Path(e['original']).read_bytes()==pathlib.Path(e['copy']).read_bytes()
rm=load(R/'manifest.json'); chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for e in chunks+rm['frozen_inputs']:out.append(check(R/e['path'],e))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 out.append(binding(p))
for p in (L/'root-cayley-parametric-subgroup-r363').glob('*'):
 if p.is_file():out.append(binding(p))
# Locate the required r363 decision by names only, never recursively copying.
for d in L.glob('*r363'):
 for p in d.glob('*'):
  if p.is_file():out.append(binding(p))
unique={e['path']:e for e in out};(P/'flat-bindings.json').write_text(json.dumps(list(unique.values()),indent=2)+'\n')
r=load(I/'reserved-ids-r608.json');q=load(I/'queue-r608.json');c=load(I/'coverage-delta.json');assert len(c)==6133
sets=[set(x['ids']) for x in load(I/'active-breadth-reservations.json')];assert len(sets)==3
for j,s in enumerate(sets):
 assert not s&set(map(int,c));assert not s&set(r['protected_ids']+[343771,343973,344924,383181])
 for t in sets[:j]:assert not s&t
assert set(r['ids'])=={x['mathdb_id'] for x in q} and len(q)==50 and set(r['ids']) in sets
(P/'binding-verification.json').write_text(json.dumps({'pass':True,'intake_payloads':len(listed),'flat_references':len(unique),'chunks':20,'frozen_inputs':8,'baseline_literal_reviews':len(c),'reservations_disjoint':True},indent=2)+'\n')
# Extract only assigned records after all binding and integrity checks.
rows=[]
for e in chunks:
 p=R/e['path']
 for line,raw in enumerate(p.open(),1):
  o=json.loads(raw);i=o.get('mathdb_id',o.get('id'))
  if i in r['ids']:rows.append({'mathdb_id':i,'chunk':str(p),'line':line,'record':o,'canonical_record_sha256':hashlib.sha256(json.dumps(o,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50
(P/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'binding_pass':True,'records':len(rows),'sample_schema':list(rows[0]['record'])}))
