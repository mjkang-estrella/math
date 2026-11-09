import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r711';R=L/'pi-mathdb-full-corpus-inventory-r301'
def meta(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def load(p):return json.loads(p.read_text())
def check(p,e):
 m=meta(p);assert m['sha256']==e['sha256'] and m['size']==e.get('size',e.get('bytes')),(str(p),'mismatch');return m
refs={}
def bind(p,e=None):
 m=check(p,e) if e else meta(p);refs[str(p)]=m
bind(I/'manifest.json');bind(I/'verification-receipt.json')
m=load(I/'manifest.json');expected={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected
for e in m['files']:bind(I/e['path'],e)
for e in load(I/'bindings.json'):
 bind(pathlib.Path(e['original']),e);bind(pathlib.Path(e['copy']),e)
inv=load(R/'manifest.json');assert meta(R/'manifest.json')['sha256']==meta(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json')['sha256']
chunks=[e for e in inv['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
for e in chunks+inv['frozen_inputs']:bind(R/e['path'],e)
q=load(I/'queue-r712.json');res=load(I/'reserved-ids-r712.json');cov=load(I/'coverage-delta.json');active=load(I/'active-breadth-reservations.json')
assert len(cov)==8683 and len(q)==50 and {e['mathdb_id'] for e in q}==set(res['ids'])
seen=set()
for a in active:
 ids=set(a['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']);seen|=ids
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md','sol-mathdb-primary-qualified-breadth-r578/failures.json','sol-mathdb-primary-qualified-breadth-r642/failures.md','sol-mathdb-primary-qualified-breadth-r684/failures.json']:
 bind(L/rel)
for rel in ['ledger.json','prior-campaign-context.json']:bind(L.parent/rel)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'initial-checks.json').write_text(json.dumps({'status':'PASS','chunks':20,'frozen_inputs':8,'baseline':8683,'assigned':50,'active_disjoint_sets':3,'intake_payload_exact':True,'direct_original_copy_pairs':len(load(I/'bindings.json'))},indent=2)+'\n')
print((P/'initial-checks.json').read_text())
