import json,hashlib,pathlib
D=pathlib.Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r721'
def load(p):return json.loads(p.read_text())
def binding(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
def check(p,h,n):
 b=binding(p);assert b['sha256']==h and b['size']==n,str(p)
refs={}
def add(p):refs[str(p)]=binding(p)
add(I/'manifest.json');assert refs[str(I/'manifest.json')]['sha256']=='110058e57a3257722135d46ba927836fce4ce435795d8ee4954901d7f68cf6eb'
m=load(I/'manifest.json'); assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
for x in m['files']:p=I/x['path'];check(p,x['sha256'],x['size']);add(p)
add(I/'verification-receipt.json')
for x in load(I/'bindings.json'):
 for k in ['original','copy']:p=pathlib.Path(x[k]);check(p,x['sha256'],x['bytes']);add(p)
R=L/'pi-mathdb-full-corpus-inventory-r301'; inv=load(R/'manifest.json')
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-breadth-intake-r304/accepted-exclusions.json',L/'root-mathdb-breadth-intake-r304/historical-dispositions.json']:
 if p.exists():add(p)
(D/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
chunks=[x for x in inv['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
for x in chunks+inv['frozen_inputs']:
 p=R/x['path'];check(p,x['sha256'],x['bytes']);add(p)
for sub in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-decision-r363/DECISION.md']:
 p=L/sub
 if p.exists():add(p)
for p in L.glob('*r363*/**/*'):
 if p.is_file() and p.name in ['DECISION.md','decision.json','SUMMARY.md']:add(p)
coverage=load(I/'coverage-delta.json');assert len(coverage)==8933
q=load(I/'queue-r722.json');res=load(I/'reserved-ids-r722.json');ids=[x['mathdb_id'] for x in q];assert len(ids)==len(set(ids))==50 and ids==res['ids']
sets=[set(x['ids']) for x in load(I/'active-breadth-reservations.json')]
assert len(sets)==3
for j,s in enumerate(sets):
 assert not s&set(map(int,coverage)); assert not s&set(res['protected_ids'])
 for t in sets[:j]:assert not s&t
(D/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(D/'pre-reading-checks.json').write_text(json.dumps(dict(status='PASS',chunks=20,frozen_inputs=8,intake_payload_exact=True,direct_original_copy_pairs=len(load(I/'bindings.json')),baseline=8933,assignment=50,reserved_sets=3,disjoint=True),indent=2)+'\n')
print('PRE-READING PASS')
