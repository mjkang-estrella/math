from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent.parent; O=Path(__file__).resolve().parent; I=L/'root-mathdb-breadth-intake-r707'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def b(p):
 d=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(d).hexdigest(),'size':len(d)}
bind={}
def ck(p,h,n):
 a=b(p);assert a['sha256']==h and a['size']==n,str(p);bind[str(p)]=a
ck(I/'manifest.json','8175880d19229d8264f232281d826d5238781c52f2f0fb6daf1af2401a7fef73',10858)
m=j(I/'manifest.json'); expected={x['path'] for x in m['files']}|set(m['excluded_exact_paths']);assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected
for x in m['files']:ck(I/x['path'],x['sha256'],x['size'])
for p in [I/'verification-receipt.json',I/'bindings.json']:bind[str(p)]=b(p)
for x in j(I/'bindings.json'):
 for k in ['original','copy']:ck(Path(x[k]),x['sha256'],x['bytes'])
rm=j(R/'manifest.json'); chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for x in chunks+rm['frozen_inputs']:ck(R/x['path'],x['sha256'],x['bytes'])
cov=j(I/'coverage-delta.json');assert len(cov)==8583
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
q=j(I/'queue-r708.json');res=j(I/'reserved-ids-r708.json');assert [x['mathdb_id'] for x in q]==res['ids'] and len(res['ids'])==50
assert any(x['ids']==res['ids'] for x in active)
# Bind context before reading it; no recursive historical expansion.
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']+list(L.glob('root*cayley*r363/*'))+list(L.glob('*r363/DECISION.md'))+list((L/'root-mathdb-accepted-exclusions-r304').glob('*.json')):
 if p.is_file():bind[str(p)]=b(p)
(O/'flat-bindings.json').write_text(json.dumps(list(bind.values()),indent=2)+'\n')
(O/'initial-checks.json').write_text(json.dumps({'intake_exact_payload':True,'direct_pairs':len(j(I/'bindings.json')),'chunks_in_place':20,'frozen_inputs':8,'baseline':len(cov),'disjoint_reservations':len(active),'assigned':50,'scientific_reading_started':False},indent=2)+'\n')
print((O/'initial-checks.json').read_text())
