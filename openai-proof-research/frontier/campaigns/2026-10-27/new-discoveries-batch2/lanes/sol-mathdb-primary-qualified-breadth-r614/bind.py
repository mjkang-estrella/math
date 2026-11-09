from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent; B=L.parent.parent; I=L.parent/'root-mathdb-breadth-intake-r613'; R=L.parent/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def sig(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
a=[]
def check(p,h,n):
 s=sig(p);assert (s['sha256'],s['size'])==(h,n),(p,s);a.append(s)
s=sig(I/'manifest.json');assert s['sha256']=='de5ee96819d21bc91207fb423373ad2150aa5165940b3930fc20123485882114';a.append(s)
m=load(I/'manifest.json')
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in m['files']}|{'manifest.json','verification-receipt.json'}
for x in m['files']:check(I/x['path'],x['sha256'],x['size'])
a.append(sig(I/'verification-receipt.json'))
for x in load(I/'bindings.json'):
 for k in ['original','copy']:check(Path(x[k]),x['sha256'],x['bytes'])
m=load(R/'manifest.json'); chunks=[x for x in m['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(m['frozen_inputs'])==8
for x in chunks+m['frozen_inputs']:check(R/x['path'],x['sha256'],x['bytes'])
# Flat context only; bind before semantic reads.
for p in [B/'ledger.json', B/'prior-campaign-context.json', L.parent/'root-mathdb-accepted-exclusions-r304'/'accepted-exclusions.json', L.parent/'root-mathdb-accepted-exclusions-r304'/'historical-dispositions.json']:
 a.append(sig(p))
for p in L.parent.glob('*r363*/**/DECISION.md'):a.append(sig(p))
a.append(sig(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'))
(L/'flat-bindings.json').write_text(json.dumps(a,indent=2)+'\n')
print('BOUND',len(a),'20 chunks,8 frozen inputs; exact intake payload and direct pairs PASS')
print('coverage schema',str(load(I/'coverage-delta.json'))[:1600]);print('reservations',str(load(I/'active-breadth-reservations.json'))[-2600:])
