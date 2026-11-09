from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r575'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def bind(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,e):
 r=bind(p);assert r['size']==e.get('size',e.get('bytes')) and r['sha256']==e['sha256'],str(p);return r
refs=[bind(I/'manifest.json'),bind(I/'verification-receipt.json')]
m=load(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
for x in m['files']:refs.append(check(I/x['path'],x))
for x in load(I/'bindings.json'):
 for k in ('original','copy'):refs.append(check(Path(x[k]),x))
refs.append(check(R/'manifest.json',next(x for x in m['files'] if x['path']=='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json')))
rm=load(R/'manifest.json'); chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for x in chunks+rm['frozen_inputs']:refs.append(check(R/x['path'],x))
for p in [L/'root-mathdb-accepted-exclusions-r304'/n for n in ['accepted-exclusions.json','historical-dispositions.json']]+[L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:refs.append(bind(p))
unique={x['path']:x for x in refs};(D/'flat-bindings.json').write_text(json.dumps(list(unique.values()),indent=2)+'\n')
(D/'binding-receipt.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),intake_payload_exact=True,direct_pairs=True,original_chunks=20,frozen_inputs=8,flat_references=len(unique)),indent=2)+'\n')
print('BOUND',len(unique))
