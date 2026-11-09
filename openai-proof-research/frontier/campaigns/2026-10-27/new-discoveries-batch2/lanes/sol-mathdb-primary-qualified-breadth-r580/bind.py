from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r579'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def J(p): return json.loads(p.read_text())
def info(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
rows={}
def bind(p,sha=None,size=None):
 r=info(p);assert sha is None or r['sha256']==sha,(p,'hash');assert size is None or r['size']==size,(p,'size');rows[str(p)]=r
bind(I/'manifest.json');bind(I/'verification-receipt.json')
m=J(I/'manifest.json');expected={r['path'] for r in m['files']};actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert actual==expected
for r in m['files']:bind(I/r['path'],r['sha256'],r['size'])
for r in J(I/'bindings.json'):
 for k in ['original','copy']:bind(Path(r[k]),r['sha256'],r['size'])
m=J(C/'manifest.json');chunks=[r for r in m['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(m['frozen_inputs'])==8
for r in chunks+m['frozen_inputs']:bind(C/r['path'],r['sha256'],r['bytes'])
for p in [L/'root-mathdb-accepted-exclusions-r304'/'accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304'/'historical-dispositions.json']:
 r=next(r for r in m['frozen_inputs'] if r['path']=='frozen/'+p.name);bind(p,r['sha256'],r['bytes'])
for p in list(L.glob('*r363/DECISION.md'))+[L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(p)
(D/'flat-bindings.json').write_text(json.dumps(list(rows.values()),indent=2)+'\n')
(D/'binding-receipt.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=len(rows),chunks=20,frozen_inputs=8,passed=True),indent=2)+'\n')
print('bound',len(rows),'files; 20 chunks and 8 frozen inputs')
