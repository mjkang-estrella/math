from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r605';R=L/'pi-mathdb-full-corpus-inventory-r301';B=L.parent
out={}
def bind(p,h=None,n=None):
 p=Path(p);b=p.read_bytes();v={'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
 if h is not None:assert v['sha256']==h,str(p)
 if n is not None:assert len(b)==n,str(p)
 out[str(p)]=v
bind(I/'manifest.json');m=json.loads((I/'manifest.json').read_text())
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
for x in m['files']:bind(I/x['path'],x['sha256'],x['size'])
bind(I/'verification-receipt.json')
for x in json.loads((I/'bindings.json').read_text()):
 for k in ['original','copy']:bind(x[k],x['sha256'],x['bytes'])
r=json.loads((R/'manifest.json').read_text());chunks=[x for x in r['files'] if x['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20
for x in chunks+r['frozen_inputs']:bind(R/x['path'],x['sha256'],x['bytes'])
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(p)
(D/'flat-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('Bound',len(out),'files; intake exact payload, original/copy pairs, 20 original chunks and 8 frozen inputs PASS')
