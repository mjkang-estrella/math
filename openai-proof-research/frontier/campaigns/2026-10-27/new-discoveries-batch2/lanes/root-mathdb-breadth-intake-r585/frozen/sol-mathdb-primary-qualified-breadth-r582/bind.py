from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;L=D.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r581';R=L/'pi-mathdb-full-corpus-inventory-r301'
def digest(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,x):
 a=digest(p);assert a['size']==x.get('size',x.get('bytes')) and a['sha256']==x['sha256'],str(p);return a
out=[]
assert digest(I/'manifest.json')['sha256']=='8e88a0e56f05c72af9c69c4f412ecc2b8750cfaa3ad973842a8a509bad0e9497'
m=json.loads((I/'manifest.json').read_text());expected={x['path'] for x in m['files']}|set(m['excluded_exact_paths']);assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected
out += [digest(I/'manifest.json'),digest(I/'verification-receipt.json')]
for x in m['files']:out.append(check(I/x['path'],x))
for x in json.loads((I/'bindings.json').read_text()):
 for k in ['original','copy']:out.append(check(Path(x[k]),x))
rm=json.loads((R/'manifest.json').read_text());chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for x in chunks+rm['frozen_inputs']:out.append(check(R/x['path'],x))
refs=[B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']
for p in refs:out.append(digest(p))
(D/'flat-bindings.json').write_text(json.dumps(list({x['path']:x for x in out}.values()),indent=2)+'\n')
print('Bound and checked intake exact payload, original/copy pairs, 20 chunks, 8 frozen inputs, and context references')
