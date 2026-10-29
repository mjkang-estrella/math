from pathlib import Path
from fractions import Fraction as Q
import json, hashlib
root=Path(__file__).resolve().parent
lane=root.parent/'sol-fresh-source-discovery-r118'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''): h.update(chunk)
    return h.hexdigest()
manifest=json.loads((lane/'finalmanifest.json').read_text())
sources=json.loads((lane/'source-lock.json').read_text())
for row in manifest:
    p=lane/row['path']
    assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],str(p)
for row in sources:
    assert sha(lane/row['copy'])==row['sha256'],row['copy']
for j in range(1,40):
    x=Q(j,100)
    deficit=(2*(x+x+1))**2-6*(x*x+(x+1)**2)
    assert deficit==4*x*x+4*x-2
    if j<=36: assert deficit<0
assert (2*Q(6,5))**2-6*(Q(1,100)+Q(121,100))==Q(-39,25)
result={'manifest_entries':len(manifest),'source_hashes':len(sources),'exact_supporting_checks':39,'public_example_deficit':'-39/25','status':'PASS','credit':0,'qualification':'Supporting arithmetic only; no external full-proof audit or current registry clearance.'}
(root/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
