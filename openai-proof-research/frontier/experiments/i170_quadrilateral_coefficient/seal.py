"""Exclusive-create the single seal only after successful immutable-first prevalidation."""
import json,hashlib
from pathlib import Path
BASE=Path(__file__).resolve().parent;ROOT=BASE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((BASE/'prevalidation.json').read_text());assert p['status']=='PASS' and p['mode']=='prevalidate'
assert p['inventory_sha256']==sha(BASE/'inventory.json')
assert p['verifier_sha256']==sha(BASE/'verify.py')
assert p['report_sha256']==sha(ROOT/'frontier/iterations/i170-quadrilateral-coefficient.md')
assert len(p['guard_probes'])==8 and set(p['guard_probes'].values())=={'BLOCKED'}
assert len(p['payloads'])==7 and all(z['byte_equality']=='PASS' for z in p['payloads'])
for z in json.loads((BASE/'inventory.json').read_text())['files']:assert sha(ROOT/z['path'])==z['sha256'],z['path']
seal={'iteration':170,'creation':'exclusive-create exactly once after successful --prevalidate; never reseal','inventory_sha256':sha(BASE/'inventory.json'),'prevalidation_sha256':sha(BASE/'prevalidation.json'),'report_sha256':p['report_sha256'],'verifier_sha256':p['verifier_sha256']}
with (BASE/'seal.json').open('x') as f:f.write(json.dumps(seal,sort_keys=True,indent=2)+'\n')
print(json.dumps({'seal_sha256':sha(BASE/'seal.json'),**seal},sort_keys=True,indent=2))
