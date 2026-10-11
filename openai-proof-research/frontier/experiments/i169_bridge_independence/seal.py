"""Exactly-once seal, only following successful prevalidation."""
import json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pre=json.loads((HERE/'prevalidation.json').read_text());inv=json.loads((HERE/'inventory.json').read_text())
assert pre['status']=='PASS' and pre['mode']=='prevalidation' and pre['inventory_sha256']==sha(HERE/'inventory.json')
for f in inv['files']:
 p=ROOT/f['path'];assert sha(p)==f['sha256'] and p.stat().st_size==f['size']
source=ROOT/'frontier/sources/i169_bridge_independence';policy=json.loads((source/'replay-policy.json').read_text())
for f in json.loads((source/'external-bindings.json').read_text())['files']:
 if f['path'] not in policy['context_only_exclusions']:assert sha(ROOT/f['path'])==f['sha256']
record={'iteration':169,'creation':'exclusive-create once following successful immutable-first prevalidation','inventory_sha256':sha(HERE/'inventory.json'),'prevalidation_sha256':sha(HERE/'prevalidation.json'),'report_sha256':sha(ROOT/'frontier/iterations/i169-bridge-independence.md'),'verifier_sha256':sha(HERE/'verify.py')}
with (HERE/'seal.json').open('x') as f:f.write(json.dumps(record,sort_keys=True,indent=2)+'\n')
print(json.dumps({'seal_sha256':sha(HERE/'seal.json'),**record},sort_keys=True,indent=2))
