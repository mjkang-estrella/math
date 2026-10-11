"""Prepare inventory before prevalidation. Refuses any post-seal mutation."""
import json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
assert not (HERE/'seal.json').exists()
REPORT=ROOT/'frontier/iterations/i169-bridge-independence.md';SOURCES=ROOT/'frontier/sources/i169_bridge_independence'
files=sorted([REPORT]+[p for d in [HERE,SOURCES] for p in d.rglob('*') if p.is_file() and not (p.parent==HERE and p.name in ['inventory.json','prevalidation.json','seal.json'])])
entries=[]
for p in files:
 data=p.read_bytes();entries.append({'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(data).hexdigest(),'size':len(data)})
(HERE/'inventory.json').write_text(json.dumps({'iteration':169,'files':entries,'control_chain':'seal binds inventory and successful prevalidation; external final seal hash closes chain'},sort_keys=True,indent=2)+'\n')
print(json.dumps({'files':len(entries),'bytes':sum(x['size'] for x in entries)},sort_keys=True))
