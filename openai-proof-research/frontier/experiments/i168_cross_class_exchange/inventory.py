"""Preparation only. Inventory may be created only before a seal exists."""
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
B=P.parents[2]
S=B/'frontier/sources/i168_cross_class_exchange'
report=B/'frontier/iterations/i168-cross-class-exchange.md'
assert not (P/'seal.json').exists(),'immutable after seal'
exclude={P/'inventory.json',P/'prevalidation.json',P/'seal.json'}
files=sorted(({x for d in [P,S] for x in d.rglob('*') if x.is_file()}|{report})-exclude)
obj={'files':[{'path':str(p.relative_to(B)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size} for p in files],'control_files':['inventory.json (bound by seal)','prevalidation.json (bound by seal)','seal.json (external hash supplied in final reply)']}
with (P/'inventory.json').open('x') as f:json.dump(obj,f,sort_keys=True,indent=2);f.write('\n')
print(json.dumps({'files':len(files),'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest()},sort_keys=True))
