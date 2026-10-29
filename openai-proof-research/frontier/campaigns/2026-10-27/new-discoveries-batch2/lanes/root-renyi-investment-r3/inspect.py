import json
from pathlib import Path
p=Path(__file__).resolve().parent.parent/'sol-renyi-registry-gap-closure-r3'
for name in ['exactcoverage.json','intervals.json','provenance.json','before.json','after.json']:
    x=json.loads((p/name).read_text())
    print(name, list(x) if isinstance(x,dict) else ['list',len(x)])
    if name=='exactcoverage.json':
        for k,v in x.items():
            if isinstance(v,list): print(k,len(v), list(v[0]) if v and isinstance(v[0],dict) else '')
    if name=='intervals.json': print({k:v for k,v in x[0].items() if k not in ['commits','files']})
