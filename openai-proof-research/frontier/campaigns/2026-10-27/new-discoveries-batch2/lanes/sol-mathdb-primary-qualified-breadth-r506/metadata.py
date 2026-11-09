from pathlib import Path
import json,re,hashlib,collections
O=Path(__file__).parent
x=[]
for e in json.loads((O/'derivative-bindings.json').read_text()):
 p=Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256'];t=b.decode();v=re.findall(r'arXiv:\s*([0-9.]+v\d+)',t);x.append({'source':p.name,'version_identifiers':sorted(set(v)),'exact_version_limit':'If empty, do not invent version: see bound HTML bytes.'})
(O/'source-versions.json').write_text(json.dumps(x,indent=2)+'\n')
print(x)
print(collections.Counter(e['disposition'] for e in json.loads((O/'dispositions.json').read_text())))
