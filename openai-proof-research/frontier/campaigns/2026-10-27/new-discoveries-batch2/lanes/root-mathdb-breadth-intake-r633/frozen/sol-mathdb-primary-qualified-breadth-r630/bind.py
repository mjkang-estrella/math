from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r629'
def rec(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def load(p):return json.loads(p.read_text())
rows={}
def bind(p,h=None,s=None):
 p=Path(p);r=rec(p)
 if h:assert r['sha256']==h,str(p)
 if s is not None:assert r['size']==s,str(p)
 rows[str(p)]=r
bind(I/'manifest.json','245456d3f80812f4ad23ee61c6353da454b3140d9e30649c2d3b0570c96edc9d',9327)
for r in load(I/'manifest.json')['files']:bind(I/r['path'],r['sha256'],r['size'])
for r in load(I/'bindings.json'):
 for k in ('original','copy'):bind(r[k],r['sha256'],r['bytes'])
bind(I/'verification-receipt.json')
M=L/'pi-mathdb-full-corpus-inventory-r301/manifest.json'
for r in load(M)["files"]:
 if r["path"].startswith("corpus/"):bind(M.parent/r["path"],r["sha256"],r["bytes"])
for r in load(M)["frozen_inputs"]:bind(M.parent/r["path"],r["sha256"],r["bytes"])
for rel in ["root-mathdb-accepted-exclusions-r304/accepted-exclusions.json","root-mathdb-accepted-exclusions-r304/historical-dispositions.json","root-cayley-adjudication-r363/DECISION.md"]:
 p=L/rel
 if p.exists():bind(p)
for p in [L.parent/"ledger.json",L.parent/"prior-campaign-context.json"]:bind(p)
(D/'flat-bindings.json').write_text(json.dumps(list(rows.values()),indent=2)+'\n')
print('INTAKE BOUND',len(rows))
