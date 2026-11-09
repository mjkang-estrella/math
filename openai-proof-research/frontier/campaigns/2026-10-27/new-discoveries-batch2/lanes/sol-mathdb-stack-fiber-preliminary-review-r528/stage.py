from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;L=D.parent;R=L.parents[3]
def rec(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
r=json.loads((L/'sol-mathdb-primary-qualified-breadth-r522/records.json').read_text());selected=[x for x in r if x.get('mathdb_id') in [365437,365439]]
(D/'literal-records.json').write_text(json.dumps(selected,indent=2)+'\n')
# Bind administrative catalogue originals before their scoped read.
rows=json.loads((D/'flat-bindings.json').read_text())
for p in [R/'sources/upstream.json',R/'sources/CONTENTS.md']:
 if p.is_file():rows.append(rec(p))
(D/'flat-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
(D/'stage-bindings.json').write_text(json.dumps([rec(p) for p in D.iterdir() if p.is_file() and p.name!='stage-bindings.json'],indent=2)+'\n')
print('selected',len(selected),'repo',R)
