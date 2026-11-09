from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent;L=O.parent
ids=set(json.loads((L/'root-mathdb-breadth-intake-r399/reserved-ids.json').read_text())['ids']);out=[]
for p in json.loads((O/'input-bindings.json').read_text())['chunks']:
 for line in open(p):
  r=json.loads(line)
  if int(r['mathdb_id']) in ids:out.append({'record':r,'chunk':p,'line_sha256':hashlib.sha256(line.encode()).hexdigest(),'canonical_sha256':hashlib.sha256(json.dumps(r,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()})
assert len(out)==50
(O/'records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for x in out:
 r=x['record']; print(json.dumps(r,ensure_ascii=False))
