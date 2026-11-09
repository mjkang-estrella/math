from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent; C=L/'pi-mathdb-full-corpus-inventory-r301'
ids=json.loads((L/'root-mathdb-breadth-intake-r387/reserved-ids.json').read_text())['ids']; found={}
for e in json.loads((C/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 for line in (C/e['path']).open():
  x=json.loads(line)
  if int(x['mathdb_id']) in ids: found[int(x['mathdb_id'])]=x
assert len(found)==50
(R/'records.json').write_text(json.dumps([found[i] for i in ids],ensure_ascii=False,indent=2)+'\n')
for i in ids:
 x=found[i];print('\nID',i);print(json.dumps(x,ensure_ascii=False))
