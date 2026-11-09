from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent;L=O.parent;ids=set(json.loads((L/'root-mathdb-breadth-intake-r401/reserved-ids.json').read_text())['ids']); found=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line); i=r.get('mathdb_id',r.get('id'))
  if i in ids:found.append({'corpus_path':str(p),'line':n,'record':r})
assert len(found)==50
(O/'statements.json').write_text(json.dumps(found,indent=2,ensure_ascii=False)+'\n')
print('record keys',list(found[0]['record']))
for a in found:print(json.dumps(a['record'],ensure_ascii=False))
