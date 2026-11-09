from pathlib import Path
import json,hashlib
W=Path(__file__).resolve().parent;L=W.parent
ids=json.loads((L/'root-mathdb-breadth-intake-r419/reserved-ids.json').read_text())['ids']; records=[]; locations={}
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('mathdb_id',r.get('id')) in ids:
   records.append(r);locations[str(r.get('mathdb_id',r.get('id'))) ]={'original':str(p),'line':n}
assert len(records)==50
(W/'records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n');(W/'record-locations.json').write_text(json.dumps(locations,indent=2)+'\n')
print('KEYS',list(records[0]))
for r in records:
 print(json.dumps(r,ensure_ascii=False))
