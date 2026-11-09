from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent;A=L/'root-mathdb-breadth-intake-r427';I=L/'pi-mathdb-full-corpus-inventory-r301'
ids=json.loads((A/'reserved-ids.json').read_text())['ids'];rows=[];locations=[]
for p in sorted((I/'corpus').glob('*.jsonl')):
 for i,line in enumerate(p.open(),1):
  o=json.loads(line)
  if o['mathdb_id'] in ids:
   rows.append(o);locations.append({'mathdb_id':o['mathdb_id'],'original':str(p),'line':i})
assert len(rows)==50
(R/'records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n');(R/'record-locations.json').write_text(json.dumps(locations,indent=2)+'\n')
for o in rows:print(o['mathdb_id'],o['title'],'\n'+o['statement']+'\nSOURCE '+o['source_url']+' '+o['source_name']+'\n')
