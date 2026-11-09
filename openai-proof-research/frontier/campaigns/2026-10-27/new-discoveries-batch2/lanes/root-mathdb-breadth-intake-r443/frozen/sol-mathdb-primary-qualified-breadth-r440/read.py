from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent
res=json.loads((L/'root-mathdb-breadth-intake-r439/reserved-ids.json').read_text()); ids=set(res['ids']); old=json.loads((L/'root-mathdb-breadth-intake-r439/coverage-delta.json').read_text());assert len(old)==2383
assert len(ids)==50 and not ids&set(res['other_active_reservations']) and not ids&{372627,372628,368940,404067,364119} and not set(map(str,ids))&set(old)
rows=[];loc=[]
I=L/'pi-mathdb-full-corpus-inventory-r301'
for e in json.loads((I/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 for i,line in enumerate((I/e['path']).open()):
  x=json.loads(line)
  if int(x['mathdb_id']) in ids:rows.append(x);loc.append({'mathdb_id':x['mathdb_id'],'path':str(I/e['path']),'line':i+1})
assert len(rows)==50
(R/'records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n');(R/'record-locations.json').write_text(json.dumps(loc,indent=2)+'\n')
print('ASSIGNED RECORD KEYS',list(rows[0]))
for x in rows:
 print('\nID',x['mathdb_id']); print(json.dumps(x,ensure_ascii=False))
