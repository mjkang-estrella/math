from pathlib import Path
import json
R=Path(__file__).resolve().parent; L=R.parent
ids=set(json.loads((L/'root-mathdb-breadth-intake-r443/reserved-ids.json').read_text())['ids'])
I=L/'pi-mathdb-full-corpus-inventory-r301'; records=[]; loc=[]
for e in json.loads((I/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 for n,line in enumerate((I/e['path']).open(),1):
  x=json.loads(line)
  if x['mathdb_id'] in ids:records.append(x);loc.append({'id':x['mathdb_id'],'path':str(I/e['path']),'line':n})
assert len(records)==50
records.sort(key=lambda x:x['mathdb_id'])
(R/'records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n');(R/'record-locations.json').write_text(json.dumps(loc,indent=2)+'\n')
(R/'literal-reading.txt').write_text('\n\n'.join(str(x['mathdb_id'])+' '+x.get('title','')+'\n'+x['statement'] for x in records))
print('keys',list(records[0]))
print((R/'literal-reading.txt').read_text())
