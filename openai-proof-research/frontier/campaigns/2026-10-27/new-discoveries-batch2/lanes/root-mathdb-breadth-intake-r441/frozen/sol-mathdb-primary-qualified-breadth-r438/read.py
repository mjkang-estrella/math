from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent;I=L/'root-mathdb-breadth-intake-r437'
ids=set(map(str,json.loads((I/'reserved-ids.json').read_text())['ids']));q=json.loads((I/'queue.json').read_text());baseline=json.loads((I/'coverage-delta.json').read_text());assert len(ids)==50 and ids=={str(x['mathdb_id']) for x in q};assert len(baseline)==2333 and not ids&set(baseline)
other=set(map(str,json.loads((I/'reserved-ids.json').read_text())['other_active_reservations']));assert len(other)==50 and not ids&other
assert not ids&{'372627','372628','368940','404067','364119'}
found=[]
for e in json.loads((L/'pi-mathdb-full-corpus-inventory-r301/manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 with (L/'pi-mathdb-full-corpus-inventory-r301'/e['path']).open() as f:
  for line in f:
   x=json.loads(line)
   if str(x['mathdb_id']) in ids:found.append(x)
assert len(found)==50
(R/'assigned-records.json').write_text(json.dumps(found,indent=2,ensure_ascii=False)+'\n')
(R/'statements.txt').write_text('\n\n'.join(str(x['mathdb_id'])+' '+x.get('title','')+'\n'+x['statement'] for x in found))
print('assigned schema keys',list(found[0]));print('baseline',len(baseline),'other-active',len(other));print(json.dumps(found[0],ensure_ascii=False))
