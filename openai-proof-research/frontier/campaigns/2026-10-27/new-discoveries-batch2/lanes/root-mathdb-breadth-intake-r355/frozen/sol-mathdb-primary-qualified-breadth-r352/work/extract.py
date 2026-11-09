from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1];B=L.parent
ids=json.loads((B/'root-mathdb-breadth-intake-r350/reserved-ids.json').read_text())['ids']; found={}
for p in sorted((B/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for line in p.open():
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   assert r['mathdb_id'] not in found
   found[r['mathdb_id']]=r
assert len(found)==50
old=json.loads((B/'pi-mathdb-primary-qualified-breadth-r351/work/records.json').read_text());assert {r['mathdb_id']:r for r in old}==found
(L/'records.json').write_text(json.dumps([found[i] for i in ids],indent=2)+'\n')
print('r351 extract independently equals all fifty corpus records')
for i in ids:
 r=found[i];print('\nID',i,r['title'],'\n'+r['statement']+'\nSOURCE '+str(r['source_url']))
