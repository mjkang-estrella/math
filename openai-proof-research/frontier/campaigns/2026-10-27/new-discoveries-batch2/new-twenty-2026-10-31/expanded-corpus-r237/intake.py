from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
B=L.parent.parent
O=L/'outputs';O.mkdir(exist_ok=True)
R=json.loads((L/'reservation.json').read_text()); ids=set(R['ids']); found={}
h=lambda x:hashlib.sha256(x).hexdigest()
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes()
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line); i=d.get('id',d.get('mathdb_id'))
  if i in ids or str(i) in set(map(str,ids)):
   (O/f'{i}.raw.jsonl').write_bytes(line)
   found[str(i)]={'chunk':str(p),'line':n,'chunk_sha256':h(data),'raw_sha256':h(line),'record':d}
(O/'records.json').write_text(json.dumps(found,indent=2))
for name,p in [('ledger',L.parent/'ledger.json'),('batch-ledger',B/'ledger.json'),('context',B/'prior-campaign-context.json')]:
 data=p.read_bytes();d=json.loads(data); (O/f'{name}-read.json').write_text(json.dumps({'path':str(p),'sha256':h(data),'content':d},indent=2))
print('found',len(found))
for i,v in found.items():print(i,json.dumps(v['record'],ensure_ascii=False))
