from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent; R=L.parent
ids=set(json.loads((L/'reservation.json').read_text())['ids'])
out={}
for p in sorted((R.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 for n,b in enumerate(p.open('rb'),1):
  x=json.loads(b); i=x.get('id',x.get('mathdb_id'))
  if i is not None and int(i) in ids:
   (L/f'raw-{i}.jsonl').write_bytes(b)
   out[str(i)]={'chunk':str(p),'line':n,'chunk_sha256':h,'raw_sha256':hashlib.sha256(b).hexdigest(),'record':x}
(L/'records.json').write_text(json.dumps(out,indent=2))
print('records',len(out))
for i,x in out.items(): print(i,json.dumps(x['record'],ensure_ascii=False))
