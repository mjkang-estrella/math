from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1]; ids=set(json.loads((L/'reservation.json').read_text())['ids']); out={}
for p in sorted((L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes(); ch=hashlib.sha256(data).hexdigest()
 for i,line in enumerate(data.splitlines(keepends=True),1):
  r=json.loads(line); k=r.get('id',r.get('mathdb_id'))
  if k in ids:
   (L/'sources'/f'{k}.jsonl').write_bytes(line)
   out[str(k)]={'chunk':str(p),'line':i,'chunk_sha256':ch,'raw_sha256':hashlib.sha256(line).hexdigest(),'record':r}
(L/'outputs/provenance.json').write_text(json.dumps(out,indent=2))
for k,v in out.items():print(k,json.dumps(v['record'],ensure_ascii=False))
