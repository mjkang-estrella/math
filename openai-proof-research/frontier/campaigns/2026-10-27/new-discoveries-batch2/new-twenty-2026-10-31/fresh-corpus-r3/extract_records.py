from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent;ids=set(json.loads((p/'reservation.json').read_text())['ids']);rows=[]
for f in sorted((p.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 b=f.read_bytes();h=hashlib.sha256(b).hexdigest()
 for n,line in enumerate(b.decode().splitlines(),1):
  r=json.loads(line);i=r.get('mathdb_id',r.get('id'))
  if i in ids:rows.append({'id':i,'chunk':f.name,'line':n,'chunk_sha256':h,'line_sha256':hashlib.sha256(line.encode()).hexdigest(),'record':r})
assert len(rows)==40
(p/'literal-records.json').write_text(json.dumps(rows,indent=2))
print('Extracted40 literal records. Line hash excludes newline; chunk hash includes original file bytes.')
