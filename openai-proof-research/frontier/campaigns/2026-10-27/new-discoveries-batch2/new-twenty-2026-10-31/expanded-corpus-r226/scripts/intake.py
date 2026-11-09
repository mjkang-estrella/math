from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1]; C=L.parent.parent
ids=set(json.loads((L/'reservation.json').read_text())['ids']); prov={}; out=[]
for p in sorted((C/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 for n,line in enumerate(p.open('rb'),1):
  r=json.loads(line); i=r.get('id',r.get('mathdb_id'))
  if str(i).isdigit() and int(i) in ids:
   i=int(i); (L/f'inputs/{i}.jsonl').write_bytes(line)
   prov[str(i)]={'chunk':str(p),'line':n,'chunk_sha256':h,'raw_sha256':hashlib.sha256(line).hexdigest()}
   out.append((i,r))
(L/'inputs/provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
(L/'inputs/statements.json').write_text(json.dumps(dict(out),indent=2)+'\n')
print('extracted',len(out)); print(json.dumps(out[:1],indent=2))
