import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parents[1]; ids=json.loads((D/'reservation.json').read_text())['ids']; out={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 data=p.read_bytes(); ch=hashlib.sha256(data).hexdigest()
 for n,line in enumerate(data.splitlines(keepends=True),1):
  o=json.loads(line)
  if o['mathdb_id'] in ids:
   i=str(o['mathdb_id']); (D/'raw'/f'{i}.jsonl').write_bytes(line)
   out[i]={**o,'provenance':{'chunk':str(p),'line_one_based':n,'chunk_sha256':ch,'raw_sha256':hashlib.sha256(line).hexdigest(),'statement_sha256':hashlib.sha256(o['statement'].encode()).hexdigest()}}
(D/'extracted.json').write_text(json.dumps(out,indent=2)+'\n')
for i in ids:
 o=out[str(i)];print(i,o['title'], '\n'+o['statement']+'\n')
