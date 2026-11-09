import json,pathlib,hashlib
L=pathlib.Path(__file__).resolve().parents[1]; B=L.parents[1]; ids=set(json.loads((L/'reservation.json').read_text())['ids']); found={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 chunkhash=hashlib.sha256(p.read_bytes()).hexdigest()
 with p.open('rb') as f:
  for n,line in enumerate(f,1):
   o=json.loads(line); i=o.get('mathdb_id',o.get('id'))
   if i is not None and int(i) in ids:
    i=int(i); (L/f'sources/{i}.raw.jsonl').write_bytes(line); found[str(i)]={'chunk':str(p),'line':n,'chunk_sha256':chunkhash,'raw_sha256':hashlib.sha256(line).hexdigest(),'record':o}
(L/'outputs/provenance.json').write_text(json.dumps(found,indent=2))
for i,v in found.items(): print(i,json.dumps(v['record'],ensure_ascii=False))
print('FOUND',len(found))
