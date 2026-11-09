import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parents[1]; B=L.parents[1]; ids=set(json.loads((L/'reservation.json').read_text())['ids']); out={}
(L/'raw').mkdir(exist_ok=True)
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 with p.open('rb') as f:
  for n,line in enumerate(f,1):
   r=json.loads(line); i=r.get('id',r.get('mathdb_id'))
   if i not in ids: continue
   (L/'raw'/f'{i}.jsonl').write_bytes(line)
   out[str(i)]={'chunk':str(p),'line':n,'chunk_sha256':h,'raw_sha256':hashlib.sha256(line).hexdigest(),'record':r}
(L/'extracted.json').write_text(json.dumps(out,indent=2,ensure_ascii=False))
for i,v in out.items(): print(i,json.dumps(v['record'],ensure_ascii=False))
