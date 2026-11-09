import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parents[1]; B=L.parents[1]
ids=set(json.loads((L/'reservation.json').read_text())['ids']); out={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 for n,line in enumerate(p.open('rb'),1):
  r=json.loads(line); i=r.get('mathdb_id',r.get('id'))
  if i in ids:
   (L/'sources'/f'{i}.raw.jsonl').write_bytes(line)
   out[i]={'chunk':str(p),'line_1based':n,'chunk_sha256':h,'raw_sha256':hashlib.sha256(line).hexdigest(),'row':r}
(L/'outputs/extracted.json').write_text(json.dumps(out,indent=2))
for i,r in out.items(): print(i,json.dumps(r['row'],ensure_ascii=False))
assert len(out)==20,len(out)
