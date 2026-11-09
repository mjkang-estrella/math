import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parents[1]; B=L.parents[1]; ids=set(json.loads((L/'reservation.json').read_text())['ids']); out={}
for f in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 h=hashlib.sha256(f.read_bytes()).hexdigest()
 for n,line in enumerate(f.open('rb'),1):
  r=json.loads(line); i=r.get('id',r.get('mathdb_id'))
  if str(i).isdigit() and int(i) in ids:
   i=int(i); (L/f'sources/{i}.raw.jsonl').write_bytes(line)
   out[str(i)]={'chunk':str(f),'line':n,'chunk_sha256':h,'raw_sha256':hashlib.sha256(line).hexdigest(),'record':r}
(L/'outputs/extracted.json').write_text(json.dumps(out,indent=2))
for i,r in out.items(): print(i,json.dumps(r['record'],ensure_ascii=False))
for f in [B/'ledger.json',B/'prior-campaign-context.json',L.parent/'ledger.json']:
 d=json.loads(f.read_text()); print('LEDGER',f,hashlib.sha256(f.read_bytes()).hexdigest()); print(json.dumps(d,ensure_ascii=False))
