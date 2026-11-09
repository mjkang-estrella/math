import json,hashlib,pathlib
L=pathlib.Path(__file__).resolve().parents[1]; B=L.parents[1]
ids=set(json.loads((L/'reservation.json').read_text())['ids']); out={}
for p in (B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl'):
 chunkhash=None
 with p.open('rb') as f:
  for n,line in enumerate(f,1):
   r=json.loads(line); i=r.get('id',r.get('mathdb_id'))
   if i not in ids: continue
   if chunkhash is None: chunkhash=hashlib.sha256(p.read_bytes()).hexdigest()
   (L/f'sources/{i}.raw.jsonl').write_bytes(line)
   out[str(i)]={'chunk':str(p),'line':n,'chunk_sha256':chunkhash,'raw_sha256':hashlib.sha256(line).hexdigest(),'record':r}
(L/'outputs/intake.json').write_text(json.dumps(out,indent=2))
for i,r in out.items(): print(i,json.dumps(r['record'],ensure_ascii=False))
for name,p in [('ledger',B/'ledger.json'),('context',B/'prior-campaign-context.json')]:
 r=json.loads(p.read_text()); (L/f'outputs/{name}-read.json').write_text(json.dumps(r,indent=2))
 print(name,'keys',list(r))
