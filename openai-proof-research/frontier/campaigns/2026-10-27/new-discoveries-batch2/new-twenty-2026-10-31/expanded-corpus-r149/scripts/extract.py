import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parents[1]; B=L.parent.parent
ids=set(json.loads((L/'reservation.json').read_text())['ids'])
found={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 with p.open('rb') as f:
  for n,line in enumerate(f,1):
   r=json.loads(line); i=r.get('mathdb_id',r.get('id'))
   if i in ids:
    (L/f'raw/{i}.jsonl').write_bytes(line)
    found[str(i)]={'chunk':str(p),'line_1based':n,'chunk_sha256':h,'raw_sha256':hashlib.sha256(line).hexdigest(),'record':r}
(L/'outputs/extracted.json').write_text(json.dumps(found,indent=2))
for i,v in found.items():print(i,json.dumps(v['record'],ensure_ascii=False))
for name,p in [('campaign',L.parent/'ledger.json'),('batch',B/'ledger.json'),('inherited',B/'prior-campaign-context.json')]:
 b=p.read_bytes(); d=json.loads(b)
 (L/f'outputs/{name}-context.json').write_bytes(b)
 print('CONTEXT',name,hashlib.sha256(b).hexdigest(),list(d))
