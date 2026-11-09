import json,pathlib,hashlib
L=pathlib.Path.cwd(); B=L.parent.parent; C=B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
ids=set(json.load(open('reservation.json'))['ids']); found={}
for p in sorted(C.glob('mathdb-normalized-chunk-*.jsonl')):
 for i,line in enumerate(p.open('rb'),1):
  r=json.loads(line); id=r.get('mathdb_id',r.get('id'))
  if id in ids:
   (L/'raw'/f'{id}.jsonl').write_bytes(line); found[str(id)]={'chunk':str(p),'line':i,'raw_sha256':hashlib.sha256(line).hexdigest(),'record':r}
 if len(found)==20:break
for x in found.values():
 p=pathlib.Path(x['chunk']); x['chunk_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
json.dump(found,open('outputs/extracted.json','w'),indent=2)
for id,x in found.items():print(id,json.dumps(x['record'],ensure_ascii=False))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L.parent/'ledger.json']:
 r=json.loads(p.read_text()); print('CONTEXT',p,hashlib.sha256(p.read_bytes()).hexdigest()); (L/'outputs'/('context-'+p.parent.name+'-'+p.name)).write_text(json.dumps(r,indent=2))
