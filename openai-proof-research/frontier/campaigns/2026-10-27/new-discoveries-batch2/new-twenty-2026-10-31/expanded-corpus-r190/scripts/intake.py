import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parent.parent
ids=set(json.loads((D/'reservation.json').read_text())['ids']); out={}
for p in (B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl'):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 with p.open('rb') as f:
  for n,b in enumerate(f,1):
   x=json.loads(b); i=x.get('mathdb_id',x.get('id'))
   if i in ids or str(i) in {str(z) for z in ids}:
    (D/f'raw/{i}.jsonl').write_bytes(b); out[str(i)]={'chunk':str(p),'line':n,'chunk_sha256':h,'raw_sha256':hashlib.sha256(b).hexdigest(),'record':x}
(D/'outputs/intake.json').write_text(json.dumps(out,indent=2))
for k,v in out.items():print(k,json.dumps(v['record'],ensure_ascii=False))
for p in [B/'ledger.json',B/'prior-campaign-context.json',D.parent/'ledger.json']:
 x=json.loads(p.read_text()); (D/'outputs'/('context-'+p.parent.name+'-'+p.name)).write_text(json.dumps(x,indent=2))
 print('CONTEXT',p, 'keys',list(x), 'sha256',hashlib.sha256(p.read_bytes()).hexdigest())
