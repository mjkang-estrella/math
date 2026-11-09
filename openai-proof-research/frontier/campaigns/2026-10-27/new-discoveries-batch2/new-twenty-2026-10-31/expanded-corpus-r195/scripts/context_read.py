import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parent.parent
for p in [B/'ledger.json',B/'prior-campaign-context.json',D.parent/'ledger.json']:
 if not p.exists():continue
 b=p.read_bytes();x=json.loads(b);(D/'outputs'/('context-'+p.parent.name+'-'+p.name)).write_bytes(b)
 print(p,hashlib.sha256(b).hexdigest())
 for k,v in x.items():
  if isinstance(v,list):
   print(k,len(v))
   for z in v:
    if isinstance(z,dict):print(z.get('mathdb_id',z.get('id')),str(z.get('title',z.get('reason',z.get('outcome',''))))[:260])
print('HISTORY');print((D/'history-matches.txt').read_text()[:20000])
