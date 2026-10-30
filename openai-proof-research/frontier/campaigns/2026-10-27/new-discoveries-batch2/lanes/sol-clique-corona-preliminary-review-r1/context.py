import pathlib,json
L=pathlib.Path(__file__).parent
for name in ['context-ledger.json','context-prior-campaign-context.json']:
 d=json.loads((L/'copies'/name).read_text()); print(name, 'keys',list(d))
 for k,v in d.items():
  if isinstance(v,list):
   print(k,len(v))
   for r in v:
    if isinstance(r,dict):print({x:r[x] for x in ['number','title','source_target','scope','status'] if x in r})
  elif not isinstance(v,dict):print(k,str(v)[:300])
d=json.loads((L/'copies/registry-screen.json').read_text())
print('REGISTRY RECORDS',[(r.get('path'),r.get('sha256')) for r in d['records']])
