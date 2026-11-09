import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];C=D.parent;B=C.parent
out={}
for p in [C/'ledger.json',B/'ledger.json',B/'prior-campaign-context.json']:
 b=p.read_bytes();o=json.loads(b);out[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'keys':list(o),'families':{k:v for k,v in o.items() if k in ['accepted','excluded_after_review','excluded','rejected','prior_accepted','accepted_results']}}
(D/'outputs/inherited-context.json').write_text(json.dumps(out,indent=2))
for p,o in out.items():
 print(p,o['sha256'])
 for k,v in o['families'].items():
  print(k)
  if isinstance(v,list):
   for x in v:print(str({a:b for a,b in x.items() if a in ['mathdb_id','title','scope','reason','status']})[:1000] if isinstance(x,dict) else str(x)[:1000])
  else: print(str(v)[:6000])
