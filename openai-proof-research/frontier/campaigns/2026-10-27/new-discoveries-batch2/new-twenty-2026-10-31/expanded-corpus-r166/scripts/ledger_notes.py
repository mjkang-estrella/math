import pathlib,json,hashlib
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166');out=[]
for rel in ['../ledger.json','../../ledger.json','../../prior-campaign-context.json']:
 p=D/rel;j=json.loads(p.read_text());x={'path':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'families':{}}
 for k in ['accepted','excluded','excluded_after_review','held_candidates','candidates']:
  a=j.get(k,[])
  if isinstance(a,list):x['families'][k]=[{q:v for q,v in r.items() if q in ['mathdb_id','title','reason','status','scope','source_target']} for r in a if isinstance(r,dict)]
 out.append(x)
(D/'outputs/inherited-family-screen.json').write_text(json.dumps(out,indent=2))
for x in out:
 print(x['path'])
 for k,a in x['families'].items():
  print(k,len(a))
  if k=='accepted':print('; '.join(str(r.get('mathdb_id'))+' '+str(r.get('title','')) for r in a))
