import pathlib,json
P=pathlib.Path(__file__).parent;L=P.parent;ids={x['mathdb_id'] for x in json.loads((L/'root-mathdb-breadth-intake-r705/queue-r706.json').read_text())}
out={}
for path in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 obj=json.loads(path.read_text());hits=[]
 def scan(o):
  if isinstance(o,dict):
   if any(isinstance(v,int) and v in ids for k,v in o.items() if 'id' in k) or any(isinstance(v,list) and any(isinstance(i,int) and i in ids for i in v) for k,v in o.items() if 'id' in k):hits.append(o)
   else:
    for v in o.values():scan(v)
  elif isinstance(o,list):
   for v in o:scan(v)
 scan(obj);out[str(path)]={'top_level_keys':list(obj)[:12] if isinstance(obj,dict) else None,'direct_assigned_id_hits':hits}
(P/'context-screen.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
