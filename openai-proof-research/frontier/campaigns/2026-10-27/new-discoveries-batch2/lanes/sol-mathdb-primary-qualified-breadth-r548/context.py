import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;ids={r['mathdb_id'] for r in json.loads((P/'dispositions.json').read_text())}
refs=json.loads((P/'flat-bindings.json').read_text())
guard=L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';b=guard.read_bytes();refs.append({'path':str(guard),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()});(P/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
result={}
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-breadth-intake-r547/adjudications.json',L/'root-mathdb-breadth-intake-r547/hypothesis-queue.json']:
 obj=json.loads(p.read_text());matches=[]
 def visit(x,path=''):
  if isinstance(x,dict):
   for k,v in x.items():
    if k in {'mathdb_id','id','problem_id'} and isinstance(v,int) and v in ids:matches.append({'location':path+'/'+k,'value':v})
    visit(v,path+'/'+k)
  elif isinstance(x,list):
   for n,v in enumerate(x):visit(v,path+'/'+str(n))
 visit(obj);result[str(p)]={'assigned_id_matches':matches,'top_level_keys':list(obj) if isinstance(obj,dict) else None}
 if 'accepted-exclusions' in str(p):result[str(p)]['family_scopes']=[{'number':r['number'],'title':r['title'],'scope':r.get('scope')} for r in obj.get('families',[])]
(P/'context-check.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:{'matches':v['assigned_id_matches'],'family_count':len(v.get('family_scopes',[]))} for k,v in result.items()},indent=2))
