import json,pathlib,time,itertools
from transfer import transform,PERMS
L=pathlib.Path(__file__).parent;start=time.monotonic();results=[]
for name in ['F','C']:
 t=json.loads((L/(name+'-table.json')).read_text());es=t['edges'];ps=t['ports'];n=t['vertices'];items=[list(e) for e in es]+[[v,-1] for v in ps]
 incident=[[i for i,(a,b) in enumerate(items) if v in (a,b)] for v in range(n)];col=[-1]*len(items);raw={};leaves=0
 def visit(i,used):
  global leaves
  if i==len(items):
   leaves+=1
   stars=[{col[j] for j in ii} for ii in incident];d=sum(len(stars[a]|stars[b])==4 for a,b in es)
   if d<=2:
    s=tuple((col[len(es)+j],sum(1<<c for c in stars[v])) for j,v in enumerate(ps));raw[s]=min(raw.get(s,3),d)
   return
  a,b=items[i];forbid={col[j] for v in [a,b] if v>=0 for j in incident[v] if j<i}
  for c in range(min(used+1,5)):
   if c not in forbid:col[i]=c;visit(i+1,max(used,c+1))
  col[i]=-1
 visit(0,0)
 allstates={}
 for r in t['rows']:
  for p in PERMS:
   s=transform(r['state'],p);allstates[s]=min(allstates.get(s,3),r['cost'])
 assert all(allstates[s]==d for s,d in raw.items())
 # Every emitted orbit also has a directly enumerated representative.
 keys={min(transform(s,p) for p in PERMS) for s in raw};assert keys=={tuple(map(tuple,r['state'])) for r in t['rows']}
 results.append({'name':name,'all_proper_canonical_colorings':leaves,'surviving_boundary_states':len(raw),'table_exact':True})
out={'pass':True,'independent_no_defect_pruning_enumeration':results,'seconds':time.monotonic()-start};(L/'exhaustive-verification.json').write_text(json.dumps(out,indent=2));print(out)
