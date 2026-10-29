import itertools,json,pathlib,sys
b=pathlib.Path(__file__).resolve().parent
out={'graphs':0,'rooted':0,'positive_excess':[],'max_root_3cost_minus_m':-100,'max_bridge_3cost_minus_m1':-100,'witnesses':[]}
def graphs():
 for n in range(2,7):
  pairs=list(itertools.combinations(range(n),2));lo,hi=(0,1<<len(pairs))
  if n==6:
   shard=int(sys.argv[1]);lo=shard*8192;hi=lo+8192
  elif int(sys.argv[1])!=0:continue
  for mask in range(lo,hi):
   edges=[e for i,e in enumerate(pairs) if mask>>i&1]
   seen={0}
   for _ in range(n):
    for u,v in edges:
     if u in seen or v in seen:seen.update((u,v))
   if len(seen)==n:yield n,edges
for n,edges in graphs():
 m=len(edges);opts=[m]*n;bridge=[m+1]*n
 full=m
 for mask in range(1<<m):
  cost=m-mask.bit_count()
  deg=[0]*n;kept=[]
  for i,(u,v) in enumerate(edges):
   if mask>>i&1:deg[u]+=1;deg[v]+=1;kept.append((u,v))
  bad={x for u,v in kept if deg[u]==deg[v] for x in (u,v)}
  if not bad:full=min(full,cost)
  for r in range(n):
   # Glued root is unconstrained but all other degrees are literal.
   if all(u==r or v==r or deg[u]!=deg[v] for u,v in kept):opts[r]=min(opts[r],cost)
   if not bad:bridge[r]=min(bridge[r],cost+1)
   if all((deg[u]+(u==r))!=(deg[v]+(v==r)) for u,v in kept):bridge[r]=min(bridge[r],cost)
 out['graphs']+=1;out['rooted']+=n
 for r in range(n):
  a=3*opts[r]-m;c=3*bridge[r]-(m+1)
  out['max_root_3cost_minus_m']=max(out['max_root_3cost_minus_m'],a)
  out['max_bridge_3cost_minus_m1']=max(out['max_bridge_3cost_minus_m1'],c)
  if a>0 or c>0:out['positive_excess'].append({'n':n,'edges':edges,'root':r,'rootcost':opts[r],'bridgecost':bridge[r]})
 if 3*full-m>2:out['witnesses'].append({'edges':edges,'n':n,'Ie':full,'excess3':3*full-m})
(b/('checks-'+sys.argv[1]+'.json')).write_text(json.dumps(out,indent=2));print(json.dumps(out))
