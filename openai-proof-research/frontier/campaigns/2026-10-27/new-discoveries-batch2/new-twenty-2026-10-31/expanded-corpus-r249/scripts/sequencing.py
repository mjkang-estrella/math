import pathlib,json,random,itertools
L=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(249);out=[]
for mods in [(49,),(51,),(57,),(63,),(75,),(81,),(3,3,3,3),(3,3,9)]:
 els=list(itertools.product(*(range(m) for m in mods)));lookup={v:i for i,v in enumerate(els)};N=len(els)
 add=[[lookup[tuple((a+b)%m for a,b,m in zip(x,y,mods))] for y in els] for x in els];inv=[next(j for j in range(N) if add[i][j]==0) for i in range(N)]
 pairs=[(i,inv[i]) for i in range(1,N) if i<inv[i]];found=0;tested=0;cap=0;maxnodes=0;certs=[]
 for trial in range(80000):
  k=min(26,len(pairs));A=[rng.choice(p) for p in rng.sample(pairs,k)];s=0
  for a in A:s=add[s][a]
  if s:continue
  tested+=1;nodes=[0]
  def dfs(left,s,seen,path):
   nodes[0]+=1
   if nodes[0]>100000:return None
   if not left:return path
   for a in left:
    t=add[s][a]
    if t in seen:continue
    if t==0 and len(left)>1:continue
    r=dfs([b for b in left if b!=a],t,seen|{t},path+[a])
    if r is not None:return r
   return None
  order=dfs(A,0,set(),[]);maxnodes=max(maxnodes,nodes[0])
  if order is not None:
   partial=[];s=0
   for a in order:s=add[s][a];partial.append(s)
   assert sorted(order)==sorted(A) and len(set(partial))==k and partial[-1]==0
   found+=1;certs.append(dict(subset=A,order=order))
  else:cap+=1
  if tested==200:break
 r=dict(moduli=mods,order=N,subset_size=k,trials=trial+1,tested=tested,witnesses=found,unresolved=cap,max_DFS_nodes=maxnodes,certificates=certs);out.append(r);print({a:b for a,b in r.items() if a!='certificates'},flush=True)
(L/'sequencing-results.json').write_text(json.dumps(out,indent=2))
