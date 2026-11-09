import os,resource,pathlib,json,itertools,functools,time
os.environ['OPENBLAS_NUM_THREADS']='1';os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import networkx as nx
D=pathlib.Path(__file__).resolve().parents[1];out={};start=time.time()
def colorable(edges,k,n):
 masks=[0]*n;es=sorted(edges,key=lambda e:-sum(sum(v in f for f in edges) for v in e))
 def go(t,used):
  if t==len(es):return True
  u,v=es[t];avail=((1<<min(k,used+1))-1)&~(masks[u]|masks[v])
  while avail:
   b=avail&-avail;avail-=b;masks[u]|=b;masks[v]|=b
   if go(t+1,max(used,b.bit_length())):return True
   masks[u]^=b;masks[v]^=b
  return False
 return go(0,0)
def matchings(G):
 es=list(G.edges());ans=[]
 def rec(j,mask,chosen):
  if j==len(es):ans.append(tuple(chosen));return
  rec(j+1,mask,chosen);u,v=es[j]
  if not mask&((1<<u)|(1<<v)):rec(j+1,mask|(1<<u)|(1<<v),chosen+[j])
 rec(0,0,[]);return es,ans
counts={str(i):0 for i in [381469,381703,381704]};bad=[]
for G in nx.graph_atlas_g():
 n=len(G)
 if n<2 or not nx.is_connected(G):continue
 es=list(G.edges());deg=max(dict(G.degree()).values());regular=len(set(dict(G.degree()).values()))==1
 if regular and deg>=3:
  e,ms=matchings(G);maximal=[m for m in ms if all(any(set(e[j])&set(f) for j in m) for f in e)];gamma=min(map(len,maximal));counts['381469']+=1
  if 4*deg*gamma>(2*deg-1)*n+2*deg:bad.append({'id':381469,'edges':es,'value':gamma})
 if colorable(es,deg,n):continue
 counts['381703']+=1
 # A class-I decomposition corresponds to grouping a proper (Delta+1)-edge coloring;
 # directly enumerate every edge bipartition, exact degree maxima p,q and both colorability checks.
 for p in range(1,deg+1):
  q=deg+1-p
  if q>deg or p>q:continue
  found=False
  for mask in range(1<<len(es)):
   A=[e for j,e in enumerate(es) if mask>>j&1];B=[e for j,e in enumerate(es) if not mask>>j&1]
   if max([sum(v in e for e in A) for v in range(n)])!=p or max([sum(v in e for e in B) for v in range(n)])!=q:continue
   if colorable(A,p,n) and colorable(B,q,n):found=True;break
  if not found:bad.append({'id':381703,'edges':es,'p':p,'q':q})
 if regular:
  counts['381704']+=1;e,ms=matchings(G);maximum=[m for m in ms if len(m)==max(map(len,ms))]
  resistance=None
  for r in range(len(es)+1):
   good=[]
   for rem in itertools.combinations(range(len(es)),r):
    if colorable([f for j,f in enumerate(es) if j not in rem],deg,n):good.append(set(rem))
   if good:resistance=r;break
  for m in maximum:
   if not any(s<=set(m) for s in good):bad.append({'id':381704,'edges':es,'matching':m,'resistance':resistance})
 print(n,nx.to_graph6_bytes(G,header=False).decode().strip(),counts,flush=True)
 # expensive dense n7 class II decompositions may exceed cap; each completed graph logged.
out={'space':'NetworkX graph atlas, connected simple unlabeled graphs of orders 2..7; completed prefix in log','counts':counts,'counterexamples':bad,'seconds':time.time()-start};(D/'outputs/graph-search.json').write_text(json.dumps(out,indent=2));print(out)
