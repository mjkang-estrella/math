import os,resource,time,itertools,json,functools
resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);import networkx as nx
start=time.time();out={'field':'F2','method':'multigraded Koszul homology, exponents 0..s; Taylor lcm bound excludes larger degrees','coverage':[],'counterexamples':[]}
def rank(cols):
 p={}
 for x in cols:
  while x:
   k=x.bit_length()-1
   if k in p:x^=p[k]
   else:p[k]=x;break
 return len(p)
def reg(G,s,symbolic=False):
 n=len(G);E=list(G.edges());covers=[tuple(v for v in range(n)if not mask>>v&1)for mask in range(1<<n)if all(not(mask>>a&1 and mask>>b&1)for a,b in E)and all(mask>>v&1 or any(mask>>u&1 for u in G[v])for v in range(n))]
 @functools.lru_cache(None)
 def ordinary(a,k):
  if k==0:return True
  if sum(a)<2*k:return False
  for u,v in E:
   if a[u] and a[v]:
    b=list(a);b[u]-=1;b[v]-=1
    if ordinary(tuple(b),k-1):return True
  return False
 def member(a):return all(sum(a[v]for v in C)>=s for C in covers)if symbolic else ordinary(a,s)
 best=-1;checked=0
 for a in itertools.product(range(s+1),repeat=n):
  if sum(a)<=best:continue
  if not member(a):continue
  support=[i for i,x in enumerate(a)if x];fac=[[]for _ in range(n+1)]
  for mask in range(1<<len(support)):
   S=tuple(support[i]for i in range(len(support))if mask>>i&1);b=list(a)
   for i in S:b[i]-=1
   if member(tuple(b)):fac[len(S)].append(S)
  ranks=[0]*(n+2)
  for i in range(1,n+1):
   idx={S:j for j,S in enumerate(fac[i-1])};ranks[i]=rank([sum(1<<idx[S[:k]+S[k+1:]]for k in range(len(S)))for S in fac[i]])
  for i in range(n+1):
   if len(fac[i])-ranks[i]-ranks[i+1]>0:best=max(best,sum(a)-i)
  checked+=1
  if time.time()-start>100:raise TimeoutError
 return best,checked
try:
 for G in nx.graph_atlas_g():
  n=len(G)
  if n<2 or n>5 or not G.number_of_edges()or any(d==0 for v,d in G.degree()):continue
  if any(G.subgraph(I).number_of_edges()==2 and sorted(dict(G.subgraph(I).degree()).values())==[1]*4 for I in itertools.combinations(range(n),4)):continue
  r,_=reg(G,1)
  for s in [4,5]:
   a,ca=reg(G,s);b,cb=reg(G,s,True);expected=max(r+s-1,2*s);row={'graph6':nx.to_graph6_bytes(G,header=False).decode().strip(),'n':n,'s':s,'regI':r,'ordinary_reg':a,'symbolic_reg':b,'expected':expected,'multidegrees_with_membership_checked':[ca,cb]};out['coverage'].append(row)
   if a!=expected or b!=expected:out['counterexamples'].append(row)
   out['seconds']=time.time()-start;json.dump(out,open('outputs/regularity.json','w'),indent=2)
except TimeoutError:out['time_cap']=True
out['seconds']=time.time()-start;json.dump(out,open('outputs/regularity.json','w'),indent=2);print('completed',len(out['coverage']),'counterexamples',out['counterexamples'])
