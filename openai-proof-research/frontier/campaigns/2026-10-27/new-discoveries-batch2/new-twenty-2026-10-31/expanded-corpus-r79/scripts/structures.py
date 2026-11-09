import pathlib,sys,json,itertools as it,math
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'deps'));import networkx as nx
from finite import color
from functools import lru_cache
mode=sys.argv[1]
def emit(i,o):(D/'outputs'/f'search-{i}.json').write_text(json.dumps(o,indent=2)+'\n')
if mode=='rainbow':
 out=[]
 for k in range(1,13):
  N=120;G=nx.Graph();G.add_nodes_from(range(N))
  for s in range(1,N//k+1):G.add_edges_from((a*s-1,b*s-1) for a in range(1,k+1) for b in range(a+1,k+1))
  w=color(G,[range(k)]*N);out.append({'k':k,'N':N,'edges':len(G.edges),'coloring':w});emit(346691,{'scope':'all homogeneous progressions of length k contained in [1,120], k=1..12; exact color CSP with no search-node cap (outer process capped)','cases':out})
elif mode=='rank2':
 def partitions(n):
  a=[0]*n
  def rec(j,m):
   if j==n:yield a.copy();return
   for z in range(m+2):a[j]=z;yield from rec(j+1,max(z,m))
  a[0]=0;yield from rec(1,0)
 def pairs(xs):
  if not xs:yield [];return
  a,*rest=xs
  for p in pairs(rest):yield [(a,)]+p
  for j,b in enumerate(rest):
   for p in pairs(rest[:j]+rest[j+1:]):yield [(a,b)]+p
 n=6;k=3;cnt=0;bad=[];Ps=list(pairs(list(range(n))))
 def pm(edges,vs):
  if not vs:return True
  a=min(vs)
  return any((min(a,b),max(a,b)) in edges and pm(edges,vs-{a,b}) for b in vs-{a})
 for parallel in partitions(n):
  if max(parallel)==0 or max(parallel.count(z) for z in set(parallel))>k:continue
  for P in Ps:
   banned={tuple(sorted(x)) for x in P if len(x)==2};edges={(a,b) for a in range(n) for b in range(a+1,n) if parallel[a]!=parallel[b] and (a,b) not in banned};cnt+=1
   if not pm(edges,set(range(n))):bad.append([parallel,P])
 emit(355100,{'scope':'all loopless labelled rank2 matroids on 6 elements with maximum parallel class<=3 (equivalent to 3-base), all partitions into singles/pairs; exact perfect matching in allowable pairs','partition_count':len(Ps),'instances':cnt,'failures':bad})
elif mode=='cycles':
 counts={};bad=[]
 for k in range(2,5):
  counts[k]=0
  for G in nx.graph_atlas_g():
   n=len(G)
   if n==0 or 2*len(G.edges)<(2*k+1)*n:continue
   counts[k]+=1
   if not any(len(c)%(2*k)==2 for c in nx.simple_cycles(G) if len(c)>=3):bad.append([k,n,nx.to_graph6_bytes(G,header=False).decode().strip()])
 emit(356366,{'scope':'all graph atlas graphs of orders1..7, k=2..4, density premise exact 2m>=(2k+1)n; checks existence of simple cycle length2 mod2k; cannot prove optimal coefficient','eligible_counts':counts,'failures':bad})
elif mode=='height2':
 vals={};cnt=0
 for n in range(1,8):
  found=set()
  for a in range(1,n):
   b=n-a
   for mask in range(1<<(a*b)):
    pred=[0]*n
    for i in range(a):
     for j in range(b):
      if mask>>(i*b+j)&1:pred[a+j]|=1<<i
    if not any(pred):continue
    @lru_cache(None)
    def dp(S):
     if S==(1<<n)-1:return 1
     return sum(dp(S|1<<v) for v in range(n) if not S>>v&1 and pred[v]&S==pred[v])
    found.add(dp(0));cnt+=1
  vals[n]=sorted(found);emit(360638,{'scope':'all labelled height-exactly-two posets represented by bipartitions a+b=n for n<=7 (duplicate representations permitted), all bipartite relations; subset DP linear extension counts','representations':cnt,'values_by_order':vals,'warning':'absence in bounded n cannot refute sufficiently-large-m universality'})
