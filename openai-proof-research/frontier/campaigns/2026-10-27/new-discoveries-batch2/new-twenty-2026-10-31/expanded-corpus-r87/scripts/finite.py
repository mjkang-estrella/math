import sys,time,json,itertools as it,random,math
from pathlib import Path
D=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(D/'vendor'))
mode=sys.argv[1]; rng=random.Random(8701)
def emit(x): print(json.dumps(x),flush=True)
if mode=='cubes':
 import networkx as nx
 # Appendix A excludes k=d. Test intended nondegenerate range 3<=k<d.
 for d in range(4,10):
  groups={};count=0;cross=0;isos=[];start=time.monotonic()
  for k in range(3,d):
   for bits in it.product('01',repeat=k):
    f=''.join(bits); comp=lambda s: ''.join('1' if c=='0' else '0' for c in s)
    if f!=min(f,f[::-1],comp(f),comp(f[::-1])):continue
    vs=[x for x in range(2**d) if f not in format(x,f'0{d}b')];V=set(vs)
    g=nx.Graph();g.add_nodes_from(vs);g.add_edges_from((x,x^(1<<i)) for x in vs for i in range(d) if x^(1<<i) in V)
    nu=sum(a!=b for a,b in zip(f,f[1:]));count+=1
    key=(len(g),g.number_of_edges(),tuple(sorted(dict(g.degree()).values())))
    for old,h,n in groups.get(key,[]):
     if n==nu:continue
     cross+=1
     if nx.is_isomorphic(g,h):isos.append([old,f,n,nu])
    groups.setdefault(key,[]).append((f,g,nu))
  emit(dict(d=d,representatives=count,cross_index_isomorphism_tests=cross,counterexamples=isos,seconds=time.monotonic()-start))
elif mode=='sequences':
 # A sequence extends iff at least two coordinates strictly increase from EACH earlier triple.
 for n in range(2,6):
  vs=list(it.product(range(n),repeat=3));N=len(vs);succ=[]
  for a in vs:
   succ.append(sum(1<<j for j,b in enumerate(vs) if sum(x<y for x,y in zip(a,b))>=2))
  best=[];nodes=0;start=time.monotonic();deadline=start+22;complete=True
  def dfs(seq,cand):
   global nodes,best
   nodes+=1
   if nodes%16384==0 and time.monotonic()>deadline:raise TimeoutError
   if len(seq)>len(best):best=seq[:]
   if len(seq)+cand.bit_count()<=len(best):return
   while cand:
    bit=cand&-cand;cand-=bit;v=bit.bit_length()-1
    # Other candidate orderings must remain available: relation is not transitive.
    dfs(seq+[v],(cand|remaining[v])&succ[v])
  # Full sequence DFS cannot remove earlier first-choice candidates, because they can occur later.
  def dfs2(seq,cand):
   global nodes,best
   nodes+=1
   if nodes%16384==0 and time.monotonic()>deadline:raise TimeoutError
   if len(seq)>len(best):best=seq[:]
   if len(seq)+cand.bit_count()<=len(best):return
   while cand:
    bit=cand&-cand;cand-=bit;v=bit.bit_length()-1
    dfs2(seq+[v],eligible(seq+[v]))
  def eligible(seq):
   c=(1<<N)-1
   for v in seq:c &= succ[v]
   return c
  try:dfs2([], (1<<N)-1)
  except TimeoutError:complete=False
  emit(dict(n=n,complete=complete,nodes=nodes,maximum_if_complete=len(best),best=[vs[v] for v in best],bound_squared=n**3,seconds=time.monotonic()-start))
elif mode=='ryser':
 # Every edge meets EACH of the three parts once; exact matching DP on edge masks.
 for sizes,iterations in [((2,2,2),None),((3,3,3),10000),((2,2,2,2),None)]:
  edges=[];off=[sum(sizes[:i]) for i in range(len(sizes))]
  for t in it.product(*(range(x) for x in sizes)):edges.append(sum(1<<(off[i]+x) for i,x in enumerate(t)))
  N=sum(sizes); r=len(sizes); tested=0;bad=[];start=time.monotonic()
  patterns=range(1,1<<len(edges)) if iterations is None else (rng.randrange(1,1<<len(edges)) for _ in range(iterations))
  for pattern in patterns:
   es=tuple(e for j,e in enumerate(edges) if pattern>>j&1)
   from functools import lru_cache
   @lru_cache(None)
   def matching(avail):
    possible=[e for e in es if e&avail==e]
    if not possible:return 0
    e=possible[0];v=e&-e
    return max(matching(avail^v),max(1+matching(avail^q) for q in possible if q&v))
   full=(1<<N)-1;nu=matching(full);found=False
   for k in range(1,r):
    for s in it.combinations(range(N),k):
     mask=sum(1<<v for v in s)
     if matching(full^mask)<nu:found=True;break
    if found:break
   tested+=1
   if not found:bad.append(pattern);break
  emit(dict(parts=sizes,tested=tested,exhaustive=iterations is None,counterexamples=bad,seconds=time.monotonic()-start))
elif mode=='squares':
 from shapely.geometry import Polygon
 from shapely.ops import unary_union
 from shapely.affinity import rotate,translate
 square=Polygon([(-.5,-.5),(.5,-.5),(.5,.5),(-.5,.5)])
 best=(0,None);tested=0;start=time.monotonic()
 for n in (2,3,4,6,8,12,20):
  local=0
  for j in range(1000):
   scale=rng.choice([.15,.3,.6,1,2]);params=[(rng.uniform(-scale,scale),rng.uniform(-scale,scale),rng.uniform(0,90)) for _ in range(n)]
   u=unary_union([translate(rotate(square,a),x,y) for x,y,a in params]);ratio=u.length/u.area;tested+=1
   if ratio>best[0]:best=(ratio,params)
   local=max(local,ratio)
  emit(dict(n=n,tested=1000,max_ratio=local,global_best=best[0],seconds=time.monotonic()-start))
 (D/'outputs/squares-best.json').write_text(json.dumps(best,indent=2)+'\n')
