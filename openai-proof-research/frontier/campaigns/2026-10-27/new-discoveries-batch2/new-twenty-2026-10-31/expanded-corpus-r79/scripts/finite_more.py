import pathlib,sys,itertools as it,json,math,collections
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'deps'));import networkx as nx
from functools import lru_cache

def emit(i,o):(D/'outputs'/f'search-{i}.json').write_text(json.dumps(o,indent=2)+'\n')
mode=sys.argv[1]
if mode=='permutations':
 def stack(p):
  if not p:return ()
  j=p.index(max(p));return stack(p[:j])+stack(p[j+1:])+(p[j],)
 out=[]
 for n in [1,3,5,7,9]:
  c=collections.Counter(stack(p) for p in it.permutations(range(1,n+1)));a=[0]*n
  for p,v in c.items():
   if v==1:a[p[0]-1]+=1
  out.append({'n':n,'permutations':math.factorial(n),'counts':a,'log_concave':all(a[j]**2>=a[j-1]*a[j+1] for j in range(1,n-1))});emit(347634,{'definition':'West recursive stack-sorting map; outputs with unique preimage counted by first entry','cases':out})
elif mode=='tournaments':
 counts={};bad=[]
 for n in [1,3,5]:
  counts[n]=0;pairs=list(it.combinations(range(n),2))
  for mask in range(1<<len(pairs)):
   arcs={(u,v) if mask>>j&1 else (v,u) for j,(u,v) in enumerate(pairs)}
   if any(sum(u==x for u,v in arcs)!=(n-1)//2 for x in range(n)):continue
   counts[n]+=1
   cycles=[]
   for p in it.permutations(range(1,n)):
    q=(0,)+p;es=frozenset(zip(q,q[1:]+q[:1]))
    if es<=arcs:cycles.append(es)
   def rec(left):
    if not left:return True
    a=min(left)
    return any(c<=left and rec(left-c) for c in cycles if a in c)
   if not rec(arcs):bad.append(mask)
  emit(355131,{'scope':'all labelled tournaments on 1,3,5 vertices; all regular ones tested by exact Hamilton cycle cover','regular_counts':counts,'failures':bad})
elif mode=='matchings':
 out=[]
 for n in [1,3,5,7,9]:
  @lru_cache(None)
  def dp(pos,mask,used):
   if pos==n*n:return int(mask==0 and used)
   if mask&1:return dp(pos+1,mask>>1,used)
   ans=dp(pos+1,mask>>1,True) if not used else 0
   if pos%n<n-1 and mask&2==0:ans+=dp(pos+1,(mask|2)>>1,used)
   if pos//n<n-1:ans+=dp(pos+1,(mask|(1<<n))>>1,used)
   return ans
  a=dp(0,0,False);k=(n-1)//2;out.append({'side':n,'a':a,'c':a//2**k,'c_mod8':(a//2**k)%8,'states':dp.cache_info().currsize});emit(367029,{'scope':'exact all monomer-domino tilings with exactly one monomer on square grids sides 1,3,5,7,9; transfer DP enumerates each matching once','cases':out})
elif mode=='schur':
 out=[]
 for c in [1,2,3]:
  a=[];nodes=[0]
  def rec(N):
   if len(a)==N:return a.copy()
   x=len(a)+1
   for z in range(min(c,max(a,default=-1)+2)):
    nodes[0]+=1
    if all(not(a[y-1]==z and a[x-y-1]==z) for y in range(1,x)):
     a.append(z);r=rec(N)
     if r:return r
     a.pop()
   return None
  N=1
  while True:
   a=[];w=rec(N)
   if w is None:break
   N+=1
  out.append({'colors':c,'S':N-1,'tested_unsat_N':N,'nodes':nodes[0]});emit(346739,{'definition':'S(r) maximum N admitting r-coloring of [1,N] with no x+y=z monochromatic (x=y allowed)','scope':'exhaustive restricted-growth color assignments r=1,2,3','cases':out})
elif mode=='circles':
 from finite import color
 out=[];bad=[]
 for G in nx.graph_atlas_g():
  n=len(G)
  if n==0 or not nx.check_planarity(G)[0]:continue
  for t in range(1,5):
   if any(len(c)<2*t for c in nx.simple_cycles(G)):continue
   p,q=2*t+2,t;a=[-1]*n
   def rec(j):
    if j==n:return True
    for x in range(p):
     if all(a[u]<0 or q<=abs(x-a[u])<=p-q for u in G[j]):
      a[j]=x
      if rec(j+1):return True
    a[j]=-1;return False
   ok=rec(0);out.append([n,t,ok])
   if not ok:bad.append([nx.to_graph6_bytes(G,header=False).decode().strip(),t])
 emit(347082,{'scope':'all simple graphs up to order7 in networkx graph atlas, filtered planar and girth>=2t for t=1..4; exact (2t+2,t) circular color CSP','cases_tested':len(out),'failures':bad})
