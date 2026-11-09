import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np,random,itertools,json,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));rng=random.Random(95002)
def connected(n,es):
 seen={0}
 while 1:
  new=seen|{v for u,v in es if u in seen}|{u for u,v in es if v in seen}
  if seen==new:return len(seen)==n
  seen=new

def calc(n,es):
 A=np.zeros((n,n));adj=[set() for _ in range(n)]
 for u,v in es:A[u,v]=A[v,u]=1;adj[u].add(v);adj[v].add(u)
 cs=[1]*n
 def cliq(R,P,X):
  if not P and not X:
   for x in R:cs[x]=max(cs[x],len(R))
   return
  pivot=max(P|X,key=lambda x:len(P&adj[x])) if P|X else 0
  for v in list(P-adj[pivot]):cliq(R|{v},P&adj[v],X&adj[v]);P.remove(v);X.add(v)
 cliq(set(),set(range(n)),set());ev=np.linalg.eigvalsh(A);lhs=sum(x*x for x in ev if x>0);rhs=sum(1-1/x for x in cs)**2
 ds=A.sum(axis=0);nz=np.maximum(ds,1);R=A/np.sqrt(nz[:,None]*nz[None,:]);energy=sum(abs(np.linalg.eigvalsh(R)))
 return lhs,rhs,energy
for n in [2,3,4,5,6,10,11,12,14,16,20]:
 bestmargin=0;tested=0;viol=[];maxtree=0;maxcyclic=0
 pairs=list(itertools.combinations(range(n),2))
 masks=range(1<<len(pairs)) if n<=6 else range(2400)
 for mask in masks:
  if n<=6:es=[e for i,e in enumerate(pairs) if mask>>i&1]
  else:
   # connected recursive tree plus sparse/dense added edges
   es=[(rng.randrange(v),v) for v in range(1,n)];p=rng.choice([0,.02,.07,.15,.3,.5,.8]);es=list(set(es)|{e for e in pairs if rng.random()<p})
  if not connected(n,es):continue
  lhs,rhs,en=calc(n,es);tested+=1;bestmargin=min(bestmargin,rhs-lhs)
  if lhs>rhs+1e-7:viol.append({'edges':es,'lhs2':lhs,'rhs2':rhs})
  if len(es)==n-1:maxtree=max(maxtree,en)
  else:maxcyclic=max(maxcyclic,en)
 print(json.dumps({'n':n,'connected_tested':tested,'elw_violations':viol,'smallest_margin_capped_at_zero':bestmargin,'max_sample_tree_RE':maxtree,'max_sample_cyclic_RE':maxcyclic,'randic_scope':'comparison among sample only; not against every tree when n>6'}),flush=True)
