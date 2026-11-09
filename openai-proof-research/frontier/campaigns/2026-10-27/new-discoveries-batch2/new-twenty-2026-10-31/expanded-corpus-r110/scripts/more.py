from pathlib import Path
import itertools,json,sys,functools,math,random
D=Path(__file__).resolve().parents[1]
def comp():
 for n in range(2,23,2):
  total=bal=0
  for mask in range(1<<(n-1)):
   p=[];s=0
   for j in range(1,n+1):
    if j==n or mask>>(j-1)&1:p.extend(range(n-j,n-s));s=j
   x=p[0];c=1
   while x!=0:x=p[x];c+=1
   if c==n:total+=1;bal+=mask>>(n//2-1)&1
  print(json.dumps(dict(n=n,compositions=1<<(n-1),cyclic=total,balanced=bal)),flush=True)
def mobius():
 def std(p):return tuple(sorted(p).index(x) for x in p)
 @functools.lru_cache(None)
 def mu(p):
  if len(p)==1:return 1
  pats=set()
  for k in range(1,len(p)):
   for x in itertools.combinations(p,k):pats.add(std(x))
  return -sum(mu(x) for x in pats)
 for n in range(1,5):
  p=list(range(n+1,3*n,2))+[x for i in range(1,n+1) for x in [i,3*n+i]]+list(range(n+2,3*n+1,2))
  print(json.dumps(dict(n=n,permutation=p,mu=mu(std(p)),cached_patterns=mu.cache_info().currsize)),flush=True)
def ulam():
 import numpy as np
 for a in [4,6,8,10,12]:
  for b in [101,103,107,109,127,151,199,251,503]:
   if math.gcd(a,b)!=1:continue
   L=100000;counts=np.zeros(L+1,dtype=np.int32);U=[]
   for x in range(1,L+1):
    if x in [a,b] or counts[x]==1:
     if U:
      v=np.array(U,dtype=int);v=v[v+x<=L];counts[v+x]+=1
     U.append(x)
   even=[x for x in U if x%2==0]
   print(json.dumps(dict(a=a,b=b,integer_embedding='v1=b, v2=a; gcd=1',cutoff=L,terms=len(U),even_terms=len(even),last_even=even[-1] if even else None,last_terms=U[-10:])),flush=True)
def ramsey():
 import numpy as np
 from scipy.optimize import milp,LinearConstraint,Bounds
 from scipy.sparse import lil_matrix
 for a,b in [(3,4),(3,5),(4,4),(3,6)]:
  for n in [(a-1)*(b-1),(a-1)*(b-1)+1]:
   E=list(itertools.combinations(range(n),2));idx={e:i for i,e in enumerate(E)};rows=[];lb=[];ub=[]
   for S in itertools.combinations(range(n),a):rows.append([idx[e] for e in itertools.combinations(S,2)]);lb.append(1);ub.append(np.inf)
   order=[];i=0;j=b-1
   while i<=j:
    order.append(i);i+=1
    if i<=j:order.append(j);j-=1
   paths=set()
   for S in itertools.combinations(range(n),b):
    for r in range(b):
     T=S[r:]+S[:r];p=[T[i] for i in order];paths.add(tuple(sorted(idx[tuple(sorted(e))] for e in zip(p,p[1:]))))
   for row in paths:rows.append(row);lb.append(-np.inf);ub.append(b-2)
   M=lil_matrix((len(rows),len(E)))
   for i,row in enumerate(rows):M[i,row]=1
   r=milp(np.zeros(len(E)),integrality=np.ones(len(E)),bounds=Bounds(0,1),constraints=LinearConstraint(M.tocsr(),lb,ub),options={'time_limit':15})
   print(json.dumps(dict(a=a,b=b,n=n,status=int(r.status),message=r.message,rows=len(rows),cyclic_path_edge_sets=len(paths),witness=None if r.x is None else np.rint(r.x).astype(int).tolist())),flush=True)
if __name__=='__main__':globals()[sys.argv[1]]()
