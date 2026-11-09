"""Discovery only: bounded enumeration, integer coordinates, floating LP, exact witness verification."""
from pathlib import Path
from itertools import combinations
import numpy as np
from scipy.optimize import linprog
import json,random,time
P=Path(__file__).parent

def adj(E):
 a={}
 for u,v in E:a.setdefault(u,[]).append(v);a.setdefault(v,[]).append(u)
 return a

def edge(u,v):return tuple(sorted((u,v)))
def canon(E,n):
 a=adj(E);out=[]
 for u,v in E:
  seen={v};stack=[u];leaves=[]
  while stack:
   x=stack.pop();seen.add(x)
   if 0<=x<n:leaves.append(x)
   stack.extend(y for y in a[x] if y not in seen)
  b=sum(1<<x for x in leaves);out.append(min(b,((1<<n)-1)^b))
 return tuple(sorted(out))
def trees(n):
 ts=[((-1,0),(-1,1),(-1,2))]
 for k in range(3,n):
  new=[]
  for E in ts:
   for i,(u,v) in enumerate(E):new.append(E[:i]+E[i+1:]+(edge(u,-k+1),edge(v,-k+1),edge(k,-k+1)))
  ts=new
 return ts

def weights(E,n):
 a=adj(E);vals={}
 for i in range(n):
  stack=[(i,-999,0)]
  while stack:
   x,pa,d=stack.pop()
   if x>i:vals[i,x]=1<<(n-1-d) # scale 2^(n-2)
   stack.extend((y,x,d+1) for y in a[x] if y!=pa)
 return [vals[i,j] for i,j in combinations(range(n),2)]

def tbr(E,n):
 out={};a=adj(E)
 for u,v in E:
  if u>=0 or v>=0:continue # leaf cuts are SPR, covered by source theorem
  F=set(E);F.remove(edge(u,v))
  for x,y in [(u,v),(v,u)]:
   z=[z for z in a[x] if z!=y]
   for q in z:F.remove(edge(x,q))
   F.add(edge(*z))
  b=adj(F);seen=set();stack=[a[u][0] if a[u][0]!=v else a[u][1]]
  while stack:
   x=stack.pop()
   if x in seen:continue
   seen.add(x);stack.extend(b[x])
  L=[e for e in F if e[0] in seen];R=[e for e in F if e[0] not in seen]
  for e in L:
   for f in R:
    G=tuple(F-{e,f})+(edge(e[0],u),edge(e[1],u),edge(f[0],v),edge(f[1],v),edge(u,v))
    out[canon(G,n)]=G
 return out

def run(n,cap=40):
 start=time.time();ts=trees(n);keys={canon(E,n):i for i,E in enumerate(ts)};W=np.array([weights(E,n) for E in ts],dtype=np.int16)
 rng=random.Random(319783+n);bases=rng.sample(range(len(ts)),min(4,len(ts)));tested=0;logs=[]
 for base in bases:
  near=list(tbr(ts[base],n).items());rng.shuffle(near)
  for key,G in near:
   j=keys[key]
   if j==base:continue
   ids=[i for i in range(len(ts)) if i not in (base,j)]
   # convex hull others meets the open segment; exact endpoint extremality still a proof obligation
   A=np.vstack([np.column_stack([W[ids].T,(W[j]-W[base])]),np.r_[np.ones(len(ids)),0]])
   b=np.r_[W[j],1]
   res=linprog(np.zeros(len(ids)+1),A_eq=A,b_eq=b,bounds=[(0,None)]*len(ids)+[(0,1)],method='highs',options={'time_limit':15})
   tested+=1
   logs.append({'base':base,'target':j,'status':res.status})
   if res.success:
    from fractions import Fraction
    support=np.flatnonzero(res.x[:-1]>1e-8);co=[Fraction(float(res.x[k])).limit_denominator(10**7) for k in support];t=Fraction(float(res.x[-1])).limit_denominator(10**7)
    exact=sum(co)==1 and 0<t<1 and all(sum(c*int(W[ids[k],d]) for c,k in zip(co,support))+t*int(W[j,d]-W[base,d])==int(W[j,d]) for d in range(W.shape[1]))
    cert={'n':n,'E':ts[base],'F':ts[j],'others':[ts[ids[k]] for k in support],'coefficients':[str(c) for c in co],'t':str(t),'exact_coordinate_check':exact}
    (P/f'bme-candidate-{n}.json').write_text(json.dumps(cert,indent=2));print('CANDIDATE',n,exact,flush=True)
    break
   if tested>=cap:break
  if res.success or tested>=cap:break
 out={'n':n,'trees':len(ts),'tests':tested,'elapsed':time.time()-start,'logs':logs,'result':'candidate' if res.success else 'no LP witness; solver statuses must be inspected','numerical_only_unless_exact_coordinate_check':True}
 (P/f'bme-run-{n}.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='logs'},flush=True)
if __name__=='__main__':
 import sys
 run(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 40)
