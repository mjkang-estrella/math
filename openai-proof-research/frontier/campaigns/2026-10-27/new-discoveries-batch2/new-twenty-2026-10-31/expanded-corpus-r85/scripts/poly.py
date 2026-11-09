from collections import defaultdict
from functools import lru_cache
import itertools,json,pathlib,sympy as s
D=pathlib.Path(__file__).resolve().parents[1]
def comps(d,n):
 if n==1:yield (d,);return
 for a in range(d+1):
  for b in comps(d-a,n-1):yield (a,)+b
@lru_cache(None)
def key(a):
 i=next((i for i in range(len(a)-1) if a[i]<a[i+1]),None)
 if i is None:return {a:1}
 b=list(a);b[i],b[i+1]=b[i+1],b[i];p=key(tuple(b));q=defaultdict(int)
 for e,c in p.items():
  u,v=e[i],e[i+1]
  # divided difference of x_i times monomial
  if u>=v:
   for t in range(u-v+1):
    f=list(e);f[i]=u-t;f[i+1]=v+t;q[tuple(f)]+=c
  else:
   for t in range(v-u-1):
    f=list(e);f[i]=v-1-t;f[i+1]=u+1+t;q[tuple(f)]-=c
 return {e:c for e,c in q.items() if c}
def test(p,n,d):
 assert all(c>0 for c in p.values())
 # exact M exchange
 E=set(p)
 for a in E:
  for b in E:
   for i in range(n):
    if a[i]<=b[i]:continue
    found=False
    for j in range(n):
     if a[j]>=b[j]:continue
     x=list(a);y=list(b);x[i]-=1;x[j]+=1;y[i]+=1;y[j]-=1
     if tuple(x) in E and tuple(y) in E:found=True;break
    if not found:return 'exchange'
 if d<2:return None
 for beta in comps(d-2,n):
  M=s.zeros(n)
  for i in range(n):
   for j in range(n):
    e=list(beta);e[i]+=1;e[j]+=1;M[i,j]=p.get(tuple(e),0)
  # Normalized coefficient derivative Hessian is exactly original coefficient.
  coeff=[x for x in M.charpoly().all_coeffs() if x]
  changes=sum((1 if a*b<0 else 0) for a,b in zip(coeff,coeff[1:]))
  if changes>1:return {'beta':beta,'matrix':str(M),'positive_eigenvalues':changes}
 return None
if __name__ == "__main__":
 counts={};bad=[]
 for n in range(1,5):
  for d in range(0,8):
   c=0
   for a in comps(d,n):
    p=key(a);err=test(p,n,d);c+=1
    if err:bad.append([a,err])
   counts[str((n,d))]=c
   print(n,d,c,'bad',len(bad),flush=True)
 (D/'outputs/343051-search.json').write_text(json.dumps(dict(compositions=counts,violations=bad,arithmetic='integer coefficients, exact characteristic polynomials, real-rooted Descartes inertia; M-convex exchange'),indent=2)+'\n')
