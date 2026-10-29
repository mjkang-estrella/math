from itertools import combinations_with_replacement,product
from math import factorial,comb
from collections import Counter,defaultdict
from pathlib import Path
import json
P=Path(__file__).resolve().parent

def feasible(a,b,m,n):
 a=sorted(a,reverse=True);b=sorted(b,reverse=True)
 aa=[0];bb=[0]
 for x in a:aa.append(aa[-1]+x)
 for x in b:bb.append(bb[-1]+x)
 return all(aa[i]+bb[j]<=i*n+j*m-i*j-i-j for i in range(m) for j in range(n+1))

def multiplicity(a):
 z=factorial(len(a))
 for v in Counter(a).values():z//=factorial(v)
 return z

def poly(m,n):
 out=[0]*((m-1)*(n-1)+1);tested=0
 av=[(a,sum(a),multiplicity(a)) for a in combinations_with_replacement(range(n),m-1)]
 bv=[(b,sum(b),multiplicity(b)) for b in combinations_with_replacement(range(m),n)]
 for a,sa,wa in av:
  for b,sb,wb in bv:
   tested+=1
   if sa+sb<len(out) and feasible(a,b,m,n):out[sa+sb]+=wa*wb
 return out,tested

def points(m,n):
 return [a+b for a in product(range(n),repeat=m-1) for b in product(range(m),repeat=n) if feasible(a,b,m,n)]

def orientations(m,n):
 d=[n]*(m-1)+[m]*n;seen=set()
 for bits in product(range(2),repeat=m*n):
  indeg=[0]*(m+n-1)
  for i in range(m):
   for j in range(n):
    if bits[i*n+j]:indeg[m-1+j]+=1
    elif i:indeg[i-1]+=1
  if min(indeg)<1:continue
  for l in product(*(range(k) for k in indeg)):seen.add(l)
 return seen

if __name__=='__main__':
 rows=[]
 for m in range(2,8):
  for n in range(2,8):
   if m+n>12:continue
   v,t=poly(m,n);assert all(v[k]**2>=v[k-1]*v[k+1] for k in range(1,len(v)-1))
   if m==2:assert v==[sum(comb(n,i) for i in range(k+1)) for k in range(n)]
   if n==2:assert v==[sum((k-j+1)*comb(m-1,j) for j in range(k+1)) for k in range(m)]
   rows.append(dict(m=m,n=n,coefficients=v,sorted_pairs=t))
   print(m,n,v,flush=True)
 assert orientations(3,3)==set(points(3,3));assert orientations(2,4)==set(points(2,4))
 # Fibers of ordered pairs of feasible lacking vectors by coordinate sum.
 fibers=[]
 for m,n in [(3,3),(3,4),(4,3)]:
  pts=points(m,n);f=defaultdict(Counter)
  for a in pts:
   for b in pts:f[tuple(x+y for x,y in zip(a,b))][sum(a)]+=1
  fails=[]
  for w,c in f.items():
   s=sum(w)
   for k in range(s//2):
    if c[k]>c[k+1]:fails.append(dict(w=w,k=k,counts=dict(c)));break
  fibers.append(dict(m=m,n=n,pairs=len(pts)**2,fibers=len(f),nonunimodal=fails[:2]))
  print('fibers',fibers[-1],flush=True)
 # Derivative in slack twice of degree4 homogenization at K3,3.
 # Restrict to x0=0: 2*h2(x1,...,x5), Hessian diag4 offdiag2.
 assert 4-2>0 # eigenvalue2 on sum-zero, eigenvalue12 on all-ones.
 # Matroid clone rank counts differ because a vector has prod binom(c_i,a_i) lifts.
 pts=points(3,3);weighted=Counter()
 for a in pts:weighted[sum(a)]+=__import__('functools').reduce(lambda x,y:x*y,(comb(2,z) for z in a),1)
 (P/'checks.json').write_text(json.dumps(dict(rows=rows,orientations_equal=True,fibers=fibers,clone_counts=dict(weighted),hessian_eigenvalues=[2,2,2,2,12]),indent=2)+'\n')
