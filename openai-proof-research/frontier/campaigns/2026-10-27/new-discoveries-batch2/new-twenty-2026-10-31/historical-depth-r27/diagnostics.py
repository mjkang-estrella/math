"""Finite diagnostic only: not a certified root isolation or Lean theorem."""
import os,resource,json,time,math
os.sched_setaffinity(0,{0,1});resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(25,25));
import numpy as np
start=time.monotonic()
def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]+=v
 for i,v in enumerate(b):c[i]+=v
 return c
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,u in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=u*v
 return c
def kmn(m,n):
 s=[1]
 for j in range(1,m+1):s=[0]+[(s[k-1] if k else 0)+k*(s[k] if k<len(s) else 0) for k in range(1,j+1)]
 f=[1];p=[0]
 for k in range(m+1):
  if k:f=mul(f,[-(k-1),1])
  power=[math.comb(n,j)*(-k)**(n-j) for j in range(n+1)]
  p=add(p,[s[k]*v for v in mul(f,power)])
 return p
def ev(p,q):
 x=0
 for v in p[::-1]:x=x*q+v
 return x
for m in range(2,11):
 for n in range(m,11):
  assert time.monotonic()-start<20
  p=kmn(m,n)
  # Independently count small q colors by left used-color cardinality.
  for q in range(1,5):
   from itertools import product
   count=sum((q-len(set(a)))**n for a in product(range(q),repeat=m)) if m<=5 else None
   if count is not None:assert ev(p,q)==count
  roots=np.roots(np.array(p[::-1],dtype=float));delta=max(m,n)
  z=max(roots,key=abs); w=max(roots,key=lambda x:x.real)
  print(json.dumps(dict(family='complete_bipartite',m=m,n=n,coefficients_ascending=p,largest_modulus_root=[float(z.real),float(z.imag)],modulus_over_delta=float(abs(z)/delta),largest_real_part=float(w.real),target_modulus_violation=bool(abs(z)>2*delta+1e-6),target_realpart_violation=bool(w.real>delta+1+1e-6))))
print(json.dumps(dict(status='bounded_nonfinding_not_proof',elapsed_seconds=time.monotonic()-start)))
