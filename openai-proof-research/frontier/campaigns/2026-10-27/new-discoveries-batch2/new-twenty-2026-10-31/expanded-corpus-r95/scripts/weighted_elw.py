import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np,random,itertools,json,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));rng=random.Random(95006)
for n in [5,6,7,8,9,10]:
 best=0;record=None;tested=0;bad=[]
 for rep in range(500):
  prob=rng.choice([.2,.35,.5,.65,.8]);es=[e for e in itertools.combinations(range(n),2) if rng.random()<prob];A=np.zeros((n,n));cs=np.ones(n)
  for a,b in es:A[a,b]=A[b,a]=1
  for mask in range(1,1<<n):
   vs=[v for v in range(n) if mask>>v&1]
   if all(A[a,b] for a,b in itertools.combinations(vs,2)):
    for v in vs:cs[v]=max(cs[v],len(vs))
  cv=1-1/cs
  for it in range(80):
   w=np.array([rng.choice([1,1,2,3,5,8,13,21,34,55,89]) for v in range(n)]);Q=A*np.sqrt(w[:,None]*w[None,:]);ev=np.linalg.eigvalsh(Q);lhs=sum(x*x for x in ev if x>1e-9);rhs=float(w@cv)**2;tested+=1
   ratio=lhs/rhs if rhs else 0
   if ratio>best:best=ratio;record={'edges':es,'weights':w.tolist(),'order':int(sum(w)),'lhs_squared':lhs,'rhs_squared':rhs}
   if lhs>rhs+1e-6:bad.append(record);break
  if bad:break
 print(json.dumps({'base_n':n,'evaluations':tested,'best_ratio':best,'best':record,'violations':bad,'scope':'integer weighted independent-set blowups; quotient eigenvalues plus zero eigenvalues'}),flush=True)
