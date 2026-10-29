import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(45,45));signal.alarm(55)
from pathlib import Path
import numpy as np,json,itertools,time
b=Path(__file__).resolve().parent;rng=np.random.default_rng(3301);start=time.monotonic();rows=[]
def ratio(B,p):return float(np.linalg.norm(np.tril(B[np.ix_(p,p)],-1),2)/np.linalg.norm(B,2))
def test(B,label,allperm=False):
 n=len(B);den=float(np.linalg.norm(B,2));best=1e9;worst=0;pbest=None;count=0
 perms=itertools.permutations(range(n)) if allperm else (rng.permutation(n) for _ in range(160))
 for p in perms:
  p=np.array(p);v=float(np.linalg.norm(np.tril(B[np.ix_(p,p)],-1),2)/den);count+=1
  if v<best:best=v;pbest=p.copy()
  worst=max(worst,v)
 # Local swap descent on best sampled ordering, not an all-permutation certificate.
 if not allperm:
  for sweep in range(3):
   changed=False
   for i in range(n):
    for j in range(i):
     p=pbest.copy();p[i],p[j]=p[j],p[i];v=float(np.linalg.norm(np.tril(B[np.ix_(p,p)],-1),2)/den);count+=1
     if v<best-1e-12:best=v;pbest=p;changed=True
   if not changed:break
 row={'family':label,'n':n,'mode':'all permutations' if allperm else 'sampled+local descent','order_evaluations':count,'minimum_found':best,'maximum_sampled':worst,'source_threshold':2/np.pi,'identity_ratio':ratio(B,np.arange(n)),'norm_B':den,'min_eigenvalue':float(np.linalg.eigvalsh(B)[0]),'best_order':pbest.tolist()};rows.append(row)
 (b/'probe-results.json').write_text(json.dumps({'diagnostic_only':True,'seed':3301,'rows':rows,'wall_seconds':time.monotonic()-start},indent=2))
for n in [3,4,5,6]:
 for rank in [2,3]:
  for complex_ in [False,True]:
   for rep in range(3):
    A=rng.normal(size=(n,rank));A=A+1j*rng.normal(size=(n,rank)) if complex_ else A;A=A/np.linalg.norm(A,axis=1)[:,None];test(A@A.conj().T,f'random-unit-Gram-r{rank}-complex{complex_}-{rep}',True)
for n in [8,12,16,24,32]:
 # Circulant PSD projections have exactly constant diagonal, no numerical renormalization needed in their mathematical definition.
 F=np.exp(2j*np.pi*np.outer(np.arange(n),np.arange(n))/n)/np.sqrt(n)
 for typ in ['interval','random']:
  for rank in [n//4,n//2,3*n//4]:
   ix=np.arange(rank) if typ=='interval' else rng.choice(n,rank,replace=False);B=(n/rank)*(F[:,ix]@F[:,ix].conj().T);test(B,f'circulant-projection-{typ}-r{rank}')
 for rank in [2,n//2]:
  A=rng.normal(size=(n,rank))+1j*rng.normal(size=(n,rank));A/=np.linalg.norm(A,axis=1)[:,None];test(A@A.conj().T,f'large-random-Gram-r{rank}')
print(json.dumps({'rows':len(rows),'order_evaluations':sum(x['order_evaluations'] for x in rows),'largest_min_found':max(x['minimum_found'] for x in rows),'diagnostic_only':True,'wall':time.monotonic()-start}))
