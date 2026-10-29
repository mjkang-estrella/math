import numpy as np,random,json,time
from pathlib import Path
P=Path(__file__).resolve().parent
rng=random.Random(830029);rows=[];cases=0;start=time.monotonic()
for d in range(4,9):
 N=2**d;vs=np.arange(N,dtype=np.uint64);pairs=[(i,j) for i in range(d) for j in range(i+1,d)]
 wedges=np.array([(((vs>>i)&1)[:,None]*((vs>>j)&1)[None,:])^(((vs>>j)&1)[:,None]*((vs>>i)&1)[None,:]) for i,j in pairs],dtype=np.uint8)
 best=None
 for trial in range(90):
  r=rng.randrange(2,min(7,len(pairs))+1);coeff=[rng.randrange(2**r) for _ in pairs]
  C=np.zeros((N,N),dtype=np.uint8)
  for w,c in zip(wedges,coeff):C^=w*c
  A=(C[1:,1:]==0).astype(np.int64);k=A.sum(axis=1)
  if np.any(k==N-1):continue # radical zero required
  # no need to require surjective bracket: enlarged central fibers remain valid
  z=2**r;n=z*(N-1);deg=z*k-1
  M1=z*int(deg@deg);twom2=z*z*int(deg@(A@deg))-M1;twom=z*int(sum(deg))
  gap=2*n*twom2-twom*M1*2
  e=n-1-deg;B=np.ones_like(A)-A
  NM1=z*int(e@e);NtwoM2=z*z*int(e@(B@e));Ntwom=z*int(sum(e));ngap=2*n*NtwoM2-2*Ntwom*NM1
  cases+=1
  val=min(gap,ngap)
  if best is None or val<best['min_gap']:best={'d':d,'r':r,'trial':trial,'min_gap':val,'comm_gap':gap,'noncomm_gap':ngap,'coefficients':coeff,'kernel_nonzero_sizes':sorted(set(map(int,k)))}
  if val<0:
   P.joinpath('witness.json').write_text(json.dumps(best,indent=2));print('WITNESS',best);raise SystemExit
 rows.append(best)
print(json.dumps({'status':'NO_COUNTEREXAMPLE_NOT_PROOF','cases':cases,'bounded_best':rows,'seconds':time.monotonic()-start},indent=2))
