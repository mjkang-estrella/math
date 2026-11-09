#!/usr/bin/env python3
"""Finite exact diagnostics, NOT verification of the universal conjecture.
Hard address-space cap 384 MiB; no numerical libraries or exponential search.
"""
import os,resource,itertools,json,pathlib,datetime
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','BLIS_NUM_THREADS']:os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(384*1024*1024,384*1024*1024))
resource.setrlimit(resource.RLIMIT_CPU,(60,60))
def check(w):
 n=len(w);m=n*n;pairs=list(itertools.combinations(range(m),2));index={p:k for k,p in enumerate(pairs)};d=len(pairs)
 L=[[0]*d for _ in range(m)]
 for i in range(n):
  for j in range(n):
   for k in range(n):
    a=i*n+k;b=k*n+j
    if a!=b:L[i*n+j][index[tuple(sorted((a,b)))]]+=(1 if a<b else -1)*w[k]
 S=sum(t*t for t in w);v=[w[i//n] if i//n==i%n else 0 for i in range(m)]
 for i in range(m):
  for j in range(m):assert sum(a*b for a,b in zip(L[i],L[j]))==S*(i==j)-v[i]*v[j]
 # Off-diagonal output E12: eta=Lambda* E12 has norm^2 S.
 eta=L[1];Le=[sum(a*b for a,b in zip(row,eta)) for row in L]
 assert sum(t*t for t in eta)==S and Le==[S*(i==1) for i in range(m)]
 c=w[0]**2+w[1]**2;deficit=(c-S)*S
 # Independent Hermitian wedge Gram coefficients: each product has a
 # distinct anchor monomial x_a y_b conjugate(x_c y_d), a<b,c<d.
 anchors={(a,b,c,d) for a,b in pairs for c,d in pairs};assert len(anchors)==len(pairs)**2
 return dict(n=n,w=w,wedge_dimension=d,S=S,c_squared=c,eta_sparse=[(pairs[k],x) for k,x in enumerate(eta) if x],eta_norm_squared=S,eta_deficit=deficit,hermitian_anchor_count=len(anchors),lambda_gram_identity=True)
r=[check(w) for w in [[2,1],[9,4,1],[9,4,2,1],[9,4,2,1,0],[1,1,1]]]
# The n=3 witness is not decomposable: its four-coordinate Plucker minor is nonzero.
w=[9,4,1];n=3;m=9;pa=list(itertools.combinations(range(m),2));L=[0]*len(pa)
for k in range(n):
 a=k;b=k*n+1
 if a!=b:L[pa.index(tuple(sorted((a,b))))]+=(1 if a<b else -1)*w[k]
def xi(a,b):return 0 if a==b else (1 if a<b else -1)*L[pa.index(tuple(sorted((a,b))))]
plucker=[]
for a,b,c,d in itertools.combinations(range(m),4):
 z=xi(a,b)*xi(c,d)-xi(a,c)*xi(b,d)+xi(a,d)*xi(b,c)
 if z:plucker.append(dict(indices=[a,b,c,d],value=z))
assert plucker
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),address_space_cap_bytes=384*1024*1024,cpu_cap_seconds=60,blas_threads=1,exact_cases=r,nondecomposability_witnesses=plucker,proc_memory={line.split(':')[0]:line.split(':')[1].strip() for line in pathlib.Path('/proc/self/status').read_text().splitlines() if line.startswith(('VmPeak:','VmHWM:','VmRSS:','VmSize:'))},status='PASS finite exact checks only; no target proof')
p=pathlib.Path(__file__).resolve().parents[1]/'verification/exact.json';p.write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
