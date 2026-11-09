import os,resource,json,itertools,re,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(25,25))
for v in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[v]='1'
t=time.monotonic();N=[0]
for k in range(1,301):N.append(k*k*(N[-1]+k+10))
def internal(s):
 if s==('01'*((len(s)+1)//2))[:len(s)]:return True
 m=re.match(r'^(?:01)+00',s)
 return bool(m and len(s)<N[(m.end()-2)//2])
count=0
for k in [3,4]:
 H=N[k-1]+3;B,r=divmod(N[k]-2*k-2-H,k)
 for pattern in ['0'*(k-2),'1'*(k-2),('01'*k)[:k-2],('10'*k)[:k-2]]:
  w='01'*k+'00'+('11'+pattern)*B+'1'*(r+H)
  assert len(w)==N[k] and not internal(w) and internal(w[:-1]);assert all(not internal(w[i:]) for i in range(1,len(w)));count+=len(w)-1
for k in range(3,301):
 H=N[k-1]+3;R=N[k]-2*k-2-H;B,r=divmod(R,k);F=(k-2)*B;D=N[k]-1-F
 assert R>=0 and 0<=r<k and D>=0 and D*k<=4*N[k]
 assert D*k*N[k]<=2*N[k]*N[k]+k*N[k-1]*N[k]+k*(3*k+5)*N[k]
# Every block begins 11, prefix alternating-run length 1; suffix alternating
# run at most k-1. Thus concatenating arbitrarily many blocks cannot make
# a crossing alternating run longer than k. Check each possible block exactly.
blocks=0
for k in range(3,11):
 for bits in itertools.product('01',repeat=k-2):
  s='11'+''.join(bits);run=1;mx=1
  for a,b in zip(s,s[1:]):run=run+1 if a!=b else 1;mx=max(mx,run)
  assert mx<2*k and run<=k-1;blocks+=1
out={'status':'PASS finite diagnostic only; all-k proof in review.md','suffixes':count,'actual_depth_words':8,'arithmetic_indices':298,'blocks_exhausted':blocks,'AS_bytes':512*1024**2,'CPU_seconds':25,'external_wall_seconds':35,'BLAS_threads':1,'elapsed':time.monotonic()-t}
Path(__file__).with_name('own-checks.json').write_text(json.dumps(out,indent=2));print(out)
