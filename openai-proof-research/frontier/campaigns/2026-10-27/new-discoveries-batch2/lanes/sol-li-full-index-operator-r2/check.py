import os
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[key]='1'
import resource,signal,random,json,itertools
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(45,45));signal.alarm(50)
from fractions import Fraction as F
from pathlib import Path
rng=random.Random(261029);N=18

def coeff(k,lower=1):
 if not k:return [F(1)]*(N+1)
 inner=coeff(k[1:],lower);s=F(0);v=[]
 for i in range(N+1):
  if i+1>=lower:s+=inner[i]
  v.append((s if k[1:] else F(i+1>=lower))/F((i+1)**k[0]))
 return v

def inv(a,b):
 c=[F(0)]*(N+1);P=[[F(0)]*(N+1) for _ in range(N+1)];P[0][0]=1
 for n in range(1,N+1):
  for j in range(2,n+1):P[j][n]=sum((c[i]*P[j-1][n-i] for i in range(1,n-j+2)),F(0))
  c[n]=(b[n]-sum((a[j]*P[j][n] for j in range(2,n+1)),F(0)))/a[1];P[1][n]=c[n]
 # independent direct polynomial composition
 out=[F(1)]+[F(0)]*N;p=[F(1)]+[F(0)]*N
 for j in range(1,N+1):
  p=[sum((p[i]*c[n-i] for i in range(n)),F(0)) for n in range(N+1)]
  for n in range(N+1):out[n]+=a[j]*p[n]
 assert out==b
 return c
res={'degree':N,'operator_laws':0,'genuine_pairs':0,'tail_generators':0,'bad':[]}
for t in range(20):
 xs=[F(rng.randrange(1,100),100) for _ in range(4)];ws=[rng.randrange(1,20) for _ in xs]
 a=[sum((w*x**n for w,x in zip(ws,xs)),F(0))/sum(ws) for n in range(N+1)];b=[x/F(n+1) for n,x in enumerate(a)];c=inv(a,b)
 a1,a2,a3,a4=a[1:5]
 assert c[1:5]==[F(1,2),a2/(12*a1),a3/(8*a1)-a2*a2/(12*a1*a1),11*a4/(80*a1)-3*a2*a3/(16*a1*a1)+11*a2**3/(144*a1**3)]
 assert min(c[1:])>0;res['operator_laws']+=1
indices=[(a,) for a in range(1,5)]+[tuple(rng.randrange(1,5) for _ in range(rng.randrange(2,6))) for _ in range(20)]
for k in indices:
 a=coeff(k);B=coeff(k,2);D=[F(0)]*(N+1)
 for n in range(1,N+1):D[n]=(B[n]-sum(((j+1)*a[j+1]*D[n-j] for j in range(1,n)),F(0)))/a[1]
 assert all(sum(((j+1)*a[j+1]*D[n-j] for j in range(n)),F(0))==B[n] for n in range(1,N+1))
 res['tail_generators']+=1
 if max(D[2:])>0:res['bad'].append({'type':'tail_generator','k':k,'D':list(map(str,D))})
 # finite-sum tail asymptotic bound coefficientwise, with q=12
 aq=coeff(k+(12,));C=coeff(k,1)
 for n in range(N+1):
  err=2**12*(aq[n]-a[n])-B[n]
  assert 0<=err<=F(2,3)**12*(n+1)*C[n]
 for kk,ll in [(k,(k[0]+1,)+k[1:]),(k+(12,),k)]:
  c=inv(coeff(kk),coeff(ll));res['genuine_pairs']+=1
  if min(c[1:])<=0:res['bad'].append({'type':'genuine','k':kk,'l':ll,'c':list(map(str,c))})
Path(__file__).with_name('checks.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
