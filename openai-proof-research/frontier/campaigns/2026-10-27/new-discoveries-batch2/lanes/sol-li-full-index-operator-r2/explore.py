import os
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[key]='1'
import resource,signal,random,json,itertools
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(50,50));signal.alarm(55)
from pathlib import Path
import mpmath as mp
mp.mp.dps=90
N=45;Z=mp.mpf(0); rng=random.Random(261029)
def inv(a,b):
 c=[Z]*(N+1);P=[[Z]*(N+1) for _ in range(N+1)];P[0][0]=1
 for n in range(1,N+1):
  for j in range(2,n+1):P[j][n]=sum(c[i]*P[j-1][n-i] for i in range(1,n-j+2))
  c[n]=(b[n]-sum(a[j]*P[j][n] for j in range(2,n+1)))/a[1];P[1][n]=c[n]
 return c
cache={}
def coeff(k):
 if k in cache:return cache[k]
 def rec(t):
  if not t:return [mp.mpf(1)]*(N+1)
  inner=rec(t[1:]);s=Z;out=[]
  for i in range(N+1):
   s+=inner[i] if t[1:] else Z
   out.append((s if t[1:] else 1)/mp.mpf(i+1)**t[0])
  return out
 cache[k]=rec(k);return cache[k]
res={'degree':N,'atomic':0,'genuine':0,'generator':0,'negative':[]}
for trial in range(100):
 xs=[mp.mpf(rng.randrange(1,1000))/1000 for _ in range(rng.randrange(2,6))];w=[rng.randrange(1,100) for _ in xs]
 a=[sum(v*x**n for x,v in zip(xs,w))/sum(w) for n in range(N+1)]
 c=inv(a,[x/(n+1) for n,x in enumerate(a)]);res['atomic']+=1
 if min(c[1:]) < -mp.mpf('1e-65'):
  res['negative'].append({'type':'atomic','x':list(map(str,xs)),'w':w,'c':list(map(str,c))});break
indices=[(a,) for a in range(1,8)]+[tuple(rng.randrange(1,6) for _ in range(rng.randrange(2,7))) for _ in range(65)]
for k in indices:
 a=coeff(k);q=[Z]*(N+1)
 for n in range(1,N+1):q[n]=(a[n]-sum((j+1)*a[j+1]*q[n-j] for j in range(1,n)))/a[1]
 res['generator']+=1 # dilation generator (H_k-1)/H_k', tail asymptotic only for singleton k
 if max(q[2:])>mp.mpf('1e-65'):res['negative'].append({'type':'generator','k':k,'q':list(map(str,q))})
 pairs=[(k,(k[0]+1,)+k[1:]),(k+(16,),k)]
 # different arbitrary tails, comparison determined by first differing component
 if k[0]<5:pairs.append((k,(k[0]+1,1,1,1,1)))
 for kk,ll in pairs:
  c=inv(coeff(kk),coeff(ll));res['genuine']+=1
  if min(c[1:]) < -mp.mpf('1e-65'):res['negative'].append({'type':'genuine','k':kk,'l':ll,'c':list(map(str,c))})
Path(__file__).with_name('explore-results.json').write_text(json.dumps(res,indent=2));print(json.dumps(res))
