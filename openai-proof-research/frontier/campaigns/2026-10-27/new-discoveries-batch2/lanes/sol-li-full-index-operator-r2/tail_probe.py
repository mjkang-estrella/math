import os
for x in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[x]='1'
import resource,signal,json,random
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(40,40));signal.alarm(45)
from pathlib import Path
import mpmath as mp
mp.mp.dps=100;N=40;rng=random.Random(261029)
def coeff(k,lower):
 v=[mp.mpf(1)]*(N+1)
 for a in reversed(k):
  # v represents inner harmonic sums after prefix summation; strict lower cutoff retained
  s=mp.mpf(0);new=[]
  for i,x in enumerate(v):
   value=x/mp.mpf(i+1)**a if i+1>=lower else mp.mpf(0)
   new.append(value);s+=value
  v=[];s=mp.mpf(0)
  for x in new:s+=x;v.append(s)
 return new
out={'degree':N,'precision':100,'samples':0,'positive_generator_coefficients':[]}
for _ in range(450):
 k=tuple(rng.randrange(1,13) for _ in range(rng.randrange(1,13)));a=coeff(k,1);B=coeff(k,2);d=[mp.mpf(0)]*(N+1)
 for n in range(1,N+1):d[n]=(B[n]-sum((j+1)*a[j+1]*d[n-j] for j in range(1,n)))/a[1]
 out['samples']+=1
 bad=[n for n in range(2,N+1) if d[n]>mp.mpf('1e-80')]
 if bad:out['positive_generator_coefficients'].append({'k':k,'degrees':bad,'D':list(map(str,d))});break
Path(__file__).with_name('tail-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
