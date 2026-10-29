import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS'):os.environ[k]='1'
import resource,signal,json,random
from pathlib import Path
from fractions import Fraction as F
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(35,35));signal.alarm(40)
rng=random.Random(261029);N=12
# Formal H^-1 (integral_0^1 H(t z) dt), no candidate code reused.
def mul(a,b,n):
 c=[F(0)]*(n+1)
 for i in range(min(len(a),n+1)):
  for j in range(min(len(b),n+1-i)):c[i+j]+=a[i]*b[j]
 return c
def inverse(a,b):
 c=[F(0)]*(N+1)
 for n in range(1,N+1):
  pow=[F(1)]+[F(0)]*n;s=F(0)
  for k in range(1,n+1):
   pow=mul(pow,c,n)
   if k>=2:s+=a[k]*pow[n]
  c[n]=(b[n]-s)/a[1]
 return c
res=[];bad=None
for sample in range(120):
 count=rng.randrange(2,7);xs=sorted(set(F(rng.randrange(1,100),100) for _ in range(count)));ws=[rng.randrange(1,20) for _ in xs];norm=sum(ws)
 a=[sum((F(w,norm)*x**n for x,w in zip(xs,ws)),F(0)) for n in range(N+1)]
 b=[v/F(n+1) for n,v in enumerate(a)];c=inverse(a,b)
 if any(v<0 for v in c[1:]):
  bad={'sample':sample,'atoms':list(map(str,xs)),'weights':ws,'c':list(map(str,c))};break
 res.append({'sample':sample,'minimum':str(min(c[1:]))})
out={'status':'finite diagnostics only','operator':'H^-1(integral_0^1 H(t z)dt)','degree':N,'tested':len(res)+(bad is not None),'negative':bad,'samples':res}
p=Path(__file__).resolve().parent;(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='samples'},indent=2))
