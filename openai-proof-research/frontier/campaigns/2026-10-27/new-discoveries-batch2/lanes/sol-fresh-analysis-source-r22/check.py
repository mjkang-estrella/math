import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal,json,itertools,time
from fractions import Fraction as F
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(35,35));signal.alarm(40)
b=Path(__file__).parent
D=9
cache={}
def coeff(k):
 if k in cache:return cache[k]
 a=[]
 for m in range(1,D+2):
  def h(t,M):
   if not t:return F(1)
   return sum((h(t[1:],i)/i**t[0] for i in range(1,M+1)),F(0))
  a.append(h(k[1:],m)/m**k[0])
 cache[k]=a;return a
def mul(a,c):
 out=[F(0)]*(D+1)
 for i in range(D+1):
  for j in range(D+1-i):out[i+j]+=a[i]*c[j]
 return out
def compose(a,p):
 out=[F(0)]*(D+1);pow=[F(1)]+[F(0)]*D
 for j in range(D+1):
  for i in range(D+1):out[i]+=a[j]*pow[i]
  pow=mul(pow,p)
 return out
def order(k,l):
 for a,c in zip(k,l):
  if a!=c:return a<c
 return len(k)>len(l)
indices=[k for r in range(1,4) for k in itertools.product(range(1,4),repeat=r)]
# test modest order first, no all-order claims
count=0;bad=[];tests=[]
for k in indices:
 for l in indices:
  if not order(k,l):continue
  a,c=coeff(k),coeff(l);p=[F(0)]*(D+1)
  for n in range(1,D+1):p[n]=(c[n]-compose(a,p)[n])/a[1]
  assert compose(a,p)==c[:D+1]
  count+=1
  neg=[(i,str(v)) for i,v in enumerate(p[1:],1) if v<=0]
  if neg:bad.append({'k':k,'l':l,'nonpositive':neg,'p':list(map(str,p))});break
 if bad:break
# Independent first-two-coefficient formulas and a generic MLR obstruction.
t=[F(1,100),F(1,2),F(1)];wl=[F(1,10),F(89,100),F(1,100)];wk=[F(1,12),F(89,108),F(5,54)]
assert sum(wl)==sum(wk)==1
ratios=[a/c for a,c in zip(wk,wl)];assert ratios[0]<ratios[1]<ratios[2]
a=sum(x*y for x,y in zip(t,wk));bb=sum(x*x*y for x,y in zip(t,wk));c=sum(x*y for x,y in zip(t,wl));d=sum(x*x*y for x,y in zip(t,wl));negative=(d-bb*(c/a)**2)/a
assert negative==F(-4234364835507,203352396973750)
for k in indices:
 a=coeff(k)
 # direct outer-index=2 formula via independent sum over weak binary tails
 binary=F(0)
 for twos in range(len(k)):
  binary+=F(1,2**(k[0]+sum(k[1:1+twos])))
 assert a[1]==binary
out={'generic_MLR_second_coefficient':str(negative),'degree':D,'pairs':count,'bad':bad,'exact_witness_364':16*(6**6*5+5**6*5+5**6*6)-(6**4+2*5**4)**2}
(b/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
