import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
import resource,signal,time,json,datetime
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(240,240));signal.alarm(280)
from pathlib import Path
from fractions import Fraction as F
from math import isqrt,gcd
L=Path(__file__).parent;started=datetime.datetime.now(datetime.timezone.utc).isoformat();D=10**30
cd=lambda a,b:-((-a)//b)
# Certified fixed-point Machin interval, each series term rounded separately.
P10=10**510
def atan_inv(v,K):
 lo=hi=0
 for j in range(K):
  den=(2*j+1)*v**(2*j+1);t=P10//den;u=cd(P10,den)
  if j%2:lo-=u;hi-=t
  else:lo+=t;hi+=u
 err=cd(P10,(2*K+1)*v**(2*K+1));return lo-err,hi+err
a=atan_inv(5,380);b=atan_inv(239,115);pl=16*a[0]-4*b[1];pu=16*a[1]-4*b[0]
assert 0<pu-pl<20000
al=F(P10,2*pu);au=F(P10,2*pl)
# CF of lower endpoint. No appeal to best approximation: rational-grid spacing only.
x=al;p0,p1=0,1;q0,q1=1,0;grids=[]
while True:
 z=x.numerator//x.denominator;p=z*p1+p0;q=z*q1+q0
 if q>1:
  eps=max(abs(al-F(p,q)),abs(au-F(p,q)));grids.append((p,q,eps))
 if q>2**810:break
 p0,p1=p1,p;q0,q1=q1,q;x=1/(x-z)
# Entire dyadic tail from 2^30 through 2^1600, using exact rational grid spacing.
tail=F(0);rows=[]
for k in range(30,1600):
 X=2**k;root=isqrt(X);best=None;choice=None
 for p,q,eps in grids:
  if q>4*isqrt(X)*10000:break
  for m in [q,max(2,q//2)]:
   delta=F(1,q)-(m-1)*eps
   if delta<=0:continue
   bound=F(cd(X,m),X)*(1+F(11,10)/(delta*root))
   if best is None or bound<best:best=bound;choice=(q,m)
 assert best is not None
 # outward round each bound to avoid giant accumulated rational denominators
 top=cd(best.numerator*D,best.denominator);tail+=F(top,D)
 rows.append({'k':k,'q':choice[0],'block':choice[1],'upper_scaled':top})
remote=F(2400,2**40);tail+=remote
print('TAIL',float(tail),flush=True)
# Finite upper prefix: frozen exact through 10000, then sparse rational-grid enumeration.
base=json.loads((L/'prefix-original.json').read_text());prefix=F(base['partial_sums'][-1]['upper_scaled'],base['scale'])
count=0;finite_rows=[]
# For n>=10001, cos t <=1-t²/2+t⁴/24. For |t|<=.5,
# use exact integer phase interval; upper exp(-x) via (1-x/1024+x²/(2*1024²))^1024.
# Outside small phase window, weak Gaussian gives exp(-64) bound.
for k in range(13,30):
 X=2**k;A=max(10001,X);Z=2*X
 if A>=Z:continue
 # y-window r=ceil(sqrt(24/X)); (8/3)*X*r²>=64
 r=F(isqrt(cd(24*D*D,X))+1,D)
 p,q,eps=next((p,q,e) for p,q,e in grids if q>=Z)
 err=Z*eps;rad=(r+err)*q
 left=(F(q,4)-rad).__floor__()-1;right=(F(q,4)+rad).__ceil__()+1
 inv=pow(p,-1,q);subtotal=0;hits=0
 for j in range(left,right+1):
  n=(j*inv)%q
  if not A<=n<Z:continue
  # |n*alpha-1/4-nearestinteger| lower bound from exact rational-grid residue
  yr=max(F(0),abs(F(j,q)-F(1,4))-n*eps)
  # t lower =2pi*y lower. For window small, t upper < .5 checked globally below.
  assert 2*F(pu,P10)*(r+2*err)<F(1,2)
  t=2*F(pl,P10)*yr
  # lower 1-cos(t) >= t²/2-t⁴/24; valid and increasing for t<=.5
  # floor x=n*(t²/2-t⁴/24)/3 at scale D, then exp bound monotonic for x<1024
  xx=n*(t*t/2-t**4/24)/3
  v=xx.numerator*D//xx.denominator;assert 0<=v<1024*D
  # ceil polynomial at scale D
  h=D-v//1024+cd(v*v,2*1024**2*D)
  for _ in range(10):h=cd(h*h,D)
  subtotal+=cd(h,n);hits+=1
 # omitted <= Z*exp(-64)/A <2*exp(-64)<2^-63 (e>2)
 omitted=F(1,2**63)
 prefix+=F(subtotal,D)+omitted;count+=hits
 finite_rows.append({'k':k,'A':A,'Z':Z,'grid_q':q,'enumerated':right-left+1,'hits':hits,'upper_scaled':subtotal,'omitted_upper':str(omitted)})
 print('PREFIX',k,hits,float(prefix),flush=True)
upper=prefix+tail
out={'status':'PASS' if upper<F(21635,10000) else 'BOUND DOES NOT CLOSE','scope':'whole actual fixed-radian series upper bound; ordinary analytic bridges described in PROOF.md','started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'finite_upper':str(prefix),'tail_upper':str(tail),'total_upper':str(upper),'total_upper_decimal_diagnostic':float(upper),'finite_hits':count,'finite_rows':finite_rows,'tail_rows':rows,'remote_upper':str(remote),'pi_lower_scaled':pl,'pi_upper_scaled':pu,'pi_scale':P10,'resources':{'AS':512*1024**2,'CPU':240,'wall_alarm':280,'BLAS_threads':1}}
(L/'checks.json').write_text(json.dumps(out,indent=2));print(out['status'],float(upper),flush=True)
