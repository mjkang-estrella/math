import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(240,240));signal.alarm(280)
import json,time,hashlib
from pathlib import Path
from fractions import Fraction as Q
from math import gcd,isqrt,factorial
L=Path(__file__).parent;C=json.loads((L/'input/checks.json').read_text());start=time.time()
ceil=lambda a,b:(a+b-1)//b
# Independently compute Machin interval with rational alternating sums, not termwise fixedpoint.
def arc(v,N):
 s=sum((Q((-1)**j,(2*j+1)*v**(2*j+1)) for j in range(N)),Q());e=Q(1,(2*N+1)*v**(2*N+1));return s-e,s+e
a,b=arc(5,380),arc(239,115);pl,pu=16*a[0]-4*b[1],16*a[1]-4*b[0]
assert Q(C['pi_lower_scaled'],C['pi_scale'])<=pl<pu<=Q(C['pi_upper_scaled'],C['pi_scale'])
al,au=1/(2*pu),1/(2*pl)
# Generate CF candidates independently, certify only selected grids, not optimality.
x=al;P0,P1,Q0,Q1=0,1,1,0;grids={}
while True:
 z=x.numerator//x.denominator;p,q=z*P1+P0,z*Q1+Q0
 if q>1:grids[q]=(p,max(abs(al-Q(p,q)),abs(au-Q(p,q))))
 if q>2**810:break
 P0,P1,Q0,Q1=P1,p,Q1,q;x=1/(x-z)
D=10**30;tail=Q(2400,2**40)
for k,row in enumerate(C['tail_rows'],30):
 assert row['k']==k
 q,m=row['q'],row['block'];p,e=grids[q];assert gcd(p,q)==1 and 2<=m<=q
 delta=Q(1,q)-(m-1)*e;assert delta>0
 bound=Q(ceil(2**k,m),2**k)*(1+Q(11,10*isqrt(2**k))/delta)
 assert Q(row['upper_scaled'],D)>=bound
 tail+=Q(row['upper_scaled'],D)
assert k==1599 and tail==Q(C['tail_upper']);print('tail independently certified',flush=True)
# Fresh prefix using Horner cosine polynomial about nearest sine maximum.
# Work interval t=n-pi/2-2*pi*j, |t|<=pi; cos Taylor through degree100.
W=10**120;mul=lambda a,b:(min(u*v for u in a for v in b)//W,ceil(max(u*v for u in a for v in b),W))
plo=pl.numerator*W//pl.denominator;phi=ceil(pu.numerator*W,pu.denominator)
coeff=[]
for j in range(51):
 z=Q((-1)**j,factorial(2*j));coeff.append((z.numerator*W//z.denominator,ceil(z.numerator*W,z.denominator)))
rem=ceil(4**102*W,factorial(102));prefix=0
for n in range(1,10001):
 j=(2*n*W-plo+2*plo)//(4*plo);c=4*j+1
 t=(n*W-ceil(c*phi,2),n*W-c*plo//2) if c>=0 else (n*W-c*plo//2,n*W-ceil(c*phi,2))
 assert max(abs(v) for v in t)<4*W
 u=mul(t,t);s=coeff[-1]
 for cc in reversed(coeff[:-1]):
  v=mul(s,u);s=(v[0]+cc[0],v[1]+cc[1])
 base=ceil(2*W+s[1]+rem,3);assert 0<base<=W,(n,t,s,base)
 v=W;e=n
 while e:
  if e&1:v=ceil(v*base,W)
  base=ceil(base*base,W);e//=2
 prefix+=ceil(v,n)
prefix=Q(prefix,W);old=Q(json.loads((L/'input/prefix-original.json').read_text())['partial_sums'][-1]['upper_scaled'],10**35)
assert abs(prefix-old)<Q(1,10**25);print('fresh Horner prefix',float(prefix),flush=True)
# All sparse terms: independent interval rational phase, and a DIFFERENT exponential bound:
# exp(-x) <= (1+x/2^18)^(-2^18). Down-round positive powers; reciprocate upwards.
hits=0;rows=[]
for row in C['finite_rows']:
 X=2**row['k'];A=max(10001,X);Z=2*X;q=row['grid_q'];p,e=grids[q]
 r=Q(isqrt(ceil(24*D*D,X))+1,D);rho=q*(r+Z*e)
 low=(Q(q,4)-rho).__floor__()-1;high=(Q(q,4)+rho).__ceil__()+1
 assert 0<low<=high<q and high-low<q and gcd(p,q)==1 and q>=Z
 inv=pow(p,-1,q);E=ceil(e.numerator*D,e.denominator);PI=pl.numerator*D//pl.denominator
 subtotal=0;cnt=0
 for residue in range(low,high+1):
  n=(residue*inv)%q
  if n<A or n>=Z:continue
  # exact rational phase lower then round, rather than candidate's separate epsilon rounding
  yl=max(Q(),abs(Q(residue,q)-Q(1,4))-n*e)
  t=(2*pl*yl*D).__floor__()
  t2=t*t//D;t4=ceil(t**4,D**3);v=n*(12*t2-t4)//72;assert 0<=v<1024*D
  h=D+v//(2**18)
  for _ in range(18):h=h*h//D
  upper=ceil(D*D,h);subtotal+=ceil(upper,n);cnt+=1
  # Fresh rational spot audit of inherited fixedpoint exponential at deterministic points.
  if cnt%997==1:
   yc=max(0,abs(4*residue-q)*D//(4*q)-n*E);tc=2*PI*yc//D
   vc=n*(12*(tc*tc//D)-ceil(tc**4,D**3))//72
   hh=D-vc//1024+ceil(vc*vc,2*1024**2*D)
   exact=(1-Q(vc,1024*D)+Q(vc*vc,2*1024**2*D*D))**1024
   for _ in range(10):hh=ceil(hh*hh,D)
   assert Q(hh,D)>=exact
 assert cnt==row['hits'];hits+=cnt;prefix+=Q(subtotal,D)+Q(1,2**63)
 rows.append(dict(k=row['k'],hits=cnt,upper_scaled=subtotal));print('fresh block',row['k'],cnt,flush=True)
assert hits==772779
assert prefix+tail<Q(21635,10000)
# Independent Ei lower with M=20000 and log10 computed by log2+log5.
def loglo(x,N):
 z=(x-1)/(x+1);return 2*sum((z**(2*j+1)/(2*j+1) for j in range(N)),Q())
def loghi(x,N):
 z=(x-1)/(x+1);return loglo(x,N)+2*z**(2*N+1)/((2*N+1)*(1-z*z))
t=loglo(Q(3),80);t=Q((t*D).__floor__(),D)
g=Q(sum(D//n for n in range(1,20001)),D)-loghi(Q(2),80)-4*loghi(Q(10),220)-Q(1,20000)
ei=g+loglo(t,25)+sum((t**j/(j*factorial(j)) for j in range(1,45)),Q())
assert ei>Q(21635,10000)
out=dict(status='PASS',method='fresh rational Machin/all selected tail grids; fresh Horner prefix; all sparse terms with reciprocal-binomial exponential upper bound; independent gamma/log/Ei',finite_upper=str(prefix),tail_upper=str(tail),total_upper=str(prefix+tail),Ei_lower=str(ei),diagnostic_total=float(prefix+tail),diagnostic_ei=float(ei),hits=hits,rows=rows,wall_seconds=time.time()-start,CPU_limit=240,AS_limit=512*1024**2,wall_limit=280)
(L/'independent-receipt.json').write_text(json.dumps(out,indent=2));print('PASS',float(prefix+tail),float(ei),time.time()-start)
