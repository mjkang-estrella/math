import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(35,35));signal.alarm(45)
from fractions import Fraction as F
from math import factorial,comb
import json
from pathlib import Path
D=10**35
def ceildiv(a,b):return -((-a)//b)
def interval(x):return (x.numerator*D//x.denominator,ceildiv(x.numerator*D,x.denominator))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):
 v=[a[i]*b[j] for i in range(2) for j in range(2)];return(min(v)//D,ceildiv(max(v),D))
def div(a,n):return(a[0]//n,ceildiv(a[1],n))
def neg(a):return(-a[1],-a[0])
def power(a,n):
 r=(D,D)
 while n:
  if n&1:r=mul(r,a)
  a=mul(a,a);n//=2
 return r
def atan(x,K):
 s=sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(K)),F(0));e=x**(2*K+1)/F(2*K+1)
 return (s-e,s+e)
a=atan(F(1,5),80);b=atan(F(1,239),25)
pi=(16*a[0]-4*b[1],16*a[1]-4*b[0]);P=(interval(pi[0])[0],interval(pi[1])[1]);assert P[1]-P[0]<=2

def sin_integer(n):
 m=(n*D+P[0])//(2*P[0]);x=(n*D-2*m*P[1],n*D-2*m*P[0]);assert max(abs(t) for t in x)<4*D
 x2=mul(x,x);term=x;s=x
 for j in range(1,50):
  term=neg(div(mul(term,x2),(2*j)*(2*j+1)));s=add(s,term)
 e=ceildiv(4**101*D,factorial(101));return(s[0]-e,s[1]+e)
rows=[];s=(0,0)
for n in range(1,10001):
 y=div(add((2*D,2*D),sin_integer(n)),3);assert 0<y[0]<=y[1]<=D
 s=add(s,div(power(y,n),n))
 if n in [10,100,1000,10000]:rows.append({'N':n,'lower_scaled':s[0],'upper_scaled':s[1]})
# Exact averaged coefficient, independent of numerical quadrature.
j={str(n):str(sum((F(comb(n,2*k)*comb(2*k,k),16**k) for k in range(n//2+1)),F(0))) for n in [1,2,4,10,20]}
assert F(j['2'])==F(9,8)
assert F(j['20'])>100
# A finite interior phase falsifier of a too-strong pointwise average shortcut.
# n=8 has sin8>0.98, so actual term is much greater than its circular average.
y=div(add((2*D,2*D),sin_integer(8)),3);lhs=div(power(y,8),8)
J8=sum((F(comb(8,2*k)*comb(2*k,k),16**k) for k in range(5)),F(0));avg=(F(2,3)**8)*J8/8
assert F(lhs[0],D)>avg
out={'status':'PASS','certificate_arithmetic':'integers and rational fractions only','scale':D,'pi_lower':str(pi[0]),'pi_upper':str(pi[1]),'partial_sums':rows,'J_n':j,'n8_term_lower':str(F(lhs[0],D)),'n8_averaged_term':str(avg),'full_source_conjecture':'UNRESOLVED','seed':'none; deterministic'}
Path(__file__).with_name('prefix-replay.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
