import json,time,math
from fractions import Fraction as F
import sympy as S
import mpmath as mp
start=time.monotonic();out={}
# Gram of projected unused normals and its inverse, all exact.
count=0
for n in range(4,13):
 for s in range(2,n):
  N=n-s;G=S.eye(N)-S.ones(N)/n
  assert G*(S.eye(N)+S.ones(N)/s)==S.eye(N)
  count+=1
out['exact_inverse_Gram_identities']=count
# Every 2-face has (a,b)=(1,2) or (2,1), angle 1/6.
y=S.Symbol('asin_quarter_over_pi',real=True)
beta_same=S.Rational(1,8)+3*y/4
beta_mixed=S.Rational(1,8)-y/4
values=[]
for k in range(1,6):
 m=6-k;v=0
 for a,b in [(1,2),(2,1)]:
  if k<a or m<b:continue
  u=k-a;w=m-b
  beta=beta_same if u==0 or w==0 else beta_mixed
  v+=S.binomial(k,a)*S.binomial(m,b)*beta/6
 values.append(S.expand(v))
assert values==[S.Rational(5,24)+5*y/4,S.Rational(1,3),S.Rational(3,8)-3*y/4,S.Rational(1,3),S.Rational(5,24)+5*y/4]
assert S.expand(values[2]-values[1])==S.Rational(1,24)-3*y/4
# asin(1/4)>1/4, pi<4 imply y>1/16>1/18, hence center<1/3.
assert F(1,16)>F(1,18)
out['exact_v2_n6']=[str(v) for v in values]
out['obstruction']='v2(center)<1/3=v2(neighbors), strictly positive values; not source counterexample'
# Classical d=1 formula, checked only as a sanity check.
cases=0
for n in range(4,31):
 q=[F(0)]+[1-F(2,math.comb(n,k)) for k in range(1,n)]+[F(0)]
 for k in range(1,n):assert q[k]**2>=q[k-1]*q[k+1];cases+=1
out['classical_d1_finite_checks']=cases
# Diagnostic independent common-factor integral, NOT proof.
mp.mp.dps=45
phi=lambda t:mp.exp(-t*t/2)/mp.sqrt(2*mp.pi)
Phi=lambda t:mp.erfc(-t/mp.sqrt(2))/2
errors=[]
for u in range(4):
 v=3-u
 val=mp.quad(lambda t:phi(t)*Phi(t/mp.sqrt(3))**u*Phi(-t/mp.sqrt(3))**v,[-mp.inf,0,mp.inf])
 closed=mp.mpf(1)/8+(3 if u in [0,3] else -1)*mp.asin(mp.mpf(1)/4)/(4*mp.pi)
 errors.append(str(abs(val-closed)));assert abs(val-closed)<mp.mpf('1e-38')
out['diagnostic_integral_errors']=errors
out['seconds']=time.monotonic()-start
out['status']='PASS bounded identities and method obstruction only'
print(json.dumps(out,indent=2))
