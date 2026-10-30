from fractions import Fraction as F
from pathlib import Path
import json,datetime
L=Path(__file__).resolve().parent
# Rational enclosure of exp(1), using geometric domination of the factorial tail.
s=F(1);term=F(1)
for k in range(1,25):term/=k;s+=term
elo=s;ehi=s+term/F(25)/(1-F(1,26))
p=(1/(2*ehi),1/(2*elo));eps=F(1,1024)
def logbox(x,N=100):
 # atanh expansion; used only on positive rational points near [0.18,1].
 z=(x-1)/(x+1);v=sum((2*z**(2*k+1)/F(2*k+1) for k in range(N)),F(0))
 err=2*abs(z)**(2*N+1)/F(2*N+1)/(1-z*z)
 return v-err,v+err
ln2=logbox(F(2));le=(-10*ln2[1],-10*ln2[0])
m=(p[0]+(1-p[0])*eps,p[1]+(1-p[1])*eps)
# -m log(m) is increasing on this interval (m<1/e).
assert m[1]<1/ehi
entlo=(1-p[0])*eps*le[0]-m[0]*logbox(m[0])[1]
enthi=(1-p[1])*eps*le[1]-m[1]*logbox(m[1])[0]
psihi=1-eps+eps*le[1]
rhs_hi=F(3,2)*p[1]*psihi
assert entlo>rhs_hi
# ULC coefficient sequence (n+1)/(2e) has strictly log-concave adjacent ratios:
# (n+1)^2-n(n+2)=1, for every integer n>=1, polynomial identity.
from sympy import symbols,expand
n=symbols('n');assert expand((n+1)**2-n*(n+2))==1
# mean(Pois(1)+Bern(1/2))=3/2; log(2)>2/3 from first atanh term.
assert ln2[0]>F(2,3)
def down(x):return str(F(x.numerator*10**12//x.denominator,10**12))
def up(x):return str(F(-((-x.numerator*10**12)//x.denominator),10**12))
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',
 scope='Exact rational diagnostic for a positive admissible test; public refutation, zero novelty credit. Universal limit argument is in discovery.md.',
 exp1_interval=[str(elo),str(ehi)],p0_interval=[str(x) for x in p],epsilon=str(eps),
 entropy_interval=[down(entlo),up(enthi)],rhs_upper=up(rhs_hi),gap_lower=down(entlo-rhs_hi),
 ulc_polynomial_identity='(n+1)^2-n(n+2)=1',log2_lower=down(ln2[0]))
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS: positive test strictly violates mean-constant inequality; rational interval gap >',float(entlo-rhs_hi))
