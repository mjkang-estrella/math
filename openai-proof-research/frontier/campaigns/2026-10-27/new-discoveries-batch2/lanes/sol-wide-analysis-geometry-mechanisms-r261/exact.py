from work import *
import sympy as s
from functools import lru_cache
u,v=s.symbols('u v',real=True)
steps=[-u,u-v,v]
f=[s.Integer(1)]+[s.expand(sum((s.I*x)**k for x in steps)/(3*s.factorial(k))) for k in range(1,7)]
B=[s.Integer(0)]*7
for n in range(1,7):B[n]=s.expand(f[n]-sum(k*B[k]*f[n-k] for k in range(1,n))/n)
P2=s.expand(B[4]+B[3]**2/2)
P4=s.expand(B[6]+B[3]*B[5]+B[4]**2/2+B[3]**2*B[4]/2+B[3]**4/24)
@lru_cache(None)
def one(k):
 if k%2:return s.Integer(0)
 if k==-2:return -s.sqrt(s.pi)
 assert k>=0
 return 2**(k+1)*s.gamma(s.Rational(k+1,2))
@lru_cache(None)
def J(p,q):
 # Unnormalised integral; integrate the nonnegative power first.
 if p<0:p,q=q,p
 assert p>=0 and q>=-2
 return s.sqrt(3*s.pi)*sum(s.binomial(p,2*j)*s.factorial2(2*j-1)*(s.Rational(3,2))**j*s.Rational(1,2)**(p-2*j)*one(p-2*j+q) for j in range(p//2+1))
def integ(expr):
 ans=0
 for term in s.expand(expr).as_ordered_terms():
  d=term.as_powers_dict();p=int(d.get(u,0));q=int(d.get(v,0));c=term/u**p/v**q
  ans+=c*J(p,q)/(4*s.pi**2)
 return s.simplify(ans)
pieces=[4*P4/u**2/v**2,s.Rational(1,3)*(1/u**2+1/v**2)*P2,s.Rational(1,60)*(v**2/u**2+u**2/v**2),s.Rational(1,36)]
vals=[integ(x) for x in pieces];d0=s.simplify(sum(vals));target=-4*s.sqrt(3)/(81*s.pi)
out=dict(B={str(k):str(B[k]) for k in range(2,7)},P2=str(P2),P4=str(P4),pieces=[str(x) for x in vals],d0=str(d0),target=str(target),difference=str(s.simplify(d0-target)),a_triangle=str(s.simplify(s.Rational(1,32)+s.pi*d0/3)))
dump('exactchecks.json',out);print(json.dumps(out,indent=2))
