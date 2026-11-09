"""Bounded exact identity/falsification checks for the formal Riccati route.

No all-order conclusion is inferred from this program.  Uses <512 MiB.
Run: python3 check.py (writes checks.json beside this file).
"""
import resource
resource.setrlimit(resource.RLIMIT_AS, (500 * 1024**2, 500 * 1024**2))
from collections import defaultdict
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import json

# Sparse Laurent polynomials: key = (u exponent, v exponent, t exponent).
def add(*ps):
    q = defaultdict(int)
    for p in ps:
        for k, c in p.items(): q[k] += c
    return {k:c for k,c in q.items() if c}

def scale(p, c): return {k:c*v for k,v in p.items() if c*v}

def mul(p, q):
    out = defaultdict(int)
    for (a,b,k), c in p.items():
        for (d,e,l), f in q.items(): out[a+d,b+e,k+l] += c*f
    return {k:c for k,c in out.items() if c}

def D(p):
    # D = -(1+t^2) d/dt = d/d(theta/2).
    out = defaultdict(int)
    for (a,b,k), c in p.items():
        out[a,b,k-1] -= k*c
        out[a,b,k+1] -= k*c
    return {k:c for k,c in out.items() if c}

def quotient(p):
    # Exact Laurent division by 1+t^2, independently by each parameter monomial.
    groups = defaultdict(dict)
    for (a,b,k), c in p.items(): groups[a,b][k] = c
    out = {}
    for (a,b), f in groups.items():
        lo = min(f)
        while f and max(f) >= lo+2:
            k = max(f); c = f[k]
            out[a,b,k-2] = c
            del f[k]
            f[k-2] = f.get(k-2,0)-c
            if not f[k-2]: del f[k-2]
        assert not f, (a,b,f)
    assert mul(out, {(0,0,0):1,(0,0,2):1}) == p
    return out

def primitive(p):
    # Unique odd Laurent primitive of an even p under D.
    out = {}
    for (a,b,k), c in quotient(p).items():
        assert k % 2 == 0
        out[a,b,k+1] = -Q(c,k+1)
    assert D(out) == p
    return out

def midpoint(p):
    out = defaultdict(Q)
    for (a,b,k), c in p.items(): out[a,b] += c
    return {k:c for k,c in out.items() if c}

def v2(c):
    c = Q(c)
    if not c: return 10**9
    def vi(x): x=abs(x); return (x & -x).bit_length()-1
    return vi(c.numerator)-vi(c.denominator)

U = {(1,0,0):1,(1,0,2):1,(0,1,0):1,(0,1,-2):1}
s = [{},U]
for n in range(1,15):
    s.append(add(scale(D(s[n]),-1),
                 *[scale(mul(s[j],s[n-j]),-1) for j in range(1,n)]))

rows=[]
for r in range(1,9):
    n=2*r-1
    assert all(k%2==0 and a+b <= r for (a,b,k) in s[n])
    prim=primitive(s[n]); J=midpoint(prim)
    kappa={k:Q((-1)**r*c,2**(4*r-2)) for k,c in J.items()}
    catalan=comb(2*r-2,r-1)//r
    top=scale(U,1)
    for _ in range(r-1): top=mul(top,U)
    homogeneous={k:c for k,c in s[n].items() if k[0]+k[1]==r}
    assert homogeneous == scale(top,(-1)**(r-1)*catalan)
    gamma=Q(2*comb(2*r,r),(2*r-1)*16**r)
    I=sum((Q(comb(r-1,j),2*j+1) for j in range(r)),Q())
    assert kappa[r,0] == gamma*I
    desired=2*r+v2(factorial(r-1))
    assert min(map(v2,kappa.values())) == -desired
    # A potentially useful stronger degree-specific bound, checked here only.
    for (a,b),c in J.items():
        assert v2(c)+v2(factorial(a+b-1)) >= 2*r-2
    rows.append({'r':r,'J_min_v2':min(map(v2,J.values())),
                 'required_J_min_v2':r-1+(r-1).bit_count(),
                 'kappa_top':str(kappa[r,0]),
                 'degree_content':{str(d):min(v2(c) for (a,b),c in J.items() if a+b==d)
                                   for d in range(1,r+1)}})

# Independent SymPy direct source pipeline, only n<=9.
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling
u,v,t=sp.symbols('u v t',real=True)
P=lambda x,k:sp.prod(x-j*(j+1) for j in range(k))
C=[sp.expand(sum(comb(k,j)*P(u,j)*P(v,k-j)*(1+sp.I)**j*(1-sp.I)**(k-j)
                 for j in range(k+1))) for k in range(10)]
A=[sp.Integer(1)]+[sp.expand(sum(2**(n-k)*(factorial(n)//factorial(k))*stirling(n,k,kind=2)*C[k]
                              for k in range(1,n+1))) for n in range(1,10)]
B=[sp.Integer(0)]
for n in range(1,10):
    B.append(sp.expand(A[n]-sum(comb(n-1,j-1)*B[j]*A[n-j] for j in range(1,n))))
    if n%2:
        r=(n+1)//2
        J=midpoint(primitive(s[n]))
        rhs=sum(sp.Rational((-1)**r*c.numerator,c.denominator)*u**a*v**b
                for (a,b),c in J.items())*factorial(n)
        assert sp.expand(sp.im(B[n])-rhs)==0
    else: assert sp.im(B[n])==0

# Test the inverse-factorial ODE coefficient identity at the whole curve.
x=(1+sp.I*t)/2; y=(1-sp.I/t)/2
Cs=[sp.expand(sum(P(u,j)*P(v,k-j)*x**j*y**(k-j)/(factorial(j)*factorial(k-j))
                 for j in range(k+1))) for k in range(6)]
Dt=lambda f:sp.expand(-(1+t*t)*sp.diff(f,t))
Ut=u*(1+t*t)+v*(1+t**-2)
for k in range(5):
    assert sp.expand(Dt(Dt(Cs[k]))+2*sp.I*k*Dt(Cs[k])+2*sp.I*Dt(Cs[k+1])-Ut*Cs[k])==0

# Generic monomial calculation underlying the all-order curve-operator identity.
xx,yy,c,d=sp.symbols('x y c d')
deltaQ=c*xx*(xx-1)+d*yy*(yy-1)+(c*xx+d*yy)*(c*(xx-1)+d*(yy-1))
diagonal=c*(c+1)*xx*(xx-1)+d*(d+1)*yy*(yy-1)
assert sp.expand(deltaQ-diagonal-c*d*(2*xx*yy-xx-yy))==0

# Mandatory falsifiers for tempting stronger statements.
# The coefficientwise primitive BEFORE midpoint evaluation is not sufficiently divisible.
pre=primitive(s[3])
coefficient=pre[2,0,1]
assert coefficient==1 and v2(coefficient)<2
# Nor do primitive monomials meet the midpoint bound individually: u^2*(t+t^3/3).
assert pre[2,0,3]==Q(1,3)
assert coefficient+pre[2,0,3]==Q(4,3)
# The obvious general shifted moment strengthening is false.
moment=sum((Q(comb(3,j),2*j+3) for j in range(4)),Q())
assert moment==Q(464,315) and v2(moment)==4 < 3+v2(4)

out={'status':'finite identity checks only; full shifted upper bound UNPROVED',
     'source_B_vs_Riccati_n_max':9,'inverse_factorial_ODE_s_max':4,
     'Riccati_n_max':15,'rows':rows,
     'falsifiers':{'coefficientwise_primitive_bound':str(coefficient),
                   'individual_primitive_terms':['1','1/3'],
                   'shifted_binomial_moment':str(moment)},
     'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
