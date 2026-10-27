"""Exact symbolic identities and rational interval certificates; no floating point."""
import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import sympy as S

def frac(x):
    return F(int(S.numer(x)), int(S.denom(x)))

def singleton(x): return (frac(x), frac(x))
def add(a,b): return (a[0]+b[0], a[1]+b[1])
def neg(a): return (-a[1],-a[0])
def mul(a,b):
    v=[x*y for x in a for y in b]
    return min(v),max(v)
def inv(a):
    assert 0<a[0]
    return 1/a[1],1/a[0]
def sqroot(q):
    q=frac(q); den=10**12
    k=isqrt(q.numerator*den*den//q.denominator)
    a,b=F(k,den),F(k+1,den)
    assert a*a<=q<b*b
    return a,b
def qf(a,v): return (v.T*a*v)[0]

I=S.eye(2)
P=S.Matrix([[1,-1],[-1,1]])/2
Q=S.diag(1,0)
assert P*P==P and Q*Q==Q and P.T==P and Q.T==Q
t=32; h=t*t
A=I+(h-1)*P; B=I+(h-1)*Q
# Inputs are diag(A,B), diag(B,I). Both lie in [I,1024 I].
# Phi is the average of the two diagonal blocks: unital completely positive.
FA=(A+B)/2; FB=(B+I)/2; T=I+(t-1)*Q
ss=S.Rational(1054721,2048)
assert A.det()==B.det()==h and T*T==B
R=A+B
assert R*A.inv()*R==ss*B
# Therefore A#B=R/sqrt(ss), and Phi(A#B)=FA/sqrt(ss)+T/2.
dd=S.Rational(4100,1054721)
r=S.trace(FA.inv()*FB)
assert dd==FB.det()/FA.det()
b=S.symbols('b')
res=(FB+b*FA)*FA.inv()*(FB+b*FA)-(r+2*b)*FB
assert all(S.rem(S.Poly(e,b),S.Poly(b*b-dd,b)).as_expr()==0 for e in res)
# (FB+sqrt(dd)*FA)/sqrt(r+2sqrt(dd)) is positive and solves Z FA^-1 Z=FB.
# Uniqueness of the positive Riccati solution identifies it with FA#FB.
v=S.Matrix([1,2]); aa=1/ss; alpha2=S.Rational(1025,64)**2
aI=sqroot(aa); bI=sqroot(dd)
cp=add(add(singleton(qf(FA*FA,v)*aa),mul(aI,singleton(qf(FA*T+T*FA,v)/2))),singleton(qf(T*T,v)/4))
dp=mul(add(add(singleton(qf(FB*FB,v)),mul(bI,singleton(qf(FB*FA+FA*FB,v)))),singleton(dd*qf(FA*FA,v))),inv(add(singleton(r),mul(singleton(2),bI))))
defect=add(mul(singleton(alpha2),cp),neg(dp))
assert defect[1]<-17000

# A separate entirely rational witness refutes the Diaz--Metcalf clause.
P2=S.ones(2)/2; A2=I+255*P2; B2=S.diag(256,1)
C=(A2+S.diag(16,1))/2; M=(I+2*A2+B2)/4
V=S.Matrix([19,-20]); E=S.Rational(257,32)**2*C*C-M*M
value=qf(E,V)
assert value==-S.Rational(2449502775,8192)
out={
 'scope':'Exact mathematical certificates, NOT Lean or novelty certification; credit 0',
 'polya':{'t':t,'A':str(A),'B':str(B),'Phi':'average of two diagonal 2x2 blocks',
          'input_pair':'diag(A,B), diag(B,I)', 'm1':1,'m2':1,'M1':32,'M2':32,
          'vector':[1,2],'sqrt_a_bounds':list(map(str,aI)),'sqrt_b_bounds':list(map(str,bI)),
          'defect_bounds':list(map(str,defect)), 'strict_upper_bound':-17000},
 'diaz':{'input_pair':'diag(I,A2), diag(B2,A2)', 'm1':1,'m2':1,'M1':16,'M2':16,
         'A2':str(A2),'B2':str(B2),'vector':[19,-20],'normalized_defect':str(value)},
 'standard_facts_used':['positive geometric mean is unique positive Riccati solution',
                       'compression and sums preserve positive semidefiniteness',
                       'block diagonal functional calculus']}
Path('exact-witnesses.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
