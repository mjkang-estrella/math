"""Read-only, finite exact algebra corroborating the independent written review.
No imports from or execution of the author packet; no file writes.
"""
from fractions import Fraction as F
from itertools import permutations
import json

class P:
    def __init__(self, value=0):
        self.c = ({k: F(v) for k, v in value.items() if v} if isinstance(value, dict)
                  else ({(0, 0, 0): F(value)} if value else {}))
    def __add__(self, other):
        other = other if isinstance(other, P) else P(other)
        d = self.c.copy()
        for k, v in other.c.items(): d[k] = d.get(k, 0) + v
        return P(d)
    __radd__ = __add__
    def __neg__(self): return P({k: -v for k, v in self.c.items()})
    def __sub__(self, other): return self + (-other if isinstance(other, P) else -F(other))
    def __rsub__(self, other): return -self + other
    def __mul__(self, other):
        other = other if isinstance(other, P) else P(other)
        d = {}
        for a, x in self.c.items():
            for b, y in other.c.items():
                k = tuple(i+j for i,j in zip(a,b))
                d[k] = d.get(k, 0) + x*y
        return P(d)
    __rmul__ = __mul__
    def __truediv__(self, c): return self * (1/F(c))
    def __pow__(self, n):
        out = P(1)
        for _ in range(n): out = out*self
        return out
    def __eq__(self, other): return self.c == (other if isinstance(other, P) else P(other)).c
    def degree(self, k): return P({a:b for a,b in self.c.items() if sum(a)==k})
    def val(self, x): return sum(c*prod(v**a for v,a in zip(x,k)) for k,c in self.c.items())

def prod(values):
    out=1
    for x in values: out*=x
    return out

def mm(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def ma(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def ms(a,c): return [[c*x for x in row] for row in a]
def det(a):
    ans=P(0)
    for s in permutations(range(3)):
        sign=(-1)**sum(s[i]>s[j] for i in range(3) for j in range(i+1,3))
        ans+=sign*prod(a[i][s[i]] for i in range(3))
    return ans

a,b,d=[P({tuple(int(i==j) for i in range(3)):1}) for j in range(3)]
corner=[F(9,2),F(7,2),F(33,7)]
A,B,D=[u+c for u,c in zip([a,b,d],corner)]
V=[A*(1+B-A),B*(9+A+F(12,11)*B*D-9*B),(11-D)*A-8*D+B*D*(1-D/11)]
assert all(v.degree(0)==0 for v in V)
J=[[p.c.get(tuple(int(i==j) for i in range(3)),F(0)) for j in range(3)] for p in V]
expected=[[F(-9,2),F(9,2),F(0)],[F(7,2),F(-27,2),F(147,11)],[F(44,7),F(132,49),F(-12)]]
assert J==expected
Q2=[a*b-a*a,a*b-F(27,7)*b*b+F(84,11)*b*d,-a*d+b*d/7-F(7,22)*d*d]
Q3=[P(0),F(12,11)*b*b*d,-b*d*d/11]
assert [p.degree(2) for p in V]==Q2 and [p.degree(3) for p in V]==Q3
v=[F(1),F(1),F(110,147)];ell=[F(308,550),F(132,550),F(147,550)]
assert mm(J,[[x] for x in v])==[[0],[0],[0]]
assert mm([ell],J)==[[0,0,0]] and sum(x*y for x,y in zip(v,ell))==1
I=[[F(i==j) for j in range(3)] for i in range(3)]
Pi=[[x*y for y in ell] for x in v];S=ma(I,ms(Pi,-1));N=mm(ma(J,ms(I,15)),S)
assert mm(N,N)==[[0]*3 for _ in range(3)] and any(x for row in N for x in row)
assert det([[a*int(i==j)-J[i][j] for j in range(3)] for i in range(3)])==a*(a+15)**2
quad=[p.val(v) for p in Q2];neutral=sum(x*y for x,y in zip(ell,quad))
assert quad==[0,F(20,7),-F(2530,3087)] and neutral==F(7,15)
# Clearing the equilibrium denominator 36(A-1), not just point testing.
num=66*a*(2*a+3)-528*(4*a-9)+11*(4*a-9)*(2*a+3)
assert num==55*(2*a-9)**2
# C=11A at the proposed first barrier zero.
barrier=a*(1+b-a)-(11*a*(1+11*a-8*b)+11*a*b)/11
assert barrier==a*(8*b-12*a)
f_log=-1/neutral;p_log=(corner[2]+corner[1]*v[2])/neutral
assert (f_log,p_log)==(F(-15,7),F(110,7))
assert 8*f_log+F(12,11)*p_log==0 and f_log+p_log/11==F(-5,7)
assert 8*F(9,2)-F(12,11)*F(33,2)==18
assert F(1,10)-F(1,11)==F(1,110)
print(json.dumps({'checks':'all finite polynomial and rational identities agree; analytic arguments are in REVIEW.md',
 'J':J,'stable_nilpotent':N,'quadratic_at_null':quad,'neutral_coefficient':neutral,
 'origin_F4':F(7,6)/44,'profile_log_exponents':[f_log,p_log],
 'equilibrium_numerator':'55(2A-9)^2','volume_integral':F(1,110)},default=str,indent=2))
