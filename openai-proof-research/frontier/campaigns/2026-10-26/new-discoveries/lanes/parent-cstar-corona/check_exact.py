"""Independent exact matrix calculations for the preliminary witness."""
from fractions import Fraction as Q
import json

def mat(a):
    return tuple(tuple(Q(x) for x in row) for row in a)

def mul(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))

def add(a,b):
    return tuple(tuple(a[i][j]+b[i][j] for j in range(2)) for i in range(2))

def scale(s,a):
    return tuple(tuple(s*x for x in row) for row in a)

zero=mat([[0,0],[0,0]])
one=mat([[1,0],[0,1]])
n=mat([[1,1],[-1,-1]])
c=mat([[Q(1,4),0],[0,0]])
cn=mul(c,n)
assert mul(n,n)==zero
assert mul(cn,cn)==scale(Q(1,4),cn)!=zero
assert mul(cn,cn)[0][0]==Q(1,16)
# For every t with 1+t/4!=0, the honest reciprocal has a nonzero
# quadratic-and-higher remainder, although (tN)^2=0.
checked=0
for t in [Q(1,k) for k in range(3,100)]:
    f=add(one,scale(t,cn))
    inv=add(one,scale(-t/(1+t/4),cn))
    assert mul(f,inv)==one==mul(inv,f)
    remainder=add(inv,scale(-1,add(one,scale(-t,cn))))
    assert remainder==scale(t*t/(4+t),cn)!=zero
    checked+=1
print(json.dumps({'status':'PASS','exact_nilpotent_checks':3,
                  'reciprocal_checks':checked,
                  'scope':'Exact algebra only; universal norm/order proof in PROOF.md'},indent=2))
