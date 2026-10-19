"""MIT; bounded exact diagnostics, never mathematical gates. No writes."""
from fractions import Fraction as F
from itertools import product
import json

def add(A,B): return [[A[i][j]+B[i][j] for j in range(2)] for i in range(2)]
def scale(a,A): return [[a*x for x in row] for row in A]
def sub(A,B): return add(A,scale(-1,B))
def norm(A): return sum(x*x for row in A for x in row)
I=[[F(1),F(0)],[F(0),F(1)]]
A=[[F(1),F(0)],[F(0),F(0)]]
checks=0
for k in range(2,41):
    t=F(1,k); e=2*t/(1+t*t); c=(1-t*t)/(1+t*t)
    Z=[[e*e,e*c],[e*c,c*c]]; S=add(A,Z)
    R=scale(1/e,sub(S,I))
    P=scale(F(1,2),add(I,R)); Q=sub(I,P)
    for B in [scale(0,I),S,scale(1+e,P),scale(1-e,Q)]:
        assert norm(sub(A,B))+norm(sub(Z,sub(S,B)))==2
        checks+=1
scalar=0
for a,b in product(range(1,31),repeat=2):
    r=F(a,b)
    E=r*r+1/(r*r)-2
    R=r*r+1/(r*r)-2*r-2/r+2
    assert 0<=R<=E
    scalar+=1
values={}
for x in product([-1,1],repeat=3):
    x1,x2,x3=x
    f=F(x2+x3,2)+F(x1*(x2-x3),2)
    g=F(x2+x3,2)+F(x1*(1-x2*x3),2)
    lo=F(x2+x3,2)-abs(F(x2-x3,2))
    hi=F(x2+x3,2)+abs(F(x2-x3,2))
    assert f in [-1,1] and g==(lo if x1==-1 else hi)
    values[x]=(f,g)
coef=[]
for mask in range(8):
    coef.append(tuple(sum(v[j]*__import__('functools').reduce(lambda a,b:a*b,[x[i] for i in range(3) if mask>>i&1],1) for x,v in values.items())/8 for j in [0,1]))
deg=[max(mask.bit_count() for mask,c in enumerate(coef) if c[j]) for j in [0,1]]
assert deg==[2,3]
print(json.dumps({'purpose':'bounded rational identities only; no mathematical gate','exact_sum_allocations':checks,'scalar_budget_pairs':scalar,'boolean_values':8,'compression_degrees':deg,'all_assertions_passed':True},indent=2))
