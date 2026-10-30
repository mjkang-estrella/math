"""One exact obstruction control; no parameter search and no source proof."""
from fractions import Fraction as Q
from itertools import combinations
import json
def det(a):
    if len(a)==1:return a[0][0]
    return sum((-1)**j*a[0][j]*det([r[:j]+r[j+1:] for r in a[1:]]) for j in range(len(a)))
def minors(a):
    return [str(det([[a[i][j] for j in ix] for i in ix])) for k in range(1,len(a)+1) for ix in combinations(range(len(a)),k)]
a=[[Q(1),Q(19,20),Q(1,2)],[Q(19,20),Q(1),Q(1,20)],[Q(1,2),Q(1,20),Q(1)]]
b=[[x*x for x in r] for r in a]
assert det(a)<0 and all(Q(x)>0 for x in minors(b))
# Secant compatibility at the three equally spaced nodes 1,2,3.
values=[Q(0),Q(19,20),Q(1)]
assert all(a[i][j]==(values[j]-values[i])/(j-i) for i in range(3) for j in range(i+1,3))
print(json.dumps(dict(L=[[str(x) for x in r] for r in a],principal_minors_L=minors(a),principal_minors_square=minors(b),secant_compatibility='PASS at nodes 1,2,3',scope='Exact finite algebra obstruction to pointwise square-root inference only. No global radially convex f, universal counterexample, or full conjecture proof.'),indent=2))
