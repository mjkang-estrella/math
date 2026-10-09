"""Exact checks of reduction identities; not a proof of the infinite theorem."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

def mat(l):
    return [[(l if i==j else 0)+(1-l)/4 for j in range(4)] for i in range(4)]
def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]

checks={}
for a,b in product([F(1),F(3,4),F(1,1000),F(999,1000)],repeat=2):
    assert mul(mat(a),mat(b))==mat(a*b)
checks['semigroup_pairs']=16

for c in [F(1,2),F(3,4),F(99,100)]:
    for k in range(1,41):
        assert sum(c**(-4*j) for j in range(1,k+1)) == (c**(-4*k)-1)/(1-c**4)
checks['common_channel_subdivisions']=120

for chain in [[F(1),F(999,1000),F(2,3),F(1,1000)], [F(3,4)]*30, [F(1)]*20]:
    p=F(1); weighted=F(0)
    for l in chain:
        p*=l; weighted+=(1-l**4)/p**4
    assert weighted==p**(-4)-1
checks['arbitrary_series_telescopes']=3
p=F(1); weighted=F(0)
for n in range(1,101):
    l=1-F(1,(n+1)**2);p*=l;weighted+=(1-l**4)/p**4
    assert p==F(n+2,2*(n+1)) and weighted==p**(-4)-1
checks['ray_prefixes']=100

# One shared internal channel followed by two perfect copies, versus
# two independent copies of that channel. Same root-leaf marginals,
# different joint experiments.
a=F(1,2);m=mat(a)
shared={(j,k):sum(m[0][u]*(j==u)*(k==u) for u in range(4)) for j,k in product(range(4),repeat=2)}
separate={(j,k):m[0][j]*m[0][k] for j,k in product(range(4),repeat=2)}
assert shared!=separate
assert sum(shared[j,k] for j,k in shared if j!=k)==0
assert sum(separate[j,k] for j,k in separate if j!=k)==F(9,16)
assert all(sum(shared[j,k] for k in range(4))==sum(separate[j,k] for k in range(4)) for j in range(4))
checks['terminal_noise_mismatch']={'lambda':'1/2','shared_disagreement':'0','independent_disagreement':'9/16','equal_one_leaf_marginals':True}

# Reveal versus hide the copy/refresh flag; quadratic posterior information.
for l in [F(1,4),F(1,2),F(3,4)]:
    assert 3*l>3*l*l
checks['copy_flag_more_informative']=3

# Two binary coordinates of a four-state Potts noise are not independent.
# The joint flip of both bits has probability (1-lambda)/4.
assert (1-a)/4 != ((1-a)/2)**2
checks['two_bit_product_reduction_fails']=True

# Test the proposed splitting estimate on long almost-unary paths, with
# square transition probabilities so all arithmetic including K is rational.
for roots in [[F(1)]*40,[F(99,100)]*40,[F(1),F(1,2),F(3,4),F(1)]*10]:
    n=len(roots);t=[z*z for z in roots];alpha=[1-z for z in t]
    lam=[F(1),F(999,1000),F(1,1000),F(2,3)]*(n//4)
    x=[F(1)]
    for j in range(n):x.append(x[-1]*t[j]/lam[j]**2)
    def kernel(i,j):
        z=F(1)
        for k in range(i,j):z*=roots[k]
        return z
    for i in range(n):assert sum(alpha[j]*kernel(i,j) for j in range(i+1,n))<=2
    for j in range(1,n+1):assert sum(alpha[i]*kernel(i,j) for i in range(j))<=2
    lhs=F(0)
    for i in range(n):
        lp=F(1)
        for j in range(i+1,n):
            lp*=lam[j-1]
            lhs+=alpha[i]*alpha[j]*x[i]*x[j]*lp
    assert lhs<=2*sum(alpha[i]*x[i]**2 for i in range(n))
checks['splitting_kernel_paths']=3
out=Path(__file__).with_name('results.json')
out.write_text(json.dumps({'status':'PASS','checks':checks,'limits':'Finite exact checks only; analytical reductions and infinite-limit arguments are in the review.'},indent=2)+'\n')
print(out.read_text())
