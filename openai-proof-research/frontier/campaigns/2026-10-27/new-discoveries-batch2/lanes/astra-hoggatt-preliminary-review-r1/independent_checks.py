"""Finite exact corroboration, NOT proof, written independently for this review."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import prod
from pathlib import Path
import json

@lru_cache(None)
def qb(q,n,k):
    if k<0 or k>n: return Q(0)
    if k==0 or k==n: return Q(1)
    return qb(q,n-1,k)+q**(n-k)*qb(q,n-1,k-1)

def f(q,n,m):
    return [q**(m*k*(k+1)//2)*prod(qb(q,n,k+j) for j in range(m)) for k in range(n-m+2)]

def mul(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def dq(q,a):return [sum(q**j for j in range(k))*a[k] for k in range(1,len(a))]

def planes(q,k,l,m):
    total=Q(0)
    for a in product(range(m+1),repeat=k*l):
        if all(a[i*l+j]>=a[(i+1)*l+j] for i in range(k-1) for j in range(l)) and all(a[i*l+j]>=a[i*l+j+1] for i in range(k) for j in range(l-1)):
            total+=q**sum(a)
    return total

counts=dict(coefficient_identity=0, literal_plane_partition_normalization=0, lamprecht_symbol_identity=0, first_linear=0)
qs=[Q(101,100),Q(3,2),Q(2),Q(7,2)]
for q in qs:
    for m in range(2,7):
        for n in range(m,m+6):
            a,b=f(q,n,1),f(q,n-1,m-1)
            got=dq(q,[x*y for x,y in zip(a,b)])
            want=[sum(q**j for j in range(n))*q**(m*(k+1))*x for k,x in enumerate(f(q,n-1,m))]
            assert got==want,(q,n,m)
            counts['coefficient_identity']+=1
        linear=f(q,m,m)
        assert linear[1]==q**m*linear[0]
        counts['first_linear']+=1
    for m,k,l in product(range(1,4),range(3),range(3)):
        n=k+l+m-1
        norm=prod(qb(q,n,j) for j in range(1,m))
        assert planes(q,k,l,m)==prod(qb(q,n,k+j) for j in range(m))/norm
        counts['literal_plane_partition_normalization']+=1
    p=1/q
    for d in range(2,10):
        r=[Q(1)];small=[Q(1)]
        for j in range(d):r=mul(r,[Q(1),p**j])
        for j in range(d-1):small=mul(small,[Q(1),p**j])
        assert dq(q,r)==[sum(p**j for j in range(d))*x for x in small]
        h=[Q(0)]+dq(q,r)
        # Coefficients of the weighted convolution f *_p^d h equal t Dq f.
        a=[Q((k+1)**2) for k in range(d+1)]
        assert [a[k]*h[k]/r[k] for k in range(d+1)]==[Q(0)]+dq(q,a)
        counts['lamprecht_symbol_identity']+=1

result=dict(status='PASS_FINITE_EXACT_CHECKS_ONLY',q_values=[str(q) for q in qs],counts=counts,not_a_proof=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
