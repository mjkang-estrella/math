"""Bounded diagnostics only. No mathematical acceptance or theorem gate."""
from itertools import product
from math import gcd, prod
import json

def factors(n):
    out=[]
    p=2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0: n//=p
        p+=1
    if n>1: out.append(n)
    return out

def capacity(x,L):
    fs=[factors(x+i) for i in range(L)]
    small=sorted({p for row in fs for p in row if p<=L})
    for bs in product(*(range(p) for p in small)):
        b=dict(zip(small,bs))
        rem=[[j for j in range(L) if all((b[p]+j)%p for p in fs[i] if p<=L)] for i in range(L)]
        large=[[p for p in row if p>L] for row in fs]
        if all(len(rem[i])<=len(large[i]) for i in range(L)):
            residues=list(b.items())
            for i in range(L): residues.extend((p,-j%p) for p,j in zip(large[i],rem[i]))
            y,M=0,1
            for p,a in residues:
                assert gcd(M,p)==1
                y+=M*((a-y)*pow(M,-1,p)%p)
                M*=p
            if y<x: y+=((x-y+M-1)//M)*M
            assert all(gcd(x+i,y+j)>1 for i in range(L) for j in range(L))
            return y,M
    return None

cases=0;positive=0
# Full independent periodic enumeration is bounded by this explicit cutoff.
for L in (2,3):
    for x in range(1,41):
        M=prod(set(p for i in range(L) for p in factors(x+i)))
        assert M<=100000
        actual=any(all(gcd(x+i,y+j)>1 for i in range(L) for j in range(L)) for y in range(M))
        computed=capacity(x,L)
        assert actual==(computed is not None),(x,L,actual,computed)
        cases+=1;positive+=actual
witnesses=[]
for x,L in [(14,2),(1274,3),(134043,4)]:
    ans=capacity(x,L)
    assert ans is not None
    witnesses.append({'x':x,'L':L,'constructed_y':ans[0],'period':ans[1]})
print(json.dumps({'periodic_exhaustive_cases':cases,'positive_cases':positive,'witnesses':witnesses,'scope':'finite diagnostics; not proof of the asymptotic working question'},indent=2))
