#!/usr/bin/env python3
"""Independent exact checks, not a proof. All calculations use Python integers
or Fraction. Literal source product and a direct rational permutation sum are
independent of the first-deficit algorithm used in discovery.md.
"""
from itertools import permutations, product
from collections import defaultdict
from fractions import Fraction
from math import comb, prod
from pathlib import Path
import json, time


def conjecture(n,k): return (-1)**(n-1)*comb(n,k)*comb(n-2,k-1)

def edges(n,k):
    # One-based source definition converted to zero-based indices.
    return ([(i,j) for i in range(n) for j in range(n) if i<j-1]
            +[(n-1,j) for j in range(k)]
            +[(i,0) for i in range(k,n-1)])

def expand(n,es):
    p={(0,)*n:1}
    for i,j in es:
        q=defaultdict(int)
        for a,c in p.items():
            b=list(a); b[i]+=1; q[tuple(b)]+=c
            b=list(a); b[j]+=1; q[tuple(b)]-=c
        p={a:c for a,c in q.items() if c}
    return p

def literal_inner(n,k):
    es=edges(n,k)
    assert len(es)==len(set(es))==n*(n-1)//2
    p=expand(n,es)
    val=0
    for a in permutations(range(n-1,-1,-1)):
        # Coefficient in prod_{i<j}(xi-xj): sign versus descending exponents.
        s=(-1)**sum(a[i]<a[j] for i in range(n) for j in range(i+1,n))
        val+=s*p.get(a,0)
    return val,len(p)

def direct_ds(n,k):
    # Distinct integer nodes; no appeal to any monomial/descent formula.
    total=Fraction(0)
    for x in permutations(range(1,n+1)):
        num=prod(x[-1]-x[j] for j in range(k))*prod(x[i]-x[0] for i in range(k,n-1))
        den=prod(x[i]-x[i+1] for i in range(n-1))
        total+=Fraction(num,den)
    assert total.denominator==1
    return total.numerator

def deficit_check(n,k):
    es=[(n-1,j) for j in range(k)]+[(i,0) for i in range(k,n-1)]
    p=expand(n,es)
    g=defaultdict(int); c=[0]*(n+1)
    for a,v in p.items():
        assert sum(a)==n-1 and all(x<=1 for x in a[1:-1])
        sums=[]; z=0
        for j in range(n-1): z+=a[j]; sums.append(z)
        bad=[j+1 for j,z in enumerate(sums) if z<j+1]
        r=min(bad,default=n)
        assert bad==list(range(r,n))
        g[r]+=v
        c[0]+=v
        for j,z in enumerate(sums,1):
            if z>=j:c[j]+=v
    expected=(-1)**k*comb(n-2,k-1)
    assert c==[expected if j==k else 0 for j in range(n+1)]
    assert all(g[r]==c[r-1]-c[r] for r in range(1,n+1))
    value=sum(v*(-1)**(n-r)*comb(n-1,r-1) for r,v in g.items())
    assert value==conjecture(n,k)
    return len(p)

def run():
    started=time.time(); log={'literal':[],'rational_ds':[],'deficit':[]}
    for n in range(2,7):
        for k in range(1,n):
            v,size=literal_inner(n,k)
            assert v==conjecture(n,k),(n,k,v)
            log['literal'].append({'n':n,'k':k,'inner':v,'monomials':size})
        print('literal',n,flush=True)
    for n in range(2,9):
        for k in range(1,n):
            v=direct_ds(n,k)
            assert v==conjecture(n,k),(n,k,v)
            log['rational_ds'].append({'n':n,'k':k,'value':v})
        print('rational_ds',n,flush=True)
    for n in range(2,17):
        for k in range(1,n):
            size=deficit_check(n,k)
            log['deficit'].append({'n':n,'k':k,'monomials':size})
        print('deficit',n,flush=True)
    log['elapsed_seconds']=time.time()-started
    log['status']='all exact checks pass; finite evidence only'
    (Path(__file__).parent/'exact_check.json').write_text(json.dumps(log,indent=2)+'\n')
    print(log['status'],log['elapsed_seconds'])
if __name__=='__main__':run()
