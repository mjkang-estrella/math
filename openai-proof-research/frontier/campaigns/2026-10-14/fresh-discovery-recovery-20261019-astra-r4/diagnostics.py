#!/usr/bin/env python3
"""Read-only exact finite checks. They do not prove the asymptotic theorem."""
import json
from fractions import Fraction
from itertools import product


def slab(p):
    # J(x,y)=(d*y,x), where d is a nonsquare, has no F_p eigenvector.
    d=next(a for a in range(1,p) if pow(a,(p-1)//2,p)==p-1)
    points={}
    for a,b in product(range(p),repeat=2):
        if a==b==0: continue
        line=[]
        for x,y in product(range(p),repeat=2):
            if (a*x+b*y)%p==1:
                line.append((x,y,(a*d*y+b*x)%p))
        assert len(line)==p
        for v in line: points[v]=points.get(v,0)+1
    assert len(points)==p**3-p and set(points.values())=={1}
    assert all(x or y for x,y,z in points)
    return {'p':p,'nonsquare':d,'lines':p*p-1,'covered_points':len(points)}


def defect(p):
    # One row whose self-dot-product is -1, padded to force t>m.
    x,y=next((a,b) for a,b in product(range(p),repeat=2) if (a*a+b*b)%p==p-1)
    X=[x,y,0]
    E=[[((1 if i==j else 0)+X[i]*X[j])%p for j in range(3)] for i in range(3)]
    assert all(sum(X[i]*E[i][j] for i in range(3))%p==0 for j in range(3))
    assert E[2][2]==1
    # Reverse defect is -E; on the forced kernel vector e_3 it equals -e_3.
    assert (-E[2][2])%p==p-1
    return {'p':p,'X':X,'kernel_witness':[0,0,1],'reverse_value':[0,0,p-1]}


def main():
    primes=[3,5,7,11,13]
    slabs=[slab(p) for p in primes]
    defects=[defect(p) for p in primes]
    for p in primes:
        for h in range(1,5):
            q=p**h
            d=(q-3)//2
            assert 2*d<=q-2
            if q>=9: assert 3*d>=q
    rows=[]
    for p in primes:
        q=p**4
        count=q*q+q+1-(p-1)*(p**3-1)
        assert count==p**8+p**3+p
        R=Fraction((p-1)*(count-1),(q+1)**2)
        assert R>1
        rows.append({'p':p,'ordinary_lower_bound':count,'row_sum':str(R)})
    # Exact exponent identities used by the event bound, for representative s.
    # The symbolic formulas are in proof.md; these substitutions catch typos.
    for s in [100,101,518,1000]:
        b=s+20;n=10*b
        assert 2*s+2+n+100*(b+2-2*s)==2402-88*s
        assert (s+1)+3*b+4*(3-b)==-7
        assert 3*b+2+4*(3-b)==-s-6
    return {'status':'PASS','scope':'Finite exact diagnostics only; no full hypergraph instance, group word problem, or asymptotic theorem is certified by this program.','slab_partitions':slabs,'signed_defects':defects,'hyperstar_decay_obstruction':rows}

if __name__=='__main__': print(json.dumps(main(),indent=2))
