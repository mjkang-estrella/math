"""Exact finite controls for the PUBLIC eight-direction calculus, not the target nine-direction one."""
from fractions import Fraction as F
from itertools import permutations
from math import comb
import json

def relations(q):
    nu=1/q-q
    r=[]
    def add(*terms):
        d={}
        for a,b,c in terms:d[8*a+b]=d.get(8*a+b,0)+c
        r.append({i:c for i,c in d.items() if c})
    for a in range(8):add((a,a,1+q**-2))
    for i,j,k in permutations([1,2,4]):
        for a,b,c in [(0,i,q**-1),(0,i|j,1),(0,7,q),(i,i|j,q**-1),(i,7,1),(i|j,7,q**-1)]:
            add((a,b,1),(b,a,c))
        add((j,i,1),(i,j,1),(i|j,0,nu))
        add((i|j,k,1),(k,i|j,q**-1),(7,0,nu))
        add((i|j,i|k,1),(i|k,i|j,1),(7,i,nu))
        add((i|j,k,1),(k,i|j,q),(i|k,j,q*nu),(j|k,i,q*nu),(7,0,nu))
        add((0,7,1),(7,0,q**-1+nu**3),(i,j|k,nu),(j,i|k,nu),(k,i|j,nu),
            (j|k,i,nu**2),(i|k,j,nu**2),(i|j,k,nu**2))
        add((0,i|j,1),(i|j,0,q**-2),(i,j,-q**-1),(j,i,-q**-1))
        add((i,7,1),(7,i,q**-2),(i|j,i|k,-q**-1),(i|k,i|j,-q**-1))
        add((0,7,1),(i|j,k,q**-2),(i,j|k,-q**-1),(j,i|k,-q**-1))
        add((k,i|j,1),(7,0,q**-2),(i|k,j,-q**-1),(j|k,i,-q**-3))
    return r

def rank(rows):
    basis={}
    for row in rows:
        d=dict(row)
        while d:
            i=min(d);c=d[i]
            if i not in basis:
                basis[i]={j:v/c for j,v in d.items()};break
            for j,v in basis[i].items():
                d[j]=d.get(j,0)-c*v
                if not d[j]:d.pop(j,None)
    return len(basis)

def run():
    out=[]
    for q in [F(1,2),F(2),F(3),F(-2)]:
        r=relations(q);r2=rank(r)
        cubic=[]
        for d in r:
            for a in range(8):
                cubic.append({a*64+i:v for i,v in d.items()})
                cubic.append({i*8+a:v for i,v in d.items()})
        out.append(dict(q=str(q),quadratic_rank=r2,degree2=64-r2,degree3=512-rank(cubic)))
    assert all(x['degree2']==18 for x in out),out
    return dict(status='finite exact controls only; public eight-dimensional contact calculus',samples=out,
                target_binomial_dimensions=[comb(9,k) for k in range(10)],
                missing='Actual nine-dimensional Reeb relation module and every-parameter flatness/PBW bridge')
def symbolic():
    from sympy import QQ, factor, sympify, Symbol, Poly
    K=QQ.frac_field('q');q=K.gens[0];basis={};pivots=[]
    for row in relations(q):
        d=dict(row)
        while d:
            i=min(d);c=d[i]
            if i not in basis:
                pivots.append(c);basis[i]={j:v/c for j,v in d.items()};break
            for j,v in basis[i].items():
                d[j]=d.get(j,0)-c*v
                if not d[j]:d.pop(j,None)
    # Every elimination division is listed. All zeros must be excluded for specialization.
    factors=set()
    for c in pivots:
        c=K(c)
        for expr in [c.numer.as_expr(),c.denom.as_expr()]:
            for f,e in Poly(expr,Symbol('q')).factor_list()[1]:factors.add(str(f.as_expr()))
    return dict(generic_rank=len(basis),pivot_factors=sorted(factors),
                qualification='public eight-generator relation transcription only; no Reeb relations supplied')
if __name__=='__main__':
    import sys
    print(json.dumps(symbolic() if '--symbolic' in sys.argv else run(),indent=2))
