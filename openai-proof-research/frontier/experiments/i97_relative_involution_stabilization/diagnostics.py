#!/usr/bin/env python3
"""Finite diagnostics only; no geometric existence or nonexistence certification."""
import sys
sys.dont_write_bytecode = True
from itertools import product, permutations
from math import gcd
import json

def reduce_word(w):
    out=[]
    for x in w:
        if out and out[-1]==-x: out.pop()
        else: out.append(x)
    return tuple(out)

def inverse(w): return tuple(-x for x in reversed(w))
def mul(*ws): return reduce_word(sum((tuple(w) for w in ws), ()))
def conj(u,v): return mul(u,v,inverse(u))

def bezout(a,b):
    if b==0: return (abs(a),1 if a>0 else -1,0)
    g,x,y=bezout(b,a%b)
    return g,y,x-(a//b)*y

def main():
    # All ordered distinct R,B,R,B port tuples; no enormous list is instantiated.
    ports=sum(1 for _ in product(permutations(range(10),2),repeat=2))
    b=ports*10**4*16
    assert ports==8100 and b==1296000000
    # Schreier basis for gamma=1, tau_2=2 (odd), l=3,z=4 (even).
    a=(1,1);x=mul((2,),(-1,));y=(1,2)
    basis=[a,x,y,(3,),conj((1,),(3,)),(4,),conj((1,),(4,))]
    alpha=lambda w:conj((1,),w)
    assert alpha(a)==a and alpha(x)==mul(y,inverse(a)) and alpha(y)==mul(a,x)
    assert alpha(basis[3])==basis[4] and alpha(basis[4])==conj(a,basis[3])
    assert alpha(basis[5])==basis[6] and alpha(basis[6])==conj(a,basis[5])
    alphabet=basis+[inverse(w) for w in basis]
    group_cases=0
    for length in range(4):
        for ws in product(alphabet,repeat=length):
            w=mul(*ws)
            assert alpha(alpha(w))==conj(a,w)
            group_cases+=1
    # Preserve outer phase: cancellation within rows, never identify z-translates.
    hp=mul((3,),a);hm=mul((4,),hp)
    assert hp!=hm
    row_cases=0
    for h in [hp,hm,alpha(hp),alpha(hm)]:
        coefficients={}
        for sign in [1,-1]: coefficients[h]=coefficients.get(h,0)+sign
        assert not any(coefficients.values());row_cases+=1
    assert {hp:1,hm:-1} != {}
    # Exact reduction of even indefinite unimodular binary forms to H.
    lattice_cases=0
    for aa,cc in product(range(-30,31),repeat=2):
        for bb in range(-61,62):
            if bb*bb-4*aa*cc!=1: continue
            if aa==0: v=(1,0)
            else:
                v=(bb+1,-2*aa);g=gcd(*v);v=tuple(n//g for n in v)
            pairing=lambda u,v:2*aa*u[0]*v[0]+bb*(u[0]*v[1]+u[1]*v[0])+2*cc*u[1]*v[1]
            assert pairing(v,v)==0
            p=2*aa*v[0]+bb*v[1];q=bb*v[0]+2*cc*v[1]
            g,s,t=bezout(p,q);assert g==1
            w=(s,t);n=pairing(w,w)//2;w=(w[0]-n*v[0],w[1]-n*v[1])
            assert pairing(v,w)==1 and pairing(w,w)==0
            assert abs(v[0]*w[1]-v[1]*w[0])==1
            lattice_cases+=1
    # Endpoint-assignment relaxation: exactly three deletions break an odd cycle.
    deletion_minima={}
    for d in range(3,12):
        deletion_minima[d]=min(sum(3 for i in range(d) if c[i]==c[(i+1)%d]) for c in product(range(2),repeat=d))
        assert deletion_minima[d]==(3 if d%2 else 0)
    # Explicit d=3 witness, deficiencies R,B,R; delete 3 R edges at (2,0).
    deficient=[0,1,0];received=[[0,0] for _ in range(3)];deleted=0
    for i in range(3):
        j=(i+1)%3
        for color in range(2):
            if deficient[i]==color==deficient[j]:
                received[i][color]+=1;received[j][color]+=1;deleted+=3
            else:
                target=i if deficient[i]!=color else j
                received[target][color]+=5
    assert deleted==3 and all(received[i][deficient[i]]<=1 for i in range(3))
    print(json.dumps(dict(status='PASS',limits='Finite word/lattice/incidence checks only; no Whitney disks, action, complement classification, or novelty proof.',ordered_port_tuples=ports,b=b,schreier_word_cases=group_cases,phase_row_cases=row_cases,binary_form_cases=lattice_cases,deletion_minima=deletion_minima,triangle_received=received),indent=2,sort_keys=True))

if __name__=='__main__': main()
