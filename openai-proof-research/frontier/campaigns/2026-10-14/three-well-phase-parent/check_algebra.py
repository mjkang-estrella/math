#!/usr/bin/env python3
"""Independent finite exact controls for saved P3R; not a spectral proof."""
from fractions import Fraction as F
from itertools import product, permutations
from pathlib import Path
import hashlib
import json

OWN=Path(__file__).resolve().parent
AUTHOR=OWN.parent/'fresh-analytic-discovery-r15'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def det(a):
    ans=0
    for p in permutations(range(3)):
        inv=sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
        v=(-1)**inv
        for i in range(3):v*=a[i][p[i]]
        ans+=v
    return ans
def main():
    before={name:digest(AUTHOR/name) for name in ['original-scope.md','candidate.md','freeze-receipt.json']}
    assert before['original-scope.md']=='0a2aeb8c581e421037ad7c87936c2016495d5babb974ab64be0fa15a16dd66f5'
    gram_cases=0
    for rho in [F(1,100),F(1,8),F(1,3),F(49,100)]:
        for sign in [-1,1]:
            g=[[1,rho,sign*rho],[rho,1,rho],[sign*rho,rho,1]]
            eig=[1+2*sign*rho,1-sign*rho,1-sign*rho]
            assert min(eig)>0 and max(eig)<2
            for t in [F(-2),F(0),F(1),F(3,2),F(5)]:
                a=[[g[i][j]-(t if i==j else 0) for j in range(3)] for i in range(3)]
                expected=1
                for e in eig:expected*=e-t
                assert det(a)==expected;gram_cases+=1
    walks=[]
    for length in range(2,11):
        total=changing=0
        for vertices in product(range(3),repeat=length):
            edges=[tuple(sorted((vertices[i],vertices[(i+1)%length]))) for i in range(length)]
            if any(a==b for a,b in edges):continue
            counts=[edges.count(e) for e in [(0,1),(1,2),(0,2)]]
            assert len({n%2 for n in counts})==1
            flip=counts[2]%2
            assert not flip or length%2==1
            total+=1;changing+=flip
        if length==3:assert total==changing==6
        if length%2==0:assert changing==0
        walks.append(dict(length=length,total=total,sign_changing=changing))
    # Residue of (a+z)e^(-4Rz)(h_-3/z^3+h_-2/z^2+h_-1/z).
    # Highest R coefficient is 8a*h_-3; outer trace factor is 8rho^3.
    residue_cases=0
    for a,R,h3,h2,h1 in product([F(1,2),F(1),F(3)],repeat=5):
        exp=[F(1),-4*R,8*R*R]
        kexp=[a*exp[0],a*exp[1]+exp[0],a*exp[2]+exp[1]]
        coefficient=h3*kexp[2]+h2*kexp[1]+h1*kexp[0]
        assert coefficient==8*a*h3*R*R-4*(h3+a*h2)*R+h2+a*h1
        residue_cases+=1
    assert 8*8*4**3==4096
    assert before=={name:digest(AUTHOR/name) for name in before}
    result=dict(status='PASS_FINITE_EXACT_CONTROLS',observed_inputs=before,gram_characteristic_cases=gram_cases,
                closed_walks=walks,residue_cases=residue_cases,
                limitations='No continuum spectral theorem, operator norm estimate, convergence proof, novelty or independent acceptance certified.',counted=False)
    (OWN/'algebra-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
