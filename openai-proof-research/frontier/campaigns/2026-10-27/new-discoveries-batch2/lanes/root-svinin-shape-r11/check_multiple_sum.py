"""Independent literal finite checks for the proposed Conjecture 3.1 proof."""
from collections import Counter
from itertools import combinations_with_replacement
from math import comb
from pathlib import Path
import json
import sympy as sp

HERE=Path(__file__).resolve().parent
z=sp.symbols('z')
rows=[]
for n in range(1,5):
    for j in range(1,6):
        M=j*(n+1)
        left=Counter()
        tuples=0
        for lam in combinations_with_replacement(range(1,j*n+1),j):
            tuples+=1
            left.update(lam[i]-i*n for i in range(j))
        assert tuples==comb(j*n+j-1,j)
        # A separate order-statistic count formula after a_i=lambda_i+i.
        counts=Counter()
        for a in range(1,M):
            for h in range(j):
                if h<=a-1 and j-1-h<=M-1-a:
                    counts[a-h*(n+1)]+=comb(a-1,h)*comb(M-1-a,j-1-h)
        assert counts==left
        right=Counter()
        dist=Counter({0:1})
        for r in range(1,j+1):
            nxt=Counter()
            for a,c in dist.items():
                for v in range(1,n+1):nxt[a+v]+=c
            dist=nxt
            for q,c in dist.items():right[q]+=comb(M,j-r)*c
        for q in range(1,j*n+1):
            assert left[q]-left[-q]==right[q]>0,(n,j,q)
        moments=[]
        for k in range(9):
            l=sum(c*q**(2*k+1) for q,c in left.items())
            r=sum(c*q**(2*k+1) for q,c in right.items())
            assert l==r
            moments.append(str(l))
        Ap=sum(z**q for q in range(1,n+1))
        Am=sum(z**(-q) for q in range(1,n+1))
        T=lambda A:sum(comb(M-1,j-1-r)*A**r for r in range(j))
        C=sum(c*z**q for q,c in left.items())
        H=lambda A:sum(comb(M,j-r)*A**r for r in range(1,j+1))
        assert sp.cancel((1-z)*C-z*(T(Am)-z**n*T(Ap)))==0
        assert sp.cancel((1+Ap)*T(Ap)-comb(M-1,j-1)-H(Ap))==0
        assert sp.cancel(C-C.subs(z,1/z)-H(Ap)+H(Am))==0
        rows.append({'n':n,'j':j,'weak_tuples':tuples,'positive_coefficients':j*n,
                     'odd_moments_0_to_8':moments})
(HERE/'multiple-sum-checks.json').write_text(json.dumps({
    'status':'PASS finite independent diagnostics; full proof is written separately',
    'grids':len(rows),'rows':rows,'credit':0},indent=2)+'\n')
print('PASS:20 literal weak-tuple counts, all antisymmetric coefficients,180 odd moments,60 symbolic identities')
