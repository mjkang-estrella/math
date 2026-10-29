"""Exact diagnostics only; the all-order proof is in FINDINGS.md."""
import resource
resource.setrlimit(resource.RLIMIT_AS, (512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU, (40,)*2)
import itertools, json
from fractions import Fraction as F
from pathlib import Path

def det(a):
    if len(a)==1: return a[0][0]
    return sum((-1)**j*a[0][j]*det([r[:j]+r[j+1:] for r in a[1:]]) for j in range(len(a)))

def good(a):
    n=len(a)
    return all(a[j][k]-F(a[j][i]*a[i][k],a[i][i])<=0
               for i in range(n) for j in range(n) if j!=i
               for k in range(n) if k!=i)

counts={'tested':0,'invertible_schur':0,'positive_diagonal_Z':0,
        'positive_diagonal_positive':0,'negative_diagonal_nonpositive':0}
examples={}
for dg in itertools.product((-1,1),repeat=3):
    for off in itertools.product((-2,-1,0,1,2),repeat=6):
        t=iter(off)
        a=[[dg[i] if i==j else next(t) for j in range(3)] for i in range(3)]
        counts['tested']+=1
        if not good(a) or det(a)==0: continue
        counts['invertible_schur']+=1
        assert len(set(dg))==1
        if dg[0]>0:
            if all(a[i][j]<0 for i in range(3) for j in range(3) if i!=j):
                kind='positive_diagonal_Z'
            else:
                assert all(x>0 for r in a for x in r)
                kind='positive_diagonal_positive'
        else:
            assert all(x<=0 for r in a for x in r)
            kind='negative_diagonal_nonpositive'
        counts[kind]+=1
        examples.setdefault(kind,a)

import sympy as s
obstructions=[]
for p,t,sgn in [(2,s.Rational(2),1),(3,s.Rational(3,5),-1)]:
    n=2*p
    B=s.Matrix(n,n,lambda i,j:sgn*(1 if i==j else t*t if i//p==j//p else t))
    A=B.inv()
    for i in range(n):
        ids=[j for j in range(n) if j!=i]
        C=B.extract(ids,ids)-B.extract(ids,[i])*B.extract([i],ids)/B[i,i]
        assert all(x<=0 for x in C)
        assert A.extract(ids,ids).inv()==C
    assert all(A[i,i]>0 for i in range(n))
    assert A[0,0]+A[0,p]<0
    assert A[p,p]+A[p,0]<0
    obstructions.append({'n':n,'B':[list(map(str,B.row(i))) for i in range(n)],
                         'det_A':str(A.det()),'A_diagonal':str(A[0,0]),
                         'A_within':str(A[0,1]),'A_cross':str(A[0,p]),
                         'two_coordinate_rowsum':str(A[0,0]+A[0,p])})
result={'counts':counts,'examples':examples,'obstructions':obstructions,
        'scope':'Finite diagnostics; no full conjecture claimed.'}
Path(__file__).with_name('check-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
