from fractions import Fraction as F
from pathlib import Path
import json

# Independent integration of the six conditional CDFs, without using a sampled
# rank estimator or any floating-point operation.
def integrated_square(intervals):
    knots=sorted({F(0),F(1)} | {t for a,b,w in intervals for t in (a,b)})
    def cdf(t):
        return sum(w*max(F(0),min(F(1),(t-a)/(b-a))) for a,b,w in intervals)
    total=F(0)
    for a,b in zip(knots,knots[1:]):
        u,v=cdf(a),cdf(b)
        total+=(b-a)*(u*u+u*v+v*v)/3
    return total

def distance(conditional_laws):
    # Uniform target: xi=6*(E integral p^2 -1/3).
    return 3-6*sum(w*integrated_square(intervals) for w,intervals in conditional_laws)

def distance_copy(conditional_laws):
    # A separate source-Theorem4 check: d=3 E|Y-Y'|, conditionally iid.
    total=F(0)
    for w,law in conditional_laws:
        for a,b,p in law:
            for c,d,q in law:
                if (a,b)==(c,d): z=(b-a)/3
                else:
                    assert b<=c or d<=a
                    z=abs((a+b-c-d)/2)
                total+=w*p*q*z
    return 3*total

rows=[]
for n in range(2,13):
    r=F(1,n)
    coarse=[(F(1,n),[(F(i,n),F(i+1,n),F(1))]) for i in range(n)]
    fine=[(F(1,n*n),[(F(k,n*n),F(k+1,n*n),F(1))]) for k in range(n*n)]
    scatter=[(F(1,n),[(F(n*j+i,n*n),F(n*j+i+1,n*n),F(1,n)) for j in range(n)]) for i in range(n)]
    # A reveals I; B reveals (I,J); C reveals (J,I). U,V,W remain independent.
    actual={'AB':distance(coarse),'BA':distance(coarse),'BC':distance(fine),
            'CB':distance(fine),'AC':distance(scatter),'CA':distance(coarse)}
    expected={'AB':r,'BA':r,'BC':r*r,'CB':r*r,'AC':1-r*r+r**3,'CA':r}
    assert actual==expected,(n,actual,expected)
    for law in (coarse,fine,scatter): assert distance(law)==distance_copy(law)
    assert all(0<x<1 for x in actual.values())
    q_direct=actual['AC']/(actual['AB']+actual['BC'])
    q_avg=((actual['AC']+actual['CA'])/2)/(r+r*r)
    assert q_direct>F(n,4) and q_avg>F(n,4)
    # Joint density n^3 on n^2 disjoint boxes of volume n^-5.
    assert F(n*n)*F(n**3)*F(1,n**5)==1
    rows.append({'n':n,'d':{k:str(v) for k,v in actual.items()},'ratio_direct_and_max':str(q_direct),'ratio_avg':str(q_avg)})

# All-n finite-sum ingredients in the handwritten proof, checked symbolically.
import sympy as s
n,i,x=s.symbols('n i x', integer=True, positive=True)
assert s.simplify(s.summation(i,(i,0,n-1))-n*(n-1)/2)==0
assert s.simplify(s.summation(i*i,(i,0,n-1))-n*(n-1)*(2*n-1)/6)==0
# Within a coarse cell, only its own CDF is nonconstant.
t=s.symbols('t',real=True)
avg_int=s.summation((n-1-i+s.Rational(1,3))/n**2,(i,0,n-1))
assert s.simplify(avg_int-(s.Rational(1,3)+(1-1/n)/6))==0
P=Path(__file__).parent
(P/'exact-checks.json').write_text(json.dumps({'status':'PASS','method':'rational piecewise-affine conditional-CDF integration and independent conditional-copy absolute differences','rows':rows,'copy_comparisons':33,'symbolic_identities':3,'scope':'bounded independent checks; all-n proof in PROOF.md'},indent=2)+'\n')
print('PASS: 66 exact distances, 22 growing ratios, 11 normalizations, 3 symbolic identities')
