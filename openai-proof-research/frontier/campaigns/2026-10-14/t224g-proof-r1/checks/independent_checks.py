#!/usr/bin/env python3
"""Reviewer-written exact finite checks for T224G interfaces. Support only; no theorem is checked."""
from fractions import Fraction as Fr
from itertools import product, combinations
import json, random

def table():
    # f(x,y)=A+Bx+Cy+Dxy with x=before-cap, y=after-cap; arbitrary rational coefficients.
    rng=random.Random(224); n=0; ctrl={'drift_without_D_half':False,'sandwich_dropped':False,'refresh_doubled':False}
    coeffs=[tuple(Fr(rng.randint(-9,9),rng.randint(1,5)) for _ in range(4)) for _ in range(200)]
    for A,B,C,D in coeffs:
        f=lambda x,y:A+B*x+C*y+D*x*y
        for w,u,b in product((0,1),repeat=3):
            p=b-w; Ev_u=Fr(w+b,2)-u
            birth=(f(u,w)+f(u,b))/2-f(u,u)
            death=(f(w,u)+f(b,u))/2-f(u,u)
            refresh=sum(f(x,y) for x in (w,b) for y in (w,b))/4-(f(w,w)+f(b,b))/2
            const=(f(w,w)+f(b,b))/2-f(u,u)
            sandwich=(w<=u<=b)
            ok=(birth==(C+D/2)*Ev_u-D*p/4 and death==(B+D/2)*Ev_u-D*p/4
                and refresh==-D*p/4 and const==(B+C+D)*Ev_u)
            if sandwich:
                assert ok,(A,B,C,D,w,u,b); n+=1
                ctrl['drift_without_D_half']|=birth!=C*Ev_u-D*p/4
                ctrl['refresh_doubled']|=birth!=(C+D/2)*Ev_u-D*p/2
            else:
                ctrl['sandwich_dropped']|=not ok
    assert all(ctrl.values()),ctrl
    return n,ctrl

def kron(a,b): return [x*y for x in a for y in b]
def tensor(vs):
    out=[Fr(1)]
    for v in vs: out=kron(out,v)
    return out

def telescoping():
    rng=random.Random(7); trials=0
    for k in range(1,5):
        for _ in range(30):
            D=[[Fr(rng.randint(-5,5)) for _ in range(3)] for _ in range(k)]
            C=[[Fr(rng.randint(-5,5)) for _ in range(3)] for _ in range(k)]
            lhs=[x-y for x,y in zip(tensor(D),tensor(C))]
            rhs=[Fr(0)]*len(lhs)
            for i in range(k):
                term=tensor(C[:i]+[[x-y for x,y in zip(D[i],C[i])]]+D[i+1:])
                rhs=[x+y for x,y in zip(rhs,term)]
            assert lhs==rhs; trials+=1
    # control: dropping the C-prefix (using D everywhere before i) must fail generically
    D=[[Fr(1),Fr(2)],[Fr(3),Fr(-1)]];C=[[Fr(0),Fr(1)],[Fr(2),Fr(5)]]
    lhs=[x-y for x,y in zip(tensor(D),tensor(C))]
    wrong=[a+b for a,b in zip(tensor([[x-y for x,y in zip(D[0],C[0])],D[1]]),tensor([D[0],[x-y for x,y in zip(D[1],C[1])]]))]
    assert wrong!=lhs
    return trials

def shared_label():
    for h1,h2 in product([Fr(x,3) for x in range(-6,7)],repeat=2):
        assert h1*h2-1==(h1-1)+(h2-1)+(h1-1)*(h2-1)
        if (h1-1)*(h2-1)!=0: assert h1*h2-1!=(h1-1)+(h2-1)
    return True

def path_inclusion_exclusion():
    # toy: k sites, each subset S gives a path (tuple); M_k has TV<=2^k and vanishes if a site has no influence
    rng=random.Random(3); checked=0
    for k in range(1,6):
        for _ in range(40):
            dead=rng.randrange(k)
            table={}
            for S in range(2**k):
                key=S & ~(1<<dead)
                table.setdefault(key,tuple(rng.randint(0,2) for _ in range(4)))
            M={}
            for S in range(2**k):
                sgn=(-1)**(k-bin(S).count('1'))
                path=table[S & ~(1<<dead)]
                M[path]=M.get(path,0)+sgn
            assert all(v==0 for v in M.values())
            # generic case: TV bound
            M2={}
            for S in range(2**k):
                path=tuple(rng.randint(0,2) for _ in range(4)); M2[path]=M2.get(path,0)+(-1)**(k-bin(S).count('1'))
            assert sum(abs(v) for v in M2.values())<=2**k
            checked+=1
    return checked

def catalan_pairings(m):
    # noncrossing perfect matchings of m points on a circle
    if m==0: return 1
    return sum(catalan_pairings(j)*catalan_pairings(m-2-j) for j in range(0,m-1,2))

def hidden_rate():
    import math
    c0,c1=1.0,3.0; cb=(c0+c1)/2
    for t in (0.1,0.5,1.0,2.0):
        a=math.exp(-2*cb*t); b=(math.exp(-2*c0*t)+math.exp(-2*c1*t))/2
        assert b>a  # strict convexity
    # Dirichlet forms on functions of V: rate * (phi(1)-phi(-1))(psi(1)-psi(-1))/2, averaged rate equal
    return True

def counterexample():
    E,W,N,S=(1,0),(-1,0),(0,3),(0,Fr(-1,2)); col={E:'b',W:'b',N:'w',S:'w'}
    def nearest(p,sites):
        d=lambda s:(p[0]-s[0])**2+(p[1]-s[1])**2
        m=min(d(s) for s in sites); return [s for s in sites if d(s)==m],m
    grid=[Fr(i,50) for i in range(-100,101)]
    base=[E,W,N,S]
    # F0: segment y=1 black (strict for x!=0; E/W tie at x=0 both black)
    for x in grid:
        ns,_=nearest((x,1),base); assert all(col[s]=='b' for s in ns)
    # G0: x=0, -2<=y<=0 white (S strictly nearest)
    for y in grid:
        if y<=0:
            ns,_=nearest((0,y),base); assert ns==[S]
    z=(0,0)
    for x in grid:  # black z: y=0 black throughout
        ns,_=nearest((x,0),base+[z]); assert all(s in (E,W,z) for s in ns) and S not in ns
    for y in grid:  # white z: x=0 white throughout
        ns,_=nearest((0,y),base+[z]); assert all(s in (z,N,S) for s in ns)
    return True

def exponents():
    # r_e ~ e^{3/4} (source A), lambda=e^{-2}, lambda r_e a_e ~ 1  => a_e ~ e^{5/4}
    a=Fr(2)-Fr(3,4); assert a==Fr(5,4)
    # normalized message error: (lambda r_e)^k a_e^{k-1} e^{2+nu} ~ e^{-5/4+2+nu} -> 0 for nu>=0
    assert Fr(-5,4)+2>0
    # double-active / restored-geometry corrections: (lambda r_e)^k a_e^{k+1} ~ a_e -> 0
    return {'a_exponent':str(a),'message_margin':str(Fr(-5,4)+2)}

if __name__=='__main__':
    n,ctrl=table()
    out={'status':'PASS_REVIEWER_FINITE_SUPPORT_ONLY','local_table_cases':n,'local_table_negative_controls':ctrl,
         'telescoping_trials':telescoping(),'shared_label_identity':shared_label(),
         'path_inclusion_exclusion_trials':path_inclusion_exclusion(),
         'noncrossing_pairings':{str(m):catalan_pairings(m) for m in (2,4,6)},
         'hidden_rate_obstruction':hidden_rate(),'four_nucleus_counterexample':counterexample(),
         'exponents':exponents(),'full_theorem_checked':False}
    assert out['noncrossing_pairings']=={'2':1,'4':2,'6':5}
    print(json.dumps(out,indent=2,sort_keys=True))
