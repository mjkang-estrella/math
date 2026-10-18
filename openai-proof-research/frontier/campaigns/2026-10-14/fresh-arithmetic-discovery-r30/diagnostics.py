#!/usr/bin/env python3
"""Exact finite word/direction checks for T259S. MIT; not a mathematical proof."""
import json
from fractions import Fraction

def red(w):
    out=[]
    for x in w:
        if out and out[-1]==-x:out.pop()
        else:out.append(x)
    return tuple(out)
def mul(*words):return red(x for w in words for x in w)
def inv(w):return tuple(-x for x in reversed(w))
def image(w,m):return mul(*(m[x] if x>0 else inv(m[-x]) for x in w))
def main():
    # a=1, b_i=i+1 in A; c=1,d=2 in F2.
    a=(1,);u=[()]
    for i in range(1,100):u.append(mul(u[-1],a,(i+1,)))
    w=mul(u[-1],a)
    q={1:(2,),2:(-2,1),3:(-2,-1),**{i:(-2,) for i in range(4,101)}}
    assert [image(v,q) for v in u]==[(),(1,)]+[()]*98
    assert image(w,q)==(2,)
    # w=u1 a suffix; recovery path from v=yu1 is u1^-1,w,suffix^-1.
    suffix=tuple(x for i in range(2,100) for x in (i+1,1))
    assert mul(u[1],a,suffix)==w
    recovery=mul(inv(u[1]),w,inv(suffix))
    assert recovery==a
    assert mul(inv(u[1]),w,suffix)!=a # incorrect inverse convention
    # Changing u2 as well to c gives a second missing row source.
    q_bad=dict(q);q_bad[3]=(-2,);q_bad[4]=(-2,-1)
    assert sum(image(v,q_bad)==(1,) for v in u)==2
    # q(w),q(b1) form a basis: d maps back to w; c maps back to wb1.
    psi={1:mul(w,(2,)),2:w}
    assert image(image(w,q),psi)==w
    assert image(image((2,),q),psi)==(2,)
    # Finite analog only of positive c-translate propagation, not infinite a.s. coverage.
    for n in range(2,53):
        known={0}
        for k in range(n-1):known|={(x+1)%n for x in known}
        assert known==set(range(n))
    # Exact epsilon cost budget and positivity of the advertised gap.
    for e in [Fraction(1,10**6),Fraction(1,2),Fraction(2),Fraction(3),Fraction(199),Fraction(200),Fraction(1000)]:
        p=min(Fraction(1,2),e/400);rho=min(Fraction(1,2),e/4)
        assert 100*p+rho<=e/2<e
    assert 3<4 # sqrt3<2, hence 4-2sqrt3>0
    print(json.dumps({'status':'PASS','row_sources':100,'ordinary_sources':99,'exceptional_index':1,'exact_recovery_word':[1],'cyclic_direction_cases':51,'cost_budget_cases':7,'negative_controls':['unreversed_suffix','second_exceptional_source'],'limits':'finite identities and convention checks only; no cost, measure, spectral or novelty proof'},sort_keys=True,indent=2))
if __name__=='__main__':main()
