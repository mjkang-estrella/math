# Original code, MIT. Bounded finite diagnostics, stdout only, no file I/O.
from itertools import product,combinations
from collections import Counter
from fractions import Fraction
import json

def norm(v,q):
    pivot=next(x for x in v if x)
    inv=pow(pivot,-1,q)
    return tuple((x*inv)%q for x in v)

def geometry(q):
    zero=(0,)*4
    points=sorted({norm(v,q) for v in product(range(q),repeat=4) if v!=zero})
    lines=set()
    for u,v in combinations(points,2):
        lines.add(frozenset(norm(tuple((a*x+b*y)%q for x,y in zip(u,v)),q)
                           for a,b in product(range(q),repeat=2) if a or b))
    assert len(points)==q**3+q*q+q+1
    assert len(lines)==(q*q+1)*(q*q+q+1)
    # F_(q^2)=F_q[t]/(t^2+t+1) for q=2; t^2-d for odd q.
    d=next((x for x in range(2,q) if pow(x,(q-1)//2,q)==q-1),1)
    def mul(x,y):
        a,b=x;c,e=y
        if q==2:return ((a*c+b*e)%q,(a*e+b*c+b*e)%q)
        return ((a*c+d*b*e)%q,(a*e+b*c)%q)
    ext=list(product(range(q),repeat=2)); nonzero=[x for x in ext if x!=(0,0)]
    spread=[frozenset(norm((*x,*mul(s,x)),q) for x in nonzero) for s in ext]
    spread.append(frozenset(norm((0,0,*x),q) for x in nonzero))
    assert len(spread)==q*q+1 and all(L in lines for L in spread)
    assert Counter(x for L in spread for x in L)==Counter({x:1 for x in points})
    P=points[0];groups=[L-{P} for L in lines if P in L];cross=[L for L in lines if P not in L]
    X=set(points)-{P};v=q*q+q+1
    assert len(groups)==v and all(len(g)==q for g in groups)
    rows=[]
    for mode in ['whole','pairs']:
        internal=(groups if mode=='whole' else [frozenset(c) for g in groups for c in combinations(sorted(g),2)])
        b=1 if mode=='whole' else q-1
        R=q*(q+1)+b; blocks=cross+internal
        paircounts=Counter(pair for B in blocks for pair in combinations(sorted(B),2))
        assert len(paircounts)==len(X)*(len(X)-1)//2 and set(paircounts.values())=={1}
        degrees=Counter(x for B in blocks for x in B)
        assert set(degrees)==X and set(degrees.values())=={R}
        hole=next(L-{P} for L in spread if P in L)
        spread_cross=[L for L in spread if P not in L]
        x=min(hole)
        fill=[B for B in internal if x in B and B<=hole]
        assert len(fill)==b and set().union(*spread_cross,*fill)==X
        assert len(spread_cross)+len(fill)==q*q+b<=R-1
        # Cross-star at any point plus its internal-star covers the whole design.
        star=[B for B in cross if x in B]
        assert len(star)==q*(q+1)
        assert set().union(*star)==X-(hole-{x})
        rows.append({'internal':mode,'points':len(X),'replication':R,'blocks':len(blocks),
                     'pair_checks':len(paircounts),'spread_cover':q*q+b,'cross_star':len(star),
                     'fractional_cross_cover_cost':str(Fraction(len(cross),q*(q+1)))})
    return {'prime':q,'projective_lines':len(lines),'spread_lines':len(spread),'cases':rows}

def sts13():
    blocks=sorted({frozenset((x+t)%13 for x in B) for B in [(0,1,4),(0,2,7)] for t in range(13)},key=lambda B:tuple(sorted(B)))
    counts=Counter(p for B in blocks for p in combinations(sorted(B),2))
    assert len(blocks)==26 and len(counts)==78 and set(counts.values())=={1}
    matching=next(C for C in combinations(blocks,3) if len(set().union(*C))==9)
    rest=sorted(set(range(13))-set().union(*matching))
    fill=[next(B for B in blocks if {rest[i],rest[i+1]}<=B) for i in [0,2]]
    cover=list(matching)+fill;assert set().union(*cover)==set(range(13)) and len(set(cover))<=5
    return {'blocks':26,'pair_checks':78,'three_disjoint':[sorted(B) for B in matching],'five_cover':[sorted(B) for B in cover]}

print(json.dumps({'purpose':'Finite diagnostics only; no theorem gate, full LR witness, or global resolution assertion.',
                  'geometry':[geometry(q) for q in [2,3,5]],'sts13':sts13()},indent=2))
