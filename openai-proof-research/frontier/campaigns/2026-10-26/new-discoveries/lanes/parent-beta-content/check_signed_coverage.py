"""Exact exploratory test of the ray-monotone signed-hull lemma in dimension2.

All arithmetic is integer/Fraction. This finite test is NOT a general proof.
"""
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json
import random


def cross(o,a,b):
    return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])


def hull(points):
    points=sorted(set(points))
    lo=[]
    for p in points:
        while len(lo)>1 and cross(lo[-2],lo[-1],p)<=0:
            lo.pop()
        lo.append(p)
    hi=[]
    for p in reversed(points):
        while len(hi)>1 and cross(hi[-2],hi[-1],p)<=0:
            hi.pop()
        hi.append(p)
    return lo[:-1]+hi[:-1]


def general(vs):
    if any(y==0 for x,y in vs):
        return False
    if any(a[0]*b[1]-a[1]*b[0]==0 for a,b in combinations(vs,2)):
        return False
    for triple in combinations(vs,3):
        for signs in product([-1,1],repeat=3):
            pts=[(s*x,s*y) for s,(x,y) in zip(signs,triple)]
            if cross(*pts)==0:
                return False
    return True


def check(vs):
    events={}
    initial=0
    for signs in product([-1,1],repeat=len(vs)):
        hs=hull([(s*x,s*y) for s,(x,y) in zip(signs,vs)])
        xs=[]
        for p,q in zip(hs,hs[1:]+hs[:1]):
            if p[1]*q[1]<0:
                xs.append(Fraction(p[0]*q[1]-q[0]*p[1],q[1]-p[1]))
        if not xs:
            continue
        assert len(xs)==2
        lo,hi=sorted(xs)
        if hi<=0:
            continue
        if lo<0:
            initial+=1
        else:
            assert lo>0
            events[lo]=events.get(lo,0)+1
        events[hi]=events.get(hi,0)-1
    count=initial
    for position,jump in sorted(events.items()):
        assert jump<=0, (vs,str(position),jump)
        count+=jump
        assert count>=0
    assert count==0
    return initial,len(events)


def main():
    rng=random.Random(367740)
    results=[]
    for n in range(3,9):
        for sample in range(25):
            while True:
                vs=[(rng.randrange(-40,41),rng.randrange(-40,41)) for _ in range(n)]
                if general(vs):
                    break
            initial,events=check(vs)
            results.append({'n':n,'sample':sample,'vectors':vs,
                            'covered_at_origin':initial,'positive_jump_locations':events})
    result={'status':'PASS_FINITE_EXPLORATORY_CHECK_ONLY','clouds':len(results),
            'signed_hulls':sum(2**r['n'] for r in results),
            'arithmetic':'integer orientation; exact Fraction crossings',
            'claim':'No positive jumps off boundary levels for tested clouds; no universal proof or credit.',
            'results':results}
    Path(__file__).with_name('signed-coverage-check.json').write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k!='results'})


if __name__=='__main__':
    main()
