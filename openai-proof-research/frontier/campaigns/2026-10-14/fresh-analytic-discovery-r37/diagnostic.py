#!/usr/bin/env python3
"""MIT. Exact finite rank/bin diagnostic; not proof of any infinite theorem."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import json


def factory(points, m):
    n=len(points[0])
    @lru_cache(None)
    def rank(mask):
        if not mask: return -1
        ans=0
        for i in range(n):
            for k in range(m):
                low=tuple(t for t in mask if points[t][i]<=F(k,m))
                high=tuple(t for t in mask if points[t][i]>=F(k+1,m))
                if low and high:
                    ans=max(ans,1+min(rank(low),rank(high)))
        return ans
    def binof(x): return min(m,(x*m).numerator//(x*m).denominator)
    def bins(mask,i):
        return [tuple(t for t in mask if binof(points[t][i])==j) for j in range(m+1)]
    def prediction(mask):
        result=[]
        for i in range(n):
            classes=bins(mask,i)
            result.append(max(range(m+1),key=lambda j:(rank(classes[j]),-j)))
        return result
    return rank,binof,bins,prediction

cases=targets=updates=0
for n,m,grid in [(2,2,[F(0),F(1,2),F(1)]),(1,3,[F(i,6) for i in range(7)])]:
    points=list(product(grid,repeat=n))
    rank,binof,bins,prediction=factory(points,m)
    for bits in range(1,1<<len(points)):
        mask=tuple(t for t in range(len(points)) if bits>>t&1)
        transcripts={}; d=rank(mask)
        for target in mask:
            C=mask; transcript=[]
            while True:
                pred=prediction(C)
                bad=[i for i in range(n) if abs(binof(points[target][i])-pred[i])>=2]
                if not bad: break
                i=bad[0]; j=binof(points[target][i]); nextC=bins(C,i)[j]
                assert rank(nextC)<rank(C)
                transcript.append((i,j)); C=nextC; updates+=1
            assert len(transcript)<=d
            v=tuple(F(j,m) for j in pred)
            assert max(abs(x-y) for x,y in zip(points[target],v))<=F(2,m)
            key=tuple(transcript)
            if key in transcripts: assert transcripts[key]==v
            transcripts[key]=v; targets+=1
        assert len(transcripts)<=sum((n*(m+1))**l for l in range(d+1))
        cases+=1
# Failing negative control: a merely adjacent bin is not a margin split.
pts=[(F(49,100),),(F(51,100),)]
r,bo,bs,pr=factory(pts,2)
assert r((0,1))==0 and abs(bo(pts[0][0])-bo(pts[1][0]))==1
adjacent_implies_drop=(r((1,))<r((0,1)))
assert not adjacent_implies_drop
# Failing negative control: arbitrary low-rank prediction need not lower rank.
pts=[(F(0),F(0)),(F(1),F(0)),(F(1),F(1))]
r,bo,bs,pr=factory(pts,2)
assert r((0,1,2))==r((1,2))==1 and r((0,))==0
arbitrary_predictor_drop=(r((1,2))<r((0,1,2)))
assert not arbitrary_predictor_drop
# Failing negative control: an external center is not an actual representative;
# replacing it by an occupied point may double its radius.
external_radius=F(1,4); actual_points=(F(0),F(1,2)); center=F(1,4)
assert max(abs(x-center) for x in actual_points)==external_radius
assert abs(actual_points[0]-actual_points[1])>external_radius
assert abs(actual_points[0]-actual_points[1])==2*external_radius
# Arithmetic exponent bound on an illustrative exact integer range only.
arithmetic=0
for N in range(1,21):
    for m in range(2,31):
        L=m.bit_length() # ceil(log2(m+1))
        assert N*(m+1)+1 <= (2*N+2)**(L+1)
        arithmetic+=1
print(json.dumps({'status':'PASS_FINITE_DIAGNOSTIC_ONLY','classes':cases,'targets':targets,'rank_decreases':updates,'arithmetic_instances':arithmetic,'negative_controls_rejected':['adjacent_bins_force_drop','arbitrary_predictor_force_drop','actual_representative_without_radius_doubling']},sort_keys=True))
