from research import *
from fractions import Fraction as F
def inside(x,K):return any(l<=x<=r for l,r in K)
def wanted(a,K):
 ends={x for I in K for x in I};cuts=sorted(ends|{x-a for x in ends}|{x+a for x in ends})
 tests=cuts+[(x+y)/2 for x,y in zip(cuts,cuts[1:])]
 return all(not inside(x,K) or inside(x-a,K) or inside(x+a,K) for x in tests)
M=F(3,2);a=F(1);b=M;z=103*M
K=[(F(0),2*M),(100*M,z-b),(z-a,z+a),(z+b,106*M),(300*M,302*M)]
ends={x for I in K for x in I};D=max(ends)-min(ends)
events=sorted({F(0),D}|{abs(x-y)/k for x in ends for y in ends for k in [1,2]})
points=[x for x in events if wanted(x,K)];spans=[(x,y) for x,y in zip(events,events[1:]) if wanted((x+y)/2,K)]
assert all(x<=1 or x==M for x in points)
assert all(y<=1 for x,y in spans)
assert wanted(M,K) and wanted(F(1),K) and not wanted(F(5,4),K)
save('interval-check.json',{'K':[[str(x),str(y)] for x,y in K],'event_count':len(events),'accepted_event_points':[str(x) for x in points],'accepted_open_spans':[[str(x),str(y)] for x,y in spans],'exact_center':'[0,1] union {3/2}','method':'All endpoint-difference and half-difference events; exact rational tests of K subset (K-a) union (K+a). Between events arrangement order is fixed.'})
print('PASS exact continuous interval arrangement: C(K)=[0,1] union {3/2}')
