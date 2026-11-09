from fractions import Fraction as F
from itertools import permutations
import json

def test(k,s):
    A=set(range(s)); B=set(range(s,k)); t=len(B)
    ps=list(permutations(sorted(B)))
    law=[(p,F(t,k*len(ps))) for p in ps]
    law += [(tuple([c]*t),F(1,k)) for c in sorted(A)]
    assert sum(q for _,q in law)==1
    for j in range(t):
        for c in range(k):
            assert sum(q for p,q in law if p[j]==c)==F(1,k)
    avail=[(set(range(k))-set(p),q) for p,q in law]
    assert min(len(a) for a,_ in avail)>=s
    forced=sum(q for a,q in avail if a<=A)
    assert forced==F(t,k)>F(s,k)
    # A different, coordinated boundary law does extend to a fully balanced star.
    good=[((tuple([c]*t),z),F(1,k*(k-1))) for c in range(k) for z in range(k) if z!=c]
    for j in range(t+1):
        for c in range(k):
            assert sum(q for (p,z),q in good if (p+(z,))[j]==c)==F(1,k)
    return dict(k=k,s=s,leaves=t,boundary_states=len(law),forced=str(forced),capacity=str(F(s,k)),balanced_alternative_states=len(good))
if __name__=='__main__':
    print(json.dumps([test(3,1),test(5,2),test(7,3)],indent=2))
