from itertools import combinations
from fractions import Fraction as Q
import json

def expectation(n, edges):
    # Inclusion-exclusion followed by an exact geometric-series sum.
    m=len(edges)
    return sum((Q(m,sum(bool(e&s) for e in edges)) if s.bit_count()%2 else
                -Q(m,sum(bool(e&s) for e in edges))) for s in range(1,1<<n))

def scan(n):
    pairs=list(combinations(range(n),2)); es=[(1<<a)|(1<<b) for a,b in pairs]
    regular={}; count=0
    for mask in range(1,1<<len(es)):
        deg=[0]*n; edges=[]
        for j,(a,b) in enumerate(pairs):
            if mask>>j&1: deg[a]+=1;deg[b]+=1;edges.append(es[j])
        if len(set(deg))!=1:continue
        regular[mask]=expectation(n,edges);count+=1
    violations=[]
    for a,x in regular.items():
        for b,y in regular.items():
            if a!=b and a&b==a and x>y:
                violations.append(dict(n=n,small=[list(pairs[j]) for j in range(len(es)) if a>>j&1],large=[list(pairs[j]) for j in range(len(es)) if b>>j&1],Esmall=str(x),Elarge=str(y),gap=str(x-y)))
                return count,violations
    return count,violations

def dp(n,edges):
    full=(1<<n)-1; values={full:Q(0)};m=len(edges)
    for s in sorted(range(full),key=int.bit_count,reverse=True):
        loops=sum((s|e)==s for e in edges)
        values[s]=(m+sum(values[s|e] for e in edges if (s|e)!=s))/(m-loops)
    return values[0]

if __name__=='__main__':
    out=[]
    for n in range(3,7):
        count,v=scan(n);out.append(dict(n=n,regular_graphs=count,violations=v))
        if v:break
    fano=[sum(1<<(x-1) for x in [a,b,a^b]) for a in range(1,8) for b in range(a+1,8) if b<(a^b)]
    full=[sum(1<<x for x in c) for c in combinations(range(7),3)]
    assert len(fano)==7 and all(sum(bool(e&(1<<v)) for e in fano)==3 for v in range(7))
    ef=expectation(7,fano);eb=expectation(7,full)
    assert ef==dp(7,fano)==Q(163,30)
    assert eb==dp(7,full)==Q(85691,15810)<ef
    # Rational Fourier coefficients for a genuine smooth strictly convex support
    # h(theta)=1-epsilon*cos(2theta)/3, rho=1+epsilon*cos(2theta)>0.
    modes=[]
    for eps in [Q(1,10),Q(1,2),Q(9,10)]:
        C=eps**2/8;area_radius_squared=1-eps**2/6
        assert 0<C<1-area_radius_squared
        modes.append(dict(epsilon=str(eps),C=str(C),R_squared=str(area_radius_squared)))
    # Verify the source's polynomial comparison without floating arithmetic.
    for p in range(1,6):
        for R in range(1,p+1):
            for t in range(11):
                assert 2*(p+t)**2-(p+R)*(R+t)==(p-R)*(2*p+R)+(3*p-R)*t+2*t*t>=0
    print(json.dumps(dict(graph_scan=out,public_fano=dict(E=str(ef),Efull=str(eb),gap=str(ef-eb),independent_DP='PASS'),robin_fourier_controls=modes,limits='Fano is public reconnaissance exclusion. Robin identities are diagnostics, not a universal source resolution.'),indent=2))
