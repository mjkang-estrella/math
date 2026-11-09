#!/usr/bin/env python3
"""Read-only exact finite author diagnostics. No independent mathematical gate."""
from fractions import Fraction as F
from itertools import combinations, product
import json
EDGES = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
CUTS = [[j for j,(u,v) in enumerate(EDGES) if ((s>>u)^(s>>v))&1]
        for s in range(1,15) if s&1]
SETS = [(s,[j for j,(u,v) in enumerate(EDGES) if (s>>u)&1 and (s>>v)&1])
        for s in range(1,16)]
def union(c,k):
    return sum(c)==3*k and all(sum(c[j] for j in es)<=k*(s.bit_count()-1) for s,es in SETS)
def good(c,h,k): return union(c,k) and union([x-y for x,y in zip(h,c)],k)
def load(d,h): return max(F(sum(d[j] for j in es),sum(h[j] for j in es)) for es in CUTS)
def inverse(m):
    n=len(m); a=[[F(x) for x in row]+[F(i==j) for j in range(n)] for i,row in enumerate(m)]
    for j in range(n):
        z=next(i for i in range(j,n) if a[i][j]);a[j],a[z]=a[z],a[j]
        q=a[j][j];a[j]=[x/q for x in a[j]]
        for i in range(n):
            if i!=j:
                q=a[i][j];a[i]=[x-q*y for x,y in zip(a[i],a[j])]
    return [r[n:] for r in a]
def resistance(h,weights):
    b=[[F(int(u==i)-int(v==i)) for i in range(1,4)] for u,v in EDGES]
    L=[[sum(h[e]*weights[e]*b[e][i]*b[e][j] for e in range(6)) for j in range(3)] for i in range(3)]
    inv=inverse(L)
    return [sum(v[i]*inv[i][j]*v[j] for i in range(3) for j in range(3)) for v in b]
def main():
    rows=[]
    for t in [1,2,3,5,10,100]:
        k=3*t+1;h=[2*t+1]*3+[4*t+1]*3;a=[t]*3+[2*t+1]*3
        assert union(h,2*k) and not union(a,k) and union([x-y for x,y in zip(h,a)],k)
        assert all(sum(h[j] for j in es)<2*k*(s.bit_count()-1) for s,es in SETS if 1<s.bit_count()<4)
        assert union([t]*3+[2*t]*3,k-1)
        raw=load([abs(F(a[j])-F(h[j],2)) for j in range(6)],h)
        assert raw==F(1,4*t+2)
        repairs=[]
        for i,j in [(0,5),(1,4),(2,3)]:
            r=a[:];r[i]+=1;r[j]-=1;assert good(r,h,k)
            d=[abs(x-y) for x,y in zip(a,r)];assert load(d,h)==F(1,6*t+2);repairs.append(d)
        avg=[sum(F(d[j],3) for d in repairs) for j in range(6)]
        assert load(avg,h)==F(1,6*t+3)
        rr=resistance(h,[1]*6); assert rr==[F(k,(2*t+1)*(7*t+2))]*3+[F(1,7*t+2)]*3
        wt=[1]*3+[2*t+1]*3; wr=resistance(h,wt)
        assert all(w*z==F(1,2*k) for w,z in zip(wt,wr))
        # Enumerate multiplicity vectors, not exponentially many equivalent labels.
        # For a fixed vector, choosing maximum overlap in each parallel class
        # minimizes every cut damage simultaneously, so this is exact for labels.
        checked=0
        if t<=3:
            best=F(100)
            for c0 in product(*(range(x+1) for x in h[:5])):
                last=3*k-sum(c0)
                if not 0<=last<=h[5]:continue
                c=list(c0)+[last]
                if good(c,h,k):
                    checked+=1;best=min(best,load([abs(x-y) for x,y in zip(a,c)],h))
            assert best==F(1,6*t+2)
        rows.append(dict(t=t,k=k,raw=str(raw),mixed=str(F(1,6*t+3)),pure=str(F(1,6*t+2)),exact_common_count_vectors=checked))
    # All-scale failure of ordinary matroid base exchange for exact halves.
    for k in [1,2,3,5,20]:
        h=[k]*6;p=[k,k,0,0,k,0];q=[k,0,k,k,0,0]
        assert good(p,h,k) and good(q,h,k)
        for f in [2,3]:
            c=p[:];c[1]-=1;c[f]+=1;assert not good(c,h,k)
    # Equal fair-complement marginals do not give a uniform response bound.
    for m in [2,6,24,100]:
        assert sum([F(1,4)]*m)==F(m,4)
    print(json.dumps(dict(kind='exact finite author support; no mathematical gate',nontight_cases=rows,
                         exchange_scales=[1,2,3,5,20],fair_complement_response=True),indent=2))
if __name__=='__main__':main()
