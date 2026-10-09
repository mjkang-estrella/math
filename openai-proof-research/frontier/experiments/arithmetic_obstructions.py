"""Exact checks for arithmetic scout obstructions; no numerical proof claims."""
from fractions import Fraction as F
from itertools import product
import json


def check_character(q):
    squares={x*x%q for x in range(1,q)}
    def chi(x):return 0 if x%q==0 else 1 if x%q in squares else -1
    inv2=pow(2,-1,q)
    a=[[chi((x+y)*inv2) for y in range(q)] for x in range(q)]
    for x in range(q):
        for z in range(q):
            assert sum(a[x][y]*a[z][y] for y in range(q)) == (q-1 if x==z else -1)
    for x in range(q):
        assert sum(a[x][y]**2 for y in range(q))==q-1
    return {'prime':q,'AA_transpose':'q I - J','twisted_row_sum':q-1}


def check_blocks():
    blocks=[]
    for a,b in product((-1,1),repeat=2):blocks.append(((a,b,a*b),F(1,8)))
    for signs in product((-1,1),repeat=4):blocks.append((signs,F(1,32)))
    states=[(b,j) for b,(signs,p) in enumerate(blocks) for j in range(len(signs))]
    index={s:i for i,s in enumerate(states)}
    trans=[]
    for b,j in states:
        if j+1<len(blocks[b][0]):trans.append([(index[b,j+1],F(1))])
        else:trans.append([(index[c,0],p) for c,(signs,p) in enumerate(blocks)])
    pi=[blocks[b][1]/F(7,2) for b,j in states]
    sign=[blocks[b][0][j] for b,j in states]
    assert sum(pi)==1
    after=[F(0) for _ in states]
    for i,row in enumerate(trans):
        for j,p in row:after[j]+=pi[i]*p
    assert after==pi
    def evolve(v):return [sum(p*v[j] for j,p in row) for row in trans]
    def moment(times):
        v=[F(1) for _ in states]
        for t in range(max(times),-1,-1):
            if t<max(times):v=evolve(v)
            if t in times:v=[x*s for x,s in zip(v,sign)]
        return sum(p*x for p,x in zip(pi,v))
    assert moment({0})==0
    pair={h:moment({0,h}) for h in range(1,17)}
    assert all(x==0 for x in pair.values())
    assert moment({0,1,2})==F(1,7)
    return {'states':len(states),'stationarity':'exact','pair_moments_1_through_16':[str(x) for x in pair.values()],'triple_moment':str(moment({0,1,2}))}


def check_dilation():
    limit=5000
    spf=list(range(limit+1))
    for p in range(2,limit+1):
        if spf[p]==p:
            for n in range(p*p,limit+1,p):
                if spf[n]==n:spf[n]=p
    lam=[1]*(limit+1)
    for n in range(2,limit+1):lam[n]=-lam[n//spf[n]]
    h,H,N=2,5,100
    ds=[6,7]
    triple=lambda n,d:lam[n]*lam[n+h*d]*lam[n+2*h*d]
    raw=sum(lam[d]*sum(triple(n,d) for n in range(d,H*N+1,d)) for d in ds)
    transferred=sum(sum(triple(n,1) for n in range(1,H*N//d+1)) for d in ds)
    assert raw==transferred
    return {'raw':raw,'dilated':transferred}

if __name__=='__main__':
    print(json.dumps({'character':[check_character(q) for q in (5,7,11,17,31,101)],'blocks':check_blocks(),'dilation':check_dilation()},indent=2))
