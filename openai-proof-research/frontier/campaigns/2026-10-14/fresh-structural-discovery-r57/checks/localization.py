#!/usr/bin/env python3
"""MIT. Finite exact author diagnostic; not an implementation of the FPRAS."""
from fractions import Fraction as Q
from itertools import product
from random import Random
import json

def pow2(k):
    return Q(2**k) if k>=0 else Q(1,2**(-k))

def run():
    rng=Random(571152); cases=0; tables=0; removed=0; nonempty_tails=0
    for trial in range(600):
        m,n=2,3; edges=[(i,m+j) for i in range(m) for j in range(n)]
        caps=[rng.randrange(4) for _ in edges]
        witness=[rng.randrange(u+1) for u in caps]
        def balance(x):
            b=[0]*(m+n)
            for (i,j),v in zip(edges,x):b[i]+=v;b[j]-=v
            return b
        b=balance(witness)
        fiber=[x for x in product(*(range(u+1) for u in caps)) if balance(x)==b]
        costs=[rng.randrange(-16,17) for _ in edges]
        cost=lambda x:sum(c*v for c,v in zip(costs,x))
        opt=min(fiber,key=cost); C=cost(opt)
        arcs=[]
        for (i,j),c,x,u in zip(edges,costs,opt,caps):
            if x<u:arcs.append((i,j,c))
            if x>0:arcs.append((j,i,-c))
        dist=[0]*(m+n)
        for _ in range(m+n):
            changed=False
            for i,j,c in arcs:
                if dist[j]>dist[i]+c:dist[j]=dist[i]+c;changed=True
            if not changed:break
        assert all(dist[j]<=dist[i]+c for i,j,c in arcs)
        reduced=[c+dist[i]-dist[j] for (i,j),c in zip(edges,costs)]
        assert all(r==0 or x==(0 if r>0 else u) for r,x,u in zip(reduced,opt,caps))
        N0=1
        for u in caps:N0*=u+1
        K=N0.bit_length()+4; delta=Q(1,8)
        lo=[0 if r>=0 else max(0,u-K//(-r)) for r,u in zip(reduced,caps)]
        hi=[u if r<=0 else min(u,K//r) for r,u in zip(reduced,caps)]
        assert all(a<=x<=z for a,x,z in zip(lo,opt,hi))
        total=Q(0); tail=Q(0)
        for x in fiber:
            gap=sum(r*v if r>0 else -r*(u-v) for r,u,v in zip(reduced,caps,x))
            assert gap==cost(x)-C and gap>=0
            inside=all(a<=v<=z for a,v,z in zip(lo,x,hi))
            assert inside or gap>K
            weight=pow2(-gap);total+=weight
            if not inside:tail+=weight;removed+=1
        assert tail<=delta*total
        for r,u,a,z in zip(reduced,caps,lo,hi):
            assert abs(r)*(z-a)<=K or r==0
            for v in [a,z]:assert 0<= (r*v if r>0 else -r*(u-v)) <=K
        cases+=1;tables+=len(fiber);nonempty_tails+=bool(tail)
    # Tiny-cost and huge binary-capacity floor arithmetic, without enumeration.
    u=2**2000; r=Q(1,2**1500); K=4096
    width=min(u,K//r)
    assert width==K*2**1500 and r*width==K
    assert len(str(width))<1000
    r2=Q(1,2**3000)
    assert min(u,K//r2)==u and r2*u<=K
    # Noncircular Lipschitz inequality for representative parameters.
    for d in range(2,31):
        for K in [1,7,101]:
            G=32*d*d*K;T=20*(100+d+2*G+20)
            gamma=Q(1,1024*d*T);A=(Q(4*T)/gamma).__ceil__()
            bins=32*d*d*(A+K)
            assert Q(2*A*d*d+(2*d*d+2*d)*K,bins)<=Q(1,8)
    return dict(status='PASS',seed=571152,random_fibers=cases,enumerated_tables=tables,
                excluded_tables=removed,fibers_with_nonempty_tail=nonempty_tails,
                huge_capacity_bits=2001,tiny_cost_denominator_bits=[1501,3001],
                scope='Finite exact localization, duality, tail and parameter identities only; no sampler implementation, proof gate or novelty claim.')

if __name__=='__main__':print(json.dumps(run(),indent=2))
