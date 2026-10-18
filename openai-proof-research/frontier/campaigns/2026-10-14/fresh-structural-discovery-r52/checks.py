#!/usr/bin/env python3
"""Finite exact controls for local flow repair; not a proof of the full target."""
from collections import deque
from fractions import Fraction
from itertools import product
from math import ceil
import json, random

class Network:
    def __init__(self,n):
        self.g=[[] for _ in range(n)]
    def edge(self,u,v,c):
        a=[v,c,len(self.g[v])]; b=[u,0,len(self.g[u])]
        self.g[u].append(a); self.g[v].append(b)
        return a
    def flow(self,s,t):
        total=0
        while True:
            parent=[None]*len(self.g); parent[s]=(-1,-1)
            queue=deque([s])
            while queue and parent[t] is None:
                u=queue.popleft()
                for j,e in enumerate(self.g[u]):
                    if e[1] and parent[e[0]] is None:
                        parent[e[0]]=(u,j); queue.append(e[0])
            if parent[t] is None: return total
            v=t; amount=10**9
            while v!=s:
                u,j=parent[v]; amount=min(amount,self.g[u][j][1]); v=u
            v=t
            while v!=s:
                u,j=parent[v]; e=self.g[u][j]
                e[1]-=amount; self.g[v][e[2]][1]+=amount; v=u
            total+=amount

def imbalance(n,arcs):
    b=[0]*n
    for u,v in arcs: b[u]+=1; b[v]-=1
    return b

def expansion(n,arcs):
    value=Fraction(n)
    for mask in range(1,2**n-1):
        size=min(mask.bit_count(),n-mask.bit_count())
        out=sum(bool(mask>>u&1) and not bool(mask>>v&1) for u,v in arcs)
        inc=sum(not bool(mask>>u&1) and bool(mask>>v&1) for u,v in arcs)
        value=min(value,Fraction(out,size),Fraction(inc,size))
    return value

def repair(n,arcs,b,h):
    assert sum(b)==0 and h>0
    k=max(map(abs,b),default=0); assert k<=h
    M=ceil(Fraction(k*n)/h)
    network=Network(2*n+2); s=2*n; t=s+1
    for v in range(n):
        network.edge(2*v,2*v+1,M)
        if b[v]>0: network.edge(s,2*v,b[v])
        if b[v]<0: network.edge(2*v,t,-b[v])
    refs=[network.edge(2*u+1,2*v,1) for u,v in arcs]
    assert network.flow(s,t)==sum(x for x in b if x>0)
    F=[a for a,e in zip(arcs,refs) if e[1]==0]
    assert imbalance(n,F)==b
    out=[0]*n; inc=[0]*n
    for u,v in F: out[u]+=1; inc[v]+=1
    assert max(out,default=0)<=M and max(inc,default=0)<=M+k
    return F,M+k

def main():
    universe=[(u,v) for u in range(4) for v in range(4) if u!=v]
    graphs=0; nonzero=0
    for mask in range(2**len(universe)):
        arcs=[e for i,e in enumerate(universe) if mask>>i&1]
        h=expansion(4,arcs)
        if h<=0: continue
        b=imbalance(4,arcs)
        if max(map(abs,b))>h: continue
        F,loss=repair(4,arcs,b,h)
        rest=set(arcs)-set(F)
        assert imbalance(4,rest)==[0]*4
        assert expansion(4,rest)>=h-loss
        graphs+=1; nonzero+=any(b)
    rng=random.Random(11818152); dense=0
    for n in [10,20,40,60]:
        for trial in range(8):
            permutation=list(range(n)); rng.shuffle(permutation)
            removed={(u,permutation[u]) for u in range(n//2) if u!=permutation[u]}
            arcs=[(u,v) for u in range(n) for v in range(n) if u!=v and (u,v) not in removed]
            # Complete bidirected cuts have expansion >=n/2; deleting a partial
            # permutation loses at most one arc per vertex on either cut side.
            h=Fraction(n,2)-1
            b=imbalance(n,arcs)
            F,loss=repair(n,arcs,b,h)
            assert imbalance(n,set(arcs)-set(F))==[0]*n
            if n>=20: assert h-loss>0
            dense+=1
    # Exact exponent windows; no numerical asymptotic inference.
    a=Fraction(77,100); h=Fraction(90,100); n=Fraction(102,100)
    assert a+n-2*h==Fraction(-1,100)
    assert Fraction(3,2)*n-2*a==Fraction(-1,100)
    assert Fraction(3,2)*n-2*Fraction(74,100)==Fraction(5,100)
    # Selected-cut neighborhood obstruction remains balanced, both variants.
    for m in range(2,12):
        arcs={(i,2*m) for i in range(m)}|{(2*m,m+i) for i in range(m)}|{(m+i,i) for i in range(m)}
        for dense_U in [False,True]:
            A=arcs|({(i,j) for i in range(m) for j in range(m) if i!=j} if dense_U else set())
            assert imbalance(2*m+1,A)==[0]*(2*m+1)
            U=set(range(m)); outgoing={v for u,v in A if u in U and v not in U}
            incoming={u for u,v in A if u not in U and v in U}
            assert outgoing=={2*m} and incoming==set(range(m,2*m))
    # Exact spider scheduling formula via deadline greedy for bounded values.
    spider=0
    for k,b,ell in product(range(2,7),range(0,15),range(1,12)):
        accepted=0
        for deadline in range(b+1,b+ell+1):
            for _ in range(k):
                if accepted<deadline: accepted+=1
        assert accepted==min(k*ell,b+ell)
        spider+=1
    print(json.dumps({'status':'PASS finite diagnostics only','all_four_vertex_digraphs_examined':4096,'admissible_self_imbalance_repairs':graphs,'nonzero_repairs':nonzero,'seed':11818152,'dense_repairs':dense,'spider_schedules':spider,'full_cycle_target':'UNRESOLVED'},indent=2))

if __name__=='__main__': main()
