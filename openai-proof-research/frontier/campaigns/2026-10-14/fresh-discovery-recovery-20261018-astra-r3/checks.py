#!/usr/bin/env python3
"""Exact finite diagnostics only; not a universal proof or independent review."""
from fractions import Fraction as F
from itertools import combinations, product, permutations
import json

def graph(n,mask):
    edges=list(combinations(range(n),2)); adj=[set() for _ in range(n)]
    for i,(a,b) in enumerate(edges):
        if mask>>i&1: adj[a].add(b);adj[b].add(a)
    return adj

def query(adj,order,root,deleted=None):
    rank={v:i for i,v in enumerate(order)}; trace=[]
    def rec(v):
        trace.append(v)
        for w in sorted(adj[v]-{deleted},key=rank.__getitem__):
            if rank[w]<rank[v] and rec(w): return False
        return True
    return rec(root),set(trace)

def lifetime_integral(laws):
    cuts=sorted({F(0),F(1)}|{x for law in laws for x,p in law if 0<x<1})
    result=F(0)
    for l,r in zip(cuts,cuts[1:]):
        t=(l+r)/2; z=F(1)
        for law in laws:z*=sum(p for x,p in law if x>t)
        result+=(r-l)*z
    return result

def main():
    count={'root_list_cases':0,'lifetime_triples':0,'deletion_trace_cases':0,'exponent_cases':0}
    for n in range(2,6):
        for mask in range(1<<(n*(n-1)//2)):
            adj=graph(n,mask)
            for v in range(n):
                d=len(adj[v])
                if not d:continue
                direct=sum(y in adj[x] for x in adj[v] for y in adj[v])
                links=sum(y in adj[x] for x,y in combinations(adj[v],2))
                assert direct==2*links
                for x,y in product(adj[v],repeat=2):
                    if x!=y and y in adj[x]:
                        a={tuple(sorted((v,x,z))) for z in adj[v]&adj[x]}
                        b={tuple(sorted((v,y,z))) for z in adj[v]&adj[y]}
                        assert tuple(sorted((v,x,y))) in a&b
                count['root_list_cases']+=1
    times=(F(1,4),F(3,4),F(2))
    probs=((F(1,2),F(1,4),F(1,4)),(F(1,3),)*3,(F(1,5),F(2,5),F(2,5)),(F(0),F(0),F(1)))
    laws=[tuple(zip(times,p)) for p in probs]
    for lawset in product(laws,repeat=3):
        a=[sum(p for x,p in law if x>1) for law in lawset]
        means=[F(0)]*3;pairs={(i,j):F(0) for i,j in combinations(range(3),2)};triple=F(0)
        for entries in product(*lawset):
            L=[x for x,p in entries];prob=entries[0][1]*entries[1][1]*entries[2][1]
            accepted=min(F(1),*L)
            Y=[int(x>1) for x in L]
            for i in range(3):means[i]+=prob*(1-accepted)*Y[i]
            for i,j in pairs:pairs[i,j]+=prob*(1-accepted)*Y[i]*Y[j]
            triple+=prob*(1-accepted)*Y[0]*Y[1]*Y[2]
        assert triple==0
        for i in range(3):
            others=[j for j in range(3) if j!=i]
            assert means[i]==a[i]*(1-lifetime_integral([lawset[j] for j in others]))
        for i,j in pairs:
            k=3-i-j
            assert pairs[i,j]==a[i]*a[j]*(1-lifetime_integral([lawset[k]]))
        count['lifetime_triples']+=1
    for n in range(1,5):
        for mask in range(1<<(n*(n-1)//2)):
            adj=graph(n,mask)
            totals=[0]*n
            orders=list(permutations(range(n)))
            for order in orders:
                for root in range(n):
                    answer,trace=query(adj,order,root)
                    for deleted in range(n):
                        if root==deleted:changed=int(answer)
                        else:
                            after,_=query(adj,order,root,deleted)
                            changed=int(answer!=after)
                            if deleted not in trace:assert not changed
                        totals[deleted]+=changed
                        count['deletion_trace_cases']+=1
            for v in range(n):assert F(totals[v],len(orders))<=1+F(len(adj[v]),2)
    for degree_power,resource_power,expected in [(153,5,F(-2699,2000)),(123,4,F(-1758,2000)),(93,3,F(-817,2000))]:
        exponent=1+F(degree_power,1000)-F(1001,2000)*resource_power
        assert exponent==expected and exponent<0
        count['exponent_cases']+=1
    print(json.dumps({'status':'FINITE_DIAGNOSTICS_PASS','counts':count,'limits':'Finite exact cases only; no T188U proof, contribution verdict, or independent gate.'},sort_keys=True))
if __name__=='__main__':main()
