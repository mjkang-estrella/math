# 338579: connected components of the cyclic shift graph K(rps) (Cain-Malheiro-Silva arXiv:1803.00361v1, Alg. 2.1, Sec. 3)
import sys, json, itertools
from collections import deque
def rps(word):
    cols=[]
    for w in word:
        if not cols or cols[-1][0] < w: cols.append([w]); continue
        m=min(i for i,c in enumerate(cols) if w <= c[0])
        cols[m]=[w]+cols[m]
    return tuple(tuple(c) for c in cols)
def words(ev):
    letters=[a+1 for a,c in enumerate(ev) for _ in range(c)]
    return set(itertools.permutations(letters))
def component(ev):
    W=words(ev); adj={}
    for w in W:
        p=rps(w)
        for s in range(1,len(w)):
            q=rps(w[s:]+w[:s])
            if q!=p: adj.setdefault(p,set()).add(q); adj.setdefault(q,set()).add(p)
        adj.setdefault(p,set())
    V=list(adj); diam=0
    for v in V:
        dist={v:0}; dq=deque([v])
        while dq:
            u=dq.popleft()
            for x in adj[u]:
                if x not in dist: dist[x]=dist[u]+1; dq.append(x)
        if len(dist)!=len(V): return len(V),None
        diam=max(diam,max(dist.values()))
    return len(V),diam
if __name__=='__main__':
    table2=[(5,),(5,3),(4,1,4),(3,3,1,2),(1,2,4,2),(1,3,2,1,2),(2,1,1,2,3),(1,2,1,2,2)]
    std=[(1,)*k for k in range(1,8)]
    for ev in table2+std: print(json.dumps({'evaluation':ev,'vertices_diameter':component(ev)}),flush=True)
    # n=4 evaluations covered by source Lemma 3.8 (min symbol >=2 copies, second smallest once)
    for ev in [(2,1,1,1),(2,1,2,1),(2,1,1,2),(3,1,1,1),(2,1,2,2),(3,1,2,1)]:
        v,d=component(ev); print(json.dumps({'evaluation':ev,'n':4,'vertices':v,'diameter':d,'lower_bound_n_minus_1':3,'violates_lower_bound':d is not None and d<3}),flush=True)
