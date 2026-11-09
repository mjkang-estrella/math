"""Raw-rules check of the 12-vertex counterexample to Zandee's Conjecture 4.3."""
from functools import lru_cache
edges=[(1, 0), (1, 2), (0, 6), (0, 10), (2, 3), (3, 4), (4, 5), (6, 7), (7, 8), (8, 9), (10, 11)]
n=12; m_all=len(edges)
inc=[[] for _ in range(n)]
for i,(u,v) in enumerate(edges): inc[u].append(i); inc[v].append(i)
def bad(st,w):
    if any(st[i]==0 for i in inc[w]): return False
    heads=[(edges[i][1] if st[i]==1 else edges[i][0]) for i in inc[w]]
    return all(h==w for h in heads) or all(h!=w for h in heads)
@lru_cache(None)
def g(st):
    s=list(st); opts=set()
    for i in range(m_all):
        if s[i]: continue
        for d in (1,2):
            s[i]=d
            if not bad(s,edges[i][0]) and not bad(s,edges[i][1]): opts.add(g(tuple(s)))
            s[i]=0
    x=0
    while x in opts: x+=1
    return x
deg=[len(inc[v]) for v in range(n)]
markable=[i for i,(u,v) in enumerate(edges) if deg[u]>1 and deg[v]>1]
print("markable edges:",len(markable))
st=[0]*m_all; st[edges.index((7,8))]=1   # 7 -> 8
print("Grundy value with 7->8 marked:", g(tuple(st)), " (Zandee 4.3 predicts parity of", len(markable)-1, ")")
print("empty board:", g(tuple([0]*m_all)))
