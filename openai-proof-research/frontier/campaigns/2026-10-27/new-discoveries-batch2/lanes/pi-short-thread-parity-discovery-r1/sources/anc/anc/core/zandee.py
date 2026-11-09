"""Test Zandee's Conjecture 4.3: tree with n markable edges, exactly one marked => SG parity == (n-1) parity.
Also: G mod 2 vs m mod 2 statistics."""
import sys, networkx as nx, decomp
from collections import Counter
N=int(sys.argv[1])
for n in range(2,N+1):
    viol=0; tot=0; pstat=Counter()
    ex=None
    for T in nx.nonisomorphic_trees(n):
        edges=list(T.edges()); deg=dict(T.degree())
        mk=[(u,v) for (u,v) in edges if deg[u]>1 and deg[v]>1]
        m=len(mk)
        g=decomp.grundy_original_tree(n,edges)
        pstat[(m%2,g%2,min(g,2))]+=1
        for (u,v) in mk:
            for (t,h) in ((u,v),(v,u)):
                lab={w:'N' for w in range(n)}
                lab[t]='O'; lab[h]='I'
                rest=[e for e in edges if e!=(u,v)]
                # legality: t,h have degree>=2 so always legal
                gg=decomp.grundy_position(lab,rest)
                tot+=1
                if gg%2 != (m-1)%2:
                    viol+=1
                    if ex is None: ex=(edges,(t,h),gg,m)
    print("n=%d one-marked positions=%d violations of Zandee 4.3=%d; (m%%2,G%%2,min(G,2)) stats=%s"%(n,tot,viol,dict(pstat)),flush=True)
    if ex: print("   example:",ex)
