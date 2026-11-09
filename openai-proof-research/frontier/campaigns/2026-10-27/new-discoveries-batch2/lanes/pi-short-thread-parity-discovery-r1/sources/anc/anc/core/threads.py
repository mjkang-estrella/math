"""For all trees with n vertices: compute max thread length (in trimmed pieces) of counterexamples.
Thread = maximal path in the trimmed forest (after deleting leaves and splitting at special vertices)
whose internal vertices have degree 2."""
import sys, networkx as nx, decomp
def max_thread(T):
    deg=dict(T.degree())
    leaves={v for v in T if deg[v]==1}
    special={u for v in leaves for u in T[v]}
    # trimmed edges
    E=[(u,v) for (u,v) in T.edges() if u not in leaves and v not in leaves]
    # split at special vertices: build graph where special vertices are duplicated per edge
    H=nx.Graph(); cnt=0
    for (u,v) in E:
        a=u if u not in special else ('s',u,cnt); cnt+=1
        b=v if v not in special else ('s',v,cnt); cnt+=1
        H.add_edge(a,b)
    best=0
    # threads: start from vertices of degree !=2, walk through degree-2 vertices
    for comp in nx.connected_components(H):
        C=H.subgraph(comp)
        ends=[v for v in C if C.degree(v)!=2]
        if not ends: continue
        for s in ends:
            for nb in C[s]:
                L=1; prev=s; cur=nb
                while C.degree(cur)==2:
                    nxt=[w for w in C[cur] if w!=prev][0]; prev,cur=cur,nxt; L+=1
                best=max(best,L)
    return best
n=int(sys.argv[1])
from collections import Counter
mt_bad=Counter(); mt_all=Counter()
for T in nx.nonisomorphic_trees(n):
    e=list(T.edges()); deg=dict(T.degree())
    m=sum(1 for (u,v) in e if deg[u]>1 and deg[v]>1)
    mt=max_thread(T)
    mt_all[mt]+=1
    g=decomp.grundy_original_tree(n,e)
    if (g==0)!=(m%2==0): mt_bad[mt]+=1
print("n=%d max-thread distribution all=%s counterexamples=%s"%(n,dict(sorted(mt_all.items())),dict(sorted(mt_bad.items()))),flush=True)
