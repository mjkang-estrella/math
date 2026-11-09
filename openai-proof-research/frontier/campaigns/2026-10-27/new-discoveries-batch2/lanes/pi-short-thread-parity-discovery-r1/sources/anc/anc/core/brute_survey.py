"""Independent census using ONLY brute.py (raw rules, no decomposition)."""
import sys, networkx as nx, brute, time
from collections import Counter
n=int(sys.argv[1]); t=time.time()
cnt=Counter(); bad=[]
for T in nx.nonisomorphic_trees(n):
    e=list(T.edges()); deg=dict(T.degree())
    m=sum(1 for (u,v) in e if deg[u]>1 and deg[v]>1)
    g=brute.grundy_tree(n,e)
    cnt[g]+=1
    if (g==0)!=(m%2==0): bad.append((m,g,sorted(e)))
print("n=%d trees=%d dist=%s counterexamples=%d time=%.0fs"%(n,sum(cnt.values()),dict(sorted(cnt.items())),len(bad),time.time()-t),flush=True)
for b in bad[:10]: print("  ",b)
