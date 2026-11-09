import sys, networkx as nx
n=int(sys.argv[1])
it = nx.nonisomorphic_trees(n) if n>1 else [nx.empty_graph(1)]
for T in it:
    e=list(T.edges())
    print(n, " ".join(f"{u} {v}" for u,v in e), 0, 0)
