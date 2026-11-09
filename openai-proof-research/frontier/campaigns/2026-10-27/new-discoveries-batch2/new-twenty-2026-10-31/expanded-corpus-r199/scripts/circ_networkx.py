"""Third check with networkx's edge_betweenness_centrality (float, unnormalized).
usage: circ_networkx.py m s1 s2 ...
"""
import sys, json
import networkx as nx
m = int(sys.argv[1]); steps = [int(x) for x in sys.argv[2:]]
G = nx.circulant_graph(m, steps)
eb = nx.edge_betweenness_centrality(G, normalized=False)
by = {}
for (u, v), x in eb.items():
    d = min((u - v) % m, (v - u) % m); by.setdefault(d, []).append(x)
print(json.dumps(dict(networkx=nx.__version__, m=m, steps=steps, edges=G.number_of_edges(),
    by_step={str(d): [min(v), max(v)] for d, v in sorted(by.items())},
    max_minus_min=max(eb.values()) - min(eb.values()))))
