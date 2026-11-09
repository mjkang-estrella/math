import networkx as nx, sys
lo, hi = int(sys.argv[1]), int(sys.argv[2])
out = sys.stdout
for n in range(lo, hi+1):
    for T in nx.nonisomorphic_trees(n):
        E = list(T.edges())
        out.write('%d %d %s\n' % (n, len(E), ' '.join('%d %d' % e for e in E)))
