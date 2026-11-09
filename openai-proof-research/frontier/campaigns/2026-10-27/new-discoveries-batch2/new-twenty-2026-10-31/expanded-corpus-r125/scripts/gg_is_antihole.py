import sys, json
sys.path.insert(0, sys.argv[1])
from gg_lib import *
for f in sys.argv[2:]:
    for l in open(f):
        n, adj = from_code(tuple(json.loads(l)))
        comp = [((1 << n) - 1) & ~(adj[x] | (1 << x)) for x in range(n)]
        # complement is a cycle iff 2-regular and connected
        isc = all(popc(c) == 2 for c in comp) and len(components(comp, (1 << n) - 1)) == 1
        print(f, n, 'complement-is-cycle' if isc else 'OTHER', adj)
