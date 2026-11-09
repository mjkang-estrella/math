import sys, os, itertools
sys.path.insert(0, os.path.dirname(__file__))
from gadget_fast import semicomplete, lam_ok, fails
W1={(0,1),(1,2),(2,3),(3,0),(0,2),(1,3),(3,1)}
def canon(arcs):
    return min(tuple(sorted((p[u],p[v]) for (u,v) in arcs)) for p in itertools.permutations(range(4)))
cW=canon(W1); classes={}
for arcs in semicomplete(4):
    for e1,e2 in itertools.combinations_with_replacement(range(4),2):
        for x1,x2 in itertools.combinations_with_replacement(range(4),2):
            if lam_ok(4,arcs,[e1,e2],[x1,x2]) and fails(4,arcs,e1,e2,[x1,x2]) and fails(4,arcs,e2,e1,[x1,x2]):
                c=canon(arcs); classes[c]=classes.get(c,0)+1
print({('W1' if c==cW else str(c)):v for c,v in classes.items()})
