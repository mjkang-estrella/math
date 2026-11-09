import sys, json, os
sys.path.insert(0, os.path.dirname(__file__))
from branching import lam_ge2, has_ns_branching, alpha
from gadget import make
Barcs=[(0,1),(0,2),(3,0),(1,2),(1,3),(3,1),(2,3)]
for M in range(2,9):
    arcs=make(M,4,Barcs,[(0,0),(1,2)],[(2,0),(2,2 if M>2 else 1)])
    n=M+4
    print(M, 'lambda>=2', lam_ge2(n,arcs), 'alpha', alpha(n,arcs), 'bad roots', [s for s in range(n) if not has_ns_branching(n,arcs,s)], flush=True)
