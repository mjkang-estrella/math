# Generate isomorphism-class representatives of all graphs on n<=N vertices (as edge bitmasks)
# by vertex augmentation with exact canonical forms (degree-refined permutation search).
import sys, json, itertools, pathlib
N=int(sys.argv[1]); out=pathlib.Path(sys.argv[2])
def pairs(n): return [(i,j) for j in range(n) for i in range(j)]
def adj_from(n,edges):
    A=[0]*n
    for i,j in edges: A[i]|=1<<j; A[j]|=1<<i
    return A
def canon(n,A):
    deg=[bin(a).count('1') for a in A]
    # refine: key = (deg, sorted neighbour degrees)
    key=[(deg[v],tuple(sorted(deg[u] for u in range(n) if A[v]>>u&1))) for v in range(n)]
    classes={}
    for v in range(n): classes.setdefault(key[v],[]).append(v)
    ks=sorted(classes)
    best=None
    for combo in itertools.product(*[itertools.permutations(classes[k]) for k in ks]):
        order=[v for grp in combo for v in grp]  # new label i -> old vertex order[i]
        pos={v:i for i,v in enumerate(order)}
        code=tuple(sorted((min(pos[i],pos[j]),max(pos[i],pos[j])) for i in range(n) for j in range(i+1,n) if A[i]>>j&1))
        code=(tuple(k for k in ks for _ in classes[k]),code)
        if best is None or code<best: best=code
    return best
reps={1:[()]}
for n in range(2,N+1):
    seen={}
    for g in reps[n-1]:
        for mask in range(1<<(n-1)):
            edges=list(g)+[(i,n-1) for i in range(n-1) if mask>>i&1]
            c=canon(n,adj_from(n,edges))
            if c not in seen: seen[c]=edges
    reps[n]=list(seen.values()); print(n,len(reps[n]),flush=True)
out.write_text(json.dumps({str(k):v for k,v in reps.items()}))
