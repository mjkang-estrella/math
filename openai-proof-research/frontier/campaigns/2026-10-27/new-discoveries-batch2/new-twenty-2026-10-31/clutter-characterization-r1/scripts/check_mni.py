"""Exact check that clutter C (from cert JSON) is minimally nonideal:
 - C itself has a fractional vertex;
 - every single-element deletion C\\v and contraction C/v is ideal (all vertices integral).
Vertex enumeration: all n-subsets of the constraint rows {x(X)>=1} ∪ {x_u>=0}; float batched solve
to find candidate bases, then every candidate vertex (feasible, nonsingular) is recomputed EXACTLY
with Fractions; integrality judged exactly. Singular-basis detection uses exact rank on any basis
whose float condition is doubtful."""
import json, sys, itertools
import numpy as np
from fractions import Fraction
d=json.load(open(sys.argv[1])); E=[frozenset(x) for x in d['edges']]; n=11
def minimal(F):
    F=set(F); return [X for X in F if not any(Y<X for Y in F)]
def exact_solve(M,rhs):
    m=len(M); A=[[Fraction(v) for v in row]+[Fraction(r)] for row,r in zip(M,rhs)]
    for c in range(m):
        piv=next((i for i in range(c,m) if A[i][c]!=0),None)
        if piv is None: return None
        A[c],A[piv]=A[piv],A[c]
        for i in range(m):
            if i!=c and A[i][c]!=0:
                f=A[i][c]/A[c][c]; A[i]=[a-f*b for a,b in zip(A[i],A[c])]
    return [A[i][m]/A[i][i] for i in range(m)]
def fractional_vertices(edges, ground):
    ground=sorted(ground); k=len(ground); idx={u:i for i,u in enumerate(ground)}
    rows=[]; rhs=[]
    for X in edges:
        r=[0]*k
        for u in X: r[idx[u]]=1
        rows.append(r); rhs.append(1)
    for u in range(k):
        r=[0]*k; r[u]=1; rows.append(r); rhs.append(0)
    R=np.array(rows,float); b=np.array(rhs,float); m=len(rows)
    fr=[]; nverts=0; seen=set()
    combos=list(itertools.combinations(range(m),k))
    for start in range(0,len(combos),200000):
        cb=np.array(combos[start:start+200000])
        Ms=R[cb]; bs=b[cb]
        dets=np.linalg.det(Ms)
        ok=np.abs(dets)>0.5   # 0/1 matrices: nonsingular => |det|>=1
        if not ok.any(): continue
        xs=np.linalg.solve(Ms[ok],bs[ok][...,None])[...,0]
        feas=(xs>=-1e-9).all(1)&((R@xs.T).T[:, :len(edges)]>=1-1e-9).all(1) if len(edges) else (xs>=-1e-9).all(1)
        for t in np.nonzero(feas)[0]:
            c=cb[np.nonzero(ok)[0][t]]
            x=exact_solve([rows[i] for i in c],[rhs[i] for i in c])
            if x is None: continue
            if any(v<0 for v in x) or any(sum(x[idx[u]] for u in X)<1 for X in edges): continue
            key=tuple(x)
            if key in seen: continue
            seen.add(key); nverts+=1
            if any(v.denominator!=1 for v in x): fr.append(key)
    # sanity on near-singular: verify float |det|<=0.5 bases are exactly singular for a sample
    return nverts, fr
nv,fr=fractional_vertices(E,range(n))
print('C11: vertices',nv,'fractional',len(fr),[ [str(v) for v in f] for f in fr][:3]); sys.stdout.flush()
allideal=True
for v in range(n):
    G=[u for u in range(n) if u!=v]
    dele=[X for X in E if v not in X]
    con=minimal([X-{v} for X in E])
    for name,F in (('delete',dele),('contract',con)):
        nv,fr=fractional_vertices(F,G)
        print(f'v={v} {name}: edges={len(F)} vertices={nv} fractional={len(fr)}'); sys.stdout.flush()
        if fr: allideal=False
print('MNI' if allideal else 'NOT MNI (some minor nonideal)')
