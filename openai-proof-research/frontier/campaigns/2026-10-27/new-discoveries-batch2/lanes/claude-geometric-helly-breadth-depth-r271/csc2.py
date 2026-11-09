"""Faster exact c.s.c. test (same criterion as csc.py; cross-checked in t_fast.py)."""
from fractions import Fraction as F
from itertools import combinations
from csc import hull,on_boundary_all,collinear,cross
def prep(X):
    H=hull(X);m=len(H);D=[]
    for i in range(m):
        a,b=H[i],H[(i+1)%m];n=(b[1]-a[1],a[0]-b[0])
        for nn in (n,(-n[0],-n[1])):
            if nn not in D: D.append(nn)
    dots={n:[n[0]*x[0]+n[1]*x[1] for x in X] for n in D}
    lines=[];need=[[] for _ in X]
    for k,n in enumerate(D):
        v=dots[n];h=max(v);l=min(v);lines.append((n,(h+l)/2))
        for i,x in enumerate(X):
            if v[i]==h: need[i].append(k)
    return H,lines,need
def center(X,skip=None):
    X=[x for i,x in enumerate(X) if i!=skip]
    if collinear(X): return ('collinear',)
    H,lines,need=prep(X)
    if not on_boundary_all(X,H): return None
    # distinct lines (L_theta and L_{theta+pi} coincide)
    seen={};U=[]
    for n,mu in lines:
        g=(n,mu)
        U.append(g)
    cands=set()
    for (n1,m1),(n2,m2) in combinations(U,2):
        d=n1[0]*n2[1]-n1[1]*n2[0]
        if d: cands.add(((m1*n2[1]-m2*n1[1])/d,(n1[0]*m2-n2[0]*m1)/d))
    for O in cands:
        ok=True
        for nd in need:
            if not any(lines[k][0][0]*O[0]+lines[k][0][1]*O[1]<=lines[k][1] for k in nd): ok=False;break
        if ok: return O
    return None
def is_min_obstruction(X):
    if center(X) is not None: return None
    w=[]
    for i in range(len(X)):
        c=center(X,skip=i)
        if c is None: return None
        w.append(c)
    return w
