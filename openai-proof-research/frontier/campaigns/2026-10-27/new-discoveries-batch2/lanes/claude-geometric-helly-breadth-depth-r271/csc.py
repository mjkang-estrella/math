"""Exact c.s.c. test for finite planar point sets (Fractions).
Criterion (derived in discovery.md, Lemma A): for X in convex position, not collinear,
O is admissible iff for every x in X there is n in D (outer normals of the edges of conv X
and their negatives) with n.x = h(n) and 2 n.O <= h(n) - h(-n), where h(n)=max_X n.y."""
from fractions import Fraction as F
from itertools import combinations
def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
def hull(P):
    P=sorted(set(P))
    if len(P)<=2: return P
    lo=[];up=[]
    for p in P:
        while len(lo)>=2 and cross(lo[-2],lo[-1],p)<=0: lo.pop()
        lo.append(p)
    for p in reversed(P):
        while len(up)>=2 and cross(up[-2],up[-1],p)<=0: up.pop()
        up.append(p)
    return lo[:-1]+up[:-1]   # strict vertices, ccw
def on_boundary_all(X,H):
    m=len(H)
    for x in X:
        if not any(cross(H[i],H[(i+1)%m],x)==0 for i in range(m)): return False
    return True
def collinear(X):
    X=list(X);return all(cross(X[0],X[1],p)==0 for p in X[2:]) if len(X)>2 else True
def data(X):
    """returns (lines, need) ; lines: list of (n,mu) with halfplane n.O<=mu ; need[x]=list of line ids"""
    H=hull(X);m=len(H);D=[]
    for i in range(m):
        a,b=H[i],H[(i+1)%m];n=(b[1]-a[1],a[0]-b[0])
        for s in (1,-1):
            nn=(s*n[0],s*n[1])
            if nn not in D: D.append(nn)
    lines=[];need={}
    for n in D:
        vals=[n[0]*x[0]+n[1]*x[1] for x in X];h=max(vals);l=min(vals)
        lines.append((n,F(h+l,2)))
    for x in X:
        need[x]=[k for k,(n,mu) in enumerate(lines) if n[0]*x[0]+n[1]*x[1]==max(n[0]*y[0]+n[1]*y[1] for y in X)]
    return lines,need
def admissible(X,O,lines=None,need=None):
    if lines is None: lines,need=data(X)
    return all(any(lines[k][0][0]*O[0]+lines[k][0][1]*O[1]<=lines[k][1] for k in need[x]) for x in X)
def candidates(lines):
    out=set()
    for (n1,m1),(n2,m2) in combinations(lines,2):
        d=n1[0]*n2[1]-n1[1]*n2[0]
        if d==0: continue
        out.add((F(m1*n2[1]-m2*n1[1],d),F(n1[0]*m2-n2[0]*m1,d)))
    return out
def csc_center(X):
    """None if not c.s.c.; else an exact admissible center."""
    X=[(F(a),F(b)) for a,b in X]
    if len(set(X))<len(X): X=list(dict.fromkeys(X))
    if collinear(X): return ('collinear',)
    H=hull(X)
    if not on_boundary_all(X,H): return None
    lines,need=data(X)
    for O in sorted(candidates(lines)):
        if admissible(X,O,lines,need): return O
    # all lines parallel cannot happen for a nondegenerate polygon
    return None
def brute_center(X,grid):
    """independent slow check: hull of X u X_O, boundary membership"""
    X=[(F(a),F(b)) for a,b in X]
    for O in grid:
        Y=X+[(2*O[0]-x[0],2*O[1]-x[1]) for x in X]
        H=hull(Y)
        if len(H)>=3 and on_boundary_all(Y,H): return O
    return None
def minimal_obstruction(X):
    X=[(F(a),F(b)) for a,b in X]
    if csc_center(X) is not None: return False,None
    w={}
    for x in X:
        c=csc_center([y for y in X if y!=x])
        if c is None: return False,x
        w[x]=c
    return True,w
