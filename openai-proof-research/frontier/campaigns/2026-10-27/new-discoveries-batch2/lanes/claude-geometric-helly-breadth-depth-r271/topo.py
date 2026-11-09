"""Exact topology of intersections of triangle center-sets M_T (Lemma 2.2 of the source).
M_T = medial triangle + three vertical-angle wedges at its vertices. Pieces are closed pointed polyhedra
given by halfplanes (a,b,c): a*x+b*y<=c."""
from fractions import Fraction as F
from itertools import combinations
def cr(u,v): return u[0]*v[1]-u[1]*v[0]
def sub(p,q): return (p[0]-q[0],p[1]-q[1])
def hp_side(p,q,r):
    """closed halfplane bounded by line pq containing r"""
    a,b=q[1]-p[1],p[0]-q[0];c=a*p[0]+b*p[1]
    if a*r[0]+b*r[1]>c: a,b,c=-a,-b,-c
    return (a,b,c)
def pieces(T):
    a,b,c=T;ma=((b[0]+c[0])/2,(b[1]+c[1])/2);mb=((c[0]+a[0])/2,(c[1]+a[1])/2);mc=((a[0]+b[0])/2,(a[1]+b[1])/2)
    P=[[hp_side(ma,mb,mc),hp_side(mb,mc,ma),hp_side(mc,ma,mb)]]
    for m,u,v in [(ma,mb,mc),(mb,mc,ma),(mc,ma,mb)]:
        r1=(2*m[0]-u[0],2*m[1]-u[1]);r2=(2*m[0]-v[0],2*m[1]-v[1])   # rays m->r1 (dir m-u), m->r2
        inner=((r1[0]+r2[0])/2,(r1[1]+r2[1])/2)
        P.append([hp_side(m,r1,inner),hp_side(m,r2,inner)])
    return P
def feasible(H):
    pts=[]
    for (a1,b1,c1),(a2,b2,c2) in combinations(H,2):
        d=a1*b2-a2*b1
        if d: pts.append(((c1*b2-c2*b1)/d,(a1*c2-a2*c1)/d))
    for p in pts:
        if all(a*p[0]+b*p[1]<=c for a,b,c in H): return True
    return False
def inM(T,p): return any(all(a*p[0]+b*p[1]<=c for a,b,c in H) for H in pieces(T))
def topology(Ts):
    """pieces of intersection of M_T for T in Ts = products of pieces; return (#components, euler char) of union"""
    prods=[[]]
    for T in Ts: prods=[q+H for q in prods for H in pieces(T)]
    cells=[q for q in prods if feasible(q)]
    n=len(cells)
    if n==0: return (0,0)
    # nerve euler characteristic up to full depth (cells convex & pointed)
    chi=0;faces=[(i,) for i in range(n)];chi+=n
    edges=[(i,j) for i,j in combinations(range(n),2) if feasible(cells[i]+cells[j])]
    # components
    par=list(range(n))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]];x=par[x]
        return x
    for i,j in edges: par[f(i)]=f(j)
    comps=len(set(f(i) for i in range(n)))
    level=[tuple(e) for e in edges];k=1
    while level:
        chi+=(-1)**k*len(level)
        nxt=set()
        for s in level:
            for j in range(s[-1]+1,n):
                if all(((min(i,j),max(i,j)) in set(edges)) for i in s):
                    H=sum((cells[i] for i in s),[])+cells[j]
                    if feasible(H): nxt.add(s+(j,))
        level=sorted(nxt);k+=1
    return comps,chi
