"""First-order (near-centrally-symmetric) model: m points w_j, directions d_0..d_m (d_m = -d_0 orientation mod pi),
arc A_j = directions between d_{j-1} and d_j. Constraint j: O-w_j in closed double cone spanned by +-d_{j-1}, +-d_j.
Feasibility test exact: O in cone iff cross(d_{j-1},v) and cross(d_j,v) have opposite weak signs."""
from fractions import Fraction as F
from itertools import combinations
def cr(a,b): return a[0]*b[1]-a[1]*b[0]
def inD(O,w,d1,d2):
    v=(O[0]-w[0],O[1]-w[1]);a=cr(d1,v);b=cr(d2,v)
    return a*b<=0
def lines(ws,ds,idx):
    L=[]
    for j in idx: L+= [(ws[j],ds[j]),(ws[j],ds[j+1])]
    return L
def meet(l1,l2):
    (p,d),(q,e)=l1,l2;den=cr(d,e)
    if den==0: return None
    t=F(cr((q[0]-p[0],q[1]-p[1]),e),den);return (p[0]+t*d[0],p[1]+t*d[1])
def feasible(ws,ds,idx):
    idx=list(idx);L=lines(ws,ds,idx)
    cands=set(ws[j] for j in idx)
    for a,b in combinations(L,2):
        P=meet(a,b)
        if P is not None: cands.add(P)
    for O in cands:
        if all(inD(O,ws[j],ds[j],ds[j+1]) for j in idx): return O
    return None
def minimal(ws,ds):
    m=len(ws)
    if feasible(ws,ds,range(m)) is not None: return None
    wit={}
    for j in range(m):
        O=feasible(ws,ds,[i for i in range(m) if i!=j])
        if O is None: return None
        wit[j]=O
    return wit
