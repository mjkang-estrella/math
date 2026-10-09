"""First-order Hodge loci (IVHS) of (a) the Mumford exceptional class Q_f on A x A and
(b) the partner class Phi on A x B (B = split Weil sixfold partner, Theorem P of the review).
Exact rational arithmetic, sparse exterior algebra, pure standard library.
Model: complex basis adapted to the Hodge decomposition (all structure constants are rational,
so no i is needed).  V = V1(x)V2(x)V3, basis index 4*i1+2*i2+i3; e_+ (bit 0) of V1 spans V1^{1,0},
V2,V3 are of type (0,0)-rotation (compact factors), so V^{1,0} = e_+ (x) V2 (x) V3.
Polarized first-order deformations: xi: V^{1,0} -> V^{0,1} with omega(x, xi y) symmetric.
Class T in wedge^4 stays Hodge to first order iff D_xi T = 0 (D_xi = derivation extension).
Run: python3 -I hodge_locus.py"""
import itertools
from fractions import Fraction as Fr
# ---------- sparse exterior algebra ----------
def wedge_basis(idx):
    idx=list(idx)
    if len(set(idx))<len(idx): return None,0
    sgn=1
    for i in range(len(idx)):
        for j in range(len(idx)-1-i):
            if idx[j]>idx[j+1]: idx[j],idx[j+1]=idx[j+1],idx[j]; sgn=-sgn
    return tuple(idx),sgn
def wedge(*vs):  # vs: sparse vectors {index: coeff} or wedge elements {tuple: coeff}
    cur={():Fr(1)}
    for v in vs:
        new={}
        for t,c in cur.items():
            for k,d in v.items():
                kk=k if isinstance(k,tuple) else (k,)
                key,s=wedge_basis(t+kk)
                if s: new[key]=new.get(key,0)+s*c*d
        cur={k:c for k,c in new.items() if c!=0}
    return cur
def add(acc,el,c=1):
    for k,v in el.items(): acc[k]=acc.get(k,0)+c*v
def clean(d): return {k:v for k,v in d.items() if v!=0}
def derive(T,xi):  # xi: dict i -> sparse vector xi(e_i)
    out={}
    for t,c in T.items():
        for pos,i in enumerate(t):
            if i not in xi: continue
            for j,d in xi[i].items():
                key,s=wedge_basis(t[:pos]+(j,)+t[pos+1:])
                if s: out[key]=out.get(key,0)+s*c*d
    return clean(out)
def rank(vecs):
    rows=[dict(v) for v in vecs if v]; piv=[]; basis=[]
    r=0
    for v in rows:
        v=dict(v)
        for (pk,pv) in basis:
            if pk in v:
                f=v[pk]/pv[pk]
                for k,x in pv.items(): v[k]=v.get(k,0)-f*x
                v=clean(v)
        if v:
            pk=min(v); basis.append((pk,v))
    return len(basis)
def solve(M,B):  # exact M X = B, M square list of lists
    n=len(M); A=[ [Fr(x) for x in M[i]]+[Fr(x) for x in B[i]] for i in range(n)]
    m=len(B[0])
    for c in range(n):
        p=next(i for i in range(c,n) if A[i][c]!=0); A[c],A[p]=A[p],A[c]
        A[c]=[x/A[c][c] for x in A[c]]
        for i in range(n):
            if i!=c and A[i][c]!=0:
                f=A[i][c]; A[i]=[x-f*y for x,y in zip(A[i],A[c])]
    return [row[n:] for row in A]
def polarized_defs(hol,anti,omega):
    # omega: function (i,j)->coeff
    M=[[omega(h,a) for a in anti] for h in hol]
    out=[]
    for a,b in itertools.combinations_with_replacement(range(len(hol)),2):
        B=[[Fr(0)]*len(hol) for _ in hol]; B[a][b]=Fr(1); B[b][a]=Fr(1)
        X=solve(M,B)   # X[k][j]: coordinate of xi(hol_j) on anti_k  (omega(h_i, sum_k X[k][j] anti_k)=B[i][j])
        xi={}
        for j,y in enumerate(hol):
            v={anti[k]:X[k][j] for k in range(len(anti)) if X[k][j]!=0}
            if v: xi[y]=v
        out.append(xi)
    return out
def tangent(T,hol,anti,omega,label):
    defs=polarized_defs(hol,anti,omega)
    r=rank([derive(T,xi) for xi in defs])
    print(f"{label}: polarized deformation dim {len(defs)}, rank {r}, first-order Hodge locus dim {len(defs)-r}")
    return len(defs)-r
eps=lambda a,b: (a==0 and b==1)-(a==1 and b==0)
def bits(x): return ((x>>2)&1,(x>>1)&1,x&1)
def omV(x,y): a,b=bits(x),bits(y); return eps(a[0],b[0])*eps(a[1],b[1])*eps(a[2],b[2])
holV=[x for x in range(8) if bits(x)[0]==0]; antiV=[x for x in range(8) if bits(x)[0]==1]
# ---------- (a) Q_f on A x A ----------
# per-factor projectors on V_i (x) V_i : Pt = |e><e|/2 with e = e01 - e10 ; PS = 1 - Pt
def Pt(a2,b2,a,b): return Fr(eps(a2,b2)*eps(a,b),2)
def PS(a2,b2,a,b): return Fr(int(a2==a and b2==b))-Pt(a2,b2,a,b)
def factor_op(P3,x,y):  # image of e_x (x) e_y under (x)P_i : dict (x2,y2)->coeff
    out={}
    bx,by=bits(x),bits(y)
    for x2 in range(8):
        for y2 in range(8):
            b2x,b2y=bits(x2),bits(y2); v=Fr(1)
            for i in range(3):
                v*=P3[i](b2x[i],b2y[i],bx[i],by[i])
                if v==0: break
            if v: out[(x2,y2)]=v
    return out
f=[Fr(1),Fr(3),Fr(7)]   # generic distinct weights on q_1,q_2,q_3
qs=[(Pt,PS,PS),(PS,Pt,PS),(PS,PS,Pt)]
pairs=list(itertools.combinations(range(8),2))
def Q_on_wedge2(x,y,shift=0):  # Q(e_x ^ e_y) as wedge-2 element in copy with offset shift
    acc={}
    for fi,P3 in zip(f,qs):
        for (x2,y2),c in factor_op(P3,x,y).items(): acc[(x2,y2)]=acc.get((x2,y2),0)+fi*c
        for (x2,y2),c in factor_op(P3,y,x).items(): acc[(x2,y2)]=acc.get((x2,y2),0)-fi*c
    out={}
    for (x2,y2),c in acc.items():
        if c and x2<y2: out[(x2+shift,y2+shift)]=out.get((x2+shift,y2+shift),0)+c
    return clean(out)
# Gram of induced pairing on wedge^2 V and its inverse (dual basis)
def g2(p,q): return omV(p[0],q[0])*omV(p[1],q[1])-omV(p[0],q[1])*omV(p[1],q[0])
G=[[Fr(g2(p,q)) for q in pairs] for p in pairs]
Ginv=solve(G,[[Fr(int(i==j)) for j in range(28)] for i in range(28)])
T={}
for I,p in enumerate(pairs):
    Qb=Q_on_wedge2(*p,shift=0)
    dual={ (pairs[J][0]+8,pairs[J][1]+8):Ginv[I][J] for J in range(28) if Ginv[I][J]!=0}
    add(T,wedge(Qb,dual))
T=clean(T)
hol2=holV+[8+x for x in holV]; anti2=antiV+[8+x for x in antiV]
def om2(i,j):
    if i<8 and j<8: return omV(i,j)
    if i>=8 and j>=8: return omV(i-8,j-8)
    return 0
hs=set(hol2); print("Q_f: terms",len(T),"holomorphic-leg counts",sorted({sum(1 for i in t if i in hs) for t in T}))
tangent(T,hol2,anti2,om2,"Q_f on A x A")
Tl=wedge({(p[0],p[1]):Fr(omV(*p)) for p in pairs},{(p[0]+8,p[1]+8):Fr(omV(*p)) for p in pairs})
tangent(clean(Tl),hol2,anti2,om2,"sanity: theta_1 . theta_2 (Lefschetz)")
# only Q_f-type with all weights equal (= Lefschetz projector onto H^2_prim) for comparison
f=[Fr(1),Fr(1),Fr(1)]
T1={}
for I,p in enumerate(pairs):
    dual={ (pairs[J][0]+8,pairs[J][1]+8):Ginv[I][J] for J in range(28) if Ginv[I][J]!=0}
    add(T1,wedge(Q_on_wedge2(*p),dual))
tangent(clean(T1),hol2,anti2,om2,"sanity: q1+q2+q3 = projector on H^2_prim (Lefschetz)")
# ---------- (b) Phi on A x B ----------
# W = (+) W_rho, rho order: r1, r1b, r2, r2b, r3, r3b ; index 8 + 2*r + k
def wi(r,k): return 8+2*r+k
holB=[wi(0,0),wi(1,0),wi(2,0),wi(2,1),wi(5,0),wi(5,1)]
antiB=[i for i in range(8,20) if i not in holB]
def om3(i,j):
    if i<8 and j<8: return omV(i,j)
    if i>=8 and j>=8:
        ri,ki=divmod(i-8,2); rj,kj=divmod(j-8,2)
        if ri%2==0 and rj==ri+1: return eps(ki,kj)
        if rj%2==0 and ri==rj+1: return -eps(kj,ki)
    return 0
lam=Fr(3)
def Phi(x):
    a,b,c=bits(x)
    el=wedge({wi(0,a):Fr(1)},{wi(2,b):Fr(1)},{wi(4,c):Fr(1)})
    add(el,wedge({wi(1,a):Fr(1)},{wi(3,b):Fr(1)},{wi(5,c):Fr(1)}),lam)
    return clean(el)
# omega-dual basis of V: b^*_x with omega(b^*_x, e_y) = delta
Om=[[Fr(omV(i,j)) for j in range(8)] for i in range(8)]
OmTinv=solve([list(r) for r in zip(*Om)],[[Fr(int(i==j)) for j in range(8)] for i in range(8)])
T3={}
for x in range(8):
    bstar={j:OmTinv[j][x] for j in range(8) if OmTinv[j][x]!=0}
    add(T3,wedge(bstar,Phi(x)))
T3=clean(T3)
hol3=holV+holB; anti3=antiV+antiB; hs=set(hol3)
print("Phi: terms",len(T3),"holomorphic-leg counts",sorted({sum(1 for i in t if i in hs) for t in T3}))
tangent(T3,hol3,anti3,om3,"Phi on A x B")
