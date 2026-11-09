# Exact certificate for 351804: G* on {0,1,2,3}: 0->1,0->2,1->0,1->2,1->3,2->0,3->0 ; pendant 4.
# G : pendant arc 0->4 (out-star at v_j=0, outdegree 2).  G'': pendant arc 1->4 (v1 = 1, unique max outdegree 3).
from fractions import Fraction as F
import itertools
n=5
Gs=[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0)]
def amat(arcs,a):
    d=[sum(1 for (u,v) in arcs if u==i) for i in range(n)]
    return [[(1-a)*(1 if (i,j) in arcs else 0)+(a*d[i] if i==j else 0) for j in range(n)] for i in range(n)],d
def det(M):
    M=[r[:] for r in M]; N=len(M); s=F(1)
    for c in range(N):
        p=next((r for r in range(c,N) if M[r][c]!=0),None)
        if p is None: return F(0)
        if p!=c: M[c],M[p]=M[p],M[c]; s=-s
        s*=M[c][c]
        for r in range(c+1,N):
            f=M[r][c]/M[c][c]
            for k in range(c,N): M[r][k]-=f*M[c][k]
    return s
def charpoly_at(M,t): return det([[ (t if i==j else 0)-M[i][j] for j in range(n)] for i in range(n)])
def charpoly_coeffs(M):
    # interpolate degree-5 monic poly from 6 points
    pts=[F(k) for k in range(6)]; vals=[charpoly_at(M,p) for p in pts]
    # Lagrange -> coefficients
    co=[F(0)]*6
    for i,xi in enumerate(pts):
        num=[F(1)]; den=F(1)
        for j,xj in enumerate(pts):
            if j==i: continue
            num=[ (num[k-1] if k>0 else 0) - xj*(num[k] if k<len(num) else 0) for k in range(len(num)+1)]
            den*=xi-xj
        for k in range(6): co[k]+=vals[i]*num[k]/den
    return co
def perron_float(M,its=5000):
    x=[1.0]*n
    for _ in range(its):
        y=[sum(float(M[i][j])*x[j] for j in range(n)) for i in range(n)]; s=max(y); x=[v/s for v in y]
    return s,x
for a in [F(1,4),F(1,5),F(1,10)]:
    G=Gs+[(0,4)]; G2=Gs+[(1,4)]
    M,d=amat(G,a); M2,d2=amat(G2,a)
    rG,xG=perron_float(M); rG2,xG2=perron_float(M2)
    print('alpha',a,'outdeg G',d,'outdeg G2',d2,'rho(G)~',rG,'rho(G2)~',rG2,'diff',rG-rG2)
    # separating rational c: midpoint rounded
    c=F(round((rG+rG2)/2*10**6),10**6)
    # lower bound for G: charpoly(c) < 0 => real eigenvalue > c
    pc=charpoly_at(M,c); print('  c =',c,' charpoly_G(c) =',pc,'(<0 needed)', pc<0)
    # upper bound for G2: positive rational x with (M2 x)_i <= c' x_i, c' < c
    x=[F(round(v*10**6),10**6) if v>1e-9 else F(1,10**6) for v in xG2]
    ratios=[sum(M2[i][j]*x[j] for j in range(n))/x[i] for i in range(n)]
    print('  CW upper ratios for G2:',[float(r) for r in ratios],'max<c:',max(ratios)<c)
    print('  charpoly G coeffs (low->high):',charpoly_coeffs(M))
    print('  charpoly G2 coeffs:',charpoly_coeffs(M2))
    print('  x (G2 weight vector) =',x)
