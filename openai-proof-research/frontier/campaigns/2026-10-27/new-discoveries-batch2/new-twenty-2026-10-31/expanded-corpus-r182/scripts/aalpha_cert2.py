# Clean integer certificate for 351804 at alpha=1/4: B = 4*A_alpha = diag(outdeg) + 3*Adj.
from fractions import Fraction as F
n=5
Gstar=[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0)]
G =Gstar+[(0,4)]   # out-star (single pendant 4) hung on vertex 0 (G*-outdegree 2)
G2=Gstar+[(1,4)]   # G'': all n-m=1 pendant vertices on v1=1, the unique max G*-outdegree vertex (3)
def B(arcs):
    d=[sum(1 for (u,v) in arcs if u==i) for i in range(n)]
    return [[3*((i,j) in arcs)+(d[i] if i==j else 0) for j in range(n)] for i in range(n)]
def det(M):
    M=[[F(x) for x in r] for r in M]; N=len(M); s=F(1)
    for c in range(N):
        p=next((r for r in range(c,N) if M[r][c]!=0),None)
        if p is None: return F(0)
        if p!=c: M[c],M[p]=M[p],M[c]; s=-s
        s*=M[c][c]
        for r in range(c+1,N):
            f=M[r][c]/M[c][c]
            for k in range(c,N): M[r][k]-=f*M[c][k]
    return s
cp=lambda M,t: det([[(t if i==j else 0)-M[i][j] for j in range(n)] for i in range(n)])
BG,BG2=B(G),B(G2)
print('B(G)  =',BG); print('B(G2) =',BG2)
# check char polys against closed forms
for t in range(-3,10):
    assert cp(BG,t)==t*(t**4-8*t**3+4*t**2-24*t+27)
    assert cp(BG2,t)==t*(t**4-8*t**3+3*t**2-13*t+17)
print('charpoly(B(G))  = s(s^4-8s^3+4s^2-24s+27)'); print('charpoly(B(G2)) = s(s^4-8s^3+3s^2-13s+17)')
c=F(781,100)
print('charpoly(B(G))(781/100) =',cp(BG,c),'<0:',cp(BG,c)<0)
x=[671,1000,296,296,1]
r=[F(sum(BG2[i][j]*x[j] for j in range(n)),x[i]) for i in range(n)]
print('Collatz-Wielandt ratios for B(G2) with x =',x,':',[str(v) for v in r],'max =',float(max(r)),' < 781/100:',max(r)<c)
print('=> rho_{1/4}(G) > 781/400 > rho_{1/4}(G\'\')')
# sanity: membership facts
import itertools
def reach(arcs,s):
    S={s};st=[s]
    while st:
        u=st.pop()
        for (a,b) in arcs:
            if a==u and b not in S:S.add(b);st.append(b)
    return S
for arcs,name in [(G,'G'),(G2,"G''")]:
    comps={frozenset(v for v in range(n) if u in reach(arcs,v) and v in reach(arcs,u)) for u in range(n)}
    print(name,'strong components:',sorted(map(sorted,comps)),' strongly connected:',len(comps)==1)
print("G* outdegrees:",[sum(1 for (u,v) in Gstar if u==i) for i in range(4)])
print('theorem threshold d1/(d1+n-m-n1+1) for G =',F(3,3+5-4-1+1))
