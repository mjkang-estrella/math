"""Bounded exact rational diagnostics; not mathematical gates."""
from fractions import Fraction as F
import json

def inertia(A):
    A=[[F(x) for x in r] for r in A];pos=neg=zero=0
    while A:
        n=len(A);i=next((i for i in range(n) if A[i][i]),None)
        if i is not None:
            order=[i]+[j for j in range(n) if j!=i]
            A=[[A[u][v] for v in order] for u in order];d=A[0][0]
            pos+=d>0;neg+=d<0
            A=[[A[u][v]-A[u][0]*A[0][v]/d for v in range(1,n)] for u in range(1,n)]
        else:
            pair=next(((i,j) for i in range(n) for j in range(i+1,n) if A[i][j]),None)
            if pair is None:zero+=n;break
            i,j=pair;order=[i,j]+[k for k in range(n) if k not in pair]
            A=[[A[u][v] for v in order] for u in order];a=A[0][1];pos+=1;neg+=1
            A=[[A[u][v]-(A[u][0]*A[1][v]+A[u][1]*A[0][v])/a for v in range(2,n)] for u in range(2,n)]
    return [pos,neg,zero]

def matmul(A,B):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]
checks=[]
for r in [F(2),F(5),F(13)]:
    c=(r+1/r)/2;h=(r-1/r)/2
    U=[[0,1,0,0],[0,0,0,1],[h,-c,0,0],[0,0,h,-c]]
    J=[-1,1,-1,1];G=[[sum(J[k]*u[k]*v[k] for k in range(4)) for v in U] for u in U]
    assert inertia(G)==[2,2,0]
    assert all(G[i][j]==0 for i,j in [(0,1),(1,2),(2,3),(3,0)])
    assert G[0][2]==G[1][3]==-c
    checks.append({'test':'two-plane-cycle','r':str(r),'inertia':inertia(G),'opposite':str(-c)})
for n in [4,6,8,10]:
    a=[F(1,2)]*(n//2)+[F(-1,2)]*(n//2)
    for t,target in [(F(0),[n-1,1,0]),(F(4,n+4),[n-2,1,1]),(F(1),[0,2,n-2])]:
        M=[[(1-t)*(i==j)-1-t*a[i]*a[j] for j in range(n)] for i in range(n)]
        assert all(M[i][j]<0 for i in range(n) for j in range(n) if i!=j)
        assert inertia(M)==target
        checks.append({'test':'interpolation','n':n,'t':str(t),'inertia':target})
for q in [3,4,5]:
    n=2*q;e=F(1,8)
    M=[[(i==j)-1 if i//q==j//q else -e for j in range(n)] for i in range(n)]
    assert inertia(M)==[n-2,2,0]
    for k in range(n):
        A=[[M[i][j] for j in range(n) if j!=k] for i in range(n) if i!=k]
        assert inertia(A)==[n-3,2,0]
    checks.append({'test':'single-deletion','q':q,'deletions':n,'negative-index':2})
# All 64 labelled simple graphs on four vertices, all three tested fibre sizes.
m=4;pairs=[(i,j) for i in range(m) for j in range(i+1,m)]
for mask in range(1<<len(pairs)):
    E={p for k,p in enumerate(pairs) if mask>>k&1};e=F(1,2*m)
    D=[[F(-1) if i==j else (-e if (min(i,j),max(i,j)) in E else F(0)) for j in range(m)] for i in range(m)]
    assert inertia(D)==[0,m,0]
    for s in [1,2,3]:
        M=[[D[i//s][j//s] for j in range(m*s)] for i in range(m*s)]
        assert inertia(M)==[0,m,m*(s-1)]
        for i in range(m*s):
            for j in range(i+1,m*s):
                edge=(i//s==j//s) or ((i//s,j//s) in E)
                assert (M[i][j]<0)==edge
        holes=[p for p in pairs if p not in E]
        if s>=2 and holes:
            u,v=holes[0];a=[1,-1]+[0]*(s-2);X=[[F(0) for _ in M] for _ in M]
            for i in range(s):
                for j in range(s):X[u*s+i][v*s+j]=X[v*s+j][u*s+i]=F(a[i]*a[j])
            assert any(x for row in X for x in row)
            assert not any(x for row in matmul(M,X) for x in row)
            assert all(X[i][j]==0 for i in range(m*s) for j in range(m*s) if i==j or M[i][j]<0)
checks.append({'test':'tensor-sign-inertia-and-SAP-witness','graphs':64,'fibre-sizes':[1,2,3],'instances':192})
print(json.dumps({'diagnostics':'all asserted exact rational identities hold','checks':checks},indent=2))
