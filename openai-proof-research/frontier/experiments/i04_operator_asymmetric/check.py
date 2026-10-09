"""Exact finite transcription/adversarial checks, not an infinite-dimensional proof.
No finite approximation of L is ever formed. Uses Python standard library only.
"""
from fractions import Fraction as F
from pathlib import Path
import json
OUT=Path(__file__).resolve().parent

def a(j,x):
    k=j if j>=0 else -j-1
    if k==0: return 10
    m=1
    while k>=8**m: m+=1
    N=2**m;t=x%N
    return 10*(k+1)+100*(N-2)+100*(t if j>=0 else N-1-t)

def logs(x,N):
    w={0:0};b={0:0}
    for j in range(N):
        w[j+1]=w[j]-a(j,x)
        b[j+1]=b[j]+a(j,x)-a(j-1,x+1)
    for j in range(-1,-N-1,-1):
        w[j]=w[j+1]+a(j,x)
        b[j]=b[j+1]-a(j,x)+a(j-1,x+1)
    return w,b
count=0
for x in range(-16,16):
    w,b=logs(x,1100);wp,_=logs(x+1,1101)
    for j in range(-1100,1101):
        assert b[j]+w[j]-wp[j-1]==-10
        count+=1
lower=[]
for m in range(1,6):
    N=2**m;n=8**m;x=N-1
    _,b=logs(x,n)
    K=700*(N-1)*8**(m-1)
    assert b[n]>=K
    lower.append(dict(m=m,coordinate=n,log_unnormalized=b[n],log_L_lower_bound=K))
cover=0
for n in range(2,513):
    m=n.bit_length()-1;N=2**m;K=700*(N-1)*8**(m-1)
    assert 64*K>=175*n**4
    for x in range(N):
        assert any((x-r)%N==N-1 for r in range(1,N+1))
        cover+=1

p={0:1};alpha=[];moments=0
for n in range(82):
    if n%2:
        m=(n-1)//2
        alpha.append(-p.get(-1,0)-sum(p.get(2*r+1,0)*alpha[r] for r in range(m)))
        assert p[n]==1
        assert p.get(-1,0)+sum(p.get(2*r+1,0)*alpha[r] for r in range(m+1))==0
        assert 1+sum(abs(v) for v in alpha)<=2**(m+1)*4**((m+1)**2)
    else:
        assert -1 not in p and not any(j%2 for j in p)
    moments+=1
    q={}
    for j,v in p.items():
        q[j+1]=q.get(j+1,0)+v
        q[j-1]=q.get(j-1,0)+(1 if j-1<=0 else 2)*v
    p=q

# Matrix-valued path operators: noncommuting base multipliers and C.
def zero(): return [[F(0) for _ in range(3)] for _ in range(3)]
def diag(v): return [[F(v[i]) if i==j else F(0) for j in range(3)] for i in range(3)]
I=diag([1]*3)
def add(A,B): return [[A[i][j]+B[i][j] for j in range(3)] for i in range(3)]
def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def tr(A): return [list(v) for v in zip(*A)]
def mv(A,v): return [sum(A[i][j]*v[j] for j in range(3)) for i in range(3)]
def av(v,w): return [a+b for a,b in zip(v,w)]
def power(A,n):
    B=I
    for _ in range(n): B=mul(A,B)
    return B
C=[[F(0),F(0),F(1,7)],[F(1,5),F(0),F(0)],[F(0),F(1,3),F(0)]]
def D(j): return diag([F(4+(j+k)%5,4) for k in range(3)])
def W(j): return diag([F(2+k)**(-j) for k in range(3)])
def Winv(j): return diag([F(2+k)**j for k in range(3)])
assert mul(C,D(1))!=mul(D(1),C)
paths=[{0:I}]
for n in range(22):
    nxt={}
    for j,B in paths[-1].items():
        nxt[j+1]=add(nxt.get(j+1,zero()),B)
        nxt[j-1]=add(nxt.get(j-1,zero()),mul(mul(D(j-1),C),B))
    paths.append(nxt)
path_dom=0
for n,P in enumerate(paths):
    for j,B in P.items():
        bound=power(C,(n-j)//2)
        assert all(0<=B[r][s]<=4**n*bound[r][s] for r in range(3) for s in range(3))
        path_dom+=1
matrix_moments=0;original_pairings=0;nonzero_outer_residuals=0
for gindex in range(3):
    g=[F(int(k==gindex)) for k in range(3)];z={-1:g}
    for n in range(1,20,2):
        P=paths[n];v=mv(tr(P[-1]),g)
        for j in range(1,n,2): v=av(v,mv(tr(P[j]),z[j]))
        z[n]=[-t for t in v]
    for n in range(21):
        total=[F(0)]*3
        for j,B in paths[n].items(): total=av(total,mv(tr(B),z.get(j,[F(0)]*3)))
        assert total==[0]*3;matrix_moments+=1
        for uindex in range(3):
            u=[F(int(k==uindex)) for k in range(3)];s=F(0)
            for j,B in paths[n].items():
                f=mv(W(j),mv(B,u));v=mv(Winv(j),z.get(j,[F(0)]*3))
                s+=sum(t*r for t,r in zip(f,v))
            assert s==0;original_pairings+=1
    residual=[F(0)]*3
    for j,B in paths[21].items(): residual=av(residual,mv(tr(B),z.get(j,[F(0)]*3)))
    assert any(residual);nonzero_outer_residuals+=1

# Constants controlling the two kernel recurrences. Rational upper bound on cube roots.
kchecks=0
for j in range(4096,20001):
    root=1
    # Cube-root bound j/128 works uniformly here by cubing, without floating point.
    assert j**3>=128**3*(j+2)
    assert F(25*j-510)-F(800*j,128)-2>1 # 2 log 2 < 2
    assert F(-25*j+655)+F(800*j,128)+2 < -1
    kchecks+=2

result=dict(unnormalized_all_index_identities=count,normalizer_lower_bounds=lower,
    residue_cover_checks=cover,scalar_orbit_moments=moments,alpha_first_20=alpha[:20],
    noncommuting_path_domination_checks=path_dom,matrix_orbit_moments=matrix_moments,
    original_weighted_pairings=original_pairings,deliberate_truncation_residuals=nonzero_outer_residuals,
    kernel_bound_checks=kchecks,finite_normalization_used=False,
    scope='Finite transcription checks only; convergence, properness, invariance and empty point spectra require the report proofs.')
(OUT/'output.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
