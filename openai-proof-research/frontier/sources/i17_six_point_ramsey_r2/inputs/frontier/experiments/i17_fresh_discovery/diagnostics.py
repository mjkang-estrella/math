"""Exact finite diagnostics for the universal local certificate in the I17 report.
Standard library only. These evaluations supplement, and do not replace, the proof.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import json, random
OUT=Path(__file__).resolve().parent

def solve(M,b):
    n=len(M); a=[list(row)+[v] for row,v in zip(M,b)]
    for j in range(n):
        p=next((i for i in range(j,n) if a[i][j]),None)
        if p is None: raise ZeroDivisionError('singular matrix')
        a[j],a[p]=a[p],a[j];d=a[j][j];a[j]=[x/d for x in a[j]]
        for i in range(n):
            if i!=j:
                d=a[i][j];a[i]=[x-d*y for x,y in zip(a[i],a[j])]
    return [a[i][-1] for i in range(n)]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def det(M):
    a=[list(r) for r in M];d=Q(1);n=len(a)
    for j in range(n):
        p=next((i for i in range(j,n) if a[i][j]),None)
        if p is None:return Q(0)
        if p!=j:a[j],a[p]=a[p],a[j];d=-d
        v=a[j][j];d*=v
        for i in range(j+1,n):
            c=a[i][j]/v
            for k in range(j+1,n):a[i][k]-=c*a[j][k]
    return d

def h(t,u):return [Q(1),(t+u)/2,t*u,t*u*(t+u)/2,t*t*u*u]
def a(t,u):return [u-t,u*u-t*t,t*u*(u-t)]
def J(t,u):return (u-t)**2

def residuals(T,U):
    H=[h(t,u) for t,u in zip(T,U)]
    fs=[a(t,u)+[J(t,u)] for t,u in zip(T,U)]
    out=[]
    for j in range(4):
        d=solve(H[:5],[v[j] for v in fs[:5]])
        out.append(fs[5][j]-dot(H[5],d))
    return out

def mobius(T,U):
    aa,bb,cc=solve([[t,Q(1),-t*u] for t,u in zip(T[:3],U[:3])],U[:3])
    return [(aa*t+bb)/(cc*t+1) for t in T]

def certificate(T,U):
    V=mobius(T,U);assert V[:3]==U[:3]
    prev=V[:];rprev=residuals(T,prev);assert rprev==[0]*4
    columns=[]
    for k in range(3,6):
        curr=prev[:];curr[k]=U[k]
        v=U[k]-V[k]
        if not v:raise ZeroDivisionError('removable divided difference at selected point')
        rcurr=residuals(T,curr)
        columns.append([(x-y)/v for x,y in zip(rcurr,rprev)])
        prev=curr;rprev=rcurr
    A=[[columns[k][j] for k in range(3)] for j in range(3)]
    b=[columns[k][3] for k in range(3)]
    c=solve(list(map(list,zip(*A))),b)
    rs=residuals(T,U);assert rs[3]==dot(c,rs[:3])
    pv=[J(t,u)-dot(c,a(t,u)) for t,u in zip(T,U)]
    d=solve([h(t,u) for t,u in zip(T[:5],U[:5])],pv[:5])
    errors=[J(t,u)-dot(c,a(t,u))-dot(d,h(t,u)) for t,u in zip(T,U)]
    assert errors==[0]*6
    # Monomial coefficient matrix for Q(x,y)=J - c.a - d.h.
    K=[[Q(0) for _ in range(3)] for _ in range(3)]
    K[0][2]=1;K[1][1]=-2;K[2][0]=1
    K[0][1]-=c[0];K[1][0]+=c[0]
    K[0][2]-=c[1];K[2][0]+=c[1]
    K[1][2]-=c[2];K[2][1]+=c[2]
    K[0][0]-=d[0];K[0][1]-=d[1]/2;K[1][0]-=d[1]/2
    K[1][1]-=d[2];K[1][2]-=d[3]/2;K[2][1]-=d[3]/2;K[2][2]-=d[4]
    for t,u in zip(T,U):assert sum(K[i][j]*t**i*u**j for i in range(3) for j in range(3))==0
    return dict(c=list(map(str,c)),d=list(map(str,d)),matrix=[[str(x) for x in row] for row in K],residuals=list(map(str,rs)),det_A=str(det(A)))

def tangent(T):
    # Exact diagonal derivative of the 4 residuals; J derivative is zero.
    H=[[t**j for j in range(5)] for t in T]
    weights=[-v for v in solve(list(map(list,zip(*H[:5]))),H[5])]+[Q(1)]
    polyprime=[product_value(t-s for s in T if s!=t) for t in T]
    assert weights==[polyprime[5]/x for x in polyprime]
    A=[[weights[k]*f(T[k]) for k in range(3,6)] for f in (lambda t:Q(1),lambda t:2*t,lambda t:t*t)]
    predicted=2*product_value(weights[3:])*product_value(T[j]-T[i] for i,j in combinations(range(3,6),2))
    assert det(A)==predicted and predicted
    return str(predicted)
def product_value(it):
    out=Q(1)
    for x in it:out*=x
    return out

def seven_residual_obstruction():
    # For seven nodes, degree-4 interpolation leaves two relations.
    # A cubic velocity produces a quadratic obstruction, unlike six.
    T=list(map(Q,range(7)));lam=[1/product_value(t-s for s in T if s!=t) for t in T]
    g=[t*(t-1)*(t-2) for t in T]
    assert all(sum(l*t**j for l,t in zip(lam,T))==0 for j in range(6))
    energy=sum(l*v*v for l,v in zip(lam,g));assert energy==1
    return {'nodes':list(map(str,T)),'velocity':list(map(str,g)),'weighted_square':str(energy),'meaning':'Comparison with known generic-seven obstruction; not a new seven-point result.'}

def checksum_obstruction():
    # Two equal weights 3^j per block; target sum 3^j. Exactly one per block.
    counts={}
    for k in range(1,6):
        weights=[3**j for j in range(k) for _ in range(2)];tar=sum(3**j for j in range(k))
        solutions=[v for v in product((0,1),repeat=2*k) if dot(weights,v)==tar]
        assert len(solutions)==2**k
        sums={}
        for x in solutions:
            for y in solutions:
                z=tuple(a+b for a,b in zip(x,y));sums[z]=sums.get(z,0)+1
        energy=sum(v*v for v in sums.values());assert energy==6**k
        counts[str(k)]={'solutions':len(solutions),'additive_energy':energy,'relative_variance':str(Q(energy,len(solutions)**2)-1)}
    return counts

def main():
    rng=random.Random(1720261009);passed=0;skipped=0;examples=[];tangents=[]
    for trial in range(140):
        T=[Q(x) for x in rng.sample(range(-20,21),6)]
        U=[t+Q(rng.randrange(-8,9),37) for t in T]
        tangents.append(tangent(T))
        try:r=certificate(T,U)
        except ZeroDivisionError:skipped+=1;continue
        passed+=1
        if len(examples)<3:examples.append({'T':list(map(str,T)),'U':list(map(str,U)),**r})
    assert passed>=100
    # Circle-coordinate change, tested exactly independently of basis assembly.
    L=[[Q(1),0,1],[1,0,-1],[0,2,0]];S=[-1,1,1]
    LS=[[sum(L[k][i]*S[k]*L[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    assert LS==[[0,0,-2],[0,4,0],[-2,0,0]]
    data={'status':'PASS','rational_certificate_evaluations':passed,'excluded_singular_or_removable_evaluation_points':skipped,'diagonal_jacobian_checks':len(tangents),'examples':examples,'seven_point_comparison':seven_residual_obstruction(),'phase_counting_obstruction':checksum_obstruction(),'scope':'Exact finite identities only; general local-ring lift is proved in report.'}
    (OUT/'diagnostics.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps({k:v for k,v in data.items() if k not in ('examples','phase_counting_obstruction')},indent=2))
if __name__=='__main__':main()
