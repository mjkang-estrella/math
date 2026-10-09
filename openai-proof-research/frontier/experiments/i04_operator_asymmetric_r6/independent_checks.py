"""Round 6 exact finite tests. No finite replacement for the actual L.
Complex model calculations use Gaussian rationals, not floating-point tolerances.
The model checks transcription only; they cannot prove infinite norm convergence.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[2]
@dataclass(frozen=True)
class G:
    r:F=F(0)
    i:F=F(0)
    def __add__(a,b):
        if not isinstance(b,G):b=G(F(b))
        return G(a.r+b.r,a.i+b.i)
    __radd__=__add__
    def __neg__(a):return G(-a.r,-a.i)
    def __sub__(a,b):return a+-b
    def __mul__(a,b):
        if not isinstance(b,G):b=G(F(b))
        return G(a.r*b.r-a.i*b.i,a.r*b.i+a.i*b.r)
    __rmul__=__mul__
    def conj(a):return G(a.r,-a.i)
    def abs2(a):return a.r*a.r+a.i*a.i
D=4
Z=tuple(tuple(G() for _ in range(D)) for _ in range(D))
def diag(xs):return tuple(tuple(xs[i] if i==j else G() for j in range(D)) for i in range(D))
I=diag([G(F(1))]*D)
def add(A,B):return tuple(tuple(A[i][j]+B[i][j] for j in range(D)) for i in range(D))
def neg(A):return tuple(tuple(-x for x in row) for row in A)
def mm(A,B):return tuple(tuple(sum((A[i][k]*B[k][j] for k in range(D)),G()) for j in range(D)) for i in range(D))
def adj(A):return tuple(tuple(A[j][i].conj() for j in range(D)) for i in range(D))
def scale(A,c):return tuple(tuple(c*x for x in row) for row in A)
def power(A,n):
    R=I
    for _ in range(n):R=mm(R,A)
    return R
def dominated(A,B):
    return all(B[i][j].i==0 and B[i][j].r>=0 and A[i][j].abs2()<=B[i][j].r**2 for i in range(D) for j in range(D))
C=tuple(tuple(G(F(1,2*i+5)) if j==(i-1)%D else G() for j in range(D)) for i in range(D))
Cstar=adj(C)
Cpow=[power(C,n) for n in range(23)]
Cspow=[adj(v) for v in Cpow]
def W(j,inverse=False):
    vals=[F(1)]*D if j==0 else [F(5+(j+2*k)%7,5) for k in range(D)]
    return diag([G(1/v if inverse else v) for v in vals])
models={
 'zero':(0,lambda j,k:G()),
 'exact_asymmetric':(2,lambda j,k:G(F(1 if j<=0 else 2))),
 'constant_imaginary':(1,lambda j,k:G(F(0),F(1))),
 'coordinate_zeros':(2,lambda j,k:G() if j%3==0 else G(F(-2 if j%2 else 1))),
 'base_zeros_phases':(1,lambda j,k:[G(),G(F(1)),G(F(0),F(-1)),G(F(3,5),F(4,5))][(j+2*k)%4]),
 'base_coordinate_complex':(3,lambda j,k:G(F((2*j+3*k)%5-2),F((j-k)%5-2))),
 'small_complex':(F(1,2),lambda j,k:G(F(1 if k%2==0 else -1,5),F(1 if j%2==0 else -1,5)))
}
counts=dict(path_operator_bounds=0,adjoint_path_operator_bounds=0,triangular_Z_bounds=0,
            annihilator_operator_identities=0,original_coordinate_operator_pairings=0,
            original_coordinate_orbits=0,wrong_order_witnesses=0,wrong_conjugation_witnesses=0)
records=[]
for name,(B,coefficient) in models.items():
    R=lambda j:diag([coefficient(j,k) for k in range(D)])
    K=2*max(1,B)
    assert all(coefficient(j,k).abs2()<=B*B for j in range(-24,25) for k in range(D))
    noncommutes=any(mm(R(j),C)!=mm(C,R(j)) for j in range(-4,5))
    paths=[{0:I}];original=[{0:I}]
    for n in range(22):
        nxt={};onxt={}
        for j,A in paths[-1].items():
            nxt[j+1]=add(nxt.get(j+1,Z),A)
            nxt[j-1]=add(nxt.get(j-1,Z),mm(mm(R(j-1),C),A))
        for j,A in original[-1].items():
            forward=mm(W(j+1),W(j,True))
            backward=mm(mm(mm(W(j-1),R(j-1)),C),W(j,True))
            onxt[j+1]=add(onxt.get(j+1,Z),mm(forward,A))
            onxt[j-1]=add(onxt.get(j-1,Z),mm(backward,A))
        paths.append(nxt);original.append(onxt)
    for n,P in enumerate(paths):
        assert P[n]==I
        for j,A in P.items():
            q=(n-j)//2
            assert dominated(A,scale(Cpow[q],K**n))
            assert dominated(adj(A),scale(Cspow[q],K**n))
            assert original[n][j]==mm(W(j),A)
            counts['path_operator_bounds']+=1
            counts['adjoint_path_operator_bounds']+=1
            counts['original_coordinate_orbits']+=1
    z={-1:I};oldA=1
    for m in range(11):
        n=2*m+1;P=paths[n]
        rhs=adj(P[-1])
        for j in range(1,n,2):rhs=add(rhs,mm(adj(P[j]),z[j]))
        z[n]=neg(rhs)
        c=K**n*oldA;newA=(1+K**n)*oldA
        assert c==newA-oldA
        assert newA<=2**(m+1)*K**((m+1)**2)
        assert dominated(z[n],scale(Cspow[m+1],c))
        counts['triangular_Z_bounds']+=1
        oldA=newA
    for n in range(23):
        total=Z;weighted=Z
        for j,A in paths[n].items():
            zj=z.get(j,Z)
            total=add(total,mm(adj(A),zj))
            weighted=add(weighted,mm(adj(original[n][j]),mm(W(j,True),zj)))
        assert total==Z and weighted==Z
        counts['annihilator_operator_identities']+=1
        counts['original_coordinate_operator_pairings']+=1
    if name=='zero':assert all(zj==Z for j,zj in z.items() if j!=-1)
    order_failure=adj(mm(R(-1),C))!=mm(adj(R(-1)),Cstar)
    wrong_conjugation=adj(mm(R(-1),C))!=tuple(tuple(mm(R(-1),C)[j][i] for j in range(D)) for i in range(D))
    counts['wrong_order_witnesses']+=int(order_failure)
    counts['wrong_conjugation_witnesses']+=int(wrong_conjugation)
    records.append(dict(name=name,B=str(B),K=str(K),noncommuting=noncommutes,wrong_order_detected=order_failure,missing_conjugation_detected=wrong_conjugation))
assert counts['wrong_order_witnesses'] and counts['wrong_conjugation_witnesses']

# Exact all-index logarithmic recurrence, independently oriented from source.
def aval(j,x):
    k=j if j>=0 else -j-1
    if k==0:return 10
    m=1
    while 8**m<=k:m+=1
    residue=x%(2**m)
    return 10*(k+1)+100*(2**m-2)+100*(residue if j>=0 else 2**m-1-residue)
def logw(x,N):
    w={0:0}
    for j in range(N):w[j+1]=w[j]-aval(j,x)
    for j in range(-1,-N-1,-1):w[j]=w[j+1]+aval(j,x)
    return w
identities=0;inverse_bound_checks=0
for x in range(-8,9):
    N=4200;w=logw(x,N+1);wp=logw(x+1,N+2);b={0:0}
    for j in range(N):b[j+1]=b[j]+aval(j,x)-aval(j-1,x+1)
    for j in range(-1,-N-1,-1):b[j]=b[j+1]-aval(j,x)+aval(j-1,x+1)
    for j in range(-N,N+1):
        assert b[j]+w[j]-wp[j-1]==-10;identities+=1
    for j in range(1,N+1):
        assert -w[j]<=410*j*j;inverse_bound_checks+=1
# Check full range residues once for each dyadic scale, with every extremal length.
cover_checks=0
for m in range(1,14):
    N=2**m;Km=700*(N-1)*8**(m-1)
    for n in (N,2*N-1):
        assert 64*Km>=175*n**4
        for x in range(N):
            r=(x+1)%N or N
            assert 1<=r<=N<=n and (x-r)%N==N-1
            cover_checks+=1
# Integer cube bounds independently imply eventual kernel signs for all j>=4096:
# j^2>=4096^2>2*128^3 and j+2<=2*j, hence (j/128)^3>=j+2.
assert 4096**2>2*128**3
assert F(25)-F(800,128)>0
assert (F(25)-F(800,128))*4096-512>1
assert -(F(25)-F(800,128))*4096+657<-1
assert F(640000,9)*F(80,27)<460**2
assert F(46)+F(564**2,74)<5000
# Compare reproduction byte-for-byte.
author=ROOT/'frontier/experiments/i04_operator_asymmetric'
assert (OUT/'reproduce_original.py').read_bytes()==(author/'check.py').read_bytes()
assert (OUT/'output.json').read_bytes()==(author/'output.json').read_bytes()
result=dict(models=records,counts=counts,all_index_log_identities=identities,
 inverse_weight_bound_checks=inverse_bound_checks,dyadic_cover_checks=cover_checks,
 reproduced_script_and_output_byte_identical=True,original_output_sha256=hashlib.sha256((OUT/'output.json').read_bytes()).hexdigest(),
 finite_normalizer_used=False,passed=True,
 scope='Exact finite algebra/transcription and elementary rational constant checks only. Synthetic cyclic C is not the actual infinite-base C and does not establish its decay or convergence.')
(OUT/'independent_output.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
