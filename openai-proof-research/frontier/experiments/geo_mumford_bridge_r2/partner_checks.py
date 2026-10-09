"""Finite checks for the split-partner theorem (review Theorem P).
(1) Hodge types of the 8 'one-from-each-sigma' tensor pieces W_{r1}(x)W_{r2}(x)W_{r3} of H^3(B):
    only the two K-coherent choices are of level one.
(2) Trace-transfer discriminant identity det Tr_{F/Q}(beta f_k f_l) = N(beta) * det Tr(f_k f_l)
    for F = Q(zeta_7)^+ (min poly x^3+x^2-2x-1), random beta; hence disc(Tr_* <a1,a2>) = N(a1 a2) mod squares.
Run: python3 -I partner_checks.py"""
import itertools, random
from fractions import Fraction as Fr
# (1) eigenspace Hodge numbers (p,q) per embedding: rho_i extends sigma_i and restricts to tau on K
hodge={('r',1):(1,1),('r',2):(2,0),('r',3):(0,2),('b',1):(1,1),('b',2):(0,2),('b',3):(2,0)}
def types(choice):
    # each 2-dim piece: list of types of basis vectors
    tl=[]
    for c,i in zip(choice,(1,2,3)):
        p,q=hodge[(c,i)]; tl.append([(1,0)]*p+[(0,1)]*q)
    out={}
    for vs in itertools.product(*tl):
        t=(sum(v[0] for v in vs),sum(v[1] for v in vs)); out[t]=out.get(t,0)+1
    return out
for choice in itertools.product('rb',repeat=3):
    t=types(choice); lvl1=set(t)<= {(2,1),(1,2)}
    print(''.join(choice), dict(sorted(t.items())), "level one" if lvl1 else "")
# (2) arithmetic in F = Q[x]/(x^3+x^2-2x-1)
def mul(a,b):
    c=[Fr(0)]*5
    for i in range(3):
        for j in range(3): c[i+j]+=a[i]*b[j]
    for k in (4,3):   # x^3 = -x^2+2x+1
        t=c[k]; c[k]=0; c[k-1]+=-t; c[k-2]+=2*t; c[k-3]+=t
    return c[:3]
def mat(a):  # multiplication matrix
    cols=[mul(a,e) for e in ([Fr(1),0,0],[0,Fr(1),0],[0,0,Fr(1)])]
    return [[cols[j][i] for j in range(3)] for i in range(3)]
def tr(a): m=mat(a); return m[0][0]+m[1][1]+m[2][2]
def det3(m): return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])-m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])+m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
E=[[Fr(1),0,0],[0,Fr(1),0],[0,0,Fr(1)]]
dF=det3([[tr(mul(E[k],E[l])) for l in range(3)] for k in range(3)])
print("disc of trace form of Q(zeta7)^+ :",dF,"(expected 49)")
random.seed(0)
for _ in range(5):
    beta=[Fr(random.randint(-9,9)) for _ in range(3)]
    if det3(mat(beta))==0: continue
    lhs=det3([[tr(mul(beta,mul(E[k],E[l]))) for l in range(3)] for k in range(3)])
    print("beta",[int(x) for x in beta],"det Tr(beta f f) =",lhs," N(beta)*dF =",det3(mat(beta))*dF, lhs==det3(mat(beta))*dF)
