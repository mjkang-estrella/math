#!/usr/bin/env python3
"""Package-free exact supporting checks; not the analytical theorem proof."""
from fractions import Fraction as F
from pathlib import Path
import json

# Q(sqrt(2),sqrt(7),i), square factors in bit order.
class Q:
    def __init__(self,x=0):
        self.a=x.a if isinstance(x,Q) else ((F(x),)+(F(0),)*7)
    @staticmethod
    def b(k):
        q=Q(); q.a=tuple(F(j==k) for j in range(8)); return q
    def __add__(self,o):
        o=Q(o); q=Q(); q.a=tuple(a+b for a,b in zip(self.a,o.a)); return q
    __radd__=__add__
    def __neg__(self):
        q=Q();q.a=tuple(-a for a in self.a);return q
    def __sub__(self,o):return self+-Q(o)
    def __rsub__(self,o):return Q(o)+-self
    def __mul__(self,o):
        o=Q(o);v=[F(0)]*8
        for j,a in enumerate(self.a):
            for k,b in enumerate(o.a):
                fac=1
                for bit,square in enumerate((2,7,-1)):
                    if (j&k)&(1<<bit):fac*=square
                v[j^k]+=a*b*fac
        q=Q();q.a=tuple(v);return q
    __rmul__=__mul__
    def __truediv__(self,n):return self*F(1,n)
    def conj(self):
        q=Q();q.a=tuple(-a if k&4 else a for k,a in enumerate(self.a));return q
    def __eq__(self,o):return self.a==Q(o).a
    def __repr__(self):return str(self.a)

r2,r7,ii=Q.b(1),Q.b(2),Q.b(4)
def zero(n,m):return [[Q() for _ in range(m)] for _ in range(n)]
def ident(n):return [[Q(j==k) for k in range(n)] for j in range(n)]
def trans(A):return [list(r) for r in zip(*A)]
def conj(A):return [[x.conj() for x in r] for r in A]
def star(A):return trans(conj(A))
def mm(A,B):return [[sum((a*b for a,b in zip(row,col)),Q()) for col in zip(*B)] for row in A]
def sc(A,s):return [[x*s for x in row] for row in A]
def add(A,B):return [[a+b for a,b in zip(row,col)] for row,col in zip(A,B)]
def eq(A,B):return A==B

def poly_mm(A,B):
    out={}
    for k,a in A.items():
        for l,b in B.items():out[k+l]=add(out.get(k+l,zero(len(a),len(b[0]))),mm(a,b))
    return {k:a for k,a in out.items() if a!=zero(len(a),len(a[0]))}
def ptrans(A):return {k:trans(v) for k,v in A.items()}
def pconj_circle(A):return {-k:conj(v) for k,v in A.items()}
def peq(A,B):
    keys=set(A)|set(B)
    for k in keys:
        sample=A.get(k,B.get(k));z=zero(len(sample),len(sample[0]))
        if A.get(k,z)!=B.get(k,z):return False
    return True

checks={}
def ck(name,condition):
    if not condition:raise AssertionError(name)
    checks[name]=True

N=zero(6,6)
for j,k,v in [(0,1,Q(F(6,5))),(0,3,r2*r7/5),(1,2,Q(F(8,5))),(3,2,-r2*r7*F(3,20)),(3,4,Q(F(5,4))),(4,5,r2)]:N[j][k]=v
X=zero(6,2); X[2][0]=r2/2;X[5][1]=r2/2
Y=zero(6,2);Y[0][0]=r2/2;Y[1][1]=r2*r7/10;Y[3][1]=Q(F(-3,5))
S=mm(star(X),X);T=mm(star(Y),Y)
ck('rank_two_S_half_identity',S==sc(ident(2),F(1,2)))
ck('rank_two_T_half_identity',T==S)
ck('orthogonal_base_Schmidt_spaces',mm(star(Y),X)==zero(2,2))
Nk=ident(6);C={};diag={};diagY={};back={}
for k in range(4):
    C[-k-1]=mm(mm(star(Y),Nk),X)
    diag[-k-1]=mm(mm(star(X),Nk),X)
    diagY[-k-1]=mm(mm(star(Y),Nk),Y)
    back[-k-1]=mm(mm(star(X),Nk),Y)
    Nk=mm(Nk,N)
ck('nilpotency_four',Nk==zero(6,6))
ck('constant_diagonal_resolvent_X',peq(diag,{-1:S}))
ck('constant_diagonal_resolvent_Y',peq(diagY,{-1:S}))
ck('backward_resolvent_zero',peq(back,{}))
# r(z)=1/z, so original mathcal M=C/r=z C.
M={k+1:v for k,v in C.items()}
Fpol={1:[[Q(),Q()],[r7/4,Q()]],2:[[Q(F(3,4)),Q()],[Q(),Q(F(-3,4))]],3:[[Q(),r7/4],[Q(),Q()]]}
ck('constant_ordered_test_conjugation',peq({k:sc(v,F(1,2)) for k,v in Fpol.items()},{k:sc(v,F(1,2)) for k,v in pconj_circle(M).items()}))
Qpol=ptrans(M)
ck('rational_exterior_inverse',peq(poly_mm(Fpol,Qpol),{0:ident(2)}))
ck('vanishing_inverse_at_infinity',all(k<0 or v==zero(2,2) for k,v in Qpol.items()))
# Non-real coefficient basis changes challenge conjugation and transpose.
U=[[ii,Q()],[Q(),Q(1)]];V=[[Q(),Q(1)],[ii,Q()]]
Fp={k:mm(mm(V,v),star(U)) for k,v in Fpol.items()}
Mp={k:mm(mm(conj(V),v),trans(U)) for k,v in M.items()}
ck('complex_basis_ordered_identity',peq(Fp,pconj_circle(Mp)))
ck('complex_basis_transpose_inverse',peq(poly_mm(Fp,ptrans(Mp)),{0:ident(2)}))
ck('mutation_adjoint_instead_of_transpose_detected',not peq(poly_mm(Fp,{k:star(v) for k,v in Mp.items()}),{0:ident(2)}))
ck('mutation_missing_half_detected',not peq(Fpol,{k:sc(v,2) for k,v in pconj_circle(M).items()}))
# Finite exact Markov variance identity using normalized counting measure.
K=[[F(3,2),F(1,2)],[F(1,2),F(3,2)]];u=[F(1),F(-1)]
Tu=[sum(K[a][b]*u[a] for a in range(2))/2 for b in range(2)]
delta=sum(x*x for x in u)/2-sum(x*x for x in Tu)/2
variance=sum(K[a][b]*K[c][b]*(u[a]-u[c])**2 for a in range(2) for b in range(2) for c in range(2))/8
ck('normalized_Markov_variance_identity',variance==2*delta==F(3,2))
ck('mutation_variance_missing_two_detected',variance!=delta)
# Exact Laurent determinant of the R019 restricted polynomial is -z^4.
def scalar_product(A,B):
    out={}
    for k,a in A.items():
        for l,b in B.items():out[k+l]=out.get(k+l,Q())+a*b
    return {k:v for k,v in out.items() if v!=0}
def entry(P,j,k):return {e:v[j][k] for e,v in P.items() if v[j][k]!=0}
a=scalar_product(entry(Fpol,0,0),entry(Fpol,1,1));b=scalar_product(entry(Fpol,0,1),entry(Fpol,1,0))
det={k:a.get(k,Q())-b.get(k,Q()) for k in set(a)|set(b)}
ck('determinant_channel_R019_minus_z4',det=={4:Q(-1)})
result={'status':'PASS','arithmetic':'exact Fraction field Q(sqrt(2),sqrt(7),i)','checks':checks,'count':len(checks),'scope':'Supporting finite identities and mutation controls only; no analytical-limit or full-theorem formalization.'}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
