#!/usr/bin/env python3
"""Independent exact Q(i) check of rectangular channels and non-scalar Grams."""
from fractions import Fraction as R
from pathlib import Path
import json

class C:
    def __init__(self,a=0,b=0):
        if isinstance(a,C): self.a,self.b=a.a,a.b
        else: self.a,self.b=R(a),R(b)
    def __add__(self,o):
        o=C(o); return C(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self): return C(-self.a,-self.b)
    def __sub__(self,o): return self+-C(o)
    def __rsub__(self,o): return C(o)+-self
    def __mul__(self,o):
        o=C(o); return C(self.a*o.a-self.b*o.b,self.a*o.b+self.b*o.a)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=C(o); d=o.a*o.a+o.b*o.b
        return self*C(o.a/d,-o.b/d)
    def __eq__(self,o):
        o=C(o); return self.a==o.a and self.b==o.b
    def conj(self): return C(self.a,-self.b)

I=C(0,1)
def mat(a): return [[C(x) for x in row] for row in a]
def eye(n): return mat([[int(j==k) for k in range(n)] for j in range(n)])
def tr(a): return [list(row) for row in zip(*a)]
def co(a): return [[x.conj() for x in row] for row in a]
def st(a): return tr(co(a))
def mul(a,b):
    assert len(a[0])==len(b)
    return [[sum((a[j][k]*b[k][l] for k in range(len(b))),C()) for l in range(len(b[0]))] for j in range(len(a))]
def scale(a,s): return [[x*s for x in row] for row in a]
def sub(a,b):
    assert len(a)==len(b) and len(a[0])==len(b[0])
    return [[x-y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def zero(a): return all(x==0 for row in a for x in row)
def inv2(a):
    d=a[0][0]*a[1][1]-a[0][1]*a[1][0]
    return scale([[a[1][1],-a[0][1]],[-a[1][0],a[0][0]]],C(1)/d)

checks={}
def ck(name,v):
    if not v: raise AssertionError(name)
    checks[name]=True

# Proper rank-two subspaces of C^3 and non-real, unequal Gram eigenvalues.
U=mat([[R(3,5),0],[I*R(4,5),0],[0,I]])
V=mat([[0,R(4,5)],[I,0],[0,I*R(3,5)]])
W=mat([[0,I],[1,0]])
H=mat([[1,I*R(1,2)],[-I*R(1,2),2]])
ck('rectangular_U_isometry',mul(st(U),U)==eye(2))
ck('rectangular_V_isometry',mul(st(V),V)==eye(2))
ck('nonreal_W_unitary',mul(st(W),W)==eye(2))
ck('non_scalar_H_positive_by_principal_minors',H==st(H) and H[0][0]==1 and H[0][0]*H[1][1]-H[0][1]*H[1][0]==R(7,4))
# F(z)=z F1, M(z)=z^-1 Mminus; all identities below are Laurent coefficients.
F1=mul(mul(V,W),st(U))
barS=mul(mul(U,H),st(U))
barT=mul(mul(mul(mul(V,W),H),st(W)),st(V))
S=co(barS); T=co(barT)
Mminus=scale(co(mul(F1,barS)),2)
ck('constant_test_exact_conjugation',mul(F1,barS)==scale(co(Mminus),R(1,2)))
ck('Gram_MstarM',mul(st(Mminus),Mminus)==scale(mul(S,S),4))
ck('Gram_MMstar',mul(Mminus,st(Mminus))==scale(mul(T,T),4))
ck('Gram_intertwining',mul(Mminus,S)==mul(T,Mminus))
J1=mul(mul(st(V),F1),U)
Qminus=scale(mul(mul(mul(inv2(H),st(U)),tr(Mminus)),V),R(1,2))
ck('restricted_J_coefficient',J1==W)
ck('rectangular_transpose_inverse',mul(J1,Qminus)==eye(2))
ck('inverse_coefficient_matches_Wstar',Qminus==st(W))
wrong_transpose=scale(mul(mul(mul(inv2(H),st(U)),st(Mminus)),V),R(1,2))
ck('mutation_adjoint_detected_rectangular',mul(J1,wrong_transpose)!=eye(2))
wrong_order=scale(mul(mul(mul(st(U),tr(Mminus)),V),inv2(H)),R(1,2))
ck('mutation_Gram_inverse_wrong_side_detected',mul(J1,wrong_order)!=eye(2))
ck('mutation_missing_half_detected_rectangular',mul(J1,scale(Qminus,2))!=eye(2))
# A nonsymmetric bistochastic kernel tests orientation of the two marginals.
K=[[R(3,2),R(3,2),0],[0,R(3,2),R(3,2)],[R(3,2),0,R(3,2)]]
u=[C(1,2),C(-2,1),C(1,-3)]
def norm2(x): return x.a*x.a+x.b*x.b
Tu=[sum((K[a][b]*u[a] for a in range(3)),C())/3 for b in range(3)]
delta=sum(map(norm2,u))/3-sum(map(norm2,Tu))/3
var=sum(K[a][b]*K[c][b]*norm2(u[a]-u[c]) for a in range(3) for b in range(3) for c in range(3))/27
ck('nonsymmetric_complex_variance',var==2*delta and delta>0)
ck('variance_factor_mutation_detected',var!=delta)
result={'status':'PASS','arithmetic':'independent rational Gaussian field Q(i)','checks':checks,'count':len(checks),'scope':'Finite algebra controls only. No analytical or full theorem certificate.'}
Path(__file__).with_name('supplemental-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
