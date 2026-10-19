#!/usr/bin/env python3
"""Read-only exact identities for a route obstruction, not the global theorem."""
from fractions import Fraction as F
from itertools import permutations, product
import json

# Q(sqrt(5)), represented by rational pairs.
def k(a=0,b=0): return (F(a),F(b))
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def neg(a): return (-a[0],-a[1])
def sub(a,b): return add(a,neg(b))
def mul(a,b): return (a[0]*b[0]+5*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(a,b): return mul(a,k(b))
def div(a,b):
    den=b[0]*b[0]-5*b[1]*b[1]
    if not den: raise ArithmeticError('zero denominator')
    return scale(mul(a,(b[0],-b[1])),1/den)
def sq(a): return mul(a,a)
def need(a,b,label):
    if a!=b: raise AssertionError(label+': '+repr(a)+' != '+repr(b))
def mm(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def comm(a,b):
    ab,ba=mm(a,b),mm(b,a)
    return [[x-y for x,y in zip(row,col)] for row,col in zip(ab,ba)]
def dot(a,b): return sum(x*y for row,col in zip(a,b) for x,y in zip(row,col))

# T = H/sqrt(6); all entries of H are integer. Polynomial coefficients
# are converted to symmetric tensor coefficients, without factorial errors.
n=5
H=[[[0]*n for _ in range(n)] for _ in range(n)]
H[0][0][0]=1
for i in range(1,n):
    for p in set(permutations((0,i,i))): H[p[0]][p[1]][p[2]]=1
for i in (1,3):
    H[i][i][i]=1
    for p in set(permutations((i,i+1,i+1))):H[p[0]][p[1]][p[2]]=-1
B=[[F(dot(H[i],H[j]),6) for j in range(n)] for i in range(n)]
need(B,[[F(5,6) if i==j==0 else F(2,3) if i==j else F(0) for j in range(n)] for i in range(n)],'initial Gram')
beta=sum((B[i][j]-int(i==j))**2 for i,j in product(range(n),repeat=2))
cost=sum(F(dot(comm(H[i],H[j]),comm(H[i],H[j])),36) for i in range(n) for j in range(i))
need(beta,F(17,36),'initial beta2');need(cost,F(1,3),'initial C')
need(H[0],[[int(i==j) for j in range(n)] for i in range(n)],'exact unit')

# Ambient basis Y_i = sqrt(c_i/6) diag(v_i), c=(1,1,3,1,3).
# Check HS Gram and row Gram rationally, and trace cubics by separating
# the parity of the sqrt(3) factors. Odd parity contractions must vanish.
vectors=[[1,1,1,1,1,1],[2,-1,-1,0,0,0],[0,1,-1,0,0,0],[0,0,0,2,-1,-1],[0,0,0,0,1,-1]]
cs=[1,1,3,1,3]
for i,j in product(range(5),repeat=2):
    raw=sum(a*b for a,b in zip(vectors[i],vectors[j]))
    need(F(raw*cs[i],6) if i==j else raw,int(i==j),'ambient Gram')
for l in range(6):need(sum(F(cs[i]*vectors[i][l]**2,6) for i in range(5)),F(5,6),'ambient row Gram')
for i,j,l in product(range(5),repeat=3):
    raw=sum(vectors[i][q]*vectors[j][q]*vectors[l][q] for q in range(6))
    odd=sum(cs[s]==3 for s in (i,j,l))
    if odd%2:
        need(raw,0,'odd sqrt(3) contraction');need(H[i][j][l],0,'odd tensor coefficient')
    else: need(F(raw*3**(odd//2),6),H[i][j][l],'ambient cubic coefficient')

# The golden-ratio critical point and all metric identities used in the proof.
tau=k(F(-1,2),F(1,2));a2=sub(k(2),tau)
need(add(sq(tau),tau),k(1),'tau equation')
need(sq(a2),scale(sq(tau),5),'a4 identity')
need(add(add(mul(sq(tau),tau),scale(tau,3)),k(1)),scale(tau,5),'maximum numerator')
need(sub(mul(add(scale(tau,2),k(1)),a2),scale(tau,5)),k(),'zero tangent eigenvalue')
gz=div(add(k(1),tau),a2);gu=div(k(1),a2)
need(gz,k(F(1,2),F(3,10)),'gz')
need(gu,k(F(1,2),F(1,10)),'gu')
need(gu,sub(k(1),scale(a2,F(1,5))),'gu multiplication ratio')
P=scale(a2,F(1,6));Q=scale(mul(sq(a2),a2),F(1,6))
need(P,k(F(5,12),F(-1,12)),'p squared')
need(Q,k(F(25,6),F(-5,3)),'d squared')
# Finite symbolic commutator/Gram formula for S' with coefficients p,d.
# A separate integer interpolation test checks those universal formulas.
for p,d in [(1,0),(0,1),(1,1),(2,3),(-3,2)]:
    R=[[[0]*4 for _ in range(4)] for _ in range(4)];R[0][0][0]=p
    for i in range(1,4):
        for z in set(permutations((0,i,i))):R[z[0]][z[1]][z[2]]=p
    R[2][2][2]=d
    for z in set(permutations((2,3,3))):R[z[0]][z[1]][z[2]]=-d
    gram=[[dot(R[i],R[j]) for j in range(4)] for i in range(4)]
    expected=[4*p*p,2*p*p,2*p*p+2*d*d,2*p*p+2*d*d]
    need(gram,[[expected[i] if i==j else 0 for j in range(4)] for i in range(4)],'corrected Gram polynomial')
    C=sum(dot(comm(R[i],R[j]),comm(R[i],R[j])) for i in range(4) for j in range(i))
    need(C,4*p**4+2*(p*p-2*d*d)**2,'corrected C polynomial')
newbeta=add(add(sq(sub(scale(P,4),k(1))),sq(sub(scale(P,2),k(1)))),scale(sq(sub(scale(add(P,Q),2),k(1))),2))
newC=add(scale(sq(P),4),scale(sq(sub(P,scale(Q,2))),2))
need(newbeta,k(F(4627,18),F(-2065,18)),'corrected beta2')
need(newC,k(F(8345,36),F(-3715,36)),'corrected C')
need(sub(newbeta,k(beta)),k(F(9237,36),F(-4130,36)),'beta increase')
need(sub(newC,k(cost)),k(F(8333,36),F(-3715,36)),'C increase')
need(9237**2-5*4130**2,37669,'positive beta increase')
need(8333**2-5*3715**2,432764,'positive C increase')
print(json.dumps({'status':'PASS_EXACT_ROUTE_OBSTRUCTION_IDENTITIES','initial_dimension':5,'physical_dimension':6,'initial_beta2':str(beta),'initial_C':str(cost),'beta_increase':'(9237-4130sqrt(5))/36','C_increase':'(8333-3715sqrt(5))/36','sign_integer_witnesses':[37669,432764],'limits':'Finite exact diagnostics; universal argument is in the proof; frozen full target remains unresolved.'},sort_keys=True,indent=2))
