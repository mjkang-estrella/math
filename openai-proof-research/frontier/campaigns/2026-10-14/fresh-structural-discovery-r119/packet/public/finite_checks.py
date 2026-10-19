#!/usr/bin/env python3
"""MIT; Myeongjin Kang. Bounded rational diagnostics, never mathematical gates."""
from fractions import Fraction as F
from itertools import product
import json

def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def trans(a): return list(map(list,zip(*a)))
def mul(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def scale(c,a): return [[c*x for x in row] for row in a]
def add(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def det(a):
    if not a: return F(1)
    return sum((-1)**j*a[0][j]*det([r[:j]+r[j+1:] for r in a[1:]]) for j in range(len(a)))
def adj(a):
    n=len(a)
    return [[(-1)**(i+j)*det([r[:i]+r[i+1:] for k,r in enumerate(a) if k!=j]) for j in range(n)] for i in range(n)]
def boost(n,j,t):
    a=eye(n);c=(1+t*t)/(1-t*t);s=2*t/(1-t*t)
    a[0][0]=a[j][j]=c;a[0][j]=a[j][0]=s
    return a

def main():
    cases=identities=singular=noncommuting=0
    for n in range(3,6):
        J=eye(n);J[0][0]=-1
        mats=[eye(n),boost(n,1,F(1,3)),boost(n,2,F(2,5))]
        mats += [mul(mats[1],mats[2]),mul(mats[2],mats[1])]
        r=eye(n);r[1][1]=r[2][2]=-1;mats.append(r)
        for L,R in product(mats,repeat=2):
            assert mul(mul(trans(L),J),L)==J and det(L)==1
            assert mul(mul(trans(R),J),R)==J and det(R)==1
            U=mul(R,mul(mul(J,trans(L)),J))
            I=eye(n);C=adj(add(I,U));delta=det(add(I,U));Q=scale(2,mul(J,C))
            T=mul(mul(trans(L),Q),R)
            checks=[mul(trans(C),J)==mul(mul(J,C),U),
                    add(Q,trans(Q))==scale(2*delta,J),
                    mul(Q,U)==add(scale(2*delta,J),scale(-1,Q)),
                    add(T,trans(T))==scale(2*delta,J)]
            for k in range(1,n):
                p=[[F(1)]]+[[F(i==k)] for i in range(1,n)]
                checks += [mul(mul(trans(p),Q),p)==[[0]],mul(mul(trans(p),T),p)==[[0]]]
            assert all(checks)
            identities+=len(checks);cases+=1;singular+=delta==0;noncommuting+=mul(L,R)!=mul(R,L)
    print(json.dumps({'scope':'BOUNDED_RATIONAL_MATRIX_IDENTITIES_ONLY','cases':cases,'identities':identities,
        'singular_I_plus_U_cases':singular,'noncommuting_pairs':noncommuting,
        'does_not_test':'arbitrary tensor rings, Ramsey forcing, priority, contribution or acceptance',
        'mathematical_gate':False},sort_keys=True))
if __name__=='__main__': main()
