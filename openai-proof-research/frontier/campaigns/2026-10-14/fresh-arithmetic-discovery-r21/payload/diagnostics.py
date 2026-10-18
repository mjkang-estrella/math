#!/usr/bin/env python3
"""Exact finite checks of proof-route barriers, not CP varieties or a classification.
Copyright Myeongjin Kang. SPDX-License-Identifier: MIT
"""
from fractions import Fraction as F
from math import comb
import json

def require(ok, message):
    if not ok:
        raise ValueError(message)

def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def main():
    out={}
    X=[1,1,2,2,2,2,1,1];Y=[1,1,1,2,1,1,1]
    require(mul([1,1],X)==mul([1,1,1],Y),'Leray-Hirsch identity')
    for a in [X,Y]:
        require(a==a[::-1],'Poincare profile')
        require(all(a[i]<=a[i+1] for i in range((len(a)-1)//2)),'HL dimensions')
    out['betti_profiles']={'X':X,'Y':Y,'identity':True,'meaning':'necessary dimension tests only'}
    m=[0,14,14,9,4,1,0,0,0]
    for i in range(9):
        require(sum((-1)**j*comb(i,j)*m[j] for j in range(i+1))==-m[i],f'involution {i}')
    lam=F(3,4)*F(m[4],m[5]);require(lam==3,'lambda')
    for k in (4,6,8):
        require(sum((-1)**j*comb(k,j)*m[8-k+j] for j in range(k+1))==0,f'odd Segre {k}')
    require(all(m[i]*m[i]>=m[i-1]*m[i+1] for i in range(1,8)),'mixed log concavity')
    # a=1: coefficient comparison proves the homogeneous degree-eight identity.
    product=mul(mul([0,1],mul(mul([1,1],[1,1]),[1,1])),[2,1])
    expected=[56*x for x in product]+[0]*3
    require(expected==[comb(8,i)*m[i] for i in range(9)],'volume factorization')
    # G2 fibre alternative: m4 onwards vanish, i2 and i4 give m2=m1,m3=m1/2;
    # i6 then equals -m1 rather than zero, normalized here by m1=1.
    g=[F(0),F(1),F(1),F(1,2)]+[F(0)]*5
    require(sum((-1)**j*comb(6,j)*g[j] for j in range(7))==-1,'G2 exclusion scalar')
    out['quadric_moments']={'m':m,'lambda':str(lam),'higher_odd_Segre':True,'volume_factorization':True}
    # Scroll P(O(1)^2+O(2)): L^3=4, f L^2=1, c1=3L-2f.
    u=F(3*4-2,4);quad=32-20*u+3*u*u
    require(u==F(5,2) and quad==F(3,4),'sevenfold homogeneous scroll')
    out['scroll']={'degree':4,'u':str(u),'sixfold_quadratic_value':str(quad)}
    # Symbolic polynomial coefficient pairing for A=(1,t,t^2,t^3).
    A=[[1],[0,1],[0,0,1],[0,0,0,1]]
    Ap=[[0],[1],[0,2],[0,0,3]]
    coeff=[F(0)]*6
    for i,j,c in [(0,3,1),(3,0,-1),(1,2,-3),(2,1,3)]:
        for k,v in enumerate(mul(A[i],Ap[j])):coeff[k]+=c*v
    require(not any(coeff),'Legendrian pairing polynomial')
    # Vandermonde values at four distinct t prove the first-four-coordinate span.
    determinant=1
    for i in range(4):
        for j in range(i+1,4):determinant*=j-i
    require(determinant==12,'Vandermonde span')
    out['cone']={'omega_A_Aprime_coefficients':[str(x) for x in coeff],
                 'rank_omega':4,'kernel_dimension':2,'span_vandermonde_det':determinant,
                 'meaning':'linear-algebraic model, not an actual CP VMRT'}
    # Both model failures are detected if old sixfold exclusions are asserted.
    negative=[]
    for name,bad in [('lambda_nonintegral',lam.denominator!=1),('same_quadratic',quad==0)]:
        try:require(bad,name)
        except ValueError:negative.append({'case':name,'status':'EXPECTED_REJECTION'})
        else:raise ValueError('negative control accepted')
    out['negative_controls']=negative
    out['status']='PASS'
    out['claim_limit']='Exact finite identities only; no geometry-existence or T0677 proof.'
    return out

if __name__=='__main__':print(json.dumps(main(),indent=2))
