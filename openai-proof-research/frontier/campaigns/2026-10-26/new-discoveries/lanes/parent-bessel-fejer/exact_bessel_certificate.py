#!/usr/bin/env python3
"""Exact rational interval/ Bernstein certificate; analytic bridges are explained separately."""
from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
import json
N=20
p=[Q((-1)**k,factorial(k)**2) for k in range(N)]
h=[Q((-1)**k,factorial(k)*factorial(k+1)) for k in range(N)]
err=2*Q(9)**N/factorial(N)**2
errh=2*Q(9)**N/(factorial(N)*factorial(N+1))
def add(A,B):return [A[0]+B[0],A[1]+B[1]]
def mul(A,B):
 a=[x*y for x in A for y in B];return [min(a),max(a)]
def horner(co,A):
 r=[Q(0),Q(0)]
 for c in co[::-1]:r=add(mul(r,A),[c,c])
 return r
def value(x):
 v=horner(p,[x*x/4]*2)[0];return [v-err,v+err]
def bernstein(co,a,b):
 d=len(co)-1
 shifted=[sum(co[j]*comb(j,k)*a**(j-k)*(b-a)**k for j in range(k,d+1)) for k in range(d+1)]
 return [sum(shifted[k]*Q(comb(i,k),comb(d,k)) for k in range(i+1)) for i in range(d+1)]
def j0interval(A):
 v=horner(p,[A[0]**2/4,A[1]**2/4]);return [v[0]-err,v[1]+err]
A=[Q(24048,10000),Q(24049,10000)];B=[Q(55200,10000),Q(55201,10000)]
sA=[Q(15507,10000),Q(15508,10000)];sB=[Q(23494,10000),Q(23495,10000)]
assert sA[0]**2<A[0] and A[1]<sA[1]**2
assert sB[0]**2<B[0] and B[1]<sB[1]**2
va=[value(a) for a in A];vb=[value(b) for b in B]
assert va[0][0]>0 and va[1][1]<0 and vb[0][1]<0 and vb[1][0]>0
bh=bernstein(h,Q(0),Q(9,4));assert min(bh)>errh
bp=bernstein(p,Q(9,4),B[0]**2/4);assert max(bp)<-err
bh2=bernstein(h,B[0]**2/4,B[1]**2/4);assert max(bh2)<-errh
jA=j0interval([Q(9,10)*a for a in A]);jB=j0interval([Q(9,10)*b for b in B])
k=add(mul([Q(2,3)*a for a in sA],jA),mul([Q(1,3)*b for b in sB],jB))
assert k[1]<-Q(1,100)
# Strictly interior alpha=2/5, x=47/50; certify powers without floating point.
rA=[Q(14204,10000),Q(14205,10000)];rB=[Q(19805,10000),Q(19806,10000)]
assert rA[0]**5<A[0]**2 and A[1]**2<rA[1]**5
assert rB[0]**5<B[0]**2 and B[1]**2<rB[1]**5
jA2=j0interval([Q(47,50)*a for a in A]);jB2=j0interval([Q(47,50)*b for b in B])
k2=add(mul([Q(2,3)*a for a in rA],jA2),mul([Q(1,3)*b for b in rB],jB2))
assert k2[1]<-Q(1,500)

# Independently verify the already public Faà di Bruno and elliptic calculations.
import sympy as s
x,y,K,E=s.symbols('x y K E');g=(x-1)*(x+2)**3
jets=[s.diff(g,x,j).subs(x,0) for j in range(1,5)]
assert jets==[-4,12,30,24]
assert s.discriminant(32*y**3+144*y**2-6*y+3,y)==-36799488
F=4*K*K/(1+x)-(4+4/(1+x)**2)*K*E+3*E*E
G=(x-1)*(2*K*K-2*(x+2)/(x+1)*K*E+(x+2)/(x+1)*E*E)
dG=s.diff(G,x)+s.diff(G,K)*(E-(1-x*x)*K)/(x*(1-x*x))+s.diff(G,E)*(E-K)/x
assert s.factor(dG-F)==0
out={'status':'PASS exact arithmetic; not Lean','N':N,'global_q_max':9,'tail_bound_J0':str(err),'tail_bound_H':str(errh),'root_brackets':[[str(x) for x in z] for z in [A,B]],'J0_endpoint_bounds':[[str(t) for t in z] for z in va+vb],'bernstein_H_positive_min':str(min(bh)),'bernstein_J0_negative_max':str(max(bp)),'bernstein_H_second_negative_max':str(max(bh2)),'sqrt_brackets':[[str(x) for x in z] for z in [sA,sB]],'J0_scaled_intervals':[[str(x) for x in z] for z in [jA,jB]],'kernel_interval':[str(x) for x in k],'kernel_interval_decimal':[float(x) for x in k],'interior_witness':{'alpha':'2/5','x':'47/50','power_brackets':[[str(x) for x in z] for z in [rA,rB]],'J0_scaled_intervals':[[str(x) for x in z] for z in [jA2,jB2]],'kernel_interval':[str(x) for x in k2],'kernel_interval_decimal':[float(x) for x in k2]},'public_prior_checks':'Faà di Bruno cubic discriminant and elliptic antiderivative verified'}
Path(__file__).with_name('bessel-exact-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS kernel bound',float(k[0]),float(k[1]),'< -1/100')
print('PASS interior kernel bound',float(k2[0]),float(k2[1]),'< -1/500')
