#!/usr/bin/env python3
"""MIT. Exact finite algebra checks, not proof of the analytic theorem."""
from fractions import Fraction as Q
from itertools import product
import json
Z=(Q(0),Q(0)); E=((Q(1),Q(0)),(Q(0),Q(1)))
def add(*xs): return tuple(sum(x[i] for x in xs) for i in range(2))
def scale(a,x): return tuple(a*v for v in x)
def sub(x,y): return add(x,scale(-1,y))
def mul(x,y): return tuple(x[i]*y[i] for i in range(2))
def lin(mat,x): return tuple(sum(mat[i][j]*x[j] for j in range(2)) for i in range(2))
def delta1(h,x,y,left=mul,right=mul): return sub(add(left(x,h(y)),right(h(x),y)),h(mul(x,y)))
def delta2(f,x,y,z,left=mul,right=mul): return sub(add(left(x,f(y,z)),f(x,mul(y,z))),add(f(mul(x,y),z),right(f(x,y),z)))
def delta3(f,w,x,y,z): return add(mul(w,f(x,y,z)),scale(-1,f(mul(w,x),y,z)),f(w,mul(x,y),z),scale(-1,f(w,x,mul(y,z))),mul(f(w,x,y),z))
def assoc(f,x,y,z): return sub(f(f(x,y),z),f(x,f(y,z)))
# Deliberately nonsymmetric, nonassociative rational perturbation.
coeff=(((Q(1,17),Q(-2,19)),(Q(3,23),Q(1,29))),((Q(-1,31),Q(2,37)),(Q(3,41),Q(-1,43))))
def phi(x,y): return tuple(sum(coeff[k][i][j]*x[i]*y[j] for i in range(2) for j in range(2)) for k in range(2))
def nu(x,y): return add(mul(x,y),phi(x,y))
H=((Q(1,101),Q(2,103)),(Q(-1,107),Q(1,109)))
def h(x): return lin(H,x)
def g(x): return sub(x,h(x))
G=((1-H[0][0],-H[0][1]),(-H[1][0],1-H[1][1]))
det=G[0][0]*G[1][1]-G[0][1]*G[1][0]
GI=((G[1][1]/det,-G[0][1]/det),(-G[1][0]/det,G[0][0]/det))
def gi(x): return lin(GI,x)
def rh(x,y): return sub(phi(x,y),delta1(h,x,y))
def prime(x,y): return gi(nu(g(x),g(y)))
checks={}
checks['delta_squared_zero']=all(delta3(lambda x,y,z:delta2(phi,x,y,z),*args)==Z for args in product(E,repeat=4))
checks['associator_expansion']=all(assoc(nu,x,y,z)==add(scale(-1,delta2(phi,x,y,z)),phi(phi(x,y),z),scale(-1,phi(x,phi(y,z)))) for x,y,z in product(E,repeat=3))
checks['wrong_associator_sign_detected']=any(assoc(nu,x,y,z)!=add(delta2(phi,x,y,z),phi(phi(x,y),z),scale(-1,phi(x,phi(y,z)))) for x,y,z in product(E,repeat=3))
checks['one_step_identity']=all(sub(nu(g(x),g(y)),g(mul(x,y)))==add(rh(x,y),mul(h(x),h(y)),phi(g(x),g(y)),scale(-1,phi(x,y))) for x,y in product(E,repeat=2))
checks['associator_covariance']=all(assoc(prime,x,y,z)==gi(assoc(nu,g(x),g(y),g(z))) for x,y,z in product(E,repeat=3))
checks['missing_outer_inverse_detected']=any(assoc(prime,x,y,z)!=assoc(nu,g(x),g(y),g(z)) for x,y,z in product(E,repeat=3))
c=Q(101,100)
def swap(x):return (x[1],x[0])
def left(x,y):return scale(c,mul(x,y))
def right(x,y):return scale(c,mul(x,y))
fake=lambda x,y:delta1(swap,x,y,left,right)
value=delta2(fake,E[0],E[0],E[1],left,right)
checks['approximate_module_square_nonzero']=value==(c*(c-1),Q(0)) and value!=Z
if not all(checks.values()): raise AssertionError(checks)
print(json.dumps({'status':'PASS_FINITE_ALGEBRA_ONLY','checks':checks,'false_complex_witness':[str(v) for v in value]},sort_keys=True,indent=2))
