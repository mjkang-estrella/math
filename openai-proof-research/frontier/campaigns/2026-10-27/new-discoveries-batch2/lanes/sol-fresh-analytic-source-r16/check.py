#!/usr/bin/env python3
import os,resource
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(35,)*2)
from fractions import Fraction as Q
from pathlib import Path
import json
# Exact Q(sqrt(17)), coefficients through degree six.
N=6
class K:
 def __init__(self,a=0,b=0):self.a=Q(a);self.b=Q(b)
 def __add__(s,t):
  if not isinstance(t,K):t=K(t)
  return K(s.a+t.a,s.b+t.b)
 __radd__=__add__
 def __neg__(s):return K(-s.a,-s.b)
 def __sub__(s,t):return s+-t
 def __rsub__(s,t):return -s+t
 def __mul__(s,t):
  if not isinstance(t,K):t=K(t)
  return K(s.a*t.a+17*s.b*t.b,s.a*t.b+s.b*t.a)
 __rmul__=__mul__
 def __truediv__(s,t):
  if not isinstance(t,K):t=K(t)
  d=t.a*t.a-17*t.b*t.b
  return s*K(t.a/d,-t.b/d)
 def __repr__(s):return f'{s.a}+({s.b})sqrt17'
 def __eq__(s,t):
  if not isinstance(t,K):t=K(t)
  return s.a==t.a and s.b==t.b
Z=lambda:[K() for _ in range(N+1)]
def const(k):r=Z();r[0]=k if isinstance(k,K) else K(k);return r
def add(a,b):return [x+y for x,y in zip(a,b)]
def scale(a,k):return [x*k for x in a]
def mul(a,b):return [sum((a[j]*b[i-j] for j in range(i+1)),K()) for i in range(N+1)]
def inv(a):
 r=Z();r[0]=K(1)/a[0]
 for i in range(1,N+1):r[i]=-sum((a[j]*r[i-j] for j in range(1,i+1)),K())/a[0]
 return r
def exp(a):
 assert a[0]==0
 r=const(1);v=const(1)
 for i in range(1,N+1):v=scale(mul(v,a),Q(1,i));r=add(r,v)
 return r
def log(a):
 assert a[0]==1
 u=add(a,const(-1));r=Z();v=const(1)
 for i in range(1,N+1):v=mul(v,u);r=add(r,scale(v,Q((-1)**(i+1),i)))
 return r
# F(t)=log(M(1,e^t)); remove the common t factor before log.
# (e^t-1)/t divided by sqrt2 atan(t/sqrt2)/t.
import math
A=[K(Q(1,math.factorial(i+1))) for i in range(N+1)]
C=[K(Q((-1)**(i//2),(i+1)*2**(i//2))) if i%2==0 else K() for i in range(N+1)]
F=log(mul(A,inv(C)))
def compose(a,b):
 assert b[0]==0
 r=Z();v=const(1)
 for c in a:r=add(r,scale(v,c));v=mul(v,b)
 return r
z=Z();z[1]=K(1)
rows=[]
for sign in [-1,1]:
 q=K(Q(5,2),Q(sign,2));p=K(0,-sign)
 assert p+2*q==5 and p*p==17
 # u=log Bq(1,e^z)
 u=scale(log(scale(add(const(1),exp(scale(z,q))),Q(1,2))),K(1)/q)
 v=compose(F,u);w=add(u,compose(F,add(z,scale(u,-1))))
 r=scale(log(scale(add(exp(scale(v,p)),exp(scale(w,p))),Q(1,2))),K(1)/p)
 D=add(r,scale(F,-1))
 assert all(c==0 for c in D[:6]);assert D[6]==K(Q(11,11520))
 # Exact component derivative limits: v'=1/4, w'=3/4, F'=1/2.
 assert v[1]==K(Q(1,4)) and w[1]==K(Q(3,4)) and F[1]==K(Q(1,2))
 lx=log(add(const(1),scale(z,-1)));ly=log(add(const(1),z))
 lm=add(lx,compose(F,add(ly,scale(lx,-1))))
 mm=exp(lm)
 assert mm[2]==K(Q(1,3))
 tx=scale(lx,K(1)/p);ty=scale(ly,K(1)/p)
 tt=exp(scale(add(tx,compose(F,add(ty,scale(tx,-1)))),p))
 predicted=(K(Q(5,3))-p)/(2*p)
 assert tt[2]==predicted
 delta=tt[2]-(q/p-1)/4
 assert delta==(K(Q(10,3))-p-q)/(4*p)
 rows.append({'branch':sign,'D_coefficients':[str(c) for c in D],
              'T_quadratic':str(tt[2]),'sandwich_quadratic_difference':str(delta)})
result={'status':'PASS','limits':{'address_space_bytes':512*1024**2,'cpu_seconds':35,'threads':1},'checks':rows,'meaning':'Exact local algebra only; no global conjecture proof'}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
