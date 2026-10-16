#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright 2026 Myeongjin Kang
"""Bounded unit-family discovery, NOT a rigorous interval certificate.
Exact quotient-ring arithmetic; Decimal embeddings and reduced floating cosines.
No network, subprocesses, source imports or file writes. JSON to stdout.
"""
from decimal import Decimal as D, localcontext
import math,json
P=(1,0,-1,-1,-1,0,1)
ONE=(1,0,0,0,0,0); X=(0,1,0,0,0,0); XI=(0,1,1,1,0,-1)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def neg(a):return tuple(-x for x in a)
def mul(a,b):
 c=[0]*11
 for i,u in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=u*v
 for k in range(10,5,-1):
  v=c[k]
  for i in range(6):c[k-6+i]-=v*P[i]
 return tuple(c[:6])
def power(a,n):
 assert n>=0
 r=ONE
 while n:
  if n&1:r=mul(r,a)
  a=mul(a,a);n//=2
 return r
def peval(a,x):
 r=D(0)
 for u in reversed(a):r=r*x+u
 return r
def cmul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def ceval(a,z):
 r=(D(0),D(0))
 for u in reversed(a):
  r=cmul(r,z);r=(r[0]+u,r[1])
 return r

def cubic(t):return t*t*t-4*t-1
def root(lo,hi):
 lo,hi=D(lo),D(hi)
 for _ in range(1100):
  mid=(lo+hi)/2
  if mid==lo or mid==hi:break
  if cubic(lo)*cubic(mid)<=0:hi=mid
  else:lo=mid
 return (lo+hi)/2

def f(x):
 # Decimal remainder keeps huge real phases out of floating cancellation.
 u=x-x.to_integral_value(rounding='ROUND_HALF_EVEN')
 c=abs(math.cos(math.pi*float(u)))
 return -math.log(c) if c else float('inf')
def side(x,beta,start):
 x=abs(x)*beta**(-start);s=0.;g=1.;n=0
 while x>D('1e-55'):
  u=x-x.to_integral_value(rounding='ROUND_HALF_EVEN')
  c=abs(math.cos(math.pi*float(u)));g=min(g,c)
  s+=f(x);x/=beta;n+=1
  assert n<6000
 return s,g,n

def run():
 with localcontext() as ctx:
  ctx.prec=300
  ys=[root('-2','-1'),root('-1','0'),root('2','3')]
  beta=(ys[2]+(ys[2]**2-4).sqrt())/2
  zs=[(y/2,(4-y*y).sqrt()/2) for y in ys[:2]]
  y=add(X,XI);yp=add(y,(2,0,0,0,0,0));yi=add(mul(y,y),(-4,0,0,0,0,0));ypi=mul(y,add(y,(-2,0,0,0,0,0)))
  assert mul(y,yi)==ONE and mul(yp,ypi)==ONE and mul(X,XI)==ONE
  deriv=(0,-2,-3,-4,0,6)
  dv=peval(deriv,beta);dvp=peval(deriv,1/beta);dz=[ceval(deriv,z) for z in zs]
  rows=[]
  for a in range(-12,13):
   for b in range(-12,13):
    if a==b==0:continue
    q=mul(power(y if a>=0 else yi,abs(a)),power(yp if b>=0 else ypi,abs(b)))
    # Exact unit q, and comparison trace-integral q/P'(beta) (not O_K claimed).
    for denom in [False,True]:
     A=peval(q,beta)/(dv if denom else 1)
     Ap=peval(q,1/beta)/(dvp if denom else 1)
     circ=[]
     for r,z in enumerate(zs):
      c=ceval(q,z);v=(c[0]*c[0]+c[1]*c[1]).sqrt()
      if denom:v/=(dz[r][0]**2+dz[r][1]**2).sqrt()
      circ.append(v)
     delta=sum(circ)
     if abs(A)<1 or delta>=1:continue
     ll,_,nl=side(A,beta,0);lr,g,nr=side(Ap,beta,1)
     L=-float(delta.ln());lam=ll+lr
     rows.append({'a':a,'b':b,'denominator_Pprime':denom,'remainder':q,'A':str(A),'Aprime':str(Ap),'Delta':str(delta),'L':L,'Lambda_approx':lam,'gamma_approx':g,'L_minus_Lambda_approx':L-lam,'terms':[nl,nr]})
  rows.sort(key=lambda r:r['L_minus_Lambda_approx'],reverse=True)
  return {'status':'DISCOVERY_ONLY_NO_INTERVAL_CERTIFICATE','mechanism':'y and y+2 real-subfield units; fixed box [-12,12]^2; q and q/Pprime compared','beta':str(beta),'unit_circle_trace_roots':[str(y) for y in ys[:2]],'candidates_evaluated':len(rows),'top':rows[:12],'symmetric_powers':[r for r in rows if r['a']==r['b'] and r['a'] in [1,2,4,8,12]],'limits':'All cosine/action and embedding numbers are discovery approximations. No global family exclusion.'}
if __name__=='__main__':print(json.dumps(run(),indent=2))
