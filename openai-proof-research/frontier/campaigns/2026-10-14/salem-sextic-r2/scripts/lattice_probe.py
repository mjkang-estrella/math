#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright 2026 Myeongjin Kang
"""Bounded six-dimensional weighted-lattice seed discovery, no certificate.
Decimal LLL decisions guide exact integer basis transformations only.
Writes no files; dependencies are the inspected local unit_probe.py.
"""
from decimal import Decimal as D,localcontext
import json,math
from unit_probe import root,peval,ceval,side,mul,power,ONE,X,XI

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def gs(B):
 stars=[];mu=[[D(0)]*6 for _ in range(6)];norm=[]
 for i in range(6):
  v=list(map(D,B[i]))
  for j in range(i):
   mu[i][j]=dot(list(map(D,B[i])),stars[j])/norm[j]
   v=[x-mu[i][j]*y for x,y in zip(v,stars[j])]
  stars.append(v);norm.append(dot(v,v));assert norm[-1]>0
 return mu,norm

def lll(B):
 B=[list(v) for v in B];T=[[int(i==j) for j in range(6)] for i in range(6)];k=1;steps=0
 while k<6:
  steps+=1;assert steps<10000
  mu,norm=gs(B)
  for j in range(k-1,-1,-1):
   q=int(mu[k][j].to_integral_value(rounding='ROUND_HALF_EVEN'))
   if q:
    B[k]=[x-q*y for x,y in zip(B[k],B[j])];T[k]=[x-q*y for x,y in zip(T[k],T[j])];mu,norm=gs(B)
  if norm[k]>=(D('0.75')-mu[k][k-1]**2)*norm[k-1]:k+=1
  else:B[k],B[k-1]=B[k-1],B[k];T[k],T[k-1]=T[k-1],T[k];k=max(k-1,1)
 return T,steps

def run():
 with localcontext() as ctx:
  ctx.prec=200
  ys=[root('-2','-1'),root('-1','0'),root('2','3')];beta=(ys[2]+(ys[2]**2-4).sqrt())/2
  zs=[(y/2,(4-y*y).sqrt()/2) for y in ys[:2]]
  E=[]
  for i in range(6):
   unit=[int(i==j) for j in range(6)];E.append([beta**i,beta**(-i)]+[c for z in zs for c in ceval(unit,z)])
  candidates=set();configs=[]
  # Fixed finite boxes, stop after these 27 lattices; no adaptive broad scan.
  for k in [1,2,3,4,5,6,8,10,12]:
   for bias in [-1,0,1]:
    # A~10^(2k+bias*k), A'~10^(2k-bias*k), circles~10^-k.
    w=[D(10)**(-(2+bias)*k),D(10)**(-(2-bias)*k)]+[D(10)**k]*4
    B=[[int((x*y*D(10)**80).to_integral_value()) for x,y in zip(row,w)] for row in E]
    T,steps=lll(B);configs.append({'k':k,'bias':bias,'steps':steps})
    for i in range(6):
     candidates.add(tuple(T[i]))
     for j in range(i):
      for s in [-1,1]:candidates.add(tuple(x+s*y for x,y in zip(T[i],T[j])))
  out=[]
  for q in sorted(candidates):
   if q==(0,)*6:continue
   A=peval(q,beta);Ap=peval(q,1/beta)
   if abs(A)<1:q=mul(q,X);A=peval(q,beta);Ap=peval(q,1/beta)
   if abs(A)<1:continue
   delta=sum((a*a+b*b).sqrt() for a,b in [ceval(q,z) for z in zs])
   if delta>=1:continue
   ll,_,_=side(A,beta,0);lr,g,_=side(Ap,beta,1);L=-float(delta.ln());lam=ll+lr
   out.append({'remainder':q,'A':str(A),'Aprime':str(Ap),'Delta':str(delta),'L':L,'Lambda_approx':lam,'gamma_approx':g,'L_minus_Lambda_approx':L-lam})
  out.sort(key=lambda x:x['L_minus_Lambda_approx'],reverse=True)
  return {'status':'DISCOVERY_ONLY_NO_INTERVAL_CERTIFICATE','mechanism':'27 six-dimensional weighted Minkowski lattices, basis vectors and signed pair sums only','configs':configs,'distinct_vectors':len(candidates),'evaluated':len(out),'best':out[:10],'limits':'Finite lattice samples; no complete O_K enumeration, no ring-of-integers determination, no nonexistence inference.'}
if __name__=='__main__':print(json.dumps(run(),indent=2))
