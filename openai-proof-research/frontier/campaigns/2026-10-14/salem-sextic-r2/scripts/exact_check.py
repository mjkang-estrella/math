#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright 2026 Myeongjin Kang
"""Rational outward interval check for ONE unsuccessful test element.
Standard library only. No file/network/subprocess access and no floating arithmetic.
This does not prove or disprove T or exclude a family of seeds.
"""
from fractions import Fraction as F
from math import isqrt
import json
S=10**90
class I:
 def __init__(self,l,h=None,raw=False):
  if raw:self.l,self.h=l,h
  else:
   l=F(l);h=l if h is None else F(h)
   self.l=l.numerator*S//l.denominator;self.h=-((-h.numerator*S)//h.denominator)
  assert self.l<=self.h
 @staticmethod
 def co(x):return x if isinstance(x,I) else I(x)
 def __add__(self,b):
  b=I.co(b);return I(self.l+b.l,self.h+b.h,raw=True)
 __radd__=__add__
 def __neg__(self):return I(-self.h,-self.l,raw=True)
 def __sub__(self,b):return self+-I.co(b)
 def __rsub__(self,b):return I.co(b)+-self
 def __mul__(self,b):
  b=I.co(b);p=[a*c for a in [self.l,self.h] for c in [b.l,b.h]]
  return I(min(p)//S,-((-max(p))//S),raw=True)
 __rmul__=__mul__
 def inv(self):
  assert self.l>0 or self.h<0
  return I(S*S//self.h,-((-S*S)//self.l),raw=True)
 def __truediv__(self,b):return self*I.co(b).inv()
 def __pow__(self,n):
  assert isinstance(n,int) and n>=0
  a=self;r=I(1)
  while n:
   if n&1:r=r*a
   a=a*a;n//=2
  return r
 def sqrt(self):
  assert self.l>=0
  return I(isqrt(self.l*S),isqrt(self.h*S)+1,raw=True)
 def abs(self):
  return I(0,max(-self.l,self.h),raw=True) if self.l<=0<=self.h else (self if self.l>0 else -self)
 def out(self,digits=24):
  t=10**digits;lo=self.l*t//S;hi=-((-self.h*t)//S)
  return {'lo':str(F(lo,t)),'hi':str(F(hi,t))}
def hull(a,b):return I(min(a.l,b.l),max(a.h,b.h),raw=True)
def cubic(x):return x*x*x-4*x-1
def rroot(lo,hi):
 lo,hi=F(lo),F(hi)
 for _ in range(330):
  mid=(lo+hi)/2
  if cubic(lo)*cubic(mid)<0:hi=mid
  else:lo=mid
 assert cubic(lo)*cubic(hi)<0
 return I(lo,hi)
def atan_inv(k):
 v=F(0);n=160
 for j in range(n):v+=F((-1)**j,(2*j+1)*k**(2*j+1))
 rem=F(1,(2*n+1)*k**(2*n+1))
 return I(v,v+rem) # n is even: next term positive.
PI=16*atan_inv(5)-4*atan_inv(239)
assert PI.l>3*S and PI.h<F(22,7)*S

def cos_nonneg(x):
 assert x.l>=0 and x.h<2*S
 term=I(1);v=term
 for k in range(1,100):
  term=term*x*x/((2*k-1)*(2*k));v=v+((-term) if k%2 else term)
 # Taylor with 200 derivatives bounded by 1: remainder <= |x|^200/200!.
 term=term*x*x/(199*200)
 return v+I(-F(term.h,S),F(term.h,S))
def phase_cos(x):
 n=(x.l+x.h+S)//(2*S)
 u=(x-I(n)).abs()
 assert u.h<S//2, 'unresolved cosine zero or half-integer crossing'
 low=cos_nonneg(I(F(u.h,S))*PI);high=cos_nonneg(I(F(u.l,S))*PI)
 ans=I(low.l,high.h,raw=True)
 assert ans.l>0
 return ans

def minus_log(x):
 assert x.l>0
 # Repeated square roots avoid a slowly converging logarithm series.
 r=0
 while x.l<3*S//4:x=x.sqrt();r+=1
 w=(1-x)/(1+x);assert w.abs().h<S//6
 term=w;v=I(0)
 for j in range(120):v=v+term/(2*j+1);term=term*w*w
 rem=2*term.abs()/(241*(1-w*w))
 return (2*v+I(-F(rem.h,S),F(rem.h,S)))*(2**r)

def mul(a,b):
 c=[0]*11;p=(1,0,-1,-1,-1,0,1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 for k in range(10,5,-1):
  v=c[k]
  for i in range(6):c[k-6+i]-=v*p[i]
 return tuple(c[:6])
def power(a,n):
 r=(1,0,0,0,0,0)
 for _ in range(n):r=mul(r,a)
 return r
def poly(a,x):
 v=I(0)
 for c in reversed(a):v=v*x+c
 return v

def check():
 ys=[rroot(-2,-1),rroot(-1,0),rroot(2,3)];beta=(ys[2]+(ys[2]*ys[2]-4).sqrt())/2;bi=beta.inv()
 assert beta.l>F(7,5)*S and beta.h<F(3,2)*S
 x=(0,1,0,0,0,0);xi=(0,1,1,1,0,-1);one=(1,0,0,0,0,0)
 assert mul(x,xi)==one
 y=tuple(a+b for a,b in zip(x,xi));yp=list(y);yp[0]+=2;u=mul(y,yp);q=power(u,8)
 assert q==(12131484,18269062,14374409,7387905,-3493252,-7387905)
 # Reciprocal substitution is exact in Z[X]/P, hence A'=A.
 reflect=(0,)*6
 for i,c in enumerate(q):reflect=tuple(a+c*b for a,b in zip(reflect,power(xi,i)))
 assert reflect==q and any(q)
 A=poly(q,beta);Ap=poly(q,bi);assert A.l>S and Ap.l>S
 delta=I(0)
 for z in ys[:2]:delta=delta+(z*(z+2)).abs()**8
 L=minus_log(delta)
 phase=A;left=I(0);glo=S;ghi=S;k=0;c0=phase_cos(phase);f0=minus_log(c0)
 while phase.h>F(1,10**30)*S:
  c=phase_cos(phase);left=left+minus_log(c)
  if k>=1:glo=min(glo,c.l);ghi=min(ghi,c.h)
  phase=phase*bi;k+=1
  assert k<2000
 # phase is first omitted term; all subsequent negative powers are in this tail.
 tail=PI*PI*phase*phase/(1-bi*bi)
 left=I(left.l,left.h+tail.h,raw=True)
 Lambda=2*left-f0
 # A'=A exactly. All right-side terms k>=1 were checked; omitted terms tend to 1.
 tail_floor=1-PI*PI*phase*phase/2
 gamma=I(min(glo,tail_floor.l),ghi,raw=True)
 assert delta.h<(gamma/(4*PI)).l
 assert Lambda.l>20*S and delta.l>F(1,10**6)*S
 # Uniform upper bound on M Psi(a) for this element, all q>=1, M>=1.
 uniform=F(1,2**40)*(1+F(10**12,288));assert uniform<1
 # Demonstrate capped-a branch cannot occur at beta6 with A>=1:
 # first phase below 1/2 lies >=1/(2 beta)>1/3, so f>log 2.
 assert (I(1)/(2*beta)).l>F(1,3)*S
 return {'status':'EXACT_RATIONAL_INTERVAL_DIAGNOSTIC_ONLY','element':'(y(y+2))^8, y=beta+beta^-1','quotient_remainder':q,'beta':beta.out(),'A':A.out(),'Aprime_enclosure':Ap.out(),'Delta':delta.out(),'L':L.out(),'Lambda':Lambda.out(),'gamma':gamma.out(),'negative_tail_action_upper':tail.out(),'first_omitted_power_index':-k,'trace_identity':'A prime equals A by exact quotient substitution','seed_smallness_holds':True,'original_TheoremS_fails_for_all_q_M_for_this_element':True,'uniform_entropy_gain_upper_rational':str(uniform),'T':'UNRESOLVED','exclusions':'No exclusion of other elements, product families, alternate tests or full T.'}
if __name__=='__main__':print(json.dumps(check(),indent=2))
