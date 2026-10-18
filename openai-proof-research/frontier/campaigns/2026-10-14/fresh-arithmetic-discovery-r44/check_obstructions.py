#!/usr/bin/env python3
"""MIT. Exact finite diagnostics only; does not prove the frozen target."""
from fractions import Fraction as F
from itertools import combinations
from math import prod,gcd
import json
checks=0

def require(ok,label):
 global checks
 if not ok:raise ValueError(label)
 checks+=1

for k in range(1,5):
 for ps in combinations([3,5,7,11],k):
  q=prod(ps);R=prod(F(p-1,p) for p in ps);D=prod(F(p-2,p) for p in ps);h=R/D
  S=[a for a in range(q) if all(a%p not in (0,1) for p in ps)]
  require(F(len(S),q)==D,'CRT density')
  require(h*D==R,'restored mean')
  require(h*h*D==R*h,'sharp second moment')
  require(h*R==prod(1+F(1,p*(p-2)) for p in ps),'product identity')
  raw=[F(1+a%7) for a in S];c=R*q/sum(raw);w=[c*x for x in raw]
  require(sum(x*x for x in w)/q>=R*h,'nonconstant Cauchy bound')
  require(min(h,F(2))*D/R==min(F(1),F(2)/h),'cap loss')
for m in range(1,8):
 for n in range(m+1,10):
  if gcd(m,n)!=1:continue
  for d in [1,3,15,105,1155]:
   a=F(1,17);b=F(1,23);q=d*m;r=d*n
   require(F(abs(r-q)*(r*a+q*b),d*d)==abs(n-m)*(n*a+m*b),'gcd cancellation')
print(json.dumps({'status':'PASS_FINITE_DIAGNOSTICS','exact_checks':checks}))
