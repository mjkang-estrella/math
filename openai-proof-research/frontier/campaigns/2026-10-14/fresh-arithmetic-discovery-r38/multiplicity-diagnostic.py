#!/usr/bin/env python3
"""MIT. Exact Murnaghan--Nakayama diagnostics, not an all-order proof."""
from functools import lru_cache
from fractions import Fraction
from math import factorial
from collections import Counter
import json

@lru_cache(None)
def parts(n,bound=None):
 if n==0:return ((),)
 if bound is None:bound=n
 return tuple((j,)+q for j in range(min(n,bound),0,-1) for q in parts(n-j,j))

@lru_cache(None)
def hooks(lam,k):
 L=len(lam); beta={lam[i]+L-i-1 for i in range(L)};out=[]
 for x in beta:
  y=x-k
  if y<0 or y in beta:continue
  new=sorted((beta-{x})|{y},reverse=True)
  nu=tuple(z-L+i+1 for i,z in enumerate(new) if z-L+i+1>0)
  out.append((nu,(-1)**sum(y<z<x for z in beta)))
 return tuple(out)

@lru_cache(None)
def chi(lam,mu):
 if not mu:return int(not lam)
 return sum(s*chi(nu,mu[1:]) for nu,s in hooks(lam,mu[0]))

def z(mu):
 v=1
 for j,c in Counter(mu).items():v*=j**c*factorial(c)
 return v

def dim(lam):
 h=1
 for i,row in enumerate(lam):
  for j in range(row):h*=row-j+sum(r>j for r in lam[i+1:])
 return factorial(sum(lam))//h

def run(m):
 rho=tuple(range(m,0,-1));n=sum(rho);ps=parts(n)
 vals=[(mu,chi(rho,mu),z(mu)) for mu in ps];vals=[(mu,c,z0) for mu,c,z0 in vals if c]
 assert sum(Fraction(c*c,z0) for mu,c,z0 in vals)==1
 assert chi(rho,(1,)*n)==dim(rho)
 rows=[]
 for lam in ps:
  g=sum(Fraction(c*c*chi(lam,mu),z0) for mu,c,z0 in vals)
  assert g.denominator==1 and g>=0
  rows.append((lam,int(g)))
 assert sum(g*dim(lam) for lam,g in rows)==dim(rho)**2
 assert dict(rows)[(n,)]==dict(rows)[(1,)*n]==1
 rest=[(lam,g) for lam,g in rows if lam not in [(n,),(1,)*n]]
 low=min(g for lam,g in rest) if rest else None
 return {'m':m,'n':n,'partitions':len(ps),'nonzero_staircase_character_classes':len(vals),'minimum_nontrivial_nonsign':low,'minimizers':[lam for lam,g in rest if g==low],'dimension_and_orthogonality_checks':'PASS','coefficients':[{'lambda':lam,'g':g} for lam,g in rows]}

if __name__=='__main__':
 import sys
 ms=list(map(int,sys.argv[1:])) or [2,3,4,5]
 print(json.dumps({'status':'finite diagnostic only','cases':[run(m) for m in ms]},indent=2))
