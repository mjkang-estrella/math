#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Exact diagnostic only. Murnaghan--Nakayama via beta-number bead moves."""
from functools import lru_cache
from fractions import Fraction
from math import factorial
from pathlib import Path
import json
@lru_cache(None)
def partitions(n,cap=None):
 if n==0:return ((),)
 if cap is None:cap=n
 return tuple((k,)+p for k in range(min(n,cap),0,-1) for p in partitions(n-k,k))
@lru_cache(None)
def removals(lam,r):
 L=len(lam);bs={a+L-i-1 for i,a in enumerate(lam)};out=[]
 for b in sorted(bs):
  t=b-r
  if t>=0 and t not in bs:
   nbs=sorted((bs-{b})|{t},reverse=True)
   nu=tuple(a-L+i+1 for i,a in enumerate(nbs) if a-L+i+1>0)
   out.append((nu,(-1)**sum(t<x<b for x in bs)))
 return tuple(out)
@lru_cache(None)
def char(lam,mu):
 if not mu:return int(not lam)
 return sum(s*char(nu,mu[1:]) for nu,s in removals(lam,mu[0]))
def z(mu):
 value=1
 for a in set(mu):value*=a**mu.count(a)*factorial(mu.count(a))
 return value
def dim(lam):
 n=sum(lam);den=1
 for i,row in enumerate(lam):
  for j in range(row):den*=row-j+sum(j<x for x in lam[i+1:])
 return factorial(n)//den
def main():
 rows=[]
 for m in range(1,6):
  n=m*(m+1)//2;ps=partitions(n);rho=tuple(range(m,0,-1));chi=[char(rho,mu) for mu in ps]
  assert char(rho,(1,)*n)==dim(rho)
  assert sum(Fraction(a*a,z(mu)) for a,mu in zip(chi,ps))==1
  failures=[];ratios=[]
  for lam in ps:
   multiplicity=sum(Fraction(a**3*char(lam,mu),z(mu)) for a,mu in zip(chi,ps))
   assert multiplicity.denominator==1 and multiplicity>=0
   if multiplicity<dim(lam):failures.append({'partition':lam,'multiplicity':int(multiplicity),'dimension':dim(lam)})
   ratios.append((multiplicity/Fraction(dim(lam)),lam))
  row={'m':m,'n':n,'partitions':len(ps),'rho_dimension':dim(rho),'cube_dimension':dim(rho)**3,'group_order':factorial(n),'regular_containment':not failures,'failures':failures,'minimum_multiplicity_to_dimension':str(min(ratios)[0]),'minimizing_partition':min(ratios)[1]};rows.append(row);print(json.dumps(row),flush=True)
 # Countercontrol to signs in bead removal: sign representation on a 2-cycle.
 assert char((1,1),(2,))==-1 and char((2,),(2,))==1
 assert char((2,1),(3,))==-1 and char((2,1),(2,1))==0
 Path('checks.json').write_text(json.dumps({'status':'finite exact diagnostics, not proof of all-m target','staircase_cube':rows,'sign_controls':'pass'},indent=2)+'\n')
if __name__=='__main__':main()
