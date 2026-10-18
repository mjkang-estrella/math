#!/usr/bin/env python3
"""MIT. Exact max-of-quotients diagnostic; finite evidence, no all-order proof."""
import importlib.util,json,sys
from pathlib import Path
from functools import lru_cache
from fractions import Fraction
from collections import defaultdict
sp=importlib.util.spec_from_file_location('mn',Path(__file__).with_name('multiplicity-diagnostic.py'));mn=importlib.util.module_from_spec(sp);sp.loader.exec_module(mn)
parts,chi,z=mn.parts,mn.chi,mn.z

def transpose(lam):return tuple(sum(x>j for x in lam) for j in range(lam[0])) if lam else ()
@lru_cache(None)
def horizontal_predecessors(lam,k):
 out=[]
 def rec(i,left,cur):
  if i==len(lam):
   if left==0:out.append(tuple(x for x in cur if x))
   return
  lo=lam[i+1] if i+1<len(lam) else 0
  for x in range(lo,lam[i]+1):
   d=lam[i]-x
   if d<=left:rec(i+1,left-d,cur+[x])
 rec(0,k,[]);return tuple(out)
@lru_cache(None)
def kostka(lam,mu):
 if not mu:return int(not lam)
 return sum(kostka(nu,mu[:-1]) for nu in horizontal_predecessors(lam,mu[-1]))

def induce(a,b):
 ca={mu:sum(v*chi(lam,mu) for lam,v in a.items()) for mu in parts(sum(next(iter(a))))}
 cb={mu:sum(v*chi(lam,mu) for lam,v in b.items()) for mu in parts(sum(next(iter(b))))}
 val=defaultdict(int)
 for u,f in ca.items():
  if not f:continue
  for v,g in cb.items():
   if not g:continue
   mu=tuple(sorted(u+v,reverse=True));mult=z(mu)//(z(u)*z(v));val[mu]+=f*g*mult
 out={}
 for lam in parts(sum(next(iter(a)))+sum(next(iter(b)))):
  c=sum(Fraction(f*chi(lam,mu),z(mu)) for mu,f in val.items() if f)
  assert c.denominator==1 and c>=0
  out[lam]=int(c)
 assert sum(c*mn.dim(lam) for lam,c in out.items())==sum(c*mn.dim(lam) for lam,c in a.items())*sum(c*mn.dim(lam) for lam,c in b.items())*mn.factorial(sum(next(iter(out))))//mn.factorial(sum(next(iter(a))))//mn.factorial(sum(next(iter(b))))
 return out

def main(maxm):
 lower={1:{(1,):1}};rows=[]
 for m in range(2,maxm+1):
  n=m*(m+1)//2;rho=tuple(range(m,0,-1));ps=parts(n)
  one={lam:sum(lower[m-1].get(nu,0) for nu in horizontal_predecessors(lam,m)) for lam in ps}
  two=induce(lower[m-2],{eta:1 for eta in parts(2*m-1) if len(eta)<=4}) if m>=3 else dict.fromkeys(ps,0)
  dom={lam:kostka(transpose(lam),rho) for lam in ps}
  lower[m]={lam:max(1,dom[lam],one[lam],two[lam]) for lam in ps}
  full={lam:max(lower[m][lam],lower[m][transpose(lam)]) for lam in ps}
  data=mn.run(m);actual={tuple(x['lambda']):x['g'] for x in data['coefficients']}
  # The stipulated source contracts are not audited here. Check only arithmetic range and recurrence output.
  bad=[{'lambda':lam,'bound':full[lam],'actual':actual[lam],'dominance':dom[lam],'one':one[lam],'two':two[lam]} for lam in ps if lam not in [(n,),(1,)*n] and full[lam]<m-1]
  rows.append({'m':m,'partitions':len(ps),'insufficient_count':len(bad),'insufficient':bad,'range_check':all(full[lam]<=actual[lam] for lam in ps),'max_of_quotients':[{'lambda':lam,'W_lower':lower[m][lam],'full_lower':full[lam]} for lam in ps]})
  print('completed m',m,'insufficient',len(bad),file=sys.stderr)
 return {'meaning':'finite max of actual quotient bounds; distinct quotients are not added; 1 uses stipulated full cyclic support','cases':rows}
if __name__=='__main__':print(json.dumps(main(int(sys.argv[1]) if len(sys.argv)>1 else 5),indent=2))
