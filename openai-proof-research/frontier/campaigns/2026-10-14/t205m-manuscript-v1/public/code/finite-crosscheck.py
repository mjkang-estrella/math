#!/usr/bin/env python3
"""MIT. Independent cell-grid strip checks through degree10; finite evidence only."""
import importlib.util,json,math
from pathlib import Path
from functools import lru_cache
from fractions import Fraction
p=Path(__file__).parent
s=importlib.util.spec_from_file_location('mn',p/'multiplicity-diagnostic.py');mn=importlib.util.module_from_spec(s);s.loader.exec_module(mn)
@lru_cache(None)
def grid(lam,k):
 cells={(i,j) for i,a in enumerate(lam) for j in range(a)};out=[]
 for nu in mn.parts(sum(lam)-k):
  if len(nu)>len(lam) or any(a>lam[i] for i,a in enumerate(nu)):continue
  skew=cells-{(i,j) for i,a in enumerate(nu) for j in range(a)}
  if any({(i+1,j),(i,j+1),(i+1,j+1)}<=skew for i,j in skew):continue
  seen={next(iter(skew))};todo=list(seen)
  while todo:
   i,j=todo.pop()
   for v in ((i-1,j),(i+1,j),(i,j-1),(i,j+1)):
    if v in skew and v not in seen:seen.add(v);todo.append(v)
  if seen==skew:out.append((nu,(-1)**(len({i for i,j in skew})-1)))
 return tuple(sorted(out))
@lru_cache(None)
def chi(lam,mu):
 if not mu:return int(not lam)
 return sum(s*chi(nu,mu[1:]) for nu,s in grid(lam,mu[0]))
def main():
 strips=chars=ortho=0
 for n in range(1,11):
  ps=mn.parts(n)
  for lam in ps:
   for k in range(1,n+1):assert grid(lam,k)==tuple(sorted(mn.hooks(lam,k)));strips+=1
   for mu in ps:assert chi(lam,mu)==mn.chi(lam,mu);chars+=1
  for a in ps:
   for b in ps:
    assert sum(Fraction(chi(a,mu)*chi(b,mu),mn.z(mu)) for mu in ps)==int(a==b);ortho+=1
 cert=json.loads((p/'finite-proof-certificate.json').read_text());square=0
 for block in cert['small_squares']:
  m=block['m'];rho=tuple(range(m,0,-1));n=sum(rho)
  for row in block['coefficients']:
   lam=tuple(row['lambda']);g=sum(Fraction(chi(rho,mu)**2*chi(lam,mu),mn.z(mu)) for mu in mn.parts(n))
   assert g==row['g'];square+=1
 print(json.dumps({'status':'PASS_FINITE_GRID_CROSSCHECK','max_degree':10,'strip_sets':strips,'character_values':chars,'orthogonality_pairs':ortho,'small_square_coefficients':square},sort_keys=True))
if __name__=='__main__':main()
