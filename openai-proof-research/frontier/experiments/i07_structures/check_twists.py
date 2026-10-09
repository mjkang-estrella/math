"""Exact finite diagnostics, not a proof of the manifold theorem."""
from itertools import product
from collections import deque
import json
from pathlib import Path

def solve(moduli,generators,channel,only_own=False):
 verts=list(product(*(range(n) for n in moduli)));values={};components=0
 for seed in verts:
  if seed in values:continue
  components+=1;values[seed]=0;queue=deque([seed])
  while queue:
   v=queue.popleft()
   for j,g in enumerate(generators):
    if only_own and channel!=j:continue
    for sign in [-1,1]:
     w=tuple((x+sign*y)%n for x,y,n in zip(v,g,moduli))
     target=values[v]^(channel==j)
     if w in values:
      if values[w]!=target:return None
     else:values[w]=target;queue.append(w)
 return values

checks=[]
# Local deficiency sets must be singleton, with prescribed xor.
nonempty=[{0},{1},{0,1}]
for delta in [0,1]:
 s=1-delta;allowed=[]
 for D,E in product(nonempty,repeat=2):
  valid=all(not(c in D and (c^s) in E) for c in [0,1])
  expected=len(D)==len(E)==1 and next(iter(E))==(next(iter(D))^delta)
  assert valid==expected
  if valid:allowed.append([sorted(D),sorted(E)])
 checks.append(dict(delta=delta,allowed=allowed))
# Five parallel edges cannot be split with <=1 going to each deficient end.
assert all(not(k<=1 and 5-k<=1) for k in range(6))
# Exact cap selection: exactly one selected end in every local chart.
cap_cases=0
for delta,c,v in product([0,1],repeat=3):
 w=v^delta;s=1-delta
 assert int(v==c)+int(w==(c^s))==1;cap_cases+=1
# All finite rank-two upper-triangular lattice quotients in these ranges.
# Represent Z^2 / <(a,0),(b,c)> by x mod a, y mod c.
case_count=0;yes=0;no=0
for a in range(1,9):
 for c in range(1,9):
  for b in range(a):
   def red(v):
    x,y=v;q,y=divmod(y,c);return ((x-q*b)%a,y)
   verts=list(product(range(a),range(c)))
   if red((1,0))==(0,0) or red((0,1))==(0,0):continue
   solutions=[]
   for i in range(2):
    val={(0,0):0};queue=deque([(0,0)]);valid=True
    while queue and valid:
     v=queue.popleft()
     for j in range(2):
      for sign in [-1,1]:
       w=red((v[0]+sign*(j==0),v[1]+sign*(j==1)));target=val[v]^(i==j)
       if w in val and val[w]!=target:valid=False;break
       if w not in val:val[w]=target;queue.append(w)
      if not valid:break
    solutions.append(valid)
   actual=all(solutions);expected=all(x%2==0 for x in [a,b,c])
   assert actual==expected,(a,b,c,solutions)
   case_count+=1;yes+=actual;no+=not actual
# Mixed odd relation defeats the naive independent-channel model.
mods=(3,2);gens=((1,1),(0,1))
naive=[solve(mods,gens,i,True) is not None for i in range(2)]
full=[solve(mods,gens,i) is not None for i in range(2)]
assert naive==[True,True] and full==[False,False]
# Positive even covers through rank 5: labels v_i select disjoint caps.
positive=[]
for r in range(1,6):
 count=0
 for v in product([0,1],repeat=r):
  for i,j,c in product(range(r),range(r),[0,1]):
   w=list(v);w[j]^=1;s=int(i!=j)
   assert int(v[i]==c)+int(w[i]==(c^s))==1;count+=1
 positive.append(dict(rank=r,vertices=2**r,plumbing_types=10*r*r,cap_cases=count,bodies=r*(10*r)**2*(10*r-1)**2*10**4*16))
result=dict(status='PASS',scope='Finite exact diagnostics only; no topological or asymptotic validation',local_deficiency=checks,local_cap_cases=cap_cases,lattice_cases=case_count,even_lattice_yes=yes,non_even_lattice_no=no,naive_mixed_relation=dict(moduli=mods,generators=gens,naive_feasible=naive,corrected_feasible=full),positive_covers=positive)
path=Path(__file__).with_name('checks.json');path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
