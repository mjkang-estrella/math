#!/usr/bin/env python3
"""Independent exact enumeration of all unordered input configurations at n=m-1.
Repeated inputs, self-loops, cycles and unused vertices are included initially.
This is validation only; the universal proof is in Lean.
"""
from itertools import combinations_with_replacement, product
from fractions import Fraction as Q
from math import gcd,lcm
import json
from pathlib import Path

def solve(a,b):
 n=len(a);a=[[Q(v) for v in row]+[Q(b[i])] for i,row in enumerate(a)]
 for j in range(n):
  pivot=next(i for i in range(j,n) if a[i][j])
  a[j],a[pivot]=a[pivot],a[j]
  v=a[j][j];a[j]=[x/v for x in a[j]]
  for i in range(n):
   if i!=j:
    v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[j])]
 return [a[i][-1] for i in range(n)]

out=[]
for m in range(2,5):
 n=m-1;v=m+n;root=m;pairs=list(combinations_with_replacement(range(v),2))
 tested=0;covering=0;denominators=set();weight_patterns=set()
 for config in product(pairs,repeat=n):
  tested+=1;seen={root};todo=[root]
  while todo:
   z=todo.pop()
   if z>=m:
    for c in config[z-m]:
     if c not in seen:seen.add(c);todo.append(c)
  if not all(j in seen for j in range(m)):continue
  covering+=1
  slots=[c for pair in config for c in pair]
  assert len(set(slots))==2*n and root not in slots and seen==set(range(v))
  matrix=[[2*int(i==j)-config[i].count(m+j) for j in range(n)] for i in range(n)]
  transpose=[list(row) for row in zip(*matrix)]
  rootdual=solve(transpose,[int(i==0) for i in range(n)])
  weights=[sum(rootdual[i]*config[i].count(j) for i in range(n)) for j in range(m)]
  assert all(w>0 for w in weights) and sum(weights)==1
  S=lcm(*(w.denominator for w in weights));s=[int(w*S) for w in weights]
  assert gcd(*s)==1 and S%2==0
  flow=[t*S for t in rootdual]
  assert all(t.denominator==1 for t in flow)
  assert 2*flow[0]==S
  for i,pair in enumerate(config):
   for c in pair:assert flow[i]==(s[c] if c<m else 2*flow[c-m])
  denominators.add(S);weight_patterns.add(tuple(sorted(s)))
 out.append(dict(m=m,n=n,configurations=tested,all_terminals_reachable=covering,
  primitive_totals=sorted(denominators),primitive_weight_patterns=sorted(weight_patterns)))
print(json.dumps(out,indent=2))
Path(__file__).with_name('small-circuits.json').write_text(json.dumps(out,indent=2)+'\n')
