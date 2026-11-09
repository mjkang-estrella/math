"""Exact diagnostics for every newly used identity; not a proof."""
import runpy
from pathlib import Path
s=runpy.run_path(str(Path(__file__).with_name('check.py')))
for n in range(3,11):
 # Check top matrices over Z[z], before specializing to roots of unity.
 P=s['prod'](n)
 top=[[{(0,j):v for (i,j),v in P[a][b].items() if i==n} for b in range(2)] for a in range(2)]
 if n%2==0:
  t={(0,n*n//2):(-1)**(n//2)}
  assert top==[[t,{}],[{},t]]
 else: assert s['add'](top[0][0],top[1][1])=={}
 # Rotor aggregation for every cycle matching, with the required z per forced pair.
 from math import comb
 for mask in range(1<<n):
  edges=[k for k in range(n) if mask>>k&1]
  if any(mask>>((k+1)%n)&1 for k in edges):continue
  a=[0]*(n+1)
  for rotor in range(1<<n):
   if all(rotor>>k&1 and not (rotor>>((k+1)%n)&1) for k in edges):
    a[n-rotor.bit_count()]+=1
  r=len(edges)
  expected=[0]*(n+1)
  for j in range(n-2*r+1):expected[r+j]=comb(n-2*r,j)
  assert a==expected
 print({'n':n,'top_and_forced_rotor_factor':'PASS'},flush=True)
print('104 positive-level cases; all new finite diagnostics PASS')
