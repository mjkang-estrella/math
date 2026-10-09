#!/usr/bin/env python3
"""Bounded exploratory search only. Failure to find a seed proves no impossibility."""
from fractions import Fraction
from collections import deque
from pathlib import Path
import json
rows=[]
for D in (3,4):
 p=[(j,i) for j in range(D-1,0,-1) for i in range(j,D)]
 f={a:Fraction(k+1,len(p)+1) for k,a in enumerate(p)};t=[]
 for i in range(1,D):t +=[Fraction(i)]+[i+f[j,i] for j in range(i,0,-1)]
 t +=[Fraction(D)]
 def om(a,b):return (1 if a>b else -1) if a!=b and abs(t[a]-t[b])<1 else 0
 B=tuple(tuple(om(i+1,j+1)-om(i+1,j)-om(i,j+1)+om(i,j) for j in range(len(t)-1)) for i in range(len(t)-1));n=len(B)
 def ac(B):
  seen=set()
  while True:
   cand=[i for i in range(n) if i not in seen and all(j in seen or B[j][i]<=0 for j in range(n))]
   if not cand:return len(seen)==n
   seen.update(cand)
 def mu(B,k):return tuple(tuple(-B[i][j] if k in (i,j) else B[i][j]+max(0,B[i][k])*max(0,B[k][j])-max(0,-B[i][k])*max(0,-B[k][j]) for j in range(n)) for i in range(n))
 q=deque([(B,())]);seen={B};found=None
 while q and len(seen)<150000:
  b,path=q.popleft()
  if ac(b):found=path;break
  if len(path)>=9:continue
  for k in range(n):
   if path and path[-1]==k:continue
   c=mu(b,k)
   if max(abs(x) for row in c for x in row)>3:continue
   if c not in seen:seen.add(c);q.append((c,path+(k,)))
 rows.append(dict(D=D,found=found,states=len(seen),queue=len(q),max_depth=9,max_entry=3,state_stop_threshold=150000,conclusion='bounded search only; no mutation-invariant obstruction established'))
p=Path(__file__).with_name('mutation-screen.json');p.write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows))
