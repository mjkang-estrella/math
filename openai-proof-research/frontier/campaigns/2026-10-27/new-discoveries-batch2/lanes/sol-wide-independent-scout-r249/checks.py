"""Exact independent backtracking; bounded instances, not a universal proof."""
from pathlib import Path
from collections import Counter
from math import comb
from fractions import Fraction
import json
L=Path(__file__).resolve().parent
def brute(n,r,kind):
 counts=[r]*n; out=Counter();nodes=0
 def rec(w):
  nonlocal nodes
  nodes+=1
  assert nodes<2000000
  if len(w)==n*r:
   if kind==0:
    s=0
    for i in range(len(w)-1,-1,-1):
     if i+1<len(w) and w[i]<w[i+1]:break
     s+=1
   else:s=sum(not w[:j] or not w[j:] or min(w[:j])>=max(w[j:]) for j in range(len(w)+1))-1
   out[s]+=1;return
  for c in range(n):
   if not counts[c]:continue
   bad=False
   for i,a in enumerate(w):
    for b in w[i+1:]:
     if (kind==0 and (a==c and b>a or a<b<c)) or (kind==1 and (a==c and b<a or a<c<b)):
      bad=True;break
    if bad:break
   if not bad:
    counts[c]-=1;rec(w+(c,));counts[c]+=1
 rec(());return out,nodes
def formula(n,r):
 if n==0:return 1
 return sum((Fraction(comb(n,j),n-j+1)*comb(n+(r-1)*j-1,n-j) for j in range(1,n+1)),Fraction(0))
records=[]
for r in range(1,9):
 d=Counter({0:1})
 for n in range(31):
  assert sum(d.values())==formula(n,r)
  if (r<=2 and n<=5) or (r<=4 and n<=3):
   for kind in (0,1):
    b,nodes=brute(n,r,kind);assert b==d,(r,n,kind,b,d)
    records.append(dict(r=r,n=n,kind=kind,count=sum(b.values()),nodes=nodes,histogram=dict(b)))
  e=Counter()
  for s,m in d.items():
   e[s+r]+=m
   for t in range(1,s+1):e[t]+=m
  d=e
(L/'check-results.json').write_text(json.dumps(dict(status='PASS',formula_checks=248,independent_cases=records),indent=2))
print('PASS: 248 exact recurrence/formula cases; ',len(records),'independent forbidden-pattern backtracking cases')
