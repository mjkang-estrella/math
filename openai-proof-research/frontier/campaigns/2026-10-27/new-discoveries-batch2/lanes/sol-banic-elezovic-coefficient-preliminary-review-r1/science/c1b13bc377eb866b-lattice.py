from work import *
from math import comb
from fractions import Fraction
import mpmath as m
m.mp.dps=65
def h(n):
 total=0
 for y in range(n+1):
  total+=comb(n,y)*sum(comb(n-y,x)*abs(y-x)*abs(n-2*y-x) for x in range(n-y+1))
 return Fraction(total,3**n)
# Independent step-distribution recursion, compared with conditional binomial sums.
dist={(0,0):1};controls=[]
for n in range(31):
 a=sum(abs(x)*abs(y)*c for (x,y),c in dist.items());assert Fraction(a,3**n)==h(n);controls.append(n)
 nxt={}
 for (x,y),c in dist.items():
  for dx,dy in [(-1,0),(1,-1),(0,1)]:nxt[(x+dx,y+dy)]=nxt.get((x+dx,y+dy),0)+c
 dist=nxt
c=2*m.sqrt(3)/(3*m.pi)+m.mpf(1)/9;ast=-2*m.sqrt(3)/(9*m.pi);d=-4*m.sqrt(3)/(81*m.pi)
rows=[]
for n in [90,91,92,180,181,182,360,361,362]:
 f=h(n);estimate=n*(m.mpf(f.numerator)/f.denominator-c*n-ast);b=d+4*m.sqrt(3)/(9*m.pi)*m.cos(2*m.pi*(n%3)/3)
 rows.append(dict(n=n,scaled_residual=str(estimate),predicted_limit=str(b),difference=str(estimate-b)))
dump('latticechecks.json',dict(exact_controls=controls,max_n=362,rows=rows,note='Finite checks only; limit justified by source Lemma7.3 and exact saddle computation.'))
print(json.dumps(rows,indent=2))
