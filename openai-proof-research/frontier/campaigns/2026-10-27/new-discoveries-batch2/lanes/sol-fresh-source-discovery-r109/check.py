from fractions import Fraction as F
from itertools import combinations
from math import factorial,comb
from pathlib import Path
import json
P=Path(__file__).resolve().parent
def det(a):
 a=[list(map(F,row)) for row in a];z=F(1);n=len(a)
 for i in range(n):
  j=next((j for j in range(i,n) if a[j][i]),None)
  if j is None:return F(0)
  if i!=j:a[i],a[j]=a[j],a[i];z=-z
  v=a[i][i];z*=v
  for k in range(i+1,n):
   q=a[k][i]/v
   for l in range(i+1,n):a[k][l]-=q*a[i][l]
 return z
def hull_volume(v):
 n=len(v[0]);total=F(0);facets=0
 for ids in combinations(range(len(v)),n):
  a=[v[i] for i in ids];d=det(a)
  if not d:continue
  # affine oriented side: append a final column 1
  signs=[]
  for j,x in enumerate(v):
   if j in ids:continue
   z=det([list(y)+[1] for y in a+[x]])
   signs.append((z>0)-(z<0))
  nonzero={s for s in signs if s}
  if len(nonzero)==1:
   assert 0 not in signs, 'non-simplicial facet excluded by chosen parameters'
   total+=abs(d);facets+=1
 return total/factorial(n),facets
rows=[]
for n in range(2,6):
 S=[tuple(F(int(i==j))-F(1,n+1) for j in range(n)) for i in range(n+1)]
 for den in [7,11]:
  for num in range(1,den):
   t=F(num,den);k=((n+1)*t).__floor__()
   pts=[tuple((1-t)*x for x in v) for v in S]+[tuple(-t*x for x in v) for v in S]
   vol,facets=hull_volume(pts);ratio=vol*factorial(n)
   target=comb(n,k)*t**k*(1-t)**(n-k)
   assert ratio==target
   rows.append({'n':n,'t':str(t),'ratio':str(ratio),'facets':facets})
loss=[]
for n in range(2,17):
 for p in range(1,9):
  c=comb(n,n//2);target=F(c,2**(n*p));old=F(1,2**(n*(p-1)))
  mink=F(sum(comb(n*p,j)*comb(n,j) for j in range(n+1)),2**(n*p))
  assert mink==F(comb((p+1)*n,n),2**(n*p))
  assert old>target and mink>target
  loss.append([n,p,str(old/target),str(mink/target)])
# General fibre homothety obstruction for a square, exact at each rational shift:
rect=[]
for q in [F(1,4),F(1,2),F(3,4),F(1)]:
 widths=(2-q,F(2));assert widths[0]!=widths[1]
 rect.append([str(q),[str(x) for x in widths],str(widths[0]*widths[1])])
(P/'check-results.json').write_text(json.dumps({'simplex_p1_independent_facet_checks':rows,'sharpness_loss_checks':loss,'square_fibre_checks':rect,'status':'PASS; diagnostics only, no source proof or refutation'},indent=2));print(len(rows),len(loss),len(rect),'PASS')
