from pathlib import Path
from fractions import Fraction as Q
from math import gcd
import json
from research import apery
from ap_classifier import check,failed_in
L=Path(__file__).resolve().parent
old=json.loads((L/'frozen/030-lines-result-12.json').read_text())
ap=next(x for x in old['supports'] if x['support']==[1,-2,1])
assert all(Q(x['parameter'][1])<=Q(10,9) for x in ap['segments'])
verts=[]
for v in ap['vertices']:
 x=Q(v['point'][0]);a=x.denominator;t=x.numerator-a
 if x>Q(10,9):verts.append([a,t]);assert a<12 or (a,t)==(13,2)
rows=[]
for t in [4,7,10,13,19]:
 for q in [10,19,100]:
  # Three specific residues exercise near-boundary/adjacent-hole orderings.
  for r in [1,2,t-1]:
   a=q*t+r
   if a%2!=1 or a%3!=2 or gcd(a,t)!=1:continue
   A=apery(a,t);F=max(A)-a;i=(a+2*t-1)//(2*t)+4;B=F-(i+1)*a
   assert B-6*t>0
   for n in range(B-6*t,B+1):
    hole=n<A[n%a]
    assert hole==((n-B)%t in {0,a%t})
   w=failed_in(A,B-6*t,B);assert w is not None
   rows.append(dict(a=a,t=t,local_witness=w,classification=check(a,t)))
(L/'lemma-checks.json').write_text(json.dumps(dict(high_ratio_vertices=verts,two_row_cases=rows),indent=2)+'\n')
print('PASS frozen AP ratio extraction and',len(rows),'targeted two-row/order/rank regressions')
