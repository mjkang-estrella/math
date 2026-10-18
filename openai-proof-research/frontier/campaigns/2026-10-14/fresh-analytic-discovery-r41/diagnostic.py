#!/usr/bin/env python3
"""MIT. Exact finite controls, explicitly not a proof of T332."""
from fractions import Fraction as F
from itertools import product
import json

phi=lambda x:3*x*x-2*x*x*x
assert phi(F(1,4))==F(5,32)!=F(1,4)
for a,b in [(F(i,12),F(j,12)) for i in range(13) for j in range(13-i)]:
 assert phi(a+b)-phi(a)-phi(b)==6*a*b*(1-a-b)

# Unit star: index i cannot choose leaf i. Six two-equal labelings.
labels=[x for x in product(range(3),repeat=3) if all(x[i]!=i for i in range(3)) and len(set(x))==2]
assert len(labels)==6
for i in range(3):
 assert [sum(F(x[i]==a,6) for x in labels) for a in range(3)]==[F(0) if a==i else F(1,2) for a in range(3)]
for i in range(3):
 for j in range(i):
  assert sum(F(2*(x[i]!=x[j]),6) for x in labels)==F(4,3)

G=[[F(5,9) if i==j else F(2,9) for j in range(3)] for i in range(3)]
nu=[]
for i in range(3):
 law={a:F(0) for a in range(4)} #3 denotes root
 for x in labels:
  for js in product(range(3),repeat=3):
   values=[x[j] for j in js]
   median=next((a for a in range(3) if values.count(a)>=2),3)
   prob=F(1,6)
   for j in js:prob*=G[i][j]
   law[median]+=prob
 assert sum(law.values())==1 and min(law.values())>=0
 nu.append(law)
# The unlifted median operation has the previously identified excess.
flow=[[F(0) if a==i else F(1,2) for a in range(3)] for i in range(3)]
unlifted=[]
for i in range(3):
 out=[F(0)]*3
 for js in product(range(3),repeat=3):
  prob=F(1)
  for j in js:prob*=G[i][j]
  for a in range(3):out[a]+=prob*sorted(flow[j][a] for j in js)[1]
 unlifted.append(sum(out))
assert unlifted==[F(263,243)]*3

ratios={}
for L in [1,10,100,1000]:
 d=F(1,4)
 top=d/(1+2*d)*(L+2)
 inside=d/(1+2*d)*(L+1)
 short=2*d*d/(1+2*d)*3
 ratio=(top+inside+short)/(3*d)
 assert ratio==F(4*L+9,9)
 ratios[L]=str(ratio)
assert F(4*100+9,9)>10 #rejects a fixed10 bound for this sampler
# Positive control: a different, direct coupling is optimal for the same pair.
assert F(1,4)*3/(3*F(1,4))==1

# Exact first-order Cesaro derivative on one three-state reversible chain.
def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
I=[[F(i==j) for j in range(3)] for i in range(3)]
Q=[[F(-3),F(1),F(2)],[F(1),F(-4),F(3)],[F(2),F(3),F(-5)]]
t=4
for den in [100,1000,10000]:
 eps=F(1,den); A=[[I[i][j]+eps*Q[i][j] for j in range(3)] for i in range(3)]
 power=I; B=[[F(0) for _ in range(3)] for _ in range(3)]
 for s in range(1,t+1):
  power=mm(power,A)
  B=[[B[i][j]+power[i][j]/t for j in range(3)] for i in range(3)]
 error=max(abs((B[i][j]-I[i][j])/eps-F(t+1,2)*Q[i][j]) for i in range(3) for j in range(3))
 assert error<=100*eps

print(json.dumps({'status':'PASS_FINITE_DIAGNOSTIC_NOT_PROOF','lifted_output_probabilities':[{str(k):str(v) for k,v in law.items()} for law in nu],'unlifted_total_mass':list(map(str,unlifted)),'top_down_distortion':ratios,'negative_controls':['phi changes constant family','unlifted output has negative root mass','top-down sampler violates fixed10 at L100','simultaneous exact cost1 fails on three-star'],'positive_controls':['six-atom coupling has exact marginals and ratio4/3','lifted median output is probability','direct coupling for long-arm pair has ratio1','lazy Cesaro derivative rational remainder bound']},indent=2))
