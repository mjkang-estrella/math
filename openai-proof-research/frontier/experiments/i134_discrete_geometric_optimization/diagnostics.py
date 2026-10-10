"""New finite identities only. No source-certificate or inherited diagnostic replay."""
from fractions import Fraction as F
from itertools import combinations

def run():
 counts={}
 ncheck=0
 for n in range(2,7):
  edges=list(combinations(range(n),2))
  for mask in range(1<<len(edges)):
   es=[e for j,e in enumerate(edges) if mask>>j&1]
   endpoints=set(x for e in es for x in e)
   assert len(endpoints)<=2*len(es)
   ncheck+=1
 counts['short_pair_endpoint_charging']=ncheck
 ncheck=0
 for n in range(3,20):
  u=[F((7*j*j+3*j)%17-8,19) for j in range(n)]
  mean=sum(u)/n
  variance=sum((x-mean)**2 for x in u)/n
  for shift in range(n):
   ds=[u[(j+shift)%n]-u[j] for j in range(n)]
   assert sum(ds)==0
   for t in [F(-1,3),F(0),F(2,5)]:
    assert sum((x-t)**2 for x in u)/n==variance+(mean-t)**2
    ncheck+=1
 counts['periodic_linear_cancellation_translation_variance']=ncheck
 ncheck=0
 for n in range(1,31):
  for k in range(n+1):
   for h in [F(1,2),F(1,3),F(1,7)]:
    # Area/N=1+t; counts are normalized by the original N.
    for t in [F(0),F(1,11),F(3,10)]:
     budget=(t+h)/(1-h)+F(k,n)
     upper_added=n*budget
     assert upper_added==n*(1+t)/(1-h)-n+k
     affected=k+25*(k+upper_added)
     assert affected==51*k+25*n*(t+h)/(1-h)
     ncheck+=1
 counts['saturation_density_and_local_modification_budget']=ncheck
 ncheck=0
 for H in [F(1,2),F(2,3),F(1)]:
  for d in [H/4,H/2,H]:
   cap=d*d/(2*H)
   assert cap>=d*d/2
   ncheck+=1
 counts['triangle_cap_area']=ncheck
 ncheck=0
 for N in range(1,30):
  for V in range(1,23):
   d=F(N,V);A=F(3,5);T=F(1,31);PM=F(7,13)
   qbound=(2*d*N*(A-T)-d*d*(V*A+PM))/N
   assert qbound==d*A-2*d*T-d*PM/V
   ncheck+=1
 counts['finite_window_positive_definite_completion']=ncheck
 return {'status':'PASS','arithmetic':'integers and fractions.Fraction only','checks':counts,'scope':'finite bookkeeping identities only; no analytic, universal-proof, source-truth, or contribution certification'}

if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2,sort_keys=True))
