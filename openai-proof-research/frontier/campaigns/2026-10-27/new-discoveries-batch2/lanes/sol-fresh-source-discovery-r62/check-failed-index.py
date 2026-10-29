from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import factorial,prod
import json,pathlib,random
P=pathlib.Path(__file__).resolve().parent

def es(v):
 e=[1]+[0]*len(v)
 for x in v:
  for j in range(len(v),0,-1):e[j]+=x*e[j-1]
 return e

def admiss(a,b):
 ea,eb=es(a),es(b)
 r=[Q(eb[len(b)-j],ea[len(a)-j]) for j in range(len(a)+1)]
 return all(x<=y for x,y in zip(r,r[1:]))

def g(a,b,t):
 # equal integer vector lengths => all Gamma(t) factors cancel
 return prod(prod(t+j for j in range(x-1)) for x in a)/prod(prod(t+j for j in range(x-1)) for x in b)

def coef(a,b,t,n):return g(a,b,t+n)/factorial(n)
def delta(a,b,t,u,v,m):
 return sum(coef(a,b,t+u,k)*coef(a,b,t+v,m-k)-coef(a,b,t,k)*coef(a,b,t+u+v,m-k) for k in range(m+1))
# deterministic shard; random generator only chooses exact rational cases
rng=random.Random(62); cases=tests=0; counter=None
for dim in (1,2,3,4):
 for trial in range(600):
  a=tuple(sorted(rng.choices(range(1,13),k=dim)));b=tuple(sorted(rng.choices(range(1,13),k=dim)))
  if not admiss(a,b):continue
  cases+=1
  t=Q(rng.choice([1,1,1,2,4]));u=Q(rng.choice([1,2,3,5]),4);v=Q(rng.choice([1,2,3,7]),4)
  for m in range(9):
   d=delta(a,b,t,u,v,m); tests+=1
   if d<0:counter=dict(a=a,b=b,mu=str(t),alpha=str(u),beta=str(v),m=m,delta=str(d));break
  if counter:break
 if counter:break
out=dict(admissible_cases=cases,coefficient_tests=tests,counterexample=counter,finite_checks_not_proof=True)
(P/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
