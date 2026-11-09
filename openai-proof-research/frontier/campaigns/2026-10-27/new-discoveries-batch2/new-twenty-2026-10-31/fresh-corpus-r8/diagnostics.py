from math import gcd
from fractions import Fraction
from pathlib import Path
import json,resource
resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
def inv(a,b):
 if a==1:return 0
 return ((a-1)*(b-1)*(a+b-1)-4*b*inv(b%a,a))//(4*a)
violations=[];cases=0
for b in range(3,301):
 v=sorted(set(inv(a,b) for a in range(1,b) if gcd(a,b)==1))
 for n in range(1,min(6,len(v))+1):
  cases+=1
  bound=Fraction((n-1)*(b+1)*(b+1-n),4*n)
  if v[n-1]<bound:violations.append([b,n,v[n-1],str(bound)])
def count(fam,k):
 return sum(all(abs(2*(a&b).bit_count()-b.bit_count())<=1 for b in fam) for a in range(1<<k))
r=dict(inversion=dict(max_b=300,distinct_value_cases=cases,violations=violations,limitation='diagnostic exact integer recurrence; no proof of general claim'),splitters=dict(overlap=count([3,6,13],7),disjoint=count([3,12,112],7),limitation='known/subsumed configuration, excluded'))
Path(__file__).with_name('diagnostics.json').write_text(json.dumps(r,indent=2))
