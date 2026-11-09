import resource
resource.setrlimit(resource.RLIMIT_AS,(480*1024**2,480*1024**2))
from collections import defaultdict
from fractions import Fraction as Q
from math import comb,factorial
from pathlib import Path
import json
# R=Z[a,b,x,w]/(w^2=1+x^2), key=(a,b,x,w), w=0,1.
def clean(p):return {k:c for k,c in p.items() if c}
def add(*ps):
 q=defaultdict(int)
 for p in ps:
  for k,c in p.items():q[k]+=c
 return clean(q)
def scale(p,c):return clean({k:c*v for k,v in p.items()})
def mul(p,q):
 out=defaultdict(int)
 for (a,b,x,w),c in p.items():
  for (A,B,X,W),C in q.items():
   if w+W<2:out[a+A,b+B,x+X,w+W]+=c*C
   else:
    out[a+A,b+B,x+X,0]+=c*C
    out[a+A,b+B,x+X+2,0]+=c*C
 return clean(out)
def deriv(p):
 out=defaultdict(int)
 for (a,b,x,w),c in p.items():
  if x:
   out[a,b,x-1,w]-=x*c;out[a,b,x+1,w]-=x*c
  if w:out[a,b,x+1,w]-=c
 return clean(out)
def v2(c):
 c=Q(c)
 if not c:return 99999
 def v(n):n=abs(n);return (n&-n).bit_length()-1
 return v(c.numerator)-v(c.denominator)
P={(1,0,0,0):1,(1,0,2,0):1,(0,1,1,1):1}
h=[{},P]
for n in range(1,15):
 h.append(add(scale(deriv(h[n]),-1),*[scale(mul(h[j],h[n-j]),-1) for j in range(1,n)]))
rows=[]
fail=[]
for r in range(1,9):
 n=2*r-1
 for d in range(1,r+1):
  q={k:c for k,c in h[n].items() if k[0]+k[1]==d and k[3]==1}
  bound=(d-1).bit_count()
  low=min(map(v2,q.values()),default=99999)
  rows.append({'r':r,'d':d,'w_odd_content':low,'candidate_bound':bound})
  if low<bound:fail.append({'r':r,'d':d,'terms':[[list(k),str(c)] for k,c in q.items() if v2(c)<bound]})
# Independent free differential polynomial recurrence: P=A+B and derivation shifts jet indices.
def fm(p,q):
 out=defaultdict(int)
 for k,c in p.items():
  for K,C in q.items():out[tuple(sorted(k+K))]+=c*C
 return clean(out)
def fd(p):
 out=defaultdict(int)
 for k,c in p.items():
  for j,(a,i) in enumerate(k):out[tuple(sorted(k[:j]+((a,i+1),)+k[j+1:]))]+=c
 return clean(out)
f=[{},{((0,0),):1,((1,0),):1}]
for n in range(1,9):f.append(add(scale(fd(f[n]),-1),*[scale(fm(f[j],f[n-j]),-1) for j in range(1,n)]))
free=[]
for n in range(1,10,2):
 for d in range(1,(n+1)//2+1):
  q={k:c for k,c in f[n].items() if len(k)==d and sum(a for a,i in k)%2}
  low=min(map(v2,q.values()),default=99999)
  if low<(d-1).bit_count():free.append({'n':n,'d':d,'min':low,'bound':(d-1).bit_count(),'witness':next([list(k),c] for k,c in q.items() if v2(c)<(d-1).bit_count())})
out={'rows':rows,'specific_failures':fail,'free_differential_failures':free,'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
Path(__file__).with_name('explore.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
