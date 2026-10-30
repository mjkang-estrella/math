"""Exact finite diagnostics, never a universal Bernoulli-tail certificate."""
import json, math, itertools, hashlib
from fractions import Fraction as F
from pathlib import Path
L=Path(__file__).resolve().parent
def parts(n,k,low=1):
 if k==1:
  if n>=low:yield (n,)
  return
 for a in range(low,n//k+1):
  for b in parts(n-a,k-1,a):yield (a,)+b
def histogram(w):
 d={(0,0):1}
 for a in w:
  e=d.copy()
  for (s,k),v in d.items():e[s+a,k+1]=e.get((s+a,k+1),0)+v
  d=e
 return d
def prob(w,p):
 d=histogram(w);D=sum(w);m=len(w);A=p.numerator;B=p.denominator
 return F(sum(v*A**k*(B-A)**(m-k) for (s,k),v in d.items() if s*B>=A*D),B**m)
def split(b,t):
 rows=[b]
 while len(rows[-1])>1:rows.append([(1-t)*x+t*y for x,y in zip(rows[-1],rows[-1][1:])])
 return [r[0] for r in rows],[r[-1] for r in rows[::-1]]
def restrict(b,a,c):
 if c<1:b,_=split(b,c)
 if a>0:_,b=split(b,a/c)
 return b
def certify(b,depth=0):
 if min(b)>=0:return True,depth
 if depth==7:return False,depth
 x,y=split(b,F(1,2));a,da=certify(x,depth+1);c,dc=certify(y,depth+1)
 return a and c,max(da,dc)
records=intervals=0;unclosed=[];maxdepth=0;digest=hashlib.sha256()
for D in range(1,19):
 for m in range(1,min(7,D)+1):
  for w in parts(D,m):
   records+=1;h=histogram(w)
   # Nonempty parameter chambers (s/D,(s+1)/D], clipped at 1/3.
   for s in range((D+2)//3):
    lo=F(s,D);hi=min(F(s+1,D),F(1,3))
    if lo>=hi:continue
    counts=[sum(v for (t,j),v in h.items() if j==k and t>=s+1) for k in range(m+1)]
    b=[F(counts[k],math.comb(m,k))-F(k,m) for k in range(m+1)]
    b=restrict(b,lo,hi);ok,depth=certify(b);maxdepth=max(maxdepth,depth);intervals+=1
    digest.update(repr((w,s,ok,depth)).encode())
    if not ok:unclosed.append([w,s])
   # Independent brute subset validation of DP at one fixed rational for each vector.
   p=F(3,10);A=0
   for mask in range(1<<m):
    s=sum(w[i] for i in range(m) if mask>>i&1);k=mask.bit_count()
    if 10*s>=3*D:A+=3**k*7**(m-k)
   assert prob(w,p)==F(A,10**m)
# Positive-weight version of the cyclic pointwise-coupling obstruction.
w=(3,1,3,1,3,1,3);loads=[F(w[i]+w[(i-1)%7],15) for i in range(7)]
assert loads==[F(2,5)]+[F(4,15)]*6
assert sum(x>=F(2,7) for x in loads)==1
cyclic_actual=prob(w,F(2,7));assert cyclic_actual>=F(2,7)
# Reproduce actual public coalescence obstruction, without claiming novelty.
p=F(3,10);before=prob((1,1,1,1),p);after=prob((2,1,1),p)
assert before==F(3483,10000) and after==F(363,1000) and after>before
# A proposed general critical-point Bernstein-coefficient positivity rule is inspected,
# not inferred from finite success. Source bytes must be tied to HTTP receipt.
assert (L/'sources/bernoulli.pdf').read_bytes()==(L/'sources/bernoulli-v1.pdf').read_bytes()
out=dict(status='PASS finite diagnostics only',weight_vectors=records,chambers=intervals,unclosed=unclosed,max_bisection_depth=maxdepth,diagnostic_digest=digest.hexdigest(),cyclic_loads=list(map(str,loads)),cyclic_actual_probability=str(cyclic_actual),merge_before=str(before),merge_after=str(after),universal_proof=False)
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
