"""Exact integer diagnostics; no empirical assertion is used as a proof."""
import json,resource,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(60,60))
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):
    if y:c[i+j]+=x*y
 return c
def shiftprod(a,k):
 c=a+[0]*k
 for i,x in enumerate(a):c[i+k]+=x
 return c
def conv_interval(a,m,step=1):
 # sliding window along each residue
 c=[0]*(len(a)+(m-1)*step)
 for i in range(len(c)):
  c[i]=(c[i-step] if i>=step else 0)+(a[i] if i<len(a) else 0)-(a[i-m*step] if 0<=i-m*step<len(a) else 0)
 return c
def unimodal(a):return a==a[::-1] and all(a[k]>=a[k-1] for k in range(1,(len(a)-1)//2+1))
t=time.monotonic();p=[1];rows=[]
for m in range(1,121):
 q=conv_interval(p,m,2)
 direct=[1]
 for i in range(2,m+1):direct=shiftprod(direct,i)
 direct=conv_interval(direct,m)
 assert q==direct
 d=len(p)-1;h=d//2
 chains=[p[j]-(p[j-1] if j else 0) for j in range(h+1)]
 assert all(x>=0 for x in chains)
 # Reconstruct all first differences from the chain expansion, independently.
 short=[{'start':j,'length':d-2*j+1,'multiplicity':v} for j,v in enumerate(chains) if v and d-2*j+1<2*m-1]
 bad=[k for k in range(1,(len(q)-1)//2+1) if q[k]<q[k-1]]
 rows.append(dict(m=m,n=m+2,degree=len(q)-1,coefficient_sum=sum(q),p_degree_parity=d%2,short_chain_count=len(short),short_chains=short if m<=12 else None,negative_first_differences=bad))
 p=shiftprod(p,m)
# Generic parity-free lemma fails even for symmetric unimodal [3].
control=conv_interval([1,1,1],3,2)
assert control==[1,1,2,1,2,1,1]
# Verify proposed even-chain lemma on exact finite parameters, not all-case proof.
for a in range(1,31):
 for m in range(1,31):assert unimodal(conv_interval([1]*(2*a),m,2))
# Minimal short odd-chain defects, explicitly retained.
odd_controls=[dict(length=l,m=m,coefficients=conv_interval([1]*l,m,2)) for l,m in [(1,3),(3,3),(5,3),(3,4),(5,4)]]
Path(__file__).with_name('exact-diagnostics.json').write_text(json.dumps(dict(scope='m=1..120, n=m+2; source already reports checks through n=800, so no computational progress credit',seconds=time.monotonic()-t,rows=rows,generic_counterexample=control,odd_controls=odd_controls),indent=2))
print('120 exact product identities and unimodality checks; 900 even-chain checks; generic obstruction',control,'seconds',time.monotonic()-t)
addition=[]
for m in range(4,19):
 d=m*(m-1)//2-1;bound=(d+2*m-1)//2-2*m;first=None;tested=0
 for mask in range(1<<(m-2)):
  s=[i for i in range(2,m) if mask>>(i-2)&1];w=sum(s)
  if w>bound:continue
  tested+=1;bits=1
  for i in range(2,m):
   if i not in s:bits|=bits<<i
  if not (bits>>(2*m)&1):first=dict(subset=s,weight=w,target_weight=w+2*m,unused=[i for i in range(2,m) if i not in s]);break
 addition.append(dict(m=m,tested=tested,first_failure=first))
Path(__file__).with_name('addition-route.json').write_text(json.dumps(addition,indent=2))
assert addition[9]['first_failure']['subset']==[3,4,5,6,7]
