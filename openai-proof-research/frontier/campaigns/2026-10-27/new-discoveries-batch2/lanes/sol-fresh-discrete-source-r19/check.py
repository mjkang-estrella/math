import os,resource,json,itertools,math,time
from pathlib import Path
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(45,)*2)
B=Path(__file__).parent
# a[i] is true iff vertex i is above its cyclic predecessor.
def blocks(a,lab):
 a=list(a);lab=list(lab)
 while True:
  k=lab.index(max(lab))
  if a[k]:
   seq=list(range(k,len(a)))+list(range(k));r=lab[k];b=1
   for j in seq[1:]:
    if (lab[j]>r)==a[j]:b+=1;r=lab[j]
   return b
  del a[k];del lab[k]
def order_count(a,t):
 # trace of product of weak-order transition matrices, independent of blocks.
 n=len(a);s=0
 for first in range(t):
  d=[int(x==first) for x in range(t)]
  for j in range(1,n):
   d=[sum(d[:y+1]) if a[j] else sum(d[y:]) for y in range(t)]
  s+=sum(d[:first+1]) if a[0] else sum(d[first:])
 return s
records=[]
for n in range(4,8):
 for a in itertools.product([False,True],repeat=n):
  # true Hasse cycle: neither direction has fewer than two edges.
  if not a[0] or sum(a)<2 or sum(a)>n-2:continue
  # one representative per rotation and reversal/complement unnecessary; rotation only
  if a!=min(a[k:]+a[:k] for k in range(n) if a[k]):continue
  h=[0]*(n+1)
  for p in itertools.permutations(range(n)):h[blocks(a,p)]+=1
  for t in range(n+1):
   lhs=math.factorial(n)*order_count(a,t);rhs=sum(c*t**k for k,c in enumerate(h))
   if lhs!=rhs:
    out=dict(status='SOURCE_IDENTITY_MISMATCH',n=n,asc=a,t=t,lhs=lhs,rhs=rhs,histogram=h)
    (B/'checks.json').write_text(json.dumps(out,indent=2));print(out);raise SystemExit(0)
  records.append(dict(n=n,asc=a,histogram=h))
out=dict(status='PASS_FINITE_ONLY',posets=len(records),labelings=sum(math.factorial(r['n']) for r in records),records=records)
(B/'checks.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='records'})
