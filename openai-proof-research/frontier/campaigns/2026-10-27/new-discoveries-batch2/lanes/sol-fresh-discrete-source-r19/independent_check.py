import os,resource,itertools,json,math
from pathlib import Path
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,)*2);resource.setrlimit(resource.RLIMIT_CPU,(45,)*2)
B=Path(__file__).parent
# No import of first check: enumerate literal convex cyclic interval partitions.
def closure(a):
 n=len(a);r=[[False]*n for _ in a]
 for i in range(n):
  lo,hi=((i-1)%n,i) if a[i] else (i,(i-1)%n)
  r[lo][hi]=True
 for k in range(n):
  for i in range(n):
   for j in range(n):r[i][j]|=r[i][k] and r[k][j]
 return r
checks=json.loads((B/'checks.json').read_text());count=0;records=[]
for rec in checks['records']:
 a=rec['asc'];n=len(a)
 if n>6:continue
 r=closure(a);parts=[]
 for mask in range(1,1<<n):
  starts=[i for i in range(n) if mask>>i&1]
  if len(starts)<2:continue
  sets=[]
  for k,i in enumerate(starts):
   end=starts[(k+1)%len(starts)];s=[i];j=(i+1)%n
   while j!=end:s.append(j);j=(j+1)%n
   sets.append(s)
  if any(any(r[x][z] and r[z][y] and z not in s for x in s for y in s for z in range(n)) for s in sets):continue
  rel=[(i,j) for i,s in enumerate(sets) for j,t in enumerate(sets) if i!=j and any(r[x][y] for x in s for y in t)]
  parts.append((sets,rel))
 h=[0]*(n+1)
 for lab in itertools.permutations(range(n)):
  valid=[]
  for root in range(n):
   if all((not a[y])==(lab[y]>lab[root]) for y in range(n)):valid.append(1)
  for sets,rel in parts:
   roots=[s[0] for s in sets]
   if any(any((lab[y]<lab[s[0]])!=a[y] for y in s[1:]) for s in sets):continue
   if any(lab[roots[i]]>=lab[roots[j]] for i,j in rel):continue
   valid.append(len(sets))
  assert len(valid)==1,(a,lab,valid)
  h[valid[0]]+=1;count+=1
 assert h==rec['histogram'],(a,h,rec['histogram'])
 records.append(dict(asc=a,histogram=h))
# Direct color enumeration independently verifies transfer counts at t=2,3.
for rec in records:
 a=rec['asc'];n=len(a)
 for t in (2,3):
  maps=sum(all((v[(i-1)%n]<=v[i] if a[i] else v[(i-1)%n]>=v[i]) for i in range(n)) for v in itertools.product(range(t),repeat=n))
  assert math.factorial(n)*maps==sum(c*t**k for k,c in enumerate(rec['histogram']))
out=dict(status='PASS_FINITE_ONLY',posets=len(records),labelings=count,direct_coloring_checks=2*len(records),records=records)
(B/'independent-checks.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='records'})
