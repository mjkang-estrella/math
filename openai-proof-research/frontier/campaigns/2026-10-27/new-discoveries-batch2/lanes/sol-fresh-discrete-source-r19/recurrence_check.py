import os,resource,json,math
from fractions import Fraction as Q
from functools import cache
from pathlib import Path
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,)*2)
B=Path(__file__).parent
@cache
def path_count(a,t):
 if not a:return 1
 d=[1]*t
 for up in a[1:]:d=[sum(d[:y+1]) if up else sum(d[y:]) for y in range(t)]
 return sum(d)
@cache
def cyc(a,t):
 if all(a):return t
 n=len(a);s=0
 for i,up in enumerate(a):
  if not up:s+=cyc(a[:i]+a[i+1:],t)
  else:
   k=(i+1)%n
   while a[k]:k=(k+1)%n
   inds=[];j=k
   while j!=i:inds.append(j);j=(j+1)%n
   s+=t*path_count(tuple(a[j] for j in inds),t)
 return Q(s,n)
checks=json.loads((B/'checks.json').read_text());total=0
for r in checks['records']:
 a=tuple(r['asc']);n=len(a)
 for t in range(n+1):
  assert cyc(a,t)==Q(sum(c*t**k for k,c in enumerate(r['histogram'])),math.factorial(n))
  total+=1
# K_2,2: cutting a cover produces path count 8 at t=2, cycle count 7.
assert path_count((True,False,True,False),2)==8
r=next(x for x in checks['records'] if x['n']==4 and x['asc']==[True,False,True,False])
assert sum(c*2**k for k,c in enumerate(r['histogram']))==24*7
out=dict(status='PASS_FINITE_ONLY',recurrence_evaluations=total,cut_obstruction=dict(cycle_count_at_2=7,path_count_at_2=8),cache_entries=cyc.cache_info().currsize)
(B/'recurrence-checks.json').write_text(json.dumps(out,indent=2));print(out)
