import os,resource,signal,json,random,itertools,math
from pathlib import Path
for k in ['OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(45,45));signal.alarm(50)
b=Path(__file__).resolve().parent
rng=random.Random(23)
def exponents(m,a):
 n=len(a)
 return [sum(v*((m+i)%d==0)-v*(i%d==0) for i,v in enumerate(a,1)) for d in range(1,m+n+1)]
def poly(m,a):
 D=m*sum(a);c=[1]+[0]*D
 for i,v in enumerate(a,1):
  for _ in range(v):
   for j in range(D,m+i-1,-1):c[j]-=c[j-m-i]
 for i,v in enumerate(a,1):
  for _ in range(v):
   for j in range(i,D+1):c[j]+=c[j-i]
 return c
def hsop(m,a):
 active=[i for i,v in enumerate(a,1) if v]
 maxnum=m+len(a)
 for mask in range(1,1<<len(active)):
  s=[v for j,v in enumerate(active) if mask>>j&1];reach=[False]*(maxnum+1);reach[0]=True
  for v in range(1,maxnum+1):reach[v]=any(v>=i and reach[v-i] for i in s)
  lhs=sum(v for i,v in enumerate(a,1) if reach[m+i]);rhs=sum(a[i-1] for i in s)
  if lhs<rhs:return {'subset':s,'lhs':lhs,'rhs':rhs}
 return None
def matching(m,a):
 A=[m+i for i,v in enumerate(a,1) for _ in range(v)];B=[i for i,v in enumerate(a,1) for _ in range(v)]
 owner={}
 def add(j,seen):
  for k,x in enumerate(A):
   if x%B[j] or k in seen:continue
   seen.add(k)
   if k not in owner or add(owner[k],seen):owner[k]=j;return True
  return False
 return all(add(j,set()) for j in range(len(B)))
report={'seed':23,'samples':0,'polynomial_cases':0,'coefficients':0,'matching_failures':[],'hsop_failures':[],'negative':None}
for t in range(10000):
 n=rng.randint(2,10);m=rng.randint(n,3*n);a=[rng.randrange(3) for i in range(n)]
 if not any(a):continue
 report['samples']+=1;e=exponents(m,a)
 if min(e)<0:continue
 c=poly(m,a);report['polynomial_cases']+=1;report['coefficients']+=len(c)
 assert c==c[::-1] and c[0]==1 and c[-1]==1
 assert sum(c)*math.prod(i**v for i,v in enumerate(a,1))==math.prod((m+i)**v for i,v in enumerate(a,1))
 if min(c)<0:
  report['negative']={'m':m,'a':a,'degree':c.index(min(c)),'coefficient':min(c)};break
 if not matching(m,a) and len(report['matching_failures'])<5:report['matching_failures'].append({'m':m,'a':a})
 if report['polynomial_cases']<=350:
  h=hsop(m,a)
  if h and len(report['hsop_failures'])<5:report['hsop_failures'].append({'m':m,'a':a,**h})
# Literal source outside-domain warning, independently reconstructed.
a=[1,3,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1]
assert min(exponents(1,a))>=0
assert poly(1,a)[7]==-1
report['source_outside_scope']={'m':1,'n':17,'coefficient_q7':-1,'in_scope':False}
report['status']='PASS; finite diagnostics only'
(b/'checks.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
