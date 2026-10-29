import os,resource,signal,json,itertools,functools,pathlib
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(min(40,resource.getrlimit(resource.RLIMIT_CPU)[1]) if resource.getrlimit(resource.RLIMIT_CPU)[1]>0 else 40,)*2);signal.alarm(48)
b=pathlib.Path(__file__).parent
def add(a,c):
 r=[0]*max(len(a),len(c))
 for i,v in enumerate(a):r[i]+=v
 for i,v in enumerate(c):r[i]+=v
 return r
def qi(a,t):
 assert t>=1
 r=[];z=0
 for i in range(len(a)+t-1):
  if i<len(a):z+=a[i]
  if 0<=i-t<len(a):z-=a[i-t]
  r.append(z)
 return r
@functools.lru_cache(None)
def B(n):
 if not any(n):return (1,)
 N=sum((j+1)*v for j,v in enumerate(n));r=[]
 for j,v in enumerate(n,1):
  if not v:continue
  m=list(n);m[j-1]-=1;a=list(B(tuple(m)))
  for h in range(2,j+1):a=qi(a,N-h+1)
  a=[0]*sum((i-j)*n[i-1] for i in range(j+1,len(n)+1))+a
  r=add(r,a)
 return tuple(r)
def degree(n):
 return sum(j*(j-1)*v*v//2-(j-1)*v for j,v in enumerate(n,1))+sum(j*(i-1)*n[i-1]*n[j-1] for i in range(1,len(n)+1) for j in range(1,i))
def unimodal(a):
 down=False
 for x,y in zip(a,a[1:]):
  if x>y:down=True
  if down and x<y:return False
 return True
def vectors(k,budget):
 if k==0:
  yield ();return
 for v in range(budget//k+1):
  for a in vectors(k-1,budget-k*v):yield a+(v,)
if __name__=='__main__':
 stats={'rows':0,'LC_failure':None,'unimodal_failure':None,'degree_failure':None,'mode_disjoint':None}
 for k,maxN in [(2,32),(3,23),(4,19),(5,17),(6,15)]:
  for n in itertools.product(range(maxN+1),repeat=k):
   if sum((j+1)*v for j,v in enumerate(n))>maxN:continue
   a=B(n);stats['rows']+=1
   if not unimodal(a):stats['unimodal_failure']=[n,a];break
   if len(a)-1!=degree(n):stats['degree_failure']=[n,len(a)-1,degree(n)];break
   for i in range(1,len(a)-1):
    if a[i]**2<a[i-1]*a[i+1] and stats['LC_failure'] is None:stats['LC_failure']=[n,i,list(a[max(0,i-2):i+3])]
  else:continue
  break
 assert B((1,2))==(1,3,4,4,3)
 assert stats['unimodal_failure'] is None and stats['degree_failure'] is None
 stats['cached_rows']=B.cache_info().currsize
 (b/'checks.json').write_text(json.dumps(stats,indent=2)+'\n');print(json.dumps(stats))
