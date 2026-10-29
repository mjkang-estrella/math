import resource,signal,os,pathlib,json,itertools,math
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(35,35));signal.alarm(45)
from check import B,degree,unimodal,add,qi
from fractions import Fraction
b=pathlib.Path(__file__).parent
def mul(a,c):
 r=[0]*(len(a)+len(c)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(c):r[i+j]+=x*y
 return r
def words(n):
 if not any(n):yield ();return
 for j,v in enumerate(n,1):
  if v:
   m=list(n);m[j-1]-=1
   for w in words(m):yield (j,)+w
def expansion(n):
 r=[];total=0
 for w in words(n):
  a=[1];m=list(n)
  for j in w:
   N=sum(i*v for i,v in enumerate(m,1));shift=sum((i-j)*m[i-1] for i in range(j+1,len(m)+1))
   for h in range(2,j+1):a=mul(a,[1]*(N-h+1))
   a=[0]*shift+a;m[j-1]-=1
  r=add(r,a);total+=1
 return tuple(r),total
out={'word_rows':0,'words':0,'common_mode_failure':None,'generic_LC_failure':None,'generic_unimodal_failure':None}
for n in itertools.product(range(4),repeat=4):
 if sum(n)>6:continue
 a,t=expansion(n);assert a==B(n);out['word_rows']+=1;out['words']+=t
 # The recurrence summands need not share a mode, despite source sum unimodality.
 modes=[];N=sum(i*v for i,v in enumerate(n,1))
 for j,v in enumerate(n,1):
  if not v:continue
  m=list(n);m[j-1]-=1;a=list(B(tuple(m)))
  for h in range(2,j+1):a=qi(a,N-h+1)
  a=[0]*sum((i-j)*n[i-1] for i in range(j+1,len(n)+1))+a
  modes.append(set(i for i,x in enumerate(a) if x==max(a)))
 if modes and not set.intersection(*modes) and out['common_mode_failure'] is None:
  out['common_mode_failure']={'n_ascending':n,'summand_modes':[sorted(x) for x in modes]}
for m in range(2,9):
 for n in range(1,5):
  N=2*m+n;D=m*(m+n-1);df=(m-1)*(m+n-2);dg=m*(m+n-2)
  f=[math.comb(df,i) for i in range(df+1)]
  for ratio in [Fraction(t,10) for t in range(11,41)]:
   g=[ratio**i for i in range(dg+1)];a=add(qi(f,N-1),[0]*m+g)
   bad=[i for i in range(1,len(a)-1) if a[i]**2<a[i-1]*a[i+1]]
   rec={'m':m,'n':n,'df':df,'dg':dg,'ratio':str(ratio),'output':[str(x) for x in a]}
   if bad and out['generic_LC_failure'] is None:out['generic_LC_failure']=dict(rec,bad_indices=bad)
   if not unimodal(a) and out['generic_unimodal_failure'] is None:out['generic_unimodal_failure']=rec
assert out['common_mode_failure'] is not None
assert out['generic_unimodal_failure'] is not None
(b/'independent.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
