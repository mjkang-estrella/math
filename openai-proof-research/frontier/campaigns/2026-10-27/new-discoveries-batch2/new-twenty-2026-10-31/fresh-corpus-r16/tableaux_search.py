import os,resource
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
os.sched_setaffinity(0,{0,1})
from pathlib import Path
import math,json,time,resource
p=Path(__file__).resolve().parent;t=time.monotonic();out=[]
def parts(n,cap):
 if n==0:yield ();return
 for k in range(min(n,cap),0,-1):
  for r in parts(n-k,k):yield (k,)+r
for m in range(1,41):
 n=2*m;seq=[0]*(n+1);count=0
 for mu in parts(m,m):
  lam=tuple(x for v in mu for x in (v,v));den=1
  for i,row in enumerate(lam):
   for j in range(row):den*=row-j+sum(v>j for v in lam[i+1:])
  f=math.factorial(n)//den;seq[lam[0]]+=f*f;count+=1
 bad=[k for k in range(1,n) if seq[k]**2<seq[k-1]*seq[k+1]]
 out.append({'n':n,'paired_shapes':count,'bad_k':bad,'sequence':[str(x) for x in seq]})
 if bad:break
(p/'tableaux-search.json').write_text(json.dumps({'scope':'sum of squares of hook-length SYT counts for all even-column shapes, n even 2..80; odd n all zero','cases':out,'elapsed':time.monotonic()-t,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'proof':False},indent=2));print('n',n,'bad',bad,'elapsed',time.monotonic()-t)
