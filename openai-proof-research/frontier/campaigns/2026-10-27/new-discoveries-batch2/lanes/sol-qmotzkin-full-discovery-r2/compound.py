#!/usr/bin/env python3
import resource,os,itertools,json,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
for v in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[v]='1'
from pathlib import Path
# Fixed 3-particle, 6-height, 6-time diagnostic. 20 states, 6 permutations/minor.
S=list(itertools.combinations(range(6),3));perms=list(itertools.permutations(range(3)))
def minor(a,b):
 return sum((-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3)) for p in perms if all(abs(a[i]-b[p[i]])<=1 for i in range(3)))
E={a:[(b,minor(a,b)) for b in S if minor(a,b)] for a in S}
a={S[0]:{(0,)*6:1}};counts=[]
for t in range(6):
 nxt={}
 for s,f in a.items():
  for b,c in E[s]:
   g=nxt.setdefault(b,{})
   for e,v in f.items():
    ee=tuple(e[i]+(i in b) for i in range(6));g[ee]=g.get(ee,0)+c*v
 a={s:{e:v for e,v in f.items() if v} for s,f in nxt.items()};counts.append(sum(map(len,a.values())))
f=a[S[0]];negative=[{'exponents':e,'coefficient':v,'q_height_degree':sum(i*e[i] for i in range(6))} for e,v in f.items() if v<0]
g={}
for e,v in f.items():
 d=sum(i*e[i] for i in range(6));g[d]=g.get(d,0)+v
out={'states':20,'steps':6,'n':3,'k':3,'terms_each_step':counts,'multivariate_terms':len(f),'negative_multivariate_terms':negative,'geometric_specialization':sorted(g.items()),'limits':{'memory_MiB':512,'CPU_seconds':60,'BLAS_threads':1}}
Path(__file__).with_name('compound-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
