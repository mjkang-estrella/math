import os
for k in ['OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS']:os.environ[k]='1'
import resource,signal,random,json,math
from fractions import Fraction
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(45,45));signal.alarm(50)
from scipy.optimize import linprog
rng=random.Random(2301);out={'samples':0,'exact_obstruction':None,'seed':2301,'interpretation':'LP is search only; only exact validation could certify an obstruction'}
for t in range(1500):
 n=rng.randint(5,35);m=rng.randint(n,2*n)
 S=sorted(rng.sample(range(max(2,n//3),n+1),rng.randint(2, min(6,n//2))))
 reach=[True]+[False]*(m+n)
 for v in range(1,m+n+1):reach[v]=any(v>=s and reach[v-s] for s in S)
 c=[int(reach[m+i])-int(i in S) for i in range(1,n+1)]
 if min(c)>=0:continue
 E=[[int((m+i)%d==0)-int(i%d==0) for i in range(1,n+1)] for d in range(2,n+1)]
 r=linprog(c,A_ub=[[-v for v in row] for row in E],b_ub=[0]*len(E),A_eq=[[1]*n],b_eq=[1],bounds=(0,None),method='highs-ds',options={'threads':1})
 out['samples']+=1
 if r.success and r.fun<-1e-7:
  f=[Fraction(float(x)).limit_denominator(100000) for x in r.x];L=math.lcm(*(v.denominator for v in f));a=[int(v*L) for v in f]
  vals=[sum(x*y for x,y in zip(row,a)) for row in E]
  lhs=sum(x*y for x,y in zip(c,a))
  if min(vals)>=0 and lhs<0:out['exact_obstruction']={'m':m,'n':n,'a':a,'subset':S,'semigroup_deficit':lhs};break
out['status']='completed bounded search'
Path(__file__).with_name('cone.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
