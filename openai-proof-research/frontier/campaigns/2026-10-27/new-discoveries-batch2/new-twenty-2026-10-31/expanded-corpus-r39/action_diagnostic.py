import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
import numpy as np,itertools,json,random
from scipy.optimize import linprog
random.seed(3902)
def action(length):
 d=length.copy();n=len(d)
 for k in range(n):d=np.minimum(d,d[:,k,None]+d[None,k,:])
 w=np.zeros_like(d)
 for i in range(n):
  for j in range(n):
   if i!=j:w[i,j]=d[i,j]**-2
 w=w/w.sum(axis=1)[:,None];A=[];B=[]
 for i in range(n):
  for j in range(n):
   if i!=j:
    v=np.zeros(n);v[i]=1;v[j]=-1;A.append(v);B.append(d[i,j])
 S=0;ks=[]
 for i in range(n):
  for j in range(i+1,n):
   bounds=[(None,None)]*n;bounds[i]=(0,0);bounds[j]=(d[i,j],d[i,j]);r=linprog(w[i]-w[j],A_ub=A,b_ub=B,bounds=bounds,method='highs',options={'threads':1});assert r.success
   k=1+r.fun/d[i,j];S+=k;ks.append(k)
 return S,ks,d
for n in [4,6,8]:
 best=1e9;arg=None
 for t in range(60):
  l=np.zeros((n,n))
  for i in range(n):
   for j in range(i+1,n):l[i,j]=l[j,i]=random.choice([1,2,3,5,10,100])
  s,ks,d=action(l)
  if s<best:best=s;arg=l.tolist()
 print(json.dumps({'n':n,'random_trials':60,'min_action_float':best,'lengths':arg,'below_n':bool(best<n-1e-7)}),flush=True)
 # Matched pairs length epsilon; all others unit, asymptotic S -> n.
 for eps in [.5,.1,.01]:
  l=np.ones((n,n))-np.eye(n)
  for i in range(0,n,2):l[i,i+1]=l[i+1,i]=eps
  s,ks,d=action(l);print(json.dumps({'n':n,'matched_epsilon':eps,'S':s,'curvatures':ks}),flush=True)
