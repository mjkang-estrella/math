import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np,itertools,json,resource,pathlib
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
def hp(w):
 n=len(w);d=2*n+4;es=[(3,1),(3,2),(1,0),(2,0)]
 for i in range(1,n+1):
  v=2*i+2;u=2*i-1 if i==1 and w[0]==0 or i>=2 and w[i-1]!=w[i-2] else 2*i
  es.extend([(v+1,v-1),(v+1,v),(v,u)])
 pre=[0]*d
 for a,b in es:pre[b]|=1<<a
 # natural labels from a topological order
 used=0;order=[]
 while len(order)<d:
  x=next(x for x in range(d) if not used>>x&1 and pre[x]&used==pre[x]);order.append(x);used|=1<<x
 lab={v:i for i,v in enumerate(order)}
 states={(0,-1):(1,)}
 for level in range(d):
  nxt={}
  for (mask,last),poly in states.items():
   for x in range(d):
    if mask>>x&1 or pre[x]&mask!=pre[x]:continue
    shift=int(last>=0 and lab[last]>lab[x]);key=(mask|1<<x,x);arr=nxt.setdefault(key,[0]*(level+2))
    for j,c in enumerate(poly):arr[j+shift]+=c
  states=nxt
 out=[sum(p[i] if i<len(p) else 0 for p in states.values()) for i in range(d+1)]
 while out[-1]==0:out.pop()
 return out
for n in range(0,13):
 count=0;bad=[]
 for w in itertools.product(range(2),repeat=n):
  if n and w[0]:continue # complement yields same construction
  h=hp(w);r=np.roots(h[::-1]);count+=1
  if any(abs(x.imag)>1e-6 or x.real>=0 for x in r):bad.append({'w':w,'h':h,'roots':[[float(x.real),float(x.imag)] for x in r]})
 print(json.dumps({'n_LR_letters':n,'words_complement_representatives':count,'bad':bad}),flush=True)
