import os,resource,itertools,time,json
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(55,55))
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
P=Path(__file__).resolve().parent;V=list(itertools.product(range(3),repeat=4));n=len(V);N=[[w for w in range(n) if w==v or all(a!=b for a,b in zip(V[v],V[w]))] for v in range(n)];pairs=[(v,w) for v in range(n) for w in N[v]];byv={v:[] for v in range(n)};rr=[];cc=[];vv=[];lo=[];hi=[]
def row(terms,l=-np.inf,h=np.inf):
 r=len(lo);lo.append(l);hi.append(h)
 for c,x in terms:rr.append(r);cc.append(c);vv.append(x)
for v in range(n):row([(w,1) for w in N[v]],1)
for idx,(v,w) in enumerate(pairs,n):
 byv[v].append(idx);row([(idx,1),(v,-1)],h=0)
 # if y_vw =1, w is a private closed neighbor of v
 row([(idx,len(N[w])-1)]+[(u,1) for u in N[w] if u!=v],h=len(N[w])-1)
for v in range(n):row([(idx,1) for idx in byv[v]]+[(v,-1)],l=0)
row([(v,1) for v in range(n)],28);row([(0,1)],1,1)
A=coo_matrix((vv,(rr,cc)),shape=(len(lo),n+len(pairs))).tocsc();t=time.monotonic();r=milp(np.zeros(n+len(pairs)),integrality=np.ones(n+len(pairs)),bounds=Bounds(0,1),constraints=LinearConstraint(A,lo,hi),options={'time_limit':35,'threads':1});out={'graph':'K3^4','threshold':28,'variables':len(r.x) if r.x is not None else n+len(pairs),'constraints':len(lo),'status':int(r.status),'message':r.message,'elapsed_s':time.monotonic()-t,'affinity':sorted(os.sched_getaffinity(0)),'memory_as':3*1024**3,'cpu_limit_s':55,'warning':'Floating-point MILP diagnostic only; neither infeasibility nor solver witness is a proof.'}
if r.x is not None:
 D=[v for v in range(n) if r.x[v]>0.5];out['D']=D;out['exact_verified']=len(D)>=28 and all(set(N[w])&set(D) for w in range(n)) and all(any(set(N[w])&set(D)=={v} for w in N[v]) for v in D)
(P/'upper-domination.json').write_text(json.dumps(out,indent=2));print(out)
