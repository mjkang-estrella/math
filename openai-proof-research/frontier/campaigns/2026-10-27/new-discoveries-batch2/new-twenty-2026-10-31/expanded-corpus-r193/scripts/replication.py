import pathlib,json,time,sys,itertools
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);cyc=bool(int(sys.argv[2]));cap=int(sys.argv[3]);start=time.monotonic()
edges=[(i,i+1) for i in range(n-1)]+([(n-1,0)] if cyc else [])
cuts=[];seen=set();history=[]
# failed k-subset criterion (perfect replication when path/even cycle)
assert not cyc or n%2==0
subsets=[[i for i in range(n) if s>>i&1] for s in range(1,1<<n)]
while time.monotonic()-start<100:
 N=n+sum(len(c) for c,k in cuts);A=lil_matrix((2*sum(len(c) for c,k in cuts)+len(cuts)+1,N));lo=[];hi=[];row=0;col=n
 A[row,:n]=1;lo.append(-np.inf);hi.append(cap);row+=1
 for opts,k in cuts:
  sels=[]
  for opt in opts:
   A[row,col]=n
   for i in opt:A[row,i]=-1
   lo.append(-np.inf);hi.append(n-k);row+=1;sels.append(col);col+=1
  for c in sels:A[row,c]=1
  lo.append(1);hi.append(np.inf);row+=1
 A=A[:row,:].tocsc();r=milp(np.r_[np.ones(n),np.zeros(N-n)],integrality=np.ones(N),bounds=Bounds(np.r_[np.ones(n),np.zeros(N-n)],np.r_[np.repeat(n,n),np.ones(N-n)]),constraints=LinearConstraint(A,lo,hi),options={'time_limit':max(1,min(15,100-(time.monotonic()-start))),'mip_rel_gap':0})
 if r.x is None:
  history.append({'status':int(r.status),'message':r.message,'cuts':len(cuts)});break
 w=np.rint(r.x[:n]).astype(int).tolist();bad=[]
 for S in subsets:
  k=len(S);ss=set(S)
  if max([w[i] for i in S]+[w[i]+w[j] for i,j in edges if i in ss and j in ss])<k:
   mask=sum(1<<i for i in S)
   if mask not in seen:bad.append((S,k,mask))
 history.append({'w':w,'sum':sum(w),'bad':len(bad),'solver_status':int(r.status),'cuts':len(cuts)});print(history[-1],flush=True)
 if not bad:break
 for S,k,mask in sorted(bad,key=lambda z:len(z[0]),reverse=True)[:100]:
  seen.add(mask);ss=set(S);cuts.append(([(i,) for i in S]+[(i,j) for i,j in edges if i in ss and j in ss],k))
(D/f'outputs/replication-{n}-{int(cyc)}.json').write_text(json.dumps({'n':n,'cycle':cyc,'cap':cap,'history':history,'seconds':time.monotonic()-start},indent=2))
