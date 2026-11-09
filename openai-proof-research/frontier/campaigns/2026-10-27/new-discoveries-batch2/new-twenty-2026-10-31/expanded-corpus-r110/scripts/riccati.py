import numpy as np,itertools,json,time,sys
from scipy.linalg import solve_discrete_are
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def edges(code):
 stack=[];E=[];i=-1
 for c in code:
  if c=='(':
   i+=1
   if stack:E.append((stack[-1],i))
   stack.append(i)
  else:stack.pop()
 return E
rooted={1:['()']}
def canon(n,E):
 adj=[[] for _ in range(n)]
 for u,v in E:adj[u].append(v);adj[v].append(u)
 def rec(v,p):return '('+''.join(sorted(rec(w,v) for w in adj[v] if w!=p))+')'
 return min(rec(v,-1) for v in range(n))
for n in range(2,10):
 avail=sorted((s,c) for s in rooted for c in rooted[s]);res=[]
 def build(rem,idx,cs):
  if not rem:res.append('('+''.join(sorted(cs))+')');return
  for j in range(idx,len(avail)):
   s,c=avail[j]
   if s<=rem:build(rem-s,j,cs+[c])
 build(n-1,0,[]);rooted[n]=res
 if n<4:continue
 free={canon(n,edges(c)):edges(c) for c in res};count=0;worst=0;fails=0
 for es in free.values():
  for ori in range(1<<(n-1)):
   E=[(v,u) if ori>>j&1 else (u,v) for j,(u,v) in enumerate(es)]
   sets={(1<<n)-1}
   for v in range(n):
    cut=[(s,t) for s,t in E if t!=v];reach={v}
    while True:
     nxt=reach|{t for s,t in cut if s in reach}|{s for s,t in cut if t in reach}
     if nxt==reach:break
     reach=nxt
    if any(t==v for s,t in E):
     mask=sum(1<<i for i in reach);sets|={mask};sets|={x&mask for x in list(sets) if x&mask}
   span=np.stack([np.outer([(x>>i)&1 for i in range(n)],[(x>>i)&1 for i in range(n)]).reshape(-1) for x in sets],axis=1)
   m=n-1;S=np.zeros((n,m));R=S.copy()
   for j,(u,v) in enumerate(E):S[u,j]=1;R[v,j]=1
   C=R-S;B=np.vstack([-S,np.eye(m)]);Q=np.diag([1.]*n+[0.]*m)
   for beta in [.5,.9]:
    A=beta**.5*np.block([[np.eye(n),R],[np.zeros((m,n+m))]])
    try:
     P=solve_discrete_are(A,B,Q,np.zeros((m,m)));den=B.T@P@B;K=np.linalg.solve(den,B.T@P@A)
     P1=P[:n,:n];N=P[:n,n:]-P1@S;H=P1-N@np.linalg.solve(den,N.T)
     err=float(np.max(np.abs(span@np.linalg.lstsq(span,H.reshape(-1),rcond=None)[0]-H.reshape(-1))))
     residual=float(np.max(np.abs(P-Q-A.T@P@A+A.T@P@B@K)));stable=float(max(abs(np.linalg.eigvals(A-B@K))))
     count+=1;worst=max(worst,err)
     if err>1e-6:
      print(json.dumps(dict(n=n,E=E,beta=beta,span_residual=err,dare_residual=residual,spectral_radius=stable)),flush=True)
      (D/'outputs/riccati-lead.json').write_text(json.dumps(dict(n=n,E=E,beta=beta,H=H.tolist(),span_residual=err)))
      sys.exit(0)
    except np.linalg.LinAlgError:fails+=1
 print(json.dumps(dict(n=n,unlabeled_trees=len(free),cases=count,numerical_failures=fails,max_span_residual=worst)),flush=True)
