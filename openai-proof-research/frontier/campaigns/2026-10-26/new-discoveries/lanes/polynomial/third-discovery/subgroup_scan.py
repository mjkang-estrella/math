from pathlib import Path
import numpy as np,json,time
b=Path(__file__).resolve().parent
N=1500
xs=np.unique(np.concatenate([np.linspace(1,3,101),np.geomspace(3,1e6,150)])).astype(np.longdouble)
g=np.zeros(N+2,dtype=np.longdouble);g[1]=1
out=[]
for ell in range(1,5):
 h=np.zeros(N+2,dtype=np.longdouble)
 for d in range(1,N+2):h[d::d]+=d*g[d]
 g=h
 if ell<3:continue
 p=np.zeros((N+2,len(xs)),dtype=np.longdouble);p[0]=1
 for n in range(1,N+2):p[n]=xs*np.sum(g[1:n+1,None]*p[n-1::-1],axis=0)/n
 mins=[];viol=[]
 for n in range(8,N+1):
  delta=(n+1)*np.log(p[n])-n*np.log(p[n+1]);i=int(np.argmin(delta));mins.append((float(delta[i]),n,float(xs[i])))
  if delta[i]<=0:viol.append((n,float(xs[i]),str(delta[i])))
 vals=sorted(mins)[:20]
 row={'ell':ell,'N':N,'x_count':len(xs),'method':'numpy longdouble recurrence; exploratory only','smallest_log_gaps':vals,'violations':viol}
 out.append(row);print(json.dumps(row),flush=True)
 (b/'subgroup-scan.json').write_text(json.dumps(out,indent=2)+'\n')
