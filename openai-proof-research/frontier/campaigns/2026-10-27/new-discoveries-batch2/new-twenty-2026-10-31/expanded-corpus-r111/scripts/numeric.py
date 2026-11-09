import pathlib,json,numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import spsolve
from scipy.optimize import linprog
L=pathlib.Path(__file__).resolve().parents[1];out=[]
for N in [4,6,10,20,30,40,60,80,100]:
 states=[(a,N-a-b,b)for a in range(1,N)for b in range(1,N-a+1)];ix={x:i for i,x in enumerate(states)};rows=list(range(len(states)));cols=rows.copy();vals=[1.]*len(states)
 for i,(a,p,b)in enumerate(states):
  for aa,pp,bb in [(b-1,2,a+p-1),(b,p-p//2,a+p//2),(b,p,a),(b,p+1,a-1)]:
   if aa>0 and bb>0:rows.append(i);cols.append(ix[aa,pp,bb]);vals.append(-.25)
 M=coo_matrix((vals,(rows,cols)),shape=(len(states),)*2).tocsr();x=spsolve(M,np.ones(len(states)))
 for a in sorted(set([1,2,(N-2)//2])):
  b=N-a-2
  if b<=0:continue
  pred=2.218141518626181819*a*b-1.0970966703340591*a-.4470795446435881*b+2.8388078373423187
  out.append({'total_nuts':N,'a':a,'b':b,'states':len(states),'mean':float(x[ix[a,2,b]]),'approximation':pred,'error':float(x[ix[a,2,b]]-pred),'linear_residual':float(abs(M@x-1).max())})
(L/'outputs/dreidel.json').write_text(json.dumps(out,indent=2));print('DREIDEL',out[-3:],flush=True)
out=[]
for n in [17,32,65,128,257]:
 for parity in [0,1]:
  points=[(i,j)for i in range(n)for j in range(n)if(i+j)%2==parity];rows=[];cols=[]
  for k,(i,j) in enumerate(points):rows.extend([i,n+j,2*n+i-j+n-1,4*n-1+i+j]);cols.extend([k]*4)
  A=coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(6*n-2,len(points))).tocsr()
  r=linprog(-np.ones(len(points)),A_ub=A,b_ub=np.full(6*n-2,2.),bounds=(0,None),method='highs',options={'threads':2,'parallel':False,'time_limit':20})
  row={'n':n,'parity':parity,'variables':len(points),'status':r.message,'optimum':float(-r.fun)if r.success else None,'ratio':float(-r.fun/n)if r.success else None};out.append(row);print(row,flush=True);(L/'outputs/checkerboard-lp.json').write_text(json.dumps(out,indent=2))
