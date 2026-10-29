import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(40,40));signal.alarm(50)
import numpy as np,math,json,pathlib,time
from scipy.linalg import eigvalsh
b=pathlib.Path(__file__).resolve().parent

def comps(k,n):
 if n==1:return [(k,)]
 return [(i,)+v for i in range(k+1) for v in comps(k-i,n-1)]
def gap(n,k,a,edges):
 st=comps(k,n);assert len(st)<=1000
 ix={s:i for i,s in enumerate(st)};M=np.zeros((len(st),len(st)))
 for i,s in enumerate(st):
  for x,y in edges:
   for x,y in [(x,y),(y,x)]:
    if s[x]:
     t=list(s);t[x]-=1;t[y]+=1;j=ix[tuple(t)]
     q=s[x]*(a[y]+s[y]);r=t[y]*(a[x]+t[x]);M[i,i]+=q;M[i,j]=-math.sqrt(q*r)
 vals=eigvalsh(M,subset_by_index=[0,1]);return float(vals[1]),float(vals[0]),len(st)
rows=[];start=time.monotonic()
for name,n,edges in [('torus4',16,sorted({tuple(sorted((4*x+y,4*((x+dx)%4)+(y+dy)%4))) for x in range(4) for y in range(4) for dx,dy in [(1,0),(0,1)]})),('cube4',16,[(i,i^(1<<j)) for i in range(16) for j in range(4) if i<(i^(1<<j))])]:
 for a in [0.001,0.03,0.3]:
  gs=[gap(n,k,[a]*n,edges) for k in [1,2,3]];rows.append({'geometry':name,'alpha':str(a),'gap123':[g[0] for g in gs],'zero_residuals':[g[1] for g in gs],'dimensions':[g[2] for g in gs]})
out={'diagnostics_only':True,'rows':rows,'seconds':time.monotonic()-start}
(b/'targeted-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
