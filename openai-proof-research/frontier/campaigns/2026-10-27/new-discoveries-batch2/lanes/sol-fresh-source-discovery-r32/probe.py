import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(35,35));signal.alarm(45)
import numpy as np,itertools,math,json,pathlib,time
from scipy.linalg import eigvalsh
from scipy.special import gammaln
b=pathlib.Path(__file__).resolve().parent

def comps(k,n):
 if n==1:return [(k,)]
 return [(i,)+v for i in range(k+1) for v in comps(k-i,n-1)]
def gap(n,k,a,edges):
 states=comps(k,n);assert len(states)<=252
 ix={s:i for i,s in enumerate(states)};M=np.zeros((len(states),len(states)))
 # Reversibility gives off-diagonal sqrt(q_ij q_ji).
 for i,s in enumerate(states):
  for x,y,w in edges:
   for x,y in [(x,y),(y,x)]:
    if s[x]:
     t=list(s);t[x]-=1;t[y]+=1;j=ix[tuple(t)]
     q=w*s[x]*(a[y]+s[y]);r=w*t[y]*(a[x]+t[x]);M[i,i]+=q;M[i,j]=-math.sqrt(q*r)
 vals=eigvalsh(M,subset_by_index=[0,1]);return float(vals[1]),float(vals[0])
rng=np.random.default_rng(2026102932);rows=[];hit=None;start=time.monotonic()
for trial in range(240):
 n=3+trial%4
 a=[float(10**rng.uniform(-2.5,1)) for _ in range(n)]
 edges=[(i,i+1,float(10**rng.uniform(-1.5,1.5))) for i in range(n-1)]
 for x in range(n):
  for y in range(x+2,n):
   if rng.random()<.3:edges.append((x,y,float(10**rng.uniform(-1.5,1.5))))
 g1,_=gap(n,1,a,edges);g2,z=gap(n,2,a,edges);gs=[]
 for k in [3,4,5]:
  g,_=gap(n,k,a,edges);gs.append(g)
 ratio=min(gs)/g2;rows.append({'trial':trial,'n':n,'alpha':a,'edges':edges,'gap1':g1,'gap2':g2,'gaps345':gs,'ratio':ratio,'zero_residual':z})
 if ratio<.999999:hit=rows[-1];break
out={'status':'diagnostics_only_not_proof','trials':len(rows),'hit':hit,'minimum_ratio':min(v['ratio'] for v in rows),'seconds':time.monotonic()-start,'rows':rows}
(b/'probe-results.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
