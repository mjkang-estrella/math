import math,random,json,time
from pathlib import Path
rng=random.Random(395581);out=[];start=time.monotonic()
def kernel(x,M):
 x=abs(x)
 if x>=math.pi:return 0.
 if M==3:return (12*(math.pi-x)*math.cos(x)+9*math.sin(x)+math.sin(3*x))/32
 return (36*(math.pi-x)+24*(math.pi-x)*math.cos(2*x)+28*math.sin(2*x)+math.sin(4*x))/192
def ldlt(A):
 N=len(A);L=[[0.]*N for _ in range(N)];D=[]
 for i in range(N):
  for j in range(i):L[i][j]=(A[i][j]-sum(L[i][k]*L[j][k]*D[k] for k in range(j)))/D[j]
  d=A[i][i]-sum(L[i][k]**2*D[k] for k in range(i));D.append(d);L[i][i]=1
  if d<=1e-12:return min(D)
 return min(D)
for M in [3,4]:
 best=(1e10,None);count=0
 for trial in range(12000):
  if time.monotonic()-start>35:break
  N=12;lam=[0.]
  for _ in range(N-1):lam.append(lam[-1]+rng.uniform(.005,1))
  span=min(lam[i+M]-lam[i] for i in range(N-M));lam=[x*math.pi/span for x in lam]
  A=[[kernel(x-y,M) for y in lam] for x in lam];q=ldlt(A);count+=1
  if q<best[0]:best=(q,lam)
 out.append({'M':M,'trials':count,'least_LDL_pivot':best[0],'lambda':best[1]})
p=Path(__file__).parent;(p/'bernstein-diagnostic.json').write_text(json.dumps({'seed':395581,'seconds':time.monotonic()-start,'method':'source exact g3/g4 formulas evaluated in double precision; LDL, stop at pivot<=1e-12','numerical_only':True,'results':out},indent=2));print(out)
