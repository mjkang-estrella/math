import numpy as np,json,gzip
from pathlib import Path
def atlas():
 gs=[]
 for line in gzip.open('sources/atlas.dat.gz','rt'):
  if line.startswith('GRAPH'):
   ident=int(line.split()[1]);edges=[]
  elif line.startswith('NODES'):
   n=int(line.split()[1]);gs.append((ident,n,edges))
  else:edges.append(tuple(map(int,line.split())))
 return gs
def matrix(n,edges):
 s=np.ones((n,n))-np.eye(n)
 for i,j in edges:s[i,j]=s[j,i]=-1
 return s
rows=[];ps=[2.0001,2.01,2.1,2.5,2.99,3,4,6]
for n in range(2,8):
 gs=[g for g in atlas() if g[1]==n]
 maxima=[(-1,None) for p in ps];hits=[]
 for g in gs:
  s=matrix(n,g[2])
  e=np.linalg.eigvalsh(s)
  for k,p in enumerate(ps):
   val=sum(abs(e)**p);base=(n-1)**p+n-1
   if val>maxima[k][0]:maxima[k]=(float(val),g[0])
   if val>base+1e-7:hits.append([p,float(val-base)])
 rows.append({'n':n,'graphs':len(gs),'maxima':maxima,'violations':hits})
# Genuine Seidel singular C5 is an obstruction to determinant comparison.
s=matrix(5,[(i,(i+1)%5) for i in range(5)])
# Continuous zero-trace, fixed-second-moment relaxation, n=5, p=2.1.
p=2.1;relax=2*10**(p/2);complete=4**p+4
out={'p_grid':ps,'atlas':rows,'continuous_relaxation':{'n':5,'p':p,'spectrum':['sqrt(10)','-sqrt(10)',0,0,0],'energy':relax,'complete_energy':complete},'C5_spectrum':np.linalg.eigvalsh(s).tolist(),'C5_S2_determinant':round(np.linalg.det(s@s))}
Path('checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
