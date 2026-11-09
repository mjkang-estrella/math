import itertools,math,json,time,random
import numpy as np
from pathlib import Path
D=Path(__file__).resolve().parents[1];t=time.time();P=65521

def rank(a):
 a=np.array(a,dtype=np.int64);r=0
 if a.size==0:return 0
 for j in range(a.shape[1]):
  nz=np.flatnonzero(a[r:,j])
  if len(nz)==0:continue
  k=r+nz[0];a[[r,k]]=a[[k,r]];a[r]=a[r]*pow(int(a[r,j]),-1,P)%P
  for k in range(r+1,len(a)):
   if a[k,j]:a[k]=(a[k]-a[k,j]*a[r])%P
  r+=1
  if r==len(a):break
 return r
out=[]
for m in range(1,5):
 for d in range(1,8):
  mons=[v for v in itertools.product(range(d+1),repeat=4) if sum(v)==d and v[2]+v[3]>=m]
  for r in range(1,9):
   best=0
   for seed in range(3):
    rng=random.Random(10000*m+100*d+10*r+seed);a=[]
    for _ in range(r):
     ends=[[rng.randrange(P) for i in range(4)]for k in range(2)];cols=[]
     for v in mons:
      pol=[1]
      for i,e in enumerate(v):
       pol=np.convolve(pol,[math.comb(e,j)*pow(ends[0][i],e-j,P)*pow(ends[1][i],j,P)%P for j in range(e+1)])%P
      cols.append(pol)
     a.extend(np.array(cols).T.tolist() if cols else [[]for _ in range(d+1)])
    best=max(best,rank(a))
   out.append({'m':m,'d':d,'r':r,'kernel_basis_dimension':len(mons),'rank_mod_p':best,'expected':min(len(mons),r*(d+1))})
res={'scope':'P3: all 224 parameter triples m=1..4,d=1..7,r=1..8; 3 deterministic specializations over F65521 per triple; rows are restrictions to simple lines of monomial basis of (x2,x3)^m in degree d','diagnostic_only':True,'generic_semantic_limit':'Maximal modular rank supplies lower bound on characteristic-zero generic rank when fat-line jet restriction is onto; deficient samples do not refute a generic claim. For d<m-1 target global sections need separate accounting.','cases':out,'deficient':[a for a in out if a['rank_mod_p']<a['expected']],'wall_seconds':time.time()-t}
(D/'outputs/maxrank.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res['deficient']))
