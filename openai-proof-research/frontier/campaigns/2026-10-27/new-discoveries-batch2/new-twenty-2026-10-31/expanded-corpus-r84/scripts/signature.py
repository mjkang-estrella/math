import itertools,math,json,random,time
import numpy as np
from pathlib import Path
P=65521
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

D=Path(__file__).resolve().parents[1];t=time.time()
def mul(a,b):return np.r_[a[0]*b[0]%P,(a[1:]*b[0]+b[1:]*a[0])%P]
def jac(d,k,m,seed,kind):
 rng=random.Random(seed);N=d*m;variables=[]
 for v in range(N):
  a=np.zeros(N+1,dtype=np.int64);a[0]=rng.randrange(P);a[v+1]=1;variables.append(a)
 one=np.zeros(N+1,dtype=np.int64);one[0]=1
 rows=[]
 for word in itertools.product(range(d),repeat=k):
  if kind=='polynomial':
   pol=[one]
   for i in word:
    new=[np.zeros(N+1,dtype=np.int64)for _ in range(len(pol)+m)]
    for s,a in enumerate(pol):
     for j in range(1,m+1):new[s+j]=(new[s+j]+mul(a,variables[i*m+j-1])*j*pow(s+j,-1,P))%P
    pol=new
   value=sum(pol)%P
  else:
   value=np.zeros(N+1,dtype=np.int64)
   for cuts in itertools.combinations_with_replacement(range(k+1),m-1):
    cuts=(0,)+cuts+(k,);term=one.copy()
    for j in range(m):
     for i in word[cuts[j]:cuts[j+1]]:term=mul(term,variables[i*m+j])
     term=term*pow(math.factorial(cuts[j+1]-cuts[j]),-1,P)%P
    value=(value+term)%P
  rows.append(value[1:])
 return rank(rows)
cases=[]
import sympy
for d,k,m in itertools.product([2,3],[3,4],range(2,5)):
 lam=sum(sum(int(sympy.mobius(e))*d**(j//e)for e in sympy.divisors(j))//j for j in range(1,k+1))
 for kind in ['polynomial','piecewise_linear']:
  rs=[jac(d,k,m,2718+s,kind)for s in range(3)];cases.append(dict(d=d,k=k,m=m,kind=kind,lambda_dk=lam,expected_affine_rank=min(lam,d*m),sample_ranks=rs))
(D/'outputs/signature.json').write_text(json.dumps({'diagnostic_only':True,'scope':'All 24 d=2,3 k=3,4 m=2..4 kind combinations; three reproducible modular specializations each; dual-number exact modular Jacobian of literal iterated integral/tensor exponential formulas','cases':cases,'deficient':[c for c in cases if max(c['sample_ranks'])<c['expected_affine_rank']],'limitation':'Generic rank lower evidence only; finite-field deficient samples do not prove generic deficiency; projective dimension is affine rank minus one for homogeneous maps.','wall_seconds':time.time()-t},indent=2)+'\n')
print('signature cases',len(cases))
