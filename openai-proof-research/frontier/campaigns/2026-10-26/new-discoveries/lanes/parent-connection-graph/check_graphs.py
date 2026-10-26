import numpy as np,itertools,random
rng=random.Random(372758)
mins=(float('inf'),None);count=0
for n in range(1,13):
 for a in range(200):
  edges=[(i,j) for i in range(n) for j in range(i+1,n) if rng.random()<rng.random()]
  m=len(edges);U=np.zeros((n,m));C=U.copy()
  for z,(i,j) in enumerate(edges):U[i,z]=U[j,z]=1;C[i,z]=-1;C[j,z]=1
  L=np.block([[np.eye(n),U],[U.T,U.T@U-np.eye(m)]])
  D=np.block([[np.zeros((n,n)),C],[C.T,np.zeros((m,m))]])
  ls=np.linalg.eigvalsh(L)[::-1];ds=np.linalg.eigvalsh(D)[::-1];g=np.cumsum(ls-ds)
  deg=np.sort(U.sum(axis=1))[::-1]
  for k in range(1,n+1):
   assert ls[:k].sum()+1e-7>=k+deg[:k].sum()/2
   assert ds[:k].sum()<=np.sqrt(2*k*deg[:k].sum())+1e-7
  if min(g)<mins[0]:mins=(float(min(g)),{'n':n,'m':m,'k':int(g.argmin())+1})
  count+=1
print({'cases':count,'minimum_gap':mins,'qualification':'numerics supporting proposed general graph proof only'})
