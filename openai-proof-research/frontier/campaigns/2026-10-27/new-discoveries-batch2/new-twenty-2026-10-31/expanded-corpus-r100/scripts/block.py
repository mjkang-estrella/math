import numpy as np,random,json
random.seed(347241);out=[]
for q in [2,3,4,6]:
 for b in [3,4,6,10,15,25]:
  n=b*q+1
  def graph(parents):
   A=np.zeros((n,n))
   for j,p in enumerate(parents):
    vs=[p]+list(range(1+j*q,1+(j+1)*q))
    for x in vs:
     for y in vs:
      if x!=y:A[x,y]=1
   return A
  P=graph([0]+[1+(j-1)*q for j in range(1,b)]);rp=np.linalg.eigvalsh(P)[-1];worst=1e9;witness=[]
  for k in range(300):
   pars=[random.randrange(j*q+1) for j in range(b)];A=graph(pars);rho=np.linalg.eigvalsh(A)[-1]
   for x in [rho+1e-5,rho+.01,rho+.1,rho+1,rho+10]:
    s1,l1=np.linalg.slogdet(x*np.eye(n)-P);s2,l2=np.linalg.slogdet(x*np.eye(n)-A)
    if l1<l2-1e-7:witness.append(dict(parents=pars,x=x,logdet_P=l1,logdet_G=l2))
   worst=min(worst,rho-rp)
  row=dict(q=q,b=b,n=n,random_graphs=300,minimum_rho_difference=worst,polynomial_violations=witness);out.append(row);print(row,flush=True)
json.dump(out,open('outputs/block.json','w'),indent=2)
