import numpy as np
rng=np.random.default_rng(314159)
def f(x,d,h):
 x=np.abs(x);x=x/np.linalg.norm(x);p=x*x
 a=((p[:,None]+p[None,:])/2).ravel();g=(x[:,None]*x[None,:]).ravel()
 return np.partition(a,-h)[-h:].sum()+np.partition(g,-h)[-h:].sum()
for d in [4,5,6,8,10,15,20,30,50,100]:
 h=2*d-5
 best=(-1,None)
 for it in range(30):
  x=rng.random(d)**(1+it%5);x[0]*=d
  for _ in range(100):
   x=np.abs(x)/np.linalg.norm(x);p=x*x
   aa=((p[:,None]+p[None,:])/2).ravel();gg=(x[:,None]*x[None,:]).ravel()
   ia=np.argpartition(aa,-h)[-h:];ig=np.argpartition(gg,-h)[-h:]
   ar=np.zeros((d,d));gr=np.zeros((d,d));ar.ravel()[ia]=.5;gr.ravel()[ig]=1
   Q=(gr+gr.T)/2+np.diag(ar.sum(0)+ar.sum(1))
   ev,evec=np.linalg.eigh(Q);nx=abs(evec[:,-1])
   if np.linalg.norm(nx-x)<1e-11:break
   x=nx
  v=f(x,d,h)
  if v>best[0]:best=(v,abs(x)/np.linalg.norm(x))
 print(d,h,best[0],best[0]-d,np.sort(best[1]**2)[::-1][:8].tolist(),flush=True)
