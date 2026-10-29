import itertools,random,math,json,numpy as np
random.seed(721)
ps=[2.001,2.2,2.5,2.9];ss=[0,.25,.5,.75,1];worst=(1e100,None);count=0
for n in range(2,7):
 states=np.array(list(itertools.product(range(5),repeat=n)))
 # each coordinate distribution mixture: old +/-a, new 0,+/-sqrt2a
 for it in range(80):
  a=[random.randint(1,15) for _ in range(n)]
  val=np.array([-1,1,0,-math.sqrt(2),math.sqrt(2)])[states]@np.array(a)
  for s in ss:
   w=np.array([(1-s)/2,(1-s)/2,s/2,s/4,s/4]);dw=np.array([-.5,-.5,.5,.25,.25])
   derivative=sum(np.prod(w[states[:,[j for j in range(n) if j!=i]]],axis=1)*dw[states[:,i]] for i in range(n))
   for p in ps:
    d=float(derivative@abs(val)**p)/sum(b*b for b in a)**(p/2);count+=1
    if d<worst[0]:worst=(d,{'a':a,'s':s,'p':p})
json.dump({'checks':count,'worst':worst,'status':'floating only; not source counterexample'},open('interpolation.json','w'),indent=2);print(count,worst)
