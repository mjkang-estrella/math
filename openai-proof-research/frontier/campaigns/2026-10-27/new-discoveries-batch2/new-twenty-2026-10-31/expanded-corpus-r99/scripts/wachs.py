import os,resource,time,itertools,json,random
resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);import numpy as np
start=time.time();n=7;W=[]
for a in itertools.permutations(range(1,n+1)):
 for bits in range(1<<n):
  v=tuple(-x if bits>>i&1 else x for i,x in enumerate(a));pos={x:i+1 for i,x in enumerate(v)};pos.update({-x:-i for x,i in list(pos.items())})
  if all(abs(pos[i]-pos[i+1])<=1 for i in range(1,n,2)):W.append(v)
def length(v):return sum(v[i]>v[j] for i in range(n)for j in range(i+1,n))+sum(x<0 for x in v)+sum(v[i]+v[j]<0 for i in range(n)for j in range(i+1,n))
W.sort(key=length);N=len(W);emb=[tuple(-x for x in reversed(v))+v for v in W];ranks=np.array([[x for k in range(1,2*n)for x in sorted(v[:k])]for v in emb],dtype=np.int8);comp=np.zeros((N,N),dtype=bool)
for i in range(N):
 comp[i,:]=np.all(ranks[i]<=ranks,axis=1)
 if time.time()-start>80:raise RuntimeError('comparison cap')
output={'n':n,'elements':N,'source_verified_n':6,'comparability':'signed embedding into symmetric Bruhat; sorted prefix criterion','bottoms':[],'counterexamples':[]}
rng=random.Random(381793);inds=list(range(N));rng.shuffle(inds)
for u in inds:
 mu=np.zeros(N,dtype=np.int64);mu[u]=1
 for v in range(u+1,N):
  if comp[u,v]:mu[v]=-np.sum(mu[:v][comp[:v,v]])
 vals=sorted(set(int(x)for x in mu));output['bottoms'].append({'index':u,'window':W[u],'intervals':int(comp[u].sum()),'mobius_values':vals})
 if any(abs(x)>1 for x in vals):output['counterexamples'].append({'u':W[u],'v':W[int(np.argmax(abs(mu)))],'mu':int(mu[int(np.argmax(abs(mu)))])})
 output['seconds']=time.time()-start;json.dump(output,open('outputs/wachs.json','w'),indent=2)
 if time.time()-start>100:break
print('elements',N,'bottoms',len(output['bottoms']),'counterexamples',output['counterexamples'])
