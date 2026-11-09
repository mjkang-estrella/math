import os,resource,time,itertools,json,random
resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);import numpy as np
start=time.time();n=8;W=[]
blocks=[(i,i+1) for i in range(1,n,2)]
for order in itertools.permutations(blocks):
 for bits in range(1<<(n//2)):
  for signs in range(1<<(n//2)):
   v=[]
   for j,pair in enumerate(order):
    pair=pair[::-1] if bits>>j&1 else pair
    v.extend([-x if signs>>j&1 else x for x in pair])
   W.append(tuple(v))
def length(v):return sum(v[i]>v[j] for i in range(n)for j in range(i+1,n))+sum(x<0 for x in v)+sum(v[i]+v[j]<0 for i in range(n)for j in range(i+1,n))
W.sort(key=length);N=len(W);emb=[tuple(-x for x in reversed(v))+v for v in W];ranks=np.array([[x for k in range(1,2*n)for x in sorted(v[:k])]for v in emb],dtype=np.int8);comp=np.zeros((N,N),dtype=bool)
for i in range(N):
 comp[i,:]=np.all(ranks[i]<=ranks,axis=1)
 if time.time()-start>80:raise RuntimeError('comparison cap')
output=json.load(open('outputs/wachs8.json')); previous_time=output['seconds']; done={r['index'] for r in output['bottoms']}
rng=random.Random(381793);inds=list(range(N));rng.shuffle(inds)
for u in inds:
 if u in done:continue
 mu=np.zeros(N,dtype=np.int64);mu[u]=1
 for v in range(u+1,N):
  if comp[u,v]:mu[v]=-np.sum(mu[:v][comp[:v,v]])
 vals=sorted(set(int(x)for x in mu));output['bottoms'].append({'index':u,'window':W[u],'intervals':int(comp[u].sum()),'mobius_values':vals})
 if any(abs(x)>1 for x in vals):output['counterexamples'].append({'u':W[u],'v':W[int(np.argmax(abs(mu)))],'mu':int(mu[int(np.argmax(abs(mu)))])})
 output['seconds']=previous_time+time.time()-start;json.dump(output,open('outputs/wachs8.json','w'),indent=2)
 if time.time()-start>100:break
print('elements',N,'bottoms',len(output['bottoms']),'counterexamples',output['counterexamples'])
