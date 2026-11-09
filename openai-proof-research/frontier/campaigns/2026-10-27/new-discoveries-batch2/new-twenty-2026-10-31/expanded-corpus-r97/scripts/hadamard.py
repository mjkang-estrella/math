import numpy as np,itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in [4,8,16]:
 H=np.array([[1-2*((i&j).bit_count()%2) for j in range(n)] for i in range(n)],dtype=np.int16)
 assert np.array_equal(H@H.T,n*np.eye(n,dtype=int))
 for r in range(1,min(n,7)):
  sets=list(itertools.combinations(range(1,n),r-1))
  # all row choices at n<=8; first 25 and spaced 25 for n16, exact list retained.
  if n==16 and len(sets)>50:sets=sets[:25]+sets[-25:]
  for s in sets:
   deleted=(0,)+s;K=H[[i for i in range(n) if i not in deleted]];d=n-r
   dist=((d-K.T@K)//2);diam=int(dist.max())
   X=(1-2*((np.arange(1<<d)[:,None]>>np.arange(d))&1)).astype(np.int16)
   okay=np.all(((d-X@K)//2)<=diam,axis=1)
   cols={tuple(K[:,i]) for i in range(n)};extend=[tuple(map(int,x)) for x in X[okay] if tuple(x) not in cols]
   out.append({'n':n,'r':r,'deleted':deleted,'diameter':diam,'new_extensions':len(extend),'first':extend[:1]})
 print('completed',n,'cases',len(out),flush=True)
(D/'outputs/hadamard.json').write_text(json.dumps(out,indent=2)+'\n')
print('extensions',sum(x['new_extensions']>0 for x in out),flush=True)
