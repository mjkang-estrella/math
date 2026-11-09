import sys; sys.path.insert(0,"/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/fresh-corpus-r10/pydeps")
import numpy as np,json,pathlib,time
L=pathlib.Path(__file__).resolve().parents[1]; out=[]
for p,q,n in [(p,q,n) for p in range(1,6) for q in range(p,6) if p+q<=8 for n in range(3,6) if (p+q)**n<=4096]:
 Q=p+q; z=Q**n; N=min(1500000,max(65536,3*z*z)); t=np.zeros(N,dtype=np.uint8); idx=np.arange(N)
 power=1
 while power<N:
  t^=((idx//power)%Q>=p).astype(np.uint8); power*=Q
 bound=z+Q-2
 if p==q and n%2==0: bound=z+Q+(2 if p==1 else 0)
 elif p==q and p==1: bound=z+Q
 elif min(p,q)==1: bound=z+Q-1
 ds=sorted(set(range(1,min(z+1,max(32,50000000//N))+1))|{z-1,z,z+1}); best=(0,0,0)
 for d in ds:
  k=N//d; a=t[:k*d].reshape(k,d).T.copy(); changes=np.ones((d,k),dtype=np.bool_); changes[:,1:]=a[:,1:]!=a[:,:-1]
  cuts=np.r_[np.flatnonzero(changes.ravel()),d*k]; dif=np.diff(cuts); j=int(dif.argmax()); run=int(dif[j]); row,pos=divmod(int(cuts[j]),k)
  if run>best[0]: best=run,d,row+pos*d
 r=dict(p=p,q=q,n=n,prefix=N,differences=ds,bound=bound,observed=best,violation=best[0]>bound);out.append(r);print(json.dumps(r),flush=True)
 (L/'outputs/words.json').write_text(json.dumps(out,indent=2))
