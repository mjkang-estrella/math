import numpy as np,sys,json,time
from pathlib import Path
D=Path(__file__).resolve().parents[1];n=int(sys.argv[1]);wheel=sys.argv[2]=='wheel';E=[(i,(i+1)%n) for i in range(n)]+[(i,n if wheel else i) for i in range(n)];nv=n+int(wheel);inc=[sum(1<<j for j,e in enumerate(E) if i in e) for i in range(nv)];b=2*n;S=1<<b;ix=np.arange(S,dtype=np.uint32);pc=np.zeros(S,dtype=np.uint8)
for k in range(b):pc+=((ix>>k)&1).astype(np.uint8)
v=np.full(S,-100,dtype=np.int8);v[0]=0;t=time.monotonic()
for k in range(1,b+1):
 I=ix[pc==k];best=np.full(len(I),-100,dtype=np.int8)
 for j,(a,c) in enumerate(E):
  bit=np.uint32(1<<j);sel=(I&bit)!=0;J=I[sel];new=J^bit
  gain=((J&inc[a])==bit).astype(np.int8)
  if c!=a:gain+=((J&inc[c])==bit).astype(np.int8)
  cand=np.where(gain>0,gain+v[new],-v[new]);best[sel]=np.maximum(best[sel],cand)
 v[I]=best;print('layer',k,'states',len(I),'seconds',time.monotonic()-t,flush=True)
r={'n':n,'family':sys.argv[2],'state_count':S,'difference':int(v[-1]),'score':[(nv+int(v[-1]))//2,(nv-int(v[-1]))//2]};print(r,flush=True);(D/f'outputs/game-{n}-{sys.argv[2]}.json').write_text(json.dumps(r,indent=2)+'\n')
