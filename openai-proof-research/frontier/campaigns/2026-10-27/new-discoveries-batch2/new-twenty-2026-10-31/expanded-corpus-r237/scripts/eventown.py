from pathlib import Path
import random,math,json
L=Path(__file__).resolve().parents[1];rng=random.Random(237);out=[]
for n in [6,8,10,12]:
 N=1<<(n//2);U=[x for x in range(1<<n) if x.bit_count()%2==0]
 for s in sorted({3,N//2,N-(1<<(n//4))}):
  if s<3:continue
  k=N+s;target=s*N//2;best=10**9;proposals=0
  for restart in range(8):
   A=[sum(3<<(2*j) for j in range(n//2) if b>>j&1) for b in range(N)]
   A+=rng.sample(list(set(U)-set(A)),s);used=set(A)
   obj=sum((x&y).bit_count()%2 for i,x in enumerate(A) for y in A[:i])
   for t in range(12000):
    i=rng.randrange(k);y=rng.choice(U)
    if y in used:continue
    proposals+=1;x=A[i]
    delta=sum(((y&z).bit_count()%2)-((x&z).bit_count()%2) for j,z in enumerate(A) if j!=i)
    temp=(1-t/12000)*2+0.05
    if delta<=0 or rng.random()<math.exp(-delta/temp):used.remove(x);used.add(y);A[i]=y;obj+=delta
    if obj<best:best=obj;bestA=A[:]
    if best<target:break
   if best<target:break
  r={'n':n,'s':s,'size':k,'target':target,'best':best,'best_family':bestA,'proposals':proposals,'restarts':restart+1};out.append(r);print({a:b for a,b in r.items() if a!='best_family'},flush=True)
  (L/'outputs/eventown.json').write_text(json.dumps(out,indent=2))
