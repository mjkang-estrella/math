import sys,json
from pathlib import Path
D=Path(__file__).resolve().parents[1]
exec(compile((D/'scripts/domatic.py').read_text().split('mode=sys.argv')[0],'domatic-core','exec'))
exec(compile((D/'scripts/graphideal.py').read_text().split('rng=random.Random')[0],'graphideal-core','exec'))
exec(compile((D/'scripts/fork.py').read_text().split('rng=random.Random')[0],'fork-core','exec'))
start=int(sys.argv[1]);stop=int(sys.argv[2]);mode=sys.argv[3];out=[]
lines=(D/'sources/graph8.g6').read_text().splitlines()
for ix,g in enumerate(lines):
 if not start<=ix<stop:continue
 vals=[ord(c)-63 for c in g];n=vals[0];assert n==8;bits=[(v>>(5-j))&1 for v in vals[1:] for j in range(6)];nb=[1<<i for i in range(n)];pos=0
 for j in range(1,n):
  for i in range(j):
   if bits[pos]:nb[i]|=1<<j;nb[j]|=1<<i
   pos+=1
 if mode=='domatic':ans=values(nb) if min(b.bit_count() for b in nb)>=4 else None;bad=ans and abs(ans[0]-ans[1])>1
 elif mode=='fork':ans=check([b^(1<<i) for i,b in enumerate(nb)]);bad=ans not in [None,True]
 else:
  seen=1
  while True:
   new=seen
   for v in range(n):
    if seen>>v&1:new|=nb[v]
   if new==seen:break
   seen=new
  ans=invariants(nb) if seen==(1<<n)-1 else None;bad=ans and ans[0]>ans[1]
 out.append([ix,ans]);
 if bad:print('WITNESS',mode,ix,g,ans,flush=True)
 if ix%100==0:
  print('progress',mode,ix,flush=True);(D/f'outputs/graph8-{mode}-{start}-{stop}.json').write_text(json.dumps(out))
(D/f'outputs/graph8-{mode}-{start}-{stop}.json').write_text(json.dumps(out));print('COMPLETE',mode,start,stop,'actual',len(out),'dataset',len(lines),flush=True)
