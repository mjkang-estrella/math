import sys,json
from pathlib import Path
D=Path(__file__).resolve().parents[1]
exec(compile((D/'scripts/domatic.py').read_text().split('mode=sys.argv')[0],'domatic-core','exec'))
exec(compile((D/'scripts/graphideal.py').read_text().split('rng=random.Random')[0],'graphideal-core','exec'))
exec(compile((D/'scripts/fork.py').read_text().split('rng=random.Random')[0],'fork-core','exec'))
entries=[]
for block in (D/'sources/atlas.dat').read_text().split('GRAPH ')[1:]:
 ls=block.splitlines();idx=int(ls[0]);n=int(ls[1].split()[1]);es=[tuple(map(int,l.split())) for l in ls[2:] if l.strip()];entries.append((idx,n,es))
res=[]
for ix,n,es in entries:
 if n!=7:continue
 nb=[1<<i for i in range(n)]
 for a,b in es:nb[a]|=1<<b;nb[b]|=1<<a
 vals=values(nb) if min(b.bit_count() for b in nb)>=4 else None
 fork=check([nb[i]^(1<<i) for i in range(n)])
 seen=1
 while True:
  new=seen
  for v in range(n):
   if seen>>v&1:new|=nb[v]
  if new==seen:break
  seen=new
 vr=invariants(nb) if seen==(1<<n)-1 else None
 if vals and abs(vals[0]-vals[1])>1:print('DOMATIC WITNESS',ix,vals,flush=True)
 if fork not in [None,True]:print('FORK WITNESS',ix,fork,flush=True)
 if vr and vr[0]>vr[1]:print('IDEAL WITNESS',ix,vr,flush=True)
 res.append({'atlas_id':ix,'domatic':vals,'fork_free':fork is not None,'fork_test':fork,'v_reg_GF2':vr})
 if ix%50==0:print('progress',ix,len(res),flush=True)
 (D/'outputs/atlas-search.json').write_text(json.dumps(res))
print('COMPLETE',len(res),flush=True)
