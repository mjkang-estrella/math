import numpy as np,itertools,json
from pathlib import Path
rng=np.random.default_rng(20261026)
def calc(fs):
 fs=sorted(fs,key=lambda x:(x.bit_count(),x));n=len(fs);idx={f:i for i,f in enumerate(fs)}
 L=np.array([[bool(a&b) for b in fs]for a in fs],dtype=float)
 d=np.zeros((n,n))
 for a in fs:
  vs=[j for j in range(a.bit_length()) if (a>>j)&1]
  for k,v in enumerate(vs):
   b=a^(1<<v)
   if b in idx:d[idx[a],idx[b]]=(-1)**k
 D=d+d.T
 el=np.linalg.eigvalsh(L)[::-1];ed=np.linalg.eigvalsh(D)[::-1];g=np.cumsum(el-ed)
 return g.min(),g,el,ed
best=0
for v in range(4,13):
 for it in range(2000):
  fs=set(range(1,1<<v)) if False else set(1<<j for j in range(v))
  dim=rng.integers(2,min(v,5)+1);pp=rng.random()*.7
  for c in itertools.combinations(range(v),dim):
   if rng.random()<pp:
    mask=sum(1<<j for j in c);x=mask
    while x:fs.add(x);x=(x-1)&mask
  if len(fs)>300:continue
  m,g,el,ed=calc(fs)
  if m<best:
   best=m
   if m< -1e-7:
    o={'vertices':v,'faces':sorted(fs),'min':float(m),'gaps':g.tolist(),'L_eigs':el.tolist(),'D_eigs':ed.tolist()};Path('third-discovery/connection-hit.json').write_text(json.dumps(o,indent=2));print(o,flush=True);raise SystemExit
 print(v,'nohit',best,flush=True)
