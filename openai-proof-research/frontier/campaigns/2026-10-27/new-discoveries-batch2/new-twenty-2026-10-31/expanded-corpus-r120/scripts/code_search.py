import random,json,itertools
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def swap(x,n):return ((x&sum(1<<i for i in range(0,n,2)))<<1)|((x&sum(1<<i for i in range(1,n,2)))>>1)
def span(rows):
 s={0};bs=[]
 for r in rows:
  if r not in s:s|={x^r for x in list(s)};bs.append(r)
 return s,bs
rng=random.Random(355525)
for n,r in [(10,3),(12,3),(14,4),(16,4),(18,5),(20,5),(22,5),(24,6)]:
 for trial in range(60):
  rows=[]
  for _ in range(r):
   x=rng.randrange(1<<n);rows.extend([x,swap(x,n)])
  C,bs=span(rows)
  sig=[tuple(sum(1 for x in C if x.bit_count()==w and x>>i&1) for w in range(n+1)) for i in range(n)]
  classes={s:[i for i in range(n) if sig[i]==s] for s in sig}
  if any(len(c)!=2 for c in classes.values()):continue
  pairs=list(classes.values()); autos=[]
  for mask in range(1<<len(pairs)):
   def perm(x):
    for j,(a,b) in enumerate(pairs):
     if mask>>j&1 and (x>>a&1)!=(x>>b&1):x^=(1<<a)|(1<<b)
    return x
   if all(perm(x) in C for x in bs):autos.append(mask)
  print('n',n,'trial',trial,'dim',len(bs),'classes',pairs,'autos',autos,flush=True)
  if len(autos)==2:
   o=dict(n=n,dimension=len(bs),rows=bs,trial=trial,classes=pairs,automorphism_masks=autos,coordinate_signatures=sig,weight_distribution=[sum(x.bit_count()==w for x in C) for w in range(n+1)])
   (D/'outputs/code-counterexample.json').write_text(json.dumps(o,indent=2)+'\n');print('FOUND',o,flush=True);raise SystemExit
 print('completed',n,60,'random orbit-generated codes',flush=True)
