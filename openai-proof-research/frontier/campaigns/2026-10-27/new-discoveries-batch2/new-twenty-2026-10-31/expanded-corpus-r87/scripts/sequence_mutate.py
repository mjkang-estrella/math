import itertools as it,random,time,json
from pathlib import Path
D=Path(__file__).resolve().parents[1]
# Read the standalone source-derived decomposition function without running its sweeps.
s=(D/'scripts/sequence_deep.py').read_text();exec(s[s.index('def decomp'):s.index('# Exact rectangular')])
rng=random.Random(8705)
for m in [2,3,4]:
 n=m*m;vs=list(it.product(range(n),repeat=3));base=[(i*m+j,i*m+k,j*m+k) for i,j,k in it.product(range(m),repeat=3)]
 best=base[:];cur=base[:];start=time.monotonic();trials=0;equal=0;bad=None
 def lt(a,b):return sum(x<y for x,y in zip(a,b))>=2
 while time.monotonic()-start<25:
  trials+=1
  seq=cur[:] if rng.random()<.8 else base[:]
  for _ in range(rng.randrange(1,min(8,len(seq)))):seq.pop(rng.randrange(len(seq)))
  candidates=rng.sample(vs,min(len(vs),300))
  for t in candidates:
   pos=0;valid=True;seen_after=False
   for i,a in enumerate(seq):
    if lt(a,t):
     if seen_after:valid=False;break
     pos=i+1
    elif lt(t,a):seen_after=True
    else:valid=False;break
   if valid:seq.insert(pos,t)
  if len(seq)>len(best):best=seq[:]
  if len(seq)>=len(base):
   equal+=1
   if len(seq)>n**1.5 or not decomp(seq):bad=seq;break
  if len(seq)>=len(cur)-1 or rng.random()<.02:cur=seq
 print(json.dumps(dict(n=n,seed_length=len(base),trials=trials,best_length=len(best),equality_or_better_sequences_tested=equal,counterexample=bad,seconds=time.monotonic()-start)),flush=True)
 (D/f'outputs/sequence-mutate-{n}.json').write_text(json.dumps(dict(best=best,counterexample=bad),indent=2)+'\n')
