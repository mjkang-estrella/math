from pathlib import Path
import runpy,random,json
R=Path(__file__).resolve().parents[1];g=runpy.run_path(str(R/'work/flag-betti.py'),run_name='flaglib');beta=g['beta'];lexcomp=g['lexcomp'];names=g['names'];rng=random.Random(142)
n=5;found=None;cache={}
for trial in range(240):
 A={s for s in range(1<<n) if s.bit_count()<=rng.randrange(1,n+1)}
 A={t for s in A for t in range(1<<n) if t&s==t}
 B={s for s in A if rng.random()<.4};B={t for s in B for t in A if t&s==t}
 D=frozenset(A-B);L=frozenset(lexcomp(A,n)-lexcomp(B,n))
 for W in (D,L):
  if W not in cache:cache[W]=beta(W,n)
 a,b=cache[D],cache[L]
 if any(v>b.get(k,0) for k,v in a.items()):
  found=dict(A=names(A,n),B=names(B,n),D=names(D,n),L=names(L,n),beta={str(k):v for k,v in a.items()},lex_beta={str(k):v for k,v in b.items()});break
print('trials',trial+1,'found',json.dumps(found))
(R/'packet/private/flag-random-n5.json').write_text(json.dumps(dict(trials=trial+1,seed=142,field=1000003,found=found),indent=2))
