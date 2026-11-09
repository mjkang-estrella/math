import itertools as it,random,json
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def shift(n,faces,p,seed):
 rng=random.Random(seed);M=[[rng.randrange(p) for _ in range(n)] for _ in range(n)];basis={};out=set()
 for i,j in it.combinations(range(n),2):
  v=[(M[a][i]*M[b][j]-M[a][j]*M[b][i])%p for a,b in faces]
  for k,w in sorted(basis.items()):
   if v[k]:c=v[k];v=[(a-c*b)%p for a,b in zip(v,w)]
  k=next((k for k,a in enumerate(v) if a),None)
  if k is not None:
   inv=pow(v[k],p-2,p);basis[k]=[a*inv%p for a in v];out.add((i,j))
 return out
rows=[]
for n in [3,4,5]:
 pairs=list(it.combinations(range(n),2));bad=[];unstable=0
 for mask in range(1<<len(pairs)):
  faces=[e for j,e in enumerate(pairs) if mask>>j&1];non=set(pairs)-set(faces)
  inc=set()
  for a,b in non:
   for k in range(n+1):inc.add((a+(a>=k),b+(b>=k)))
  nextfaces=[e for e in it.combinations(range(n+1),2) if e not in inc]
  outcomes=[]
  for seed,p in [(103,1000003),(104,1000033)]:
   a=shift(n,faces,p,seed);b=shift(n+1,nextfaces,p,seed)
   violations=[(x+(x>=k),y+(y>=k)) for x,y in set(pairs)-a for k in range(n+1) if (x+(x>=k),y+(y>=k)) in b]
   outcomes.append((a,b,violations))
  if outcomes[0][:2]!=outcomes[1][:2]:unstable+=1
  elif outcomes[0][2]:bad.append(dict(mask=mask,violations=outcomes[0][2]))
 rows.append(dict(n=n,graph_complexes=1<<len(pairs),unstable_specializations=unstable,stable_violations=bad));print(rows[-1],flush=True)
(D/'outputs/shifting.json').write_text(json.dumps(dict(rows=rows,limitation='Exterior degree-2 diagnostic with two finite-field specializations; genericity and symmetric shifting not certified'),indent=2)+'\n')
