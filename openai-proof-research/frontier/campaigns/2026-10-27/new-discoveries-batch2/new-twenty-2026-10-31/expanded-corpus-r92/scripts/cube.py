import itertools,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[1];out=[]
for d in [2,3,4]:
 N=2**d;edges=[(x,x^(1<<i)) for x in range(N) for i in range(d) if x<(x^(1<<i))]
 orders=itertools.permutations(range(1,N)) if d<=3 else (random.Random(k).sample(range(1,N),N-1) for k in range(20000))
 count=0;regular={};bad=[]
 for tail in orders:
  p=[0]+list(tail);pos=[0]*N
  for i,v in enumerate(p):pos[v]=i
  prof=[[] for _ in p]
  for u,v in edges:
   z=abs(pos[u]-pos[v]);z=min(z,N-z);prof[u].append(z);prof[v].append(z)
  prof=[tuple(sorted(z,reverse=True)) for z in prof];count+=1
  if len(set(prof))!=1:continue
  a=prof[0];regular[str(a)]=regular.get(str(a),0)+1
  # Source sorts descending, unlike MathDB paraphrase.
  failures=[]
  if any(2*a[i] > N-2**(d-(i+1)) for i in range(d)):failures.append('profile')
  if d>=3 and not any(z%2==0 for z in a):failures.append('no-even')
  if d>=4 and any(a.count(z)>1 for z in a if z%2):failures.append('repeated-odd')
  if failures:bad.append(dict(order=p,profile=a,failures=failures))
 out.append(dict(d=d,orders=count,regular_profiles=regular,failures=bad));print(out[-1]);(D/'outputs/cube.json').write_text(json.dumps(out,indent=2))
