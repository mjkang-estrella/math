import itertools as it,math,random,resource,time,json,pathlib
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90));random.seed(40)
L=pathlib.Path(__file__).resolve().parent;out={}
# Response column for each target k chooses its guessed position. This is not required to be a permutation.
for n in (3,4,5,6):
 ps=list(it.permutations(range(n)));score=lambda rows:sum(max(sum(p[k]==r[k] for k in range(n)) for r in rows) for p in ps)
 rows=[tuple((i+j)%n for i in range(n)) for j in range(n)];base=score(rows);best=base;w=rows
 # finite coordinate ascent, 4 restarts, each coordinate all n alternative guesses
 for restart in range(4):
  a=[list(r) for r in (rows if restart==0 else [tuple(random.randrange(n) for k in range(n)) for j in range(n)])];cur=score(a)
  for step in range(3):
   changed=False
   for j in range(n):
    for k in range(n):
     old=a[j][k];opt=old
     for v in range(n):
      a[j][k]=v;s=score(a)
      if s>cur:cur=s;opt=v;changed=True
     a[j][k]=opt
   if not changed:break
  if cur>best:best=cur;w=a
 out[str(n)]={'cyclic_latin_score':base,'best_diagnostic_score':best,'response_maps':w}
 print(n,out[str(n)],flush=True)
# Exact symmetrized moment identity: ordered Exp lifetimes; integrate using spacings permutation.
from fractions import Fraction as F
for n,d in [(3,3),(4,3),(4,4)]:
 edges=list(it.combinations(range(n),2));x=[F(i+1,sum(range(1,len(edges)+1))) for i in range(len(edges))]
 literal=F(0)
 for es in it.product(range(len(edges)),repeat=d):
  u=set();v=F(1)
  for e in es:u.update(edges[e]);v*=x[e]/len(u)
  literal+=v
 # moment via multinomial expansion in independent spacings rate n-j
 moment=F(0)
 for p in it.permutations(range(n)):
  ranks={v:j for j,v in enumerate(p)}
  a=[sum((x[k] for k,e in enumerate(edges) if min(ranks[v] for v in e)>=j),F(0)) for j in range(n)]
  # E[(sum a_j Exp(n-j))^d]/d! = h_d(a_j/(n-j))
  h=[F(1)]+[F(0)]*d
  for j in range(n):
   z=a[j]/(n-j)
   for k in range(1,d+1):h[k]+=z*h[k-1]
  moment+=h[d]/math.factorial(n)
 print('moment identity',n,d,literal,moment,literal==moment,flush=True)
 out[f'moment-{n}-{d}']={'literal':str(literal),'moment_over_factorial':str(moment),'equal':literal==moment}
(L/'diagnostics.json').write_text(json.dumps(out,indent=2))
