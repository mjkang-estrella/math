"""Bounded exact finite-field necessary-condition probes. No proof of the conjecture."""
import random,json,time
from pathlib import Path
B=Path(__file__).parent

def transpose(a):return list(map(list,zip(*a)))
def mul(a,b,p=None):
 z=[[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
 return [[x%p for x in row] for row in z] if p else z

def rank(a,p):
 a=[[x%p for x in row] for row in a];j=0
 for k in range(len(a[0])):
  q=next((i for i in range(j,len(a)) if a[i][k]),None)
  if q is None:continue
  a[j],a[q]=a[q],a[j];c=pow(a[j][k],-1,p);a[j]=[x*c%p for x in a[j]]
  for i in range(j+1,len(a)):
   c=a[i][k]
   if c:a[i]=[(x-c*y)%p for x,y in zip(a[i],a[j])]
  j+=1
  if j==len(a):break
 return j

def extension(a,r,rng):
 # a is the current-rank by preceding-rank up matrix; graph cliques partition
 # the pair requirements. Singletons fill unused updegrees.
 n=len(a);g=[[sum(x*y for x,y in zip(u,v)) for v in a] for u in a];need=[g[i][i]+r for i in range(n)]
 assert all(g[i][j] in (0,1) for i in range(n) for j in range(i))
 edges={(i,j) for i in range(n) for j in range(i+1,n) if g[i][j]};rows=[]
 while edges:
  i,j=rng.choice(sorted(edges));cl=[i,j]
  candidates=[k for k in range(n) if k not in cl];rng.shuffle(candidates)
  for k in candidates:
   if rng.random()<.7 and all(tuple(sorted((k,x))) in edges for x in cl):cl.append(k)
  # Singleton slack can run out with poor clique choices; restart this extension.
  for x in cl:
   need[x]-=1
   if need[x]<0:return None
  for x in cl:
   for y in cl:
    if x<y:edges.remove((x,y))
  rows.append([int(x in cl) for x in range(n)])
 rows += [[int(i==j) for i in range(n)] for j in range(n) for _ in range(need[j])]
 assert mul(transpose(rows),rows)==[[g[i][j]+r*int(i==j) for j in range(n)] for i in range(n)]
 return rows

def test(a,r,sizes):
 n=len(sizes)-1;m=len(a);g=[[sum(x*y for x,y in zip(u,v)) for v in a] for u in a];T=[[g[i][j]+r*int(i==j) for j in range(m)] for i in range(m)]
 delta=[sizes[i]-(sizes[i-1] if i else 0) for i in range(n+1)]
 factors=[[r*(i+1) for i in range(n+1) if delta[n-i]>=j] for j in range(1,m+1)]
 count=0
 for p in (2,3,5):
  for lam in sorted({x%p for f in factors for x in f}):
   A=[[(T[i][j]-lam*int(i==j))%p for j in range(m)] for i in range(m)];power=[[int(i==j) for j in range(m)] for i in range(m)]
   exponents=[sum(x%p==lam for x in f) for f in factors]
   for k in range(1,max(exponents)+1):
    power=mul(power,A,p);got=m-rank(power,p);want=sum(min(k,e) for e in exponents);count+=1
    assert got==want,dict(r=r,sizes=sizes,p=p,lam=lam,k=k,got=got,want=want,a=a)
 return count

rng=random.Random(85029);count=0;prefixes=0;skips=0;shapes=set();maxrank=0;started=time.monotonic()
for r in (1,2,3):
 for run in range(45):
  a=[[]];sizes=[1]
  for n in range(7):
   if len(a)>20:skips+=1;break
   count+=test(a,r,sizes);prefixes+=1;shapes.add((r,tuple(sizes)));maxrank=max(maxrank,n)
   aa=None
   for attempt in range(12):
    aa=extension(a,r,rng)
    if aa is not None:break
   if aa is None:skips+=1;break
   a=aa;sizes.append(len(a))
# Route falsifier: same rational spectrum as genuine rank2 Young DU,
# but wrong reduction mod2. Thus rational diagonalization cannot prove Z[t] SNF.
assert rank([[1-1,0],[0,3-1]],2)==0
assert rank([[2-1,1],[1,2-1]],2)==1
out={'status':'NO_COUNTEREXAMPLE_IN_BOUNDED_SAMPLE','seed':85029,'prefixes_checked':prefixes,'distinct_rank_sequences':len(shapes),'finite_field_kernel_equalities':count,'max_rank':maxrank,'dimension_cap':20,'r_values':[1,2,3],'primes':[2,3,5],'skipped_or_stopped':skips,'seconds':time.monotonic()-started,'route_falsifier':'diag(1,3) vs [[2,1],[1,2]] at eigenvalue1 modulo2','scope':'necessary field reductions only; not integral SNF proof; prefixes not exhaustively enumerated'}
(B/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
