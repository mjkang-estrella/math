import itertools as it,json,math,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def save(n,o):
 (D/'outputs'/n).write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o),flush=True)
def moufang(t):
 n=len(t)
 return all(t[t[x][y]][t[z][x]]==t[x][t[t[y][z]][x]] for x,y,z in it.product(range(n),repeat=3))
def reduced(n):
 t=[list(range(n))]+[[i]+[-1]*(n-1) for i in range(1,n)]
 def go(k):
  if k==(n-1)**2:
   if moufang(t):yield [r[:] for r in t]
   return
  i,j=divmod(k,n-1);i+=1;j+=1
  for x in range(n):
   if x not in t[i] and all(t[a][j]!=x for a in range(i)):
    t[i][j]=x;yield from go(k+1);t[i][j]=-1
 yield from go(0)
def loops():
 out=[]
 for n in [1,2,4]:
  ts=list(reduced(n)) if n>1 else [[[0]]]
  allts=set()
  for t in ts:
   for p in it.permutations(range(n)):
    u=[[0]*n for _ in range(n)]
    for i,j in it.product(range(n),repeat=2):u[p[i]][p[j]]=p[t[i][j]]
    allts.add(tuple(sum(u,[])))
  arr=list(allts);mini=n*n;count=0
  # canonical isomorphism signatures from all permutations
  sig={}
  for a in arr:
   sig[a]=min(tuple(a[p[i]*n+p[j]] for i,j in it.product(range(n),repeat=2)) for p in [tuple(range(n))]) # replaced below by orbit membership
  orbit={}
  for idx,t in enumerate(ts):
   for p in it.permutations(range(n)):
    u=[0]*(n*n)
    for i,j in it.product(range(n),repeat=2):u[p[i]*n+p[j]]=p[t[i][j]]
    orbit.setdefault(tuple(u),idx)
  # reduced tables may be isomorphic: use power statistics (complete only at n<=4)
  def signature(a):return sorted(sum(a[i*n+j]==a[j*n+i] for j in range(n)) for i in range(n)), sorted(sum(a[i*n+i]==a[j*n+j] for j in range(n)) for i in range(n))
  for a,b in it.combinations(arr,2):
   count+=1;dist=sum(x!=y for x,y in zip(a,b))
   if signature(a)!=signature(b):mini=min(mini,dist)
  out.append(dict(n=n,reduced_Moufang_tables=len(ts),all_labeled_loop_tables=len(arr),pairs=count,min_distance_different_power_signatures=mini,nonequivalent_associator_pairs=0,note='All tables associative at these orders; signatures distinguish C4 from V4. No nonassociative coverage.'))
 save('loop-small.json',out)
def autarkies():
 out=[]
 for n,maxc in [(1,2),(2,8),(3,5)]:
  cls=[tuple(i*(j+1) for j,i in enumerate(s) if i) for s in it.product([-1,0,1],repeat=n) if any(s)]
  tested=eligible=fail=0
  for k in range(1,maxc+1):
   for F in it.combinations(cls,k):
    vs=set(abs(x) for c in F for x in c)
    if len(vs)!=n:continue
    tested+=1
    sig=min(sum(any(abs(x) in V for x in c) for c in F)-len(V) for r in range(1,n+1) for V in map(set,it.combinations(vs,r)))
    if sig<1:continue
    nm=[j for j in range(1,100) if (j+1)&j][sig-1]
    if min(sum(any(abs(x)==v for x in c) for c in F) for v in vs)<=nm:continue
    eligible+=1
    found=False
    for a in it.product([-1,0,1],repeat=n):
     if not any(a):continue
     if all(not any(a[abs(x)-1] for x in c) or any(a[abs(x)-1]==(1 if x>0 else -1) for x in c) for c in F):found=True;break
    if not found:fail+=1
  out.append(dict(n=n,clauses_universe=len(cls),max_clauses=maxc,full_variable_clause_sets=tested,antecedent_satisfying=eligible,without_autarky=fail,scope='Existence diagnostic only; cannot establish or refute uniform polynomial-time complexity. Empty clause omitted: it affects neither touched clauses nor variable-neighborhood surplus.'))
 save('autarky-small.json',out)
def carmichael():
 ps=[p for p in range(3,1000,2) if all(p%d for d in range(2,math.isqrt(p)+1))]
 exps=[(e,f) for e in range(1,13) for f in range(e,13) if e+f>=3]
 sets={}
 for e,f in exps:sets[e,f]={(p,q) for p in ps for q in ps if p!=q and pow(p,e,q-1)==1 and pow(q,f,p-1)==1}
 collisions=[]
 for a,b in it.combinations(exps,2):
  if sets[a]==sets[b] and not ((a[1]==b[1] and b[0]%a[0]==0) or (a[0]==b[0] and b[1]%a[1]==0)):
   collisions.append(dict(a=a,b=b,pair_count=len(sets[a])))
 save('carmichael-small.json',dict(prime_min=3,prime_max=997,prime_count=len(ps),exponents=exps,prime_order='all ordered distinct odd primes; no p<q restriction',tested_prime_pairs_per_exponent=len(ps)*(len(ps)-1),collisions=collisions,note='Only bounded-set collisions. Universal equality of infinite prime-pair sets is not certified by any collision.'))
if __name__=='__main__':globals()[sys.argv[1]]()
