import numpy as np,itertools,json,sys,time
from collections import defaultdict
rng=np.random.default_rng(348914)
def parts(n):
 a=[0]*n
 def go(i,m):
  if i==n:yield tuple(a);return
  for c in range(m+2):a[i]=c;yield from go(i+1,max(m,c))
 yield from go(1,0)
def exact(c,ij,kl):
 n=len(c); k=max(c)+1
 # multivariate entries of B^l; common diagonal tI can be removed
 v=[[{} for j in range(n)] for i in range(n)]
 for i in range(n):v[i][i][(0,)*k]=1
 for l in range(n):
  if v[ij[0]][ij[1]]!=v[kl[0]][kl[1]]:return False
  w=[[defaultdict(int) for j in range(n)] for i in range(n)]
  for i in range(n):
   for mid in [(i-1)%n,(i+1)%n]:
    col=c[mid if mid==(i-1)%n else i]
    for j in range(n):
     for mon,count in v[mid][j].items():
      mm=list(mon);mm[col]+=1;w[i][j][tuple(mm)]+=count
  v=w
 return True
out=[]
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 start=time.time();count=0;candidates=0;fail=[]
 for c in parts(n):
  count+=1
  # only one representative under dihedral and colour renaming
  def norm(x):
   d={};return tuple(d.setdefault(z,len(d)) for z in x)
  if any(norm(tuple(c[(s+e*i)%n] for i in range(n)))<c for s in range(n) for e in [-1,1]):continue
  maps=[]
  for s in range(n):
   for e in [-1,1]:
    perm=[(s+e*i)%n for i in range(n)]
    if all(c[i]==c[perm[i] if e==1 else perm[(i+1)%n]] for i in range(n)):maps.append(perm)
  pairs=[(i,j) for i in range(n) for j in range(i,n)]
  orbit={a:min(tuple(sorted((p[a[0]],p[a[1]]))) for p in maps) for a in pairs}
  weights=rng.integers(1,10,max(c)+1);A=np.eye(n)*(30*n)
  for i in range(n):A[i,(i+1)%n]=A[(i+1)%n,i]=weights[c[i]]
  inv=np.linalg.inv(A);groups=defaultdict(list)
  for a in pairs:groups[round(inv[a]*1e14)].append(a)
  for g in groups.values():
   for a,b in itertools.combinations(g,2):
    if orbit[a]==orbit[b]:continue
    candidates+=1
    if exact(c,a,b):fail.append({'colours':c,'a':a,'b':b});print('WITNESS',fail[-1],flush=True)
  if fail:break
 row=dict(n=n,partitions_visited=count,candidate_pairs_exact_checked=candidates,witnesses=fail,wall=time.time()-start)
 out.append(row);print(row,flush=True)
 json.dump(out,open('outputs/cycles-'+sys.argv[1]+'.json','w'),indent=2)
 if fail:break
