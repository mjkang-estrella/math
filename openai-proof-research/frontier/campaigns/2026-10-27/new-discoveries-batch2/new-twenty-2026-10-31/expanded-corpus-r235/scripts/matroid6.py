from pathlib import Path
import sys,json,itertools,time
sys.path.insert(0,str(Path(__file__).resolve().parent))
# Do not import matroids.py: it runs a sweep at import.
D=Path(__file__).resolve().parents[1];n=6;N=64;M=[]
for r in range(n+1):
 level=[x for x in range(N) if x.bit_count()==r];L=len(level);ix={x:j for j,x in enumerate(level)}
 exchanges={(a,b):[sum(1<<ix[a^(1<<i)^(1<<j)] for j in range(n) if (b&~a)>>j&1) for i in range(n) if (a&~b)>>i&1] for a in level for b in level}
 for pick in range(1,1<<L):
  bases=[a for j,a in enumerate(level) if pick>>j&1]
  if any(not (pick&opts) for a in bases for b in bases for opts in exchanges[a,b]):continue
  fam=sum(1<<x for x in range(N) if any(x&b==x for b in bases))
  cir=[x for x in range(N) if not fam>>x&1 and all(fam>>(x^(1<<i))&1 for i in range(n) if x>>i&1)]
  M.append((fam,cir))
 print('rank',r,'matroids_so_far',len(M),flush=True)
(D/'matroids6.json').write_text(json.dumps(M)+'\n')
F={f for f,c in M};groups={}
for f,c in M:
 for k in range(min(4,len(c))+1):
  for X in itertools.combinations(c,k):
   mask=sum(1<<x for x in X);groups[mask]=groups.get(mask,0)|f
print('families_size_at_most_4',len(groups),flush=True)
checks=0;fails=[]
for X,f in groups.items():
 if f not in F:continue
 xs=[x for x in range(N) if X>>x&1];dp=[-99]*N;dp[0]=0
 for u in range(N):
  if dp[u]<0:continue
  for x in xs:
   if x&~u:dp[u|x]=max(dp[u|x],dp[u]+1)
 v=[min((f|u).bit_count()-l for u,l in enumerate(dp) if l>=0) for f in range(N)]
 bad=next(((a,b) for a in range(N) for b in range(a+1,N) if v[a]+v[b]<v[a|b]+v[a&b]),None);checks+=1
 if bad:fails.append({'X':X,'f':f,'bad':bad,'v':v});print('FAIL',fails[-1],flush=True)
print('unique_maximal_checked',checks,'failures',len(fails),flush=True)
(D/'matroid6-search.json').write_text(json.dumps({'matroids':len(M),'families':len(groups),'unique_maximal_checked':checks,'failures':fails},indent=2)+'\n')
