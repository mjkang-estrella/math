from pathlib import Path
import itertools,json
D=Path(__file__).resolve().parents[1];M=json.loads((D/'matroids6.json').read_text());F={f for f,c in M};G={};N=64
for f,c in M:
 for X in itertools.combinations(c,5):
  mask=sum(1<<x for x in X);G[mask]=G.get(mask,0)|f
print('families_of_size_5',len(G),flush=True)
count=0;fails=[]
for X,f in G.items():
 if f not in F:continue
 xs=[x for x in range(N) if X>>x&1];dp=[-99]*N;dp[0]=0
 for u in range(N):
  if dp[u]<0:continue
  for x in xs:
   if x&~u:dp[u|x]=max(dp[u|x],dp[u]+1)
 v=[min((f|u).bit_count()-l for u,l in enumerate(dp) if l>=0) for f in range(N)]
 bad=next(((a,b) for a in range(N) for b in range(a+1,N) if v[a]+v[b]<v[a|b]+v[a&b]),None);count+=1
 if bad:fails.append({'X':X,'f':f,'v':v,'bad':bad});print('FAIL',fails[-1],flush=True)
print('unique_maximal',count,'failures',len(fails),flush=True)
(D/'matroid6-extend.json').write_text(json.dumps({'family_size':5,'families':len(G),'unique_maximal':count,'fails':fails},indent=2)+'\n')
