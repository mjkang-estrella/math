import itertools,functools,random,json
rng=random.Random(2082026)
def value(n,extra,mask=None):
 adj=[1<<i for i in range(n)]
 for i in range(n-1):adj[i]|=1<<(i+1);adj[i+1]|=1<<i
 for i,j in extra:adj[i]|=1<<j;adj[j]|=1<<i
 full=(1<<n)-1
 @functools.lru_cache(None)
 def f(s,turn):
  if s==full:return 0
  vals=[f(s|a,1-turn) for a in adj if s|a!=s]
  return 1+(max(vals) if turn else min(vals))
 return f(0,0)
for n in range(8,9):
 possible=[(i,j) for i in range(n) for j in range(i+2,n)]
 count=0;best=-1;witness=None
 runs=range(1<<len(possible)) if n<=8 else range(200)
 for code in runs:
  if n<=8:e=[e for j,e in enumerate(possible) if code>>j&1]
  else:
   density=[.05,.1,.2,.4,.6][code%5];e=[e for e in possible if rng.random()<density]
  v=value(n,e);count+=1
  if v>best:best=v;witness=e
  if v>(n+1)//2:print(json.dumps({'COUNTEREXAMPLE':True,'n':n,'extra_edges':e,'game_value':v}),flush=True);raise SystemExit
 print(json.dumps({'n':n,'count':count,'space':'all labelled supergraphs of fixed Hamiltonian path' if n<=8 else 'seeded samples of supergraphs of fixed Hamiltonian path','maximum_game_value':best,'conjectured_bound':(n+1)//2,'best_extra_edges':witness}),flush=True)
