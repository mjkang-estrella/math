import pathlib,json,random,itertools,time,sys
L=pathlib.Path(__file__).resolve().parents[1]; rng=random.Random(152); out=[]
def bound(n,g):
 a=(g+1)//2;b=g//2;phi=max(0,n-3*g-2*a-b+1)
 return 2*g+2*a*b+min(n-3*g,2*a-b+1)*(2*a+1)+sum(2*a+1+(i+1)//2 for i in range(1,phi+1))
for g in [3,4,5]:
 for n in range(3*g,3*g+7):
  best=-1; calls=0; trials=50 if g==3 else 15
  for trial in range(trials):
   a=rng.randrange(1,g); side=[int(i>=a) for i in range(g)]
   side += [1-side[i] for i in range(g) for _ in range(2)]
   side += [rng.randrange(2) for _ in range(n-3*g)]
   adj=[1<<i for i in range(n)]; edges=[]
   for i in range(g):
    for j in [g+2*i,g+2*i+1]: adj[i]|=1<<j;adj[j]|=1<<i;edges.append((i,j))
   # ensure extra vertices dominated by a random dominator
   for j in range(3*g,n):
    choices=[i for i in range(g) if side[i]!=side[j]];i=rng.choice(choices);adj[i]|=1<<j;adj[j]|=1<<i;edges.append((i,j))
   combos=list(itertools.combinations(range(n),g));full=(1<<n)-1
   def valid():
    global calls
    calls+=1
    for c in combos[1:]:
     u=0
     for v in c:u|=adj[v]
     if u==full:return False
    return True
   if not valid():continue
   avail=[(i,j) for i in range(n) for j in range(i+1,n) if side[i]!=side[j] and not (adj[i]>>j&1)];rng.shuffle(avail)
   for i,j in avail:
    adj[i]|=1<<j;adj[j]|=1<<i
    if valid():edges.append((i,j))
    else:adj[i]^=1<<j;adj[j]^=1<<i
   if len(edges)>best:best=len(edges); witness=edges
  r=dict(n=n,gamma=g,bound=bound(n,g),best=best,trials=trials,checks=calls,violation=best>bound(n,g),edges=witness);out.append(r);print(json.dumps(r),flush=True);(L/'outputs/domination.json').write_text(json.dumps(out,indent=2))
