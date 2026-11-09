import itertools,random,time,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(101)
C=[sum(1<<j for j in x) for x in itertools.combinations(range(9),4)];compat=[sum(1<<j for j,y in enumerate(C) if not x&y) for x in C];allc=(1<<126)-1
out=[]
for side in [4,5,6,7]:
 for rep in range(25):
  pts=list(itertools.product(range(side),repeat=2));rng.shuffle(pts);chosen=[]
  adjacent=lambda a,b:(a[0]-b[0],a[1]-b[1]) in [(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)]
  for p in pts:
   nei=[q for q in chosen if adjacent(p,q)]
   if not any(adjacent(a,b) for a,b in itertools.combinations(nei,2)) and rng.random()<.95:chosen.append(p)
  n=len(chosen);adj=[[j for j,q in enumerate(chosen) if adjacent(p,q)] for p in chosen];nodes=[0];start=time.monotonic()
  def dfs(dom,assigned):
   nodes[0]+=1
   if nodes[0]>20000:return None
   if assigned==(1<<n)-1:return True
   i=min((j for j in range(n) if not assigned>>j&1),key=lambda j:(dom[j].bit_count(),-len(adj[j])))
   options=dom[i]
   while options:
    bit=options&-options;options-=bit;c=bit.bit_length()-1;new=dom[:];new[i]=bit;bad=False
    for j in adj[i]:
     if assigned>>j&1:continue
     new[j]&=compat[c]
     if not new[j]:bad=True;break
    if not bad:
     r=dfs(new,assigned|1<<i)
     if r is not False:return r
   return False
  dom=[allc]*n
  if n:dom[0]=1
  status=dfs(dom,0);r={'side':side,'rep':rep,'n':n,'status':status,'nodes':nodes[0],'coordinates':chosen};out.append(r)
  if status is not True:print(r,flush=True)
 print('completed side',side,'25 samples',flush=True)
(D/'outputs/hex-replay.json').write_text(json.dumps(out,indent=2)+'\n')
