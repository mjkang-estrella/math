import pathlib,json,functools,random
D=pathlib.Path(__file__).resolve().parents[1]
def connected(adj,s):
 if s==0:return True
 seen=s&-s;todo=seen
 while todo:
  bit=todo&-todo;todo-=bit;v=bit.bit_length()-1;new=adj[v]&s&~seen;seen|=new;todo|=new
 return seen==s
rows=[];hits=[];rng=random.Random(187)
for n in [2,4,6,8]:
 ng=nw=0
 for a in range(1,n//2+1):
  pairs=[(i,j) for i in range(a) for j in range(a,n)]; masks=range(1<<len(pairs)) if n<=6 else [rng.getrandbits(len(pairs)) for _ in range(150)]
  for mask in masks:
   adj=[0]*n
   for k,(i,j) in enumerate(pairs):
    if mask>>k&1:adj[i]|=1<<j;adj[j]|=1<<i
   full=(1<<n)-1
   if not connected(adj,full):continue
   ng+=1
   moves={s:[v for v in range(n) if s>>v&1 and connected(adj,s^(1<<v))] for s in range(1,1<<n) if connected(adj,s)}
   for w in (range(1<<n) if n<=6 else [rng.getrandbits(n) for _ in range(32)]):
    @functools.lru_cache(None)
    def game(s):return max(((1 if w>>v&1 else 0)-game(s^(1<<v)) for v in moves[s]),default=0) if s else 0
    val=game(full);nw+=1
    if val<0:hits.append({'n':n,'adj':adj,'weight_mask':w,'score':val});print('HIT',hits[-1],flush=True)
 rows.append({'n':n,'connected_labelled_bipartition_presentations':ng,'binary_weight_assignments':nw});print(rows[-1],flush=True)
(D/'outputs/grabbing.json').write_text(json.dumps({'rows':rows,'hits':hits},indent=2))
