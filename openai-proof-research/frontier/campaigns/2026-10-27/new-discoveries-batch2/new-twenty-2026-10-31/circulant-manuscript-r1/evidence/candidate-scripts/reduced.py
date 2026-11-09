import itertools,functools,collections,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
@functools.lru_cache(None)
def words(w):
 if tuple(sorted(w))==w:return [()]
 out=[]
 for i in range(len(w)-1):
  if w[i]>w[i+1]:
   v=list(w);v[i],v[i+1]=v[i+1],v[i]
   out.extend(r+(i,) for r in words(tuple(v)))
 return out
out=[]
for n in [3,4,5,6]:
 count=0;worst=0;fail=[];maxwords=0
 for w in itertools.permutations(range(n)):
  inv=[(i,j) for i in range(n) for j in range(i+1,n) if w[i]>w[j]]
  if n==6 and len(inv)>8:continue
  W=words(w);index={r:i for i,r in enumerate(W)};adj=[];maxwords=max(maxwords,len(W))
  for r in W:
   nb=[]
   for i in range(len(r)-1):
    if abs(r[i]-r[i+1])>1:nb.append(index[r[:i]+(r[i+1],r[i])+r[i+2:]])
   for i in range(len(r)-2):
    if r[i]==r[i+2] and abs(r[i]-r[i+1])==1:nb.append(index[r[:i]+(r[i+1],r[i],r[i+1])+r[i+3:]])
   adj.append(nb)
  diam=0
  for a in range(len(W)):
   dist=[-1]*len(W);dist[a]=0;q=collections.deque([a])
   while q:
    v=q.popleft()
    for b in adj[v]:
     if dist[b]<0:dist[b]=dist[v]+1;q.append(b)
   assert min(dist)>=0;diam=max(diam,max(dist))
  L=sum(len(set(a+b))==4 for a,b in itertools.combinations(inv,2))+sum(w[a]>w[b]>w[c] for a,b,c in itertools.combinations(range(n),3))
  pats=sum(w[c]<w[d]<w[a]<w[b] for a,b,c,d in itertools.combinations(range(n),4))
  if diam>L-pats:fail.append(dict(w=w,diam=diam,L=L,patterns=pats))
  count+=1;worst=max(worst,diam)
 row=dict(n=n,permutations=count,inversion_cap=8 if n==6 else None,max_word_count=maxwords,max_diameter=worst,failures=fail);out.append(row);print(row,flush=True);(D/'outputs/reduced.json').write_text(json.dumps(out,indent=2))
