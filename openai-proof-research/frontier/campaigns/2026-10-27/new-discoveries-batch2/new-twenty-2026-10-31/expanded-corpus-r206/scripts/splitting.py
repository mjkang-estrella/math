import itertools,random,functools,pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(206)
def run(n,edges):
 m=len(edges);vm=[(1<<a)|(1<<b) for a,b in edges];full=(1<<m)-1
 matches=[]
 def rec(at,used,mask,k):
  if k==4:matches.append(mask);return
  for i in range(at,m):
   if not used&vm[i]:rec(i+1,used|vm[i],mask|1<<i,k+1)
 rec(0,0,0,0)
 if not matches or functools.reduce(int.__or__,matches)!=full:return None
 adj=[sum(1<<j for j in range(m) if j!=i and vm[i]&vm[j]) for i in range(m)]
 deg=max(sum(v in e for e in edges) for v in range(n))
 def color(k):
  colors=[0]*k
  def dfs(left):
   if not left:return True
   i=max((i for i in range(m) if left>>i&1),key=lambda i:sum(bool(adj[i]&c) for c in colors)*100+adj[i].bit_count())
   for c in range(k):
    if not colors[c]&adj[i]:
     empty=colors[c]==0;colors[c]|=1<<i
     if dfs(left^(1<<i)):return True
     colors[c]^=1<<i
     if empty:break
   return False
  return dfs(full)
 chi=deg if color(deg) else deg+1;by=[[s for s in matches if s>>i&1] for i in range(m)]
 @functools.lru_cache(None)
 def cover(left,k):
  if not left:return True
  if left.bit_count()>4*k or k==0:return False
  i=min((i for i in range(m) if left>>i&1),key=lambda i:len(by[i]));todo=sorted({left&~s for s in by[i]},key=int.bit_count)
  return any(cover(z,k-1) for z in todo)
 base=max(chi,(m+3)//4)
 if cover(full,base):return {'base':base,'cover_at_base':True,'matchings':len(matches)}
 # a subset is t-splitting iff no matching uses >t of its edges and it contains an ordinary (t+1)-matching
 def split_exists(t,size):
  if size>m:return False
  for ss in itertools.combinations(range(m),size):
   S=sum(1<<i for i in ss)
   if any((s&S).bit_count()>t for s in matches):continue
   for chosen in itertools.combinations(ss,t+1):
    used=0;ok=True
    for i in chosen:
     if used&vm[i]:ok=False;break
     used|=vm[i]
    if ok:return True
  return False
 L=base
 while split_exists(1,L+1) or split_exists(2,2*L+1):L+=1
 hit=not cover(full,L)
 return {'base':base,'cover_at_base':False,'formula_rhs':L,'counterexample':hit,'edges':edges,'matchings':len(matches)}
for case in range(int(sys.argv[1])):
 n=rng.randrange(8,13);m=rng.randrange(n, min(22,2*n)+1);edges=rng.sample(list(itertools.combinations(range(n),2)),m);r=run(n,edges)
 print(json.dumps({'case':case,'n':n,'m':m,'result':r}),flush=True)
 if r and r.get('counterexample'):(D/'outputs/splitting-hit.json').write_text(json.dumps(r));break
