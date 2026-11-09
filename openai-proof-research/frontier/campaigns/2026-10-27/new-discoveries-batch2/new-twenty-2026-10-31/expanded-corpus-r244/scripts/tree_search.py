import itertools,json,pathlib,sys,time,runpy
gen=runpy.run_path(str(pathlib.Path(__file__).resolve().parent/"treegen.py"))
D=pathlib.Path(__file__).resolve().parents[1]
def domsets(dist,k,g):
 n=len(dist);full=(1<<n)-1;balls=[sum(1<<v for v in range(n) if dist[u][v]<=k) for u in range(n)]
 out=[]
 for s in itertools.combinations(range(n),g):
  b=0
  for u in s:b|=balls[u]
  if b==full:out.append(s)
 return out
def gamma(dist,k):
 for g in range(1,len(dist)+1):
  s=domsets(dist,k,g)
  if s:return g,s
def win(dist,k,ss):
 # Minimum dominating configurations cannot contain duplicates, since fewer distinct guards would dominate.
 g=len(ss[0]);n=len(dist)
 def adjacent(a,b):
  masks=[sum(1<<j for j,v in enumerate(b) if dist[u][v]<=k) for u in a]
  def f(i,used):
   if i==g:return True
   m=masks[i]&~used
   while m:
    bit=m&-m;m-=bit
    if f(i+1,used|bit):return True
   return False
  return f(0,0)
 adj=[[] for s in ss]
 for i,a in enumerate(ss):
  for j in range(i+1):
   if adjacent(a,ss[j]):adj[i].append(j);adj[j].append(i) if i!=j else None
 alive=set(range(len(ss))); rounds=0
 while True:
  dead=[]
  for i in alive:
   cover=set()
   for j in adj[i]:
    if j in alive:cover.update(ss[j])
   if len(cover)!=n:dead.append(i)
  if not dead:return bool(alive),len(alive),rounds
  alive.difference_update(dead);rounds+=1
  if not alive:return False,0,rounds
rows=[];start=int(sys.argv[1]);stop=int(sys.argv[2]);cases=0;tested=0
for n,tree_list in gen["trees"](stop):
 if n<start:continue
 total=eligible=0
 for T in tree_list:
  total+=1;dist=gen["distances"](T)
  for k in range(3,min(7,n)):
   g,ss=gamma(dist,k);h,_=gamma(dist,k//2);cases+=1
   if g==h or g==1:continue
   eligible+=1;tested+=1;w,count,rounds=win(dist,k,ss)
   if w:
    result={'n':n,'k':k,'gamma_k':g,'gamma_half':h,'edges':[(u,v) for u in range(n) for v in T[u] if u<v],'minimum_dominating_sets':ss,'winning_states':count,'rounds':rounds}
    (D/'tree-candidate.json').write_text(json.dumps(result,indent=2));print('CANDIDATE',json.dumps(result),flush=True);raise SystemExit
 rows.append({'n':n,'trees':total,'game_instances':eligible});print(rows[-1],flush=True)
(D/f'tree-results-{start}-{stop}.json').write_text(json.dumps({'rows':rows,'parameter_cases':cases,'game_instances':tested},indent=2))
