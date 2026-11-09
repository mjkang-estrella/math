import sys,itertools,json,time
limit=int(sys.argv[1]);seedlen=int(sys.argv[2]);
def free(w):
 n=len(w)
 return all(w[a:a+d]!=w[a+d:a+2*d] for d in range(1,n//2+1) for a in range(n-2*d+1))
def insfree(w,j,c):
 u=w[:j]+c+w[j:];n=len(u)
 for d in range(1,n//2+1):
  for a in range(max(0,j-2*d+1),min(j,n-2*d)+1):
   if u[a:a+d]==u[a+d:a+2*d]:return None
 return u
A='123';seeds=[''];counts=[]
for n in range(1,seedlen+1):
 seeds=[w+c for w in seeds for c in A if free(w+c)]
 counts.append((n,len(seeds)))
print('squarefree seed counts',counts,flush=True)
cache={};eligible=0;terminations=[];maxback=0
for ix,w in enumerate(seeds):
 pot=sum(insfree(w,j,c) is not None for j in range(1,len(w)) for c in A)
 if pot<=2:continue
 eligible+=1;start=w;steps=0
 while len(w)<limit:
  if w in cache:
   w=cache[w]
   if w is None:break
   steps+=1;continue
  found=False
  for j in range(len(w),-1,-1):
   for c in A:
    nw=insfree(w,j,c)
    if nw is not None:
     cache[w]=nw;maxback=max(maxback,len(w)-j);w=nw;steps+=1;found=True;break
   if found:break
  if not found:cache[w]=None;break
 if w is None or len(w)<limit:
  o=dict(seed=start,potential=pot,terminal=w,steps=steps);terminations.append(o);print('TERMINATED',o,flush=True)
 if ix%100==0:print('progress',ix,'eligible',eligible,'cached',len(cache),flush=True)
print(json.dumps(dict(seed_length=seedlen,all_squarefree_seeds=len(seeds),eligible_potential_gt2=eligible,target_length=limit,terminations=terminations,max_backtrack=maxback,cached_words=len(cache))),flush=True)
