import pathlib,json,itertools,time
D=pathlib.Path(__file__).resolve().parents[1];rows=[]
for n in range(9,19):
 tested=0;worst={}
 for bits in range(1,1<<(n//2)):
  ds=[d for d in range(1,n//2+1) if bits>>(d-1)&1];adj=[]
  for v in range(n):adj.append(sum(1<<w for w in range(n) if min((v-w)%n,(w-v)%n) in ds))
  if any(adj[u]&adj[v] for u in range(n) for v in range(u) if adj[u]>>v&1):continue
  tested+=1;cnt=[0]*(n+1)
  for root in range(n):
   def rec(v,path,mask):
    if adj[v]>>root&1 and len(path)>2:
     if len(path)>=5 and path[1]<v:cnt[len(path)]+=1
     return
    poss=adj[v]&~mask&~((1<<(root+1))-1)
    while poss:
     bit=poss&-poss;poss-=bit;w=bit.bit_length()-1
     if adj[w]&(mask&~(1<<v)&~(1<<root)):continue
     rec(w,path+[w],mask|bit)
   for first in range(root+1,n):
    if adj[root]>>first&1:rec(first,[root,first],(1<<root)|(1<<first))
  for k in range(5,n+1):
   if cnt[k]*k**k>n**k:print('COUNTEREXAMPLE',n,ds,k,cnt[k],flush=True);raise SystemExit
   if cnt[k]>worst.get(k,0):worst[k]=cnt[k]
 rows.append(dict(n=n,tested_trianglefree_circulants=tested,maxima=worst));print(rows[-1],flush=True)
(D/'cycles-coverage.json').write_text(json.dumps(rows,indent=2))
