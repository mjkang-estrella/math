import random,json,itertools
R=random.Random(203);rows=[]
for n in range(8,12):
 tested=eligible=0
 for trial in range(300):
  p=[.35,.5,.65,.8][trial%4];adj=[0]*n
  for i in range(n):
   for j in range(i):
    if R.random()<p:adj[i]|=1<<j;adj[j]|=1<<i
  deg=[a.bit_count() for a in adj];inds=[]
  for I in range(1,1<<n):
   if all(not (adj[i]&I) for i in range(n) if I>>i&1):inds.append(I)
  tested+=1
  if any(I.bit_count()>min(deg[i] for i in range(n) if I>>i&1)-1 for I in inds):continue
  eligible+=1
  K=min(k for k in range(1,n+1) if min([sum(deg[i] for i in range(n) if I>>i&1) for I in inds if I.bit_count()==k+1]or[10**9])>=n)
  cyc=set()
  for root in range(n):
   paths={(1<<root,root)}
   for size in range(1,n-root):
    nxt=set()
    for mask,last in paths:
     rem=adj[last]&~mask&~((1<<(root+1))-1)
     while rem:
      b=rem&-rem;rem-=b;v=b.bit_length()-1;mm=mask|b;nxt.add((mm,v))
      if size>=2 and adj[v]>>root&1:cyc.add(mm)
    paths=nxt
  memo={0:0}
  def cover(mask):
   if mask in memo:return memo[mask]
   bit=mask&-mask;v=min([1+cover(mask^C) for C in cyc if C&bit and C&mask==C]or[n+1]);memo[mask]=v;return v
  best=cover((1<<n)-1);assert best<=K,(n,adj,best,K)
 rows.append({'n':n,'random_graphs':tested,'hypothesis_qualifying':eligible});print(json.dumps(rows[-1]),flush=True)
