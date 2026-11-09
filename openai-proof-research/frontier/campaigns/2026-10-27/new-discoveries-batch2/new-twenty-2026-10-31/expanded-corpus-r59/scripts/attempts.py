import sys,random,itertools,math
mode=sys.argv[1]
if mode=='pell':
 P=[0,1]
 for n in range(1,1100):P.append(2*P[-1]+P[-2])
 S=0;bad=[]
 for n in range(1,1001):
  S+=P[n];pred=1 if n%4 in (1,2) else (n+1)//2
  div=[m for m in range(1,n+2) if P[m]<=S and S%P[m]==0]
  if max(div)!=pred:bad.append((n,pred,max(div)))
  if n<=24:print(n,'sum',S,'dividing_indices',div)
 print('Exact integer check n=1..1000, all possible positive indices checked by strict growth:',bad)
 # Strong divisibility alone only bounds indices from factor products; gcd(m,a) may be small while P_m divides P_a^2.
 print('Boundary n=0 excluded: all P_m divide zero, no largest index. No credit for this endpoint.')
elif mode=='rigid':
 rng=random.Random(590205)
 for n,r in [(6,3),(6,4),(7,4),(8,4),(9,4),(10,4),(8,5),(9,5),(10,5)]:
  V=list(range(1<<n)); neigh=[{y for y in V if (x^y).bit_count()<=r} for x in V];best=0;rigids=0
  for trial in range(500):
   A=[];pool=set(V)
   while pool:
    x=rng.choice(sorted(pool));A.append(x);pool.intersection_update(neigh[x]);pool.difference_update(A)
   if all(any((x^y).bit_count()==r for y in A) for x in A):
    rigids+=1
    if len(A)>best:best=len(A);w=sorted(A)
  print(n,r,'500 greedy maximal sets; rigid count',rigids,'largest rigid',best,'bound',2**r,'witness',w if best else None,flush=True)
else:
 import numpy as np
 rng=random.Random(59365143);best=(-1e10,None);count=0
 def matching(adj,mask,memo):
  if not mask:return 0
  if mask in memo:return memo[mask]
  v=(mask&-mask).bit_length()-1;rest=mask^(1<<v);ans=matching(adj,rest,memo);c=adj[v]&rest
  while c:
   b=c&-c;c-=b;ans=max(ans,1+matching(adj,rest^b,memo))
  memo[mask]=ans;return ans
 for n in range(4,13):
  local=(-1e10,None)
  for z in range(2000):
   prob=rng.random();edges=[(i,j) for i in range(n) for j in range(i) if rng.random()<prob];adj=[0]*n;L=np.zeros((n,n))
   for i,j in edges:adj[i]|=1<<j;adj[j]|=1<<i;L[i,i]+=1;L[j,j]+=1;L[i,j]-=1;L[j,i]-=1
   nn=sum(bool(a) for a in adj)
   if nn<3:continue
   nu=matching(adj,(1<<n)-1,{});e=np.linalg.eigvalsh(L)[::-1];c=0
   for k in range(1,nn-1):
    c+=e[k-1];d=c-len(edges)-k*nu
    if d>local[0]:local=(float(d),{'n':n,'k':k,'m':len(edges),'nu':nu,'edges':edges})
   count+=1
  print('n',n,'largest numerical excess',local,flush=True)
 print('sample count',count,'Floating eigenvalues are diagnostics, no spectral certificate.')
