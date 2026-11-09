import random,json
from pathlib import Path
L=Path(__file__).resolve().parents[1]
def gap(a):
 g=0
 for i,b in enumerate(a):
  s=0;c=b
  while c:
   bit=c&-c;c-=bit;s|=a[bit.bit_length()-1]
  g+=(s&~(b|(1<<i))).bit_count()-b.bit_count()
 return g
for n in range(1,7):
 es=[(i,j) for i in range(n) for j in range(i+1,n)];a=[0]*n;bal=[0]*n;count=[0];mingap=[0]
 def dfs(k):
  if k==len(es):
   if any(bal):return
   count[0]+=1;g=gap(a);mingap[0]=min(g,mingap[0])
   if g<0:print('WITNESS',a,flush=True);raise RuntimeError('negative')
   return
  i,j=es[k];dfs(k+1)
  a[i]|=1<<j;bal[i]+=1;bal[j]-=1;dfs(k+1);a[i]^=1<<j;bal[i]-=1;bal[j]+=1
  a[j]|=1<<i;bal[j]+=1;bal[i]-=1;dfs(k+1);a[j]^=1<<i;bal[j]-=1;bal[i]+=1
 dfs(0);print(json.dumps({'n':n,'all_labeled_oriented_eulerian':count[0],'min_gap':mingap[0]}),flush=True)
r=random.Random(210)
for n in [8,12,16,24,32,48,63]:
 low=10**9
 for trial in range(1000):
  a=[0]*n
  for step in range(3*n):
   v=r.sample(range(n),r.randrange(3,min(n+1,10)));edges=list(zip(v,v[1:]+v[:1]))
   if all(not ((a[i]>>j|a[j]>>i)&1) for i,j in edges):
    for i,j in edges:a[i]|=1<<j
  g=gap(a);low=min(low,g)
  if g<0:print('WITNESS',a,flush=True);raise RuntimeError('negative')
 print(json.dumps({'n':n,'seeded_cycle_union_samples':1000,'seed':210,'min_gap':low}),flush=True)
