from pathlib import Path
import time,random,math,json
D=Path(__file__).resolve().parents[1];random.seed(339235)
for n in [8,10]:
 V=2*n;E=[(i,(i+1)%V) for i in range(V)]+[(i,i+n) for i in range(n)];m=len(E);start=time.monotonic();best=10**9;found=None;steps=0
 while time.monotonic()-start<15 and found is None:
  c=[]
  for v in range(V):
   choices=list(set(range(3))-{c[w] for u,w in E if u==v and w<v}-{c[u] for u,w in E if w==v and u<v})
   if not choices:break
   c.append(random.choice(choices))
  if len(c)<V:continue
  groups=[[i for i in range(V) if c[i]==k] for k in range(3)]
  l=list(range(1,m+1));random.shuffle(l)
  def score():
   s=[0]*V
   for (u,v),z in zip(E,l):s[u]+=z;s[v]+=z
   return sum(len(g)*sum(s[i]**2 for i in g)-sum(s[i] for i in g)**2 for g in groups),s
  cur,_=score()
  for it in range(2500):
   i,j=random.sample(range(m),2);l[i],l[j]=l[j],l[i];nc,s=score();temp=.3+15*(1-it/2500)
   if nc<=cur or random.random()<math.exp((cur-nc)/temp):cur=nc
   else:l[i],l[j]=l[j],l[i]
   best=min(best,cur);steps+=1
   if cur==0:
    _,s=score()
    if len(set(s))==3 and all(s[u]!=s[v] for u,v in E):found=l[:];break
  if found:break
 print('n=%d found=%d best=%d trials=%d labels=%s'%(n,found is not None,best,steps,','.join(map(str,found or []))),flush=True)
