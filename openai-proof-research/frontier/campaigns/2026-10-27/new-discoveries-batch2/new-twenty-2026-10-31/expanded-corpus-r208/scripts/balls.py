import random,json,pathlib,math,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(208)
def score(n,edges):
 b=[1<<i for i in range(n)];s=set(b)
 for i,j in edges:
  b[i]|=1<<j;b[j]|=1<<i;s.add(b[i]);s.add(b[j])
 return len(s)
for n in range(6,17):
 e=[(i,j) for i in range(n) for j in range(i+1,n)];top=0;best=[];count=0
 for run in range(5):
  rng.shuffle(e);cur=score(n,e)
  for it in range(3000):
   i=rng.randrange(len(e));j=rng.randrange(len(e));e[i],e[j]=e[j],e[i];v=score(n,e);count+=1;t=.02+.8*(1-it/3000)
   if v>=cur or rng.random()<math.exp((v-cur)/t):cur=v
   else:e[i],e[j]=e[j],e[i]
   if cur>top:top=cur;best=e[:]
 print(json.dumps(dict(n=n,evaluations=count,best=top,conjectured=n*n-(3*n+1)//2+2,edges=best)),flush=True)
