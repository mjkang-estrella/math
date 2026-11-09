import random,time,math,json,pathlib
r=random.Random(365453); edges=[]
for t in range(6):
 l=2*t; rr=l+1; x=12+2*(t//3); y=x+1
 edges += [(l,rr),(l,x),(l,y),(rr,x),(rr,y)]
groups=[[2*t for t in range(6)],[2*t+1 for t in range(6)],[12,13],[14,15]]
def score(w):
 return sum(len(g)*sum(w[x]**2 for x in g)-sum(w[x] for x in g)**2 for g in groups)
start=time.monotonic(); best=10**9; count=0; found=None
while time.monotonic()-start<12:
 a=list(range(1,31));r.shuffle(a);w=[0]*16
 for z,(u,v) in zip(a,edges):w[u]+=z;w[v]+=z
 cur=score(w)
 for k in range(10000):
  if k%1000==0 and time.monotonic()-start>=12:break
  i,j=r.sample(range(30),2);d=a[j]-a[i];u,v=edges[i];x,y=edges[j]
  w[u]+=d;w[v]+=d;w[x]-=d;w[y]-=d
  ns=score(w);temp=0.3+50*(1-k/10000)
  if ns<=cur or r.random()<math.exp((cur-ns)/temp):a[i],a[j]=a[j],a[i];cur=ns
  else:w[u]-=d;w[v]-=d;w[x]+=d;w[y]+=d
  best=min(best,cur);count+=1
  if cur==0 and all(w[u]!=w[v] for u,v in edges):
   assert sorted(a)==list(range(1,31))
   verify=[sum(z for z,(u,v) in zip(a,edges) if t in (u,v)) for t in range(16)]
   assert w==verify and len(set(w))==4
   found=dict(labels=a,weights=w);break
 if found:break
out=dict(result=found,best_objective=best,iterations=count,elapsed=time.monotonic()-start,
         limitation="Restricted four-color grouping heuristic; failure has no mathematical force.")
root=pathlib.Path(__file__).resolve().parents[1]
(root/'outputs/four.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
