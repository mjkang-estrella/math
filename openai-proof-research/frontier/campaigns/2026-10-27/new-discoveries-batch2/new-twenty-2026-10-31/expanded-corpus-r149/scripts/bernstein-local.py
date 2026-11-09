import pathlib,json,random,math,time
L=pathlib.Path(__file__).resolve().parents[1]
data=[json.loads(x) for x in (L/'outputs/bernstein.log').read_text().splitlines()]
cases=[E for row in data for E in row['unresolved_examples']]
rng=random.Random(149);start=time.monotonic()
def cost(E,c):
 pars=[list(range(12)) for _ in range(3)];score=0
 def root(P,x):
  while P[x]!=x:x=P[x]
  return x
 for a,b in E:
  scores=[c[a][i]+c[6+b][i] for i in range(3)];v=max(scores)
  if scores.count(v)>1:score+=2
  i=scores.index(v);P=pars[i];x=root(P,a);y=root(P,6+b)
  if x==y:score+=1
  else:P[x]=y
 return score
outs=[]
for k,E in enumerate(cases):
 c=[[rng.randrange(-30,31) for _ in range(2)] for v in range(12)]
 for v in c:v.append(-sum(v))
 cur=cost(E,c);best=cur;solution=None
 for step in range(200000):
  a=rng.randrange(12);j=rng.randrange(3);l=(j+rng.randrange(1,3))%3
  delta=rng.choice([-12,-8,-4,-2,-1,1,2,4,8,12])
  c[a][j]+=delta;c[a][l]-=delta;new=cost(E,c)
  temp=.08+.55*(1-(step%10000)/10000)
  if new<=cur or rng.random()<math.exp((cur-new)/temp):cur=new
  else:c[a][j]-=delta;c[a][l]+=delta
  best=min(cur,best)
  if cur==0:solution=c;break
 out=dict(case=k,edges=E,steps=step+1,min_cost=best,labels=solution)
 outs.append(out);print(json.dumps(out),flush=True)
(L/'outputs/bernstein-local.json').write_text(json.dumps(outs,indent=2))
print(json.dumps(dict(cases=len(cases),solved=sum(x['labels'] is not None for x in outs),seconds=time.monotonic()-start)),flush=True)
