import itertools as it,random,json,time,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1];rng=random.Random(9401)
def dist(a):
 n=len(a);d=[[0 if i==j else 1 if j in a[i] else 999 for j in range(n)]for i in range(n)]
 for k in range(n):
  for i in range(n):
   for j in range(n):d[i][j]=min(d[i][j],d[i][k]+d[k][j])
 return d
class GP:
 def __init__(self,d):
  self.n=len(d);self.d=d;self.bad={};self.end={}
  for a,b in it.combinations(range(self.n),2):
   mid=end=0
   for c in range(self.n):
    if c in (a,b):continue
    x,y,z=d[a][b],d[a][c],d[b][c]
    if x+y==z or x+z==y:end|=1<<c
    if x==y+z:mid|=1<<c
   self.bad[a,b]=mid|end;self.end[a,b]=end
 def check(self,s):
  cover=terminal=sum(1<<v for v in s)
  for a,b in it.combinations(sorted(s),2):
   if self.bad[a,b]&sum(1<<v for v in s):return False,False
   cover|=self.bad[a,b];terminal|=self.end[a,b]
  return cover==(1<<self.n)-1,terminal==(1<<self.n)-1
 def lower(self):
  for k in range(1,self.n+1):
   for s in it.combinations(range(self.n),k):
    if self.check(s)[0]:return k
 def greedy(self):
  cand=list(range(self.n));rng.shuffle(cand);s=[]
  for v in cand:
   if all(not(self.bad[min(a,b),max(a,b)]>>v&1) for a,b in it.combinations(s,2)):s.append(v)
  return tuple(sorted(s))
def graph(n,p):
 a=[set()for _ in range(n)]
 for i,j in it.combinations(range(n),2):
  if rng.random()<p:a[i].add(j);a[j].add(i)
 return a
mode=sys.argv[1];out=[];t=time.monotonic()
if mode=='terminal':
 for n in [8,10,12,14,16,18,20,24,28,32]:
  count=0;hard=[];diams={}
  for rep in range(60):
   a=graph(n,2.8/n if rep<40 else .25);d=dist(a)
   if max(d[0])==999:continue
   g=GP(d);diam=max(map(max,d));diams[diam]=diams.get(diam,0)+1
   found=None
   for trial in range(200):
    s=g.greedy()
    if g.check(s)[1]:found=s;break
   if found is None:hard.append({'edges':[[i,j] for i in range(n)for j in a[i]if i<j]})
   count+=1
  r=dict(n=n,graphs=count,diameters=diams,no_terminal_found=hard);print(r,flush=True);out.append(r)
elif mode=='product':
 factors=[]
 for n in [7,8,9,10]:
  for rep in range(30):
   a=graph(n,.6+.35*rng.random());d=dist(a)
   if max(d[0])==999:continue
   g=GP(d);k=g.lower()
   if k>=3:factors.append((d,k))
 print('factors',len(factors),[k for d,k in factors],flush=True)
 for rep in range(300):
  d,k=rng.choice(factors);e,l=rng.choice(factors);m=len(e);dd=[[d[a//m][b//m]+e[a%m][b%m]for b in range(len(d)*m)]for a in range(len(d)*m)];g=GP(dd);best=999
  for trial in range(30):
   s=g.greedy();best=min(best,len(s))
   if len(s)<min(k,l):print('COUNTEREXAMPLE',d,e,s,flush=True);break
  r=dict(rep=rep,orders=[len(d),m],factor_lower=[k,l],best_found=best);print(r,flush=True);out.append(r)
elif mode=='antimagic':
 for n in range(5,31):
  eligible=success=0;hard=[]
  for rep in range(120):
   a=graph(n,rng.choice([.15,.3,.5,.7,.9]));nb=[tuple(sorted(s))for s in a]
   if len(set(nb))<n:continue
   eligible+=1;found=False
   for trial in range(2000):
    p=list(range(1,n+1));rng.shuffle(p);w=[sum(p[v]for v in s)for s in a]
    if len(set(w))==n:found=True;success+=1;break
   if not found:hard.append([list(s)for s in a])
  r=dict(n=n,eligible=eligible,labeling_found=success,unresolved=hard);out.append(r);print(r,flush=True)
(D/f'outputs/graphs-{mode}.json').write_text(json.dumps(out,indent=2)+'\n')
