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
