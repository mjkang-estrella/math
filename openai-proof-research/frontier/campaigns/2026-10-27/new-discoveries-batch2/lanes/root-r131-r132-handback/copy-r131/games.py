import random,json,sys
from pathlib import Path
from functools import lru_cache
L=Path(__file__).resolve().parent
def solve(n,edges,total=False,greedy=False):
 adj=[0]*n;full=(1<<n)-1
 for a,b in edges:adj[a]|=1<<b;adj[b]|=1<<a
 @lru_cache(None)
 def info(s):
  dominated=0
  for i in range(n):
   if s>>i&1:dominated|=adj[i] if total else adj[i]|(1<<i)
  rem=full^dominated;active=0
  for i in range(n):
   if rem>>i&1 and (adj[i]&rem or (total and s>>i&1)):active|=1<<i
  return active
 @lru_cache(None)
 def value(s,turn):
  active=info(s)
  legal=[i for i in range(n) if not s>>i&1 and (adj[i] if total else adj[i]|1<<i)&active]
  if not legal:return 0
  if greedy and turn==0:
   gains=[active.bit_count()-info(s|1<<i).bit_count() for i in legal];m=max(gains)
   legal=[i for i,g in zip(legal,gains) if g==m]
  vals=[value(s|1<<i,1-turn)+1 for i in legal]
  return min(vals) if turn==0 else max(vals)
 d=value(0,0);st=value(0,1)
 return d,st,value.cache_info().currsize
def tree(n,rng):
 code=[rng.randrange(n) for _ in range(n-2)];degree=[1]*n
 for x in code:degree[x]+=1
 edges=[]
 for x in code:
  leaf=next(i for i,d in enumerate(degree) if d==1);edges.append((leaf,x));degree[leaf]-=1;degree[x]-=1
 u,v=[i for i,d in enumerate(degree) if d==1];edges.append((u,v));return edges
if __name__=='__main__':
 rng=random.Random(131);rec=[];fail=[]
 for n in range(3,15):
  for typ in ['tree','mindeg2']:
   for k in range(12):
    E=tree(n,rng) if typ=='tree' else [(i,(i+1)%n) for i in range(n)]
    if typ=='mindeg2':E+= [(i,j) for i in range(n) for j in range(i+2,n) if rng.random()<.12]
    E=sorted(set(tuple(sorted(e)) for e in E))
    d,s,c=solve(n,E);dt,st,ct=solve(n,E,True);dg,sg,cg=solve(n,E,True,True)
    r=dict(n=n,type=typ,edges=E,ordinary=[d,s],total=[dt,st],total_greedy=[dg,sg],states=[c,ct,cg]);rec.append(r)
    if 3*dt>2*n or 7*d>3*n or (typ=='mindeg2' and 7*s>3*n):fail.append(r);print('TARGET COUNTEREXAMPLE',r,flush=True)
  print('completed n',n,flush=True)
 # Source examples check literal rules, including failure of Continuation Principle.
 fixtures=[]
 for n in [3,4,5,6]:
  for typ in ['path','cycle']:
   E=[(i,i+1) for i in range(n-1)]+ ([(0,n-1)] if typ=='cycle' else [])
   fixtures.append(dict(n=n,type=typ,ordinary=solve(n,E)[:2],total=solve(n,E,True)[:2]))
 assert next(x for x in fixtures if x['n']==5 and x['type']=='path')['total']==(2,4)
 out=dict(seed=131,cases=len(rec),scope='12 random labeled trees and 12 cycle-plus-random-chord graphs for each n=3..14, not exhaustive',failures=fail,greedy_failures=[r for r in rec if 3*r['total_greedy'][0]>2*r['n']],fixtures=fixtures,records=rec)
 (L/'game-check-results.json').write_text(json.dumps(out,indent=2));print('cases',len(rec),'target failures',len(fail),'greedy failures',len(out['greedy_failures']))
