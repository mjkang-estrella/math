"""Bounded exact path-cover checks, not a universal proof."""
from functools import lru_cache
from pathlib import Path
import json,datetime
L=Path(__file__).resolve().parent
def verify(c,n,t):
 return len(c)==n and set(c)==set(range(1,n+1)) and all(b-a in (1,3,7,-t) for a,b in zip(c,c[1:]+c[:1]))
def cover(n,t,starts):
 starts=tuple(starts);ends={a+t:i for i,a in enumerate(starts)};r=len(starts)
 if len(set(starts))!=r or min(starts)!=1 or max(starts)+t!=n:return None,0
 nodes=0
 @lru_cache(None)
 def go(p,ages,links):
  nonlocal nodes
  nodes+=1
  if p>n:
   if any(x<0 for x in links):return None
   at=0;seen=set()
   while at not in seen:seen.add(at);at=links[at]
   return () if len(seen)==r and at==0 else None
  if p in starts:choices=[starts.index(p)]
  else:choices=[i for i,a in enumerate(ages) if a in (1,3,7) and links[i]<0]
  for i in choices:
   if p in starts and ages[i]!=-1:continue
   aa=tuple(1 if j==i else (a+1 if a>=0 else -1) for j,a in enumerate(ages));ll=list(links)
   if p in ends:ll[i]=ends[p]
   if any(a>7 and ll[j]<0 for j,a in enumerate(aa)):continue
   z=go(p+1,aa,tuple(ll))
   if z is not None:return (i,)+z
  return None
 word=go(1,(-1,)*r,(-1,)*r)
 if word is None:return None,nodes
 paths=[[p for p,c in enumerate(word,1) if c==i] for i in range(r)]
 succ={a:b for path in paths for a,b in zip(path,path[1:])}
 for path in paths:succ[path[-1]]=path[-1]-t
 cycle=[1]
 for _ in range(n-1):cycle.append(succ[cycle[-1]])
 assert succ[cycle[-1]]==1 and verify(cycle,n,t)
 return cycle,nodes
def two(n,t):
 s=n-t
 if not(t<n<=2*t and n%4==0 and t%2==0):return None
 word=[0]*(s-1)
 for j in range((t-s+2)//2):word.extend([1 if j%2==0 else 0]*2)
 word.extend([0]*(s-1))
 paths=[[p for p,c in enumerate(word,1) if c==i] for i in (0,1)]
 return paths[0]+paths[1]
out=[];states=0
for t in (range(16,49,2) if __name__=='__main__' else []):
 for n in range(t+1,2*t+2):
  if n%4==0:
   c=two(n,t);assert c is not None and verify(c,n,t)
  eligible=n%4 in (1,2) or (t%4==2 and n%4==3)
  if not eligible:continue
  s=n-t;r=3 if n%2 else 4
  if s<r:continue
  c,z=cover(n,t,list(range(1,r))+[s]);states+=z
  out.append(dict(t=t,n=n,starts=list(range(1,r))+[s],found=c is not None,states=z,cycle=c))
if __name__=='__main__':
 result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=out,states=states,successes=sum(x['found'] for x in out),failures=[(x['t'],x['n']) for x in out if not x['found']],scope='Fixed-start r=3/4 increasing path-cover ansatz only; failed ansatz is not non-Hamiltonicity.')
 (L/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
 print({k:v for k,v in result.items() if k!='records'})
