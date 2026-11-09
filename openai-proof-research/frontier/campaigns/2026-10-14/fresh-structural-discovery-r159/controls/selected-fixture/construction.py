"""Finite support for prefreeze calculations; no claim of novelty or review."""
from pathlib import Path
from itertools import combinations
from collections import Counter
import json
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r159')
def factors(n):
 if n<2:return []
 if n%2:
  return [[((c+i)%n,(c-i)%n) for i in range(1,(n+1)//2)] for c in range(n)]
 m=n-1
 return [[(n-1,c)]+[((c+i)%m,(c-i)%m) for i in range(1,(m+1)//2)] for c in range(m)]
def diagnosis(a,b,x,y):
 t=x+y;p=a-x;q=b-y
 if not(0<=x<=a and 0<=y<=b and t>=1):return 'invalid'
 if (x and b<t-1) or (y and a<t-1):return 'degree'
 dx=x>=3 and x%2==1 and q==x-1
 dy=y>=3 and y%2==1 and p==y-1
 if dx and not dy and p==0:return 'no-left-helper'
 if dy and not dx and q==0:return 'no-right-helper'
 if dx and dy and min(p,q)==2:return 'two-core-obstruction'
 return 'feasible'
def construct(a,b,x,y):
 why=diagnosis(a,b,x,y)
 if why!='feasible':return None
 A=list(range(x));B=list(range(a,a+y));U=list(range(x,a));V=list(range(a+y,a+b));paths=[[u,v] for u in A for v in B]
 residual=[]
 def side(term,steiner):
  n=len(term);F=factors(n)
  if len(F)<=len(steiner):
   for k,matching in enumerate(F):
    for i,j in matching:paths.append([term[i],steiner[k],term[j]])
   return []
  assert n%2 and len(steiner)==n-1
  order=[v for pair in F[0] for v in pair]
  for k,c in enumerate(order):
   for i,j in F[c]:paths.append([term[i],steiner[k],term[j]])
  return [(term[order[k]],steiner[k],steiner[k+1],term[order[k+1]]) for k in range(0,n-1,2)]
 rx=side(A,V);ry=side(B,U)
 if rx and not ry:
  paths.extend([[s,u,U[0],v,t] for s,u,v,t in rx])
 elif ry and not rx:
  paths.extend([[s,u,V[0],v,t] for s,u,v,t in ry])
 elif rx and ry:
  assert len(U)>=4 and len(V)>=4
  core={}
  def put(pa):core[frozenset([pa[0],pa[-1]])]=pa
  put([U[0],V[0],U[1]]);put([U[2],V[2],U[3]])
  put([V[0],U[2],V[1]]);put([V[2],U[0],V[3]])
  for k in range(4,len(U),2):put([U[k],V[0],U[k+1]])
  for k in range(4,len(V),2):put([V[k],U[0],V[k+1]])
  for s,u,v,t in rx+ry:
   pa=core[frozenset([u,v])]
   if pa[0]!=u:pa=pa[::-1]
   paths.append([s]+pa+[t])
 return paths

def verify(a,b,x,y,paths):
 terminals=set(range(x))|set(range(a,a+y));pairs=Counter();used=set()
 for pa in paths:
  assert len(pa)==len(set(pa))
  assert pa[0] in terminals and pa[-1] in terminals
  assert not(set(pa[1:-1])&terminals)
  pairs[frozenset([pa[0],pa[-1]])]+=1
  for u,v in zip(pa,pa[1:]):
   assert 0<=u<a+b and 0<=v<a+b and (u<a)!=(v<a)
   e=frozenset([u,v]);assert e not in used;used.add(e)
 assert pairs==Counter(frozenset(d) for d in combinations(terminals,2))
 p=a-x;q=b-y
 dx=max(0,x*(x-1)//2-q*(x//2));dy=max(0,y*(y-1)//2-p*(y//2))
 cost=x*y+x*(x-1)+y*(y-1)+2*(dx+dy)
 assert len(used)==cost
 assert all(len(pa)<=5 for pa in paths)
 return cost

def exhaustive(a,b,x,y,cap=100000):
 # Independent tiny instance search; direct cross edges are removed by the proven shortcut.
 U=set(range(x,a));V=set(range(a+y,a+b));nonterm=U|V
 demands=list(combinations(range(x),2))+list(combinations(range(a,a+y),2))
 states=0;options=[]
 for s,t in demands:
  out=[]
  def walk(pa,mask):
   if pa[-1]==t:out.append(mask);return
   for w in sorted(nonterm|{t}):
    u=pa[-1]
    if w in pa or (u<a)==(w<a):continue
    left,right=(u,w) if u<a else (w,u)
    walk(pa+[w],mask|(1<<(left*b+right-a)))
  walk([s],0);options.append(out)
 options.sort(key=len)
 def dfs(k,mask):
  nonlocal states
  states+=1
  if states>cap:raise RuntimeError('cap')
  if k==len(options):return True
  return any(dfs(k+1,mask|p) for p in options[k] if not(mask&p))
 try:return dfs(0,0),states
 except RuntimeError:return 'cap',states

if __name__=='__main__':
 counts=Counter();cases=0;costsum=0;examples={}
 for a in range(1,17):
  for b in range(1,17):
   for x in range(a+1):
    for y in range(b+1):
     if not x+y:continue
     d=diagnosis(a,b,x,y);counts[d]+=1;cases+=1
     pa=construct(a,b,x,y)
     if pa is not None:costsum+=verify(a,b,x,y,pa)
     if (a,b,x,y) in [(4,4,2,3),(5,5,3,3),(9,9,5,5),(6,5,3,3)]:examples[str((a,b,x,y))]={'diagnosis':d,'paths':pa}
 small=[]
 for a in range(1,5):
  for b in range(1,5):
   for x in range(a+1):
    for y in range(b+1):
     if x+y<2:continue
     result,states=exhaustive(a,b,x,y)
     assert result!='cap'
     assert result==(diagnosis(a,b,x,y)=='feasible'),(a,b,x,y,result)
     small.append({'a':a,'b':b,'x':x,'y':y,'routable':result,'states':states})
 result={'cases':cases,'diagnoses':dict(counts),'verified_cost_sum':costsum,'exhaustive_small':small,'examples':examples,'limit':'Finite support only; not a mathematical or contribution gate.'}
 (ROOT/'receipts/biclique-routes.json').write_text(json.dumps(result,indent=2))
 print(json.dumps({'cases':cases,'diagnoses':dict(counts),'small_cases':len(small),'small_search_states':sum(s['states'] for s in small),'costsum':costsum},indent=2))
