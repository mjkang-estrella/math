from check import treecalc,add
from itertools import permutations
from pathlib import Path
import json

def direct(par,delay):
 N=len(par)-1; anc={}
 for v in range(1,N+1):
  a=[];p=par[v]
  while p>0:a.append(p);p=par[p]
  anc[v]=set(a)
 # DFS child order determines left-right order of incomparable vertices.
 order=[]
 def dfs(v):
  for w in range(1,N+1):
   if par[w]==v:dfs(w)
  if v:order.append(v)
 dfs(0);rank={v:i for i,v in enumerate(order)}
 pairs=[(u,v) for u in range(1,N+1) for v in range(1,N+1) if rank[u]<rank[v] and v not in anc[u] and u not in anc[v]]
 q=(0,);legal=0
 for perm in permutations(range(1,N+1)):
  pos={v:i+1 for i,v in enumerate(perm)}
  if any(pos[v]>pos[a] for v in anc for a in anc[v]):continue
  if any(pos[v]<d for v,d in delay.items()):continue
  exponent=sum(pos[u]<pos[v] for u,v in pairs);q=add(q,(1,),exponent);legal+=1
 assert q==treecalc(par,delay)
 return {'parents':par,'delays':delay,'Q':q,'legal_orders':legal,'permutations_tested':__import__('math').factorial(N)}
cases=[([-1,0,0,2,0],{1:1,3:1,4:2}),([-1,0,1,1,0,4,4],{2:3,3:1,5:1,6:2})]
a=[direct(*c) for c in cases]
# The second genuine-source polynomial fails log concavity, while remaining unimodal.
b=a[1]['Q'];fails=[i for i in range(1,len(b)-1) if b[i]*b[i]<b[i-1]*b[i+1]]
assert fails==[6]
Path('independent-checks.json').write_text(json.dumps({'cases':a,'logconcavity_failures':fails},indent=2));print('independent direct-order check PASS, exact log-concavity failure index6')
