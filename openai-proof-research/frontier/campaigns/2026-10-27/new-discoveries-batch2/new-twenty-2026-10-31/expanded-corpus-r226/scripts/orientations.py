from pathlib import Path
from itertools import combinations,product
import random,json
L=Path(__file__).resolve().parents[1]
def avoiding(M,F):
 n=len(M);d=sum(M[0]);allow=set(range(d+1))-set(F)
 def rec(v,out):
  if v==n:return True
  later=[j for j in range(v+1,n) if M[v][j]]
  for values in product(*(range(M[v][j]+1) for j in later)):
   if out[v]+sum(values) not in allow:continue
   nxt=list(out)
   for j,x in zip(later,values):nxt[j]+=M[v][j]-x
   if all(any(nxt[j]<=a<=nxt[j]+sum(M[j][l] for l in range(v+1,n)) for a in allow) for j in range(v+1,n)) and rec(v+1,nxt):return True
  return False
 return rec(0,[0]*n)
results=[]
for d in range(7,12):
 count=0
 for a in range(d+1):
  for b in range(d-a+1):
   c=d-a-b;M=[[0,a,b,c],[a,0,c,b],[b,c,0,a],[c,b,a,0]]
   for F in combinations(range(d+1),(d-1)//2):
    assert avoiding(M,F),(d,M,F)
    count+=1
 row=dict(degree=d,vertices=4,labelled_regular_multigraphs=(d+1)*(d+2)//2,maximal_forbidden_lists_checked=count);print(json.dumps(row),flush=True);results.append(row)
r=random.Random(226);count=0
for trial in range(100):
 n=6;d=7;M=[[0]*n for _ in range(n)]
 for _ in range(d):
  vs=list(range(n));r.shuffle(vs)
  for u,v in zip(vs[::2],vs[1::2]):M[u][v]+=1;M[v][u]+=1
 for F in combinations(range(d+1),3):
  assert avoiding(M,F),(M,F)
  count+=1
print(json.dumps(dict(degree=7,vertices=6,sampled_graphs=100,seed=226,lists_checked=count)),flush=True)
(L/'inputs/orientation-coverage.json').write_text(json.dumps(results+[dict(degree=7,vertices=6,sampled_graphs=100,seed=226,lists_checked=count)],indent=2)+'\n')
