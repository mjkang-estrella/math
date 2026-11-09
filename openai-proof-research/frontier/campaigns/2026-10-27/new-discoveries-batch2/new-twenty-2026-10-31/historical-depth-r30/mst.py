from fractions import Fraction as F
from itertools import combinations
from collections import defaultdict
import pathlib,json,math
W=pathlib.Path(__file__).resolve().parent
E=[(3*r+c,3*rr+cc) for r in range(3) for c in range(3) for rr,cc in [(r+1,c),(r,c+1)] if rr<3 and cc<3];out=[]
for T in combinations(range(12),8):
 adj=[[] for _ in range(9)]
 for i,e in enumerate(T):
  u,v=E[e];adj[u].append((v,i));adj[v].append((u,i))
 seen={0};todo=[0]
 while todo:
  u=todo.pop()
  for v,i in adj[u]:
   if v not in seen:seen.add(v);todo.append(v)
 if len(seen)!=9:continue
 masks=[0]*8;stretch=0
 for j,e in enumerate(set(range(12))-set(T)):
  u,v=E[e];todo=[(u,-1,0)]
  while todo:
   a,parent,path=todo.pop()
   if a==v:break
   for b,i in adj[a]:
    if b!=parent:todo.append((b,a,path|(1<<i)))
  stretch+=path.bit_count()
  for i in range(8):
   if path>>i&1:masks[i]|=1<<j
 union=[0]*256;dp=[F(0)]*256;dp[0]=F(1)
 for s in range(1,256):
  bit=s&-s;i=bit.bit_length()-1;union[s]=union[s^bit]|masks[i]
  dp[s]=sum((dp[s^(1<<i)] for i in range(8) if s>>i&1),F(0))/(s.bit_count()+union[s].bit_count())
 out.append(dict(tree=list(T),probability=str(dp[-1]),stretch_sum_chords=stretch))
assert len(out)==192;assert sum((F(x['probability']) for x in out),F(0))==1
out.sort(key=lambda x:F(x['probability']),reverse=True)
(W/'mst-3x3-all.json').write_text(json.dumps(dict(edges=E,trees=out),indent=2)+'\n')
print('3x3 trees',len(out),'total probability 1; exact Fractions, diagnostic semantics not Lean certified');print('maximum',out[0]);print('minimum',out[-1])
by=defaultdict(list)
for x in out:by[x['stretch_sum_chords']].append(x)
for k,v in by.items():
 if F(v[0]['probability'])!=F(v[-1]['probability']):print('equal stretch unequal probability',k,v[0],v[-1]);break
print('8x8 recurrence cost: branches',2**63,'dual chords',2**49,'states; no such sweep attempted')
