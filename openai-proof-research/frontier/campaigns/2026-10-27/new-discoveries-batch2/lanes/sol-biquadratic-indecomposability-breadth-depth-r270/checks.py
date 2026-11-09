from pathlib import Path
from itertools import combinations
from collections import deque,Counter
from math import isqrt
from fractions import Fraction as F
import json
L=Path(__file__).resolve().parent
# Exact isolating bounds: integer arithmetic only.
Q=10**8
roots={n:(F(isqrt(n*Q*Q),Q),F(isqrt(n*Q*Q)+1,Q)) for n in (14,26,91)}
def interval(a,coeff):
 lo=hi=F(a)
 for n,c in coeff.items():
  x,y=roots[n];lo+=c*(x if c>=0 else y);hi+=c*(y if c>=0 else x)
 return lo,hi
emb=[]
for s in (-1,1):
 for t in (-1,1):
  lo,hi=interval(13,{14:s*F(5,2),91:t,26:s*t*F(5,2)})
  assert lo>0;emb.append([str(lo),str(hi)])
assert 14*91==49*26 and 26**2>25*26
# Quadratic decomposition is impossible since each of its two integer
# constant coefficients must be >=5*b+1 and >=5*(5-b)+1.
assert all((5*b)**2<=26*b*b<(5*b+1)**2 for b in range(6))
# b=0 has exact root 0, but strict positivity still forces constant >=1.
assert all((5*b+1)+(5*(5-b)+1)==27 for b in range(6))
# A second, distinct source family: a routine existence control for Problem2.22.
triples=list(combinations(range(5),3))
cyclic=[tuple(sorted({i,(i+1)%5,(i+2)%5})) for i in range(5)]
blocks=triples+cyclic
G=[set() for _ in range(20)]
for j,T in enumerate(blocks,5):
 for i in T:G[i].add(j);G[j].add(i)
D=[]
for u in range(20):
 d=[-1]*20;d[u]=0;q=deque([u])
 while q:
  v=q.popleft()
  for w in G[v]:
   if d[w]<0:d[w]=d[v]+1;q.append(w)
 assert min(d)>=0;D.append(d)
assert [len(G[i]) for i in range(5)]==[9]*5
assert [len(G[i]) for i in range(5,20)]==[3]*15
counts=set()
for u in range(5):
 for v in G[u]:
  counts.add((sum(D[u][w]<D[v][w] for w in range(20)),sum(D[v][w]<D[u][w] for w in range(20))))
assert counts=={(11,9)}
twins=Counter(tuple(sorted(G[i])) for i in range(5,20))
assert set(twins.values())=={1,2}
result=dict(arithmetic='integer/Fraction only; no floats',biquadratic_embedding_intervals=emb,
 quadratic_split_minimum_constant_sum=27,graph_vertices=20,graph_edges=sum(map(len,G))//2,
 graph_W_counts=sorted(counts),graph_twin_multiplicities=sorted(set(twins.values())),
 graph_diameter=max(map(max,D)),status='PASS; controls are not novelty evidence')
(L/'checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
