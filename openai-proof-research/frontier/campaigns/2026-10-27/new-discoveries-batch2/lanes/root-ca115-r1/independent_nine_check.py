"""Second code path: tuple columns and the literal Wolfram rule table.
No rotation/Boolean-simplification logic from column_graph.py is reused.
Also emits finite inductive certificates (forward/backward invariant sets).
"""
from itertools import product
from collections import deque
import json
from pathlib import Path

P=9
table={(1,1,1):0,(1,1,0):1,(1,0,1):1,(1,0,0):1,
       (0,1,1):0,(0,1,0):0,(0,0,1):1,(0,0,0):1}
def enc(c):return sum(x<<t for t,x in enumerate(c))
words=list(product((0,1),repeat=P))
valid=[c for c in words if all(c[(t-1)%P]^c[(t+1)%P]==1 for t in range(P) if c[t]==0)]
def legal(l,m,r):
    return all(m[(t+1)%P]==(m[(t-1)%P]^table[l[t],m[t],r[t]]) for t in range(P))
vertices=list(product(valid,repeat=2))
edges={v:[(v[1],r) for r in valid if legal(*v,r)] for v in vertices}
pred={v:[] for v in vertices}
for v,vs in edges.items():
    for w in vs:pred[w].append(v)
bg=tuple(int(t%3==1) for t in range(P));root=(bg,bg)
def reach(adj):
    seen={root};q=deque([root])
    while q:
        for w in adj[q.popleft()]:
            if w not in seen:seen.add(w);q.append(w)
    return seen
fw=reach(edges);bw=reach(pred);core=fw&bw
assert len(core)==3
assert all(all(c[t]==c[(t+3)%P] for c in v for t in range(P)) for v in core)
assert all(w in fw for v in fw for w in edges[v])
assert all(v in bw for w in bw for v in pred[w])
def pairs(s):return sorted([enc(x),enc(y)] for x,y in s)
result=dict(period=P,background=enc(bg),valid_columns=sorted(map(enc,valid)),
            vertex_count=len(vertices),edge_count=sum(map(len,edges.values())),
            forward=pairs(fw),backward=pairs(bw),core=pairs(core),
            statement='Every finite spatial loop through the background has 3-periodic columns. This excludes exact temporal period 9 for every finite initial configuration.')
Path('nine-certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('forward','backward','valid_columns')}))
print('forward',len(fw),'backward',len(bw),'intersection',len(core))
