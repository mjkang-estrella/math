"""Deterministic ordinary finite verification; not a Lean certificate."""
import json
from pathlib import Path
p=Path(__file__).parent
d=json.loads((p/'coloring-diagnostics.json').read_text());v=d['vertex_colors'];e=d['edge_colors'];n=12
assert len(v)==len(e)==n and all(0<=x<7 for x in v+e)
for i in range(n):
 assert v[i]!=v[(i+1)%n]
 assert e[i]!=e[(i+1)%n]
 assert e[i]!=v[i] and e[i]!=v[(i+1)%n]
ps=[]
for i in range(n):
 E={e[i-1],e[i]}; V={v[i-1],v[i],v[(i+1)%n]}
 ps.append([E,V,E|{v[i]},E|V])
assert all(len({frozenset(row[j]) for row in ps})==n for j in range(4))
assert [[sorted(row[j]) for row in ps] for j in range(4)]==d['palettes']
H={(i,(i+1)%n) for i in range(n) if i%3!=2}
leaf_edges=[]
for i in range(n):
 inc=[ed for ed in H if i in ed]
 if len(inc)==1:leaf_edges.append(inc[0])
assert len(leaf_edges)==len(set(leaf_edges))==8
print('PASS: proper7-total coloring, all four palette injections; eight distinct leaf edges in H. Ordinary proof only.')
