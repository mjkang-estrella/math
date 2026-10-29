"""Exact controls for source Definition 2.2, not a lower-bound proof."""
from pathlib import Path
import json
H=Path(__file__).resolve().parent
results=[]
def path_exists(adj,s,t,edges):
 def rec(v,left,mask):
  if left==0:return v==t
  if v==t:return False
  for w in adj[v]:
   if not mask>>w&1 and rec(w,left-1,mask|1<<w):return True
  return False
 return rec(s,edges,1<<s)
for ell in range(3,6):
 for n1,n2 in [(ell+2,ell+2),(ell+2,ell+3),(ell+3,ell+2),(ell+3,ell+3)]:
  N=n1+n2;adj=[set() for _ in range(N)]
  def edge(i,j):adj[i].add(j);adj[j].add(i)
  # B1=0..ell-1, B2=n1..n1+ell-1, x1=0,x2=1,y1=n1.
  for i in range(ell,n1):edge(i,n1)
  for j in range(n1+ell,N):edge(0,j)
  edge(1,n1)
  for i in range(ell):
   for j in range(n1+1,n1+ell):edge(i,j)
  E=sum(map(len,adj))//2
  assert E==n1+n2+ell*ell-3*ell+1
  # Peel leaves to independently certify no cycle of forbidden length.
  core=set(range(N));change=True
  while change:
   gone={i for i in core if len(adj[i]&core)<2};change=bool(gone);core-=gone
  assert len(core)<2*ell
  missing=[(i,j) for i in range(n1) for j in range(n1,N) if j not in adj[i]]
  assert all(path_exists(adj,i,j,2*ell-1) for i,j in missing)
  results.append({'ell':ell,'n1':n1,'n2':n2,'edges':E,'missing_edges_certified':len(missing),'core_size':len(core)})
print(json.dumps({'status':'PASS','scope':'12 fixed source-construction controls only; no minimality or conjecture proof','cases':results},indent=2))
