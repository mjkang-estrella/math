from pathlib import Path
from itertools import combinations
from fractions import Fraction
from collections import Counter
import json
D=Path(__file__).resolve().parents[1]
def connected(n,es,mask=None):
 if mask is None:mask=(1<<n)-1
 if not mask:return False
 seen=mask&-mask;old=0
 while seen!=old:
  old=seen
  for a,b in es:
   if seen>>a&1 and mask>>b&1:seen|=1<<b
   if seen>>b&1 and mask>>a&1:seen|=1<<a
 return seen==mask
def degenerate(adj):
 a=[set(x) for x in adj];rem=set(range(len(a)));d=0
 while rem:
  v=min(rem,key=lambda v:len(a[v]&rem));d=max(d,len(a[v]&rem));rem.remove(v)
 return d
states={(tuple(combinations(range(3),2)),((0,1,2),))};out=[]
for n in range(3,9):
 hist=Counter();rob=Fraction(1);count=0;skipped=0
 for es,inner in states:
  faces=inner+((0,1,2),) # outer distinguished by index, even for triangle.
  if n>=4:
   closed=[]
   for s in range(1,1<<n):
    if not connected(n,es,s):continue
    cover=s
    for a,b in es:
     if s>>a&1:cover|=1<<b
     if s>>b&1:cover|=1<<a
    if cover==(1<<n)-1:closed.append(s)
   for R in range(1,1<<n):rob=min(rob,Fraction(R.bit_count()-min((R&s).bit_count() for s in closed),R.bit_count()))
  # Remove at most two edges, never vertices: precisely bounded subfamily.
  for num in range(3):
   for deleted in combinations(es,num):
    remain=[e for e in es if e not in deleted]
    if not connected(n,remain):skipped+=1;continue
    par=list(range(len(faces)))
    def find(a):
     while par[a]!=a:a=par[a]
     return a
    for a,b in deleted:
     inc=[j for j,f in enumerate(faces) if a in f and b in f]
     par[find(inc[0])]=find(inc[1])
    roots=sorted({find(j) for j in range(len(faces))});fi={r:n+j for j,r in enumerate(roots)};adj=[set() for _ in range(n+len(roots))]
    def edge(a,b):
     if a!=b:adj[a].add(b);adj[b].add(a)
    for a,b in remain:
     edge(a,b);inc=[j for j,f in enumerate(faces) if a in f and b in f];edge(fi[find(inc[0])],fi[find(inc[1])])
    for j,f in enumerate(faces):
     for v in f:edge(v,fi[find(j)])
    hist[degenerate(adj)]+=1;count+=1
  # end deletions
 r={'n':n,'stacking_states':len(states),'connected_edge_deletion_instances':count,'disconnected_skipped':skipped,'coupled_graph_degeneracy_histogram':dict(hist),'robust_connectivity_minimum_over_stacked':str(rob) if n>=4 else None,'scope':'not all triangulations; inherited labels; deletions at most two; degeneracy >=6 is inconclusive for 6-list colourability'};out.append(r);print(r,flush=True)
 nxt=set()
 for es,faces in states:
  for j,f in enumerate(faces):
   a,b,c=f;newes=tuple(sorted(es+tuple((v,n) for v in f)));newfaces=tuple(sorted(faces[:j]+faces[j+1:]+tuple(tuple(sorted((u,v,n))) for u,v in [(a,b),(a,c),(b,c)])));nxt.add((newes,newfaces))
 states=nxt
(D/'outputs/stacked.json').write_text(json.dumps(out,indent=2))
