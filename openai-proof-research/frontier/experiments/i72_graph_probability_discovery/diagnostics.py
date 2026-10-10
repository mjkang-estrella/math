"""Finite exact diagnostics. No file writes; no stochastic or asymptotic proof claims."""
from fractions import Fraction as F
from itertools import combinations,product
from collections import Counter
import json

def regular_graphs(n,d):
 adj=[set() for _ in range(n)]
 def rec(v):
  if v==n:
   yield frozenset((i,j) for i in range(n) for j in adj[i] if i<j);return
  k=d-len(adj[v]);cand=[u for u in range(v+1,n) if len(adj[u])<d]
  if k<0 or k>len(cand):return
  for neigh in combinations(cand,k):
   for u in neigh:adj[v].add(u);adj[u].add(v)
   yield from rec(v+1)
   for u in neigh:adj[v].remove(u);adj[u].remove(v)
 yield from rec(0)
def edge(x,y):return tuple(sorted((x,y)))
def adjacency(n,G):
 a=[set() for _ in range(n)]
 for u,v in G:a[u].add(v);a[v].add(u)
 return a
def girth(n,G):
 a=adjacency(n,G);ans=n+1
 for root in range(n):
  dist={root:0};parent={root:-1};queue=[root]
  for u in queue:
   for v in a[u]:
    if v not in dist:dist[v]=dist[u]+1;parent[v]=u;queue.append(v)
    elif parent[u]!=v:ans=min(ans,dist[u]+dist[v]+1)
 return ans
def distance(n,G,S,T):
 a=adjacency(n,G);seen=set(S);front=set(S);r=0
 while front:
  if front&set(T):return r
  front={v for u in front for v in a[u]}-seen;seen|=front;r+=1
 return n+1
def switch(G,ab,cd):
 a,b=ab;c,d=cd
 if len({a,b,c,d})<4:return None
 old={edge(a,b),edge(c,d)};new={edge(a,d),edge(c,b)}
 if new&G:return None
 return frozenset((G-old)|new)
def matrix(n,G):return [[int(edge(i,j) in G) if i!=j else 0 for j in range(n)] for i in range(n)]
def mul(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def charpoly(A):
 n=len(A);B=[[int(i==j) for j in range(n)] for i in range(n)];coef=[1]
 for k in range(1,n+1):
  B=mul(A,B);tr=sum(B[i][i] for i in range(n));assert tr%k==0;c=-tr//k;coef.append(c)
  for i in range(n):B[i][i]+=c
 return coef

def graph_checks():
 out=[]
 for n in (6,8):
  gs=list(regular_graphs(n,3));assert len(gs)=={6:70,8:19355}[n]
  hist=Counter(girth(n,G) for G in gs);out.append({'n':n,'regular_graphs':len(gs),'girth_histogram':dict(sorted(hist.items()))})
  # Every triangle-free state for n=6, representative n=8 states from each girth.
  reps=[G for G in gs if girth(n,G)>3] if n==6 else [next(G for G in gs if girth(n,G)==g) for g in hist if g>3]
  stats=Counter()
  for G in reps:
   for g in range(3,girth(n,G)):
    oriented=[(a,b) for e in sorted(G) for a,b in (e,e[::-1])]
    for ab,cd in product(oriented,repeat=2):
     H=switch(G,ab,cd);stats['proposals']+=1
     if H is None:continue
     if distance(n,G,ab,cd)>g:assert girth(n,H)>g;stats['far_valid']+=1
     if girth(n,H)>g:
      a,b=ab;c,d=cd;assert switch(H,(a,d),(c,b))==G;stats['accepted_involutions']+=1
     else:stats['girth_rejections']+=1
  out[-1]['switch_checks']=dict(stats)
 # Exact graph surgery diagnostic: K3,3 -> prism by one alternative switch.
 G=frozenset((a,b) for a in range(3) for b in range(3,6))
 H=switch(G,(0,3),(4,1));assert H
 cG=charpoly(matrix(6,G));cH=charpoly(matrix(6,H))
 assert cG==[1,0,-9,0,0,0,0]
 assert cH==[1,0,-9,-4,12,0,0]
 # nonvacuous far-switch check: union of two Petersen graphs, girth 5.
 P={edge(i,(i+1)%5) for i in range(5)}|{edge(i,i+5) for i in range(5)}|{edge(i+5,((i+2)%5)+5) for i in range(5)}
 PP=frozenset(P|{(a+10,b+10) for a,b in P});assert girth(20,PP)==5
 far=0
 for ab in sorted(P):
  for c,d in sorted(P):
   cd=(c+10,d+10);assert distance(20,PP,ab,cd)>4
   H2=switch(PP,ab,cd);assert H2 and girth(20,H2)>4;far+=1
 return {'enumerations':out,'surgery_characteristic_polynomials':[cG,cH],'petersen_far_switches':far}

def inverse(A):
 n=len(A);B=[[F(x) for x in row]+[F(i==j) for j in range(n)] for i,row in enumerate(A)]
 for i in range(n):
  k=next(k for k in range(i,n) if B[k][i]);B[i],B[k]=B[k],B[i];x=B[i][i];B[i]=[a/x for a in B[i]]
  for k in range(n):
   if k!=i:
    x=B[k][i];B[k]=[a-x*b for a,b in zip(B[k],B[i])]
 return [r[n:] for r in B]
def connection_matrix(n,edges,probs):
 T=[[F(0) for _ in range(n)] for _ in range(n)]
 for bits in product((0,1),repeat=len(edges)):
  prob=F(1);G=set()
  for e,p,b in zip(edges,probs,bits):
   prob*=p if b else 1-p
   if b:G.add(e)
  a=adjacency(n,G)
  for i in range(n):
   seen={i};queue=[i]
   for u in queue:
    for v in a[u]-seen:seen.add(v);queue.append(v)
   for j in seen:T[i][j]+=prob
 return T

def percolation_checks():
 n=5;base=[(i,i+1) for i in range(n-1)];extra=[(0,2),(0,4),(1,4)];p=[F(1,3)]*4;q=[F(1,50),F(1,40),F(1,30)]
 T=connection_matrix(n,base,p);U=connection_matrix(n,base+extra,p+q);B=[[F(0) for _ in range(n)] for _ in range(n)]
 for (i,j),v in zip(extra,q):B[i][j]=B[j][i]=v
 BT=mul(B,T);assert max(map(sum,BT))<1
 Iminus=[[F(i==j)-BT[i][j] for j in range(n)] for i in range(n)]
 upper=mul(T,inverse(Iminus));assert all(U[i][j]<=upper[i][j] for i in range(n) for j in range(n))
 return {'configurations':2**7,'kernel_entries':n*n,'min_entrywise_slack':str(min(upper[i][j]-U[i][j] for i in range(n) for j in range(n))),'max_BT_row_sum':str(max(map(sum,BT)))}

def matchings(vs):
 if not vs:yield frozenset();return
 a=vs[0]
 for j in range(1,len(vs)):
  b=vs[j]
  for M in matchings(vs[1:j]+vs[j+1:]):yield M|{edge(a,b)}
def weighted_check():
 states=list(matchings(list(range(6))));cycle={edge(i,(i+1)%6) for i in range(6)};M=next(m for m in states if m<=cycle)
 ans=[]
 for L in (1,4,12):
  delta=F(1,2**L);w={m:delta**len(m-cycle) for m in states};Z=sum(w.values());assert Z==2+3*delta+6*delta**2+4*delta**3
  exitprob=sum(min(F(1),w[m]/w[M])*F(1,180) for m in states if len(M-m)==2)
  assert exitprob==(delta+delta**2)/60
  ans.append({'L':L,'Z':str(Z),'escape':str(exitprob),'stationary_start':str(w[M]/Z)})
 # Literal cross-switch no longer self-adjoint/isometry in weighted L2.
 a=frozenset({(0,1),(2,3)});b=frozenset({(0,2),(1,3)});pa=F(2,3);pb=F(1,3)
 assert pa!=pb # indicator norm squared changes under the involution.
 return {'K6_regression':ans,'weighted_involution_norm_squares':[str(pa),str(pb)]}

def run():
 return {'scope':'finite exact algebra and enumeration only; no analytic or contribution certification','graphs':graph_checks(),'percolation':percolation_checks(),'sampling':weighted_check()}
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
