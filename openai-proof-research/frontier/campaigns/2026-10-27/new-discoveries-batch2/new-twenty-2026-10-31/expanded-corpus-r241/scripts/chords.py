from pathlib import Path
import sys,math
D=Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'))
import networkx as nx
def pairings(xs):
 if not xs:yield [];return
 for j in range(1,len(xs)):
  for q in pairings(xs[1:j]+xs[j+1:]):yield [(xs[0],xs[j])]+q
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 total=conn=chordal=0
 for P in pairings(list(range(2*n))):
  total+=1;G=nx.Graph();G.add_nodes_from(range(n))
  for i,(a,b) in enumerate(P):
   for j,(c,d) in enumerate(P[:i]):
    if a<c<b<d or c<a<d<b:G.add_edge(i,j)
  if nx.is_connected(G):
   conn+=1
   if nx.is_chordal(G):chordal+=1
 print('ROW',n,total,conn,chordal,'Catalan(n-1)^2',(math.comb(2*n-2,n-1)//n)**2,flush=True)
