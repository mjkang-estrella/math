import random
class Graph:
 def __init__(self,E):self.E=list(E)
 def nodes(self):return list(set(v for e in self.E for v in e))
 def edges(self):return self.E
class nx:
 @staticmethod
 def line_graph(G):
  e=G.E;return Graph([(a,b) for j,a in enumerate(e) for b in e[:j] if set(a)&set(b)])
 @staticmethod
 def random_regular_graph(d,n,seed):
  rng=random.Random(seed);E={tuple(sorted((i,(i+1)%n))) for i in range(n)}|{(i,i+n//2) for i in range(n//2)}
  for _ in range(n*20):
   a,b=rng.sample(sorted(E),2);u,v=a;x,y=b
   if rng.randrange(2):x,y=y,x
   if len({u,v,x,y})<4:continue
   p=tuple(sorted((u,x)));q=tuple(sorted((v,y)))
   if p in E or q in E:continue
   E.remove(a);E.remove(b);E.add(p);E.add(q)
  return Graph(sorted(E))
 @staticmethod
 def is_connected(G):
  seen={G.E[0][0]}
  while True:
   t=seen|{v for e in G.E if any(u in seen for u in e) for v in e}
   if t==seen:return len(t)==len(G.nodes())
   seen=t
 @staticmethod
 def bridges(G):
  vs=G.nodes()
  return [e for e in G.E if len(set(v for f in G.E if f!=e for v in f))<len(vs) or not nx.is_connected(Graph([f for f in G.E if f!=e]))]
