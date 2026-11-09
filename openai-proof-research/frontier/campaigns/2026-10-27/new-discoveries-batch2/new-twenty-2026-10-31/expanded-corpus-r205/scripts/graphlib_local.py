class Graph:
 def __init__(self):self.a={}
 def add_nodes_from(self,vs):
  for v in vs:self.a.setdefault(v,set())
 def add_edge(self,a,b):self.a[a].add(b);self.a[b].add(a)
 def degree(self,v):return len(self.a[v])
 def __iter__(self):return iter(self.a)
 def __len__(self):return len(self.a)
 def subgraph(self,vs):
  vs=set(vs);g=Graph();g.a={v:self.a[v]&vs for v in vs};return g
def connected_components(g):
 todo=set(g)
 while todo:
  c={todo.pop()};q=list(c)
  for v in q:
   for u in g.a[v]&todo:todo.remove(u);c.add(u);q.append(u)
  yield c
def find_cliques(g):
 def go(R,P,X):
  if not P and not X:yield list(R);return
  u=max(P|X,key=lambda v:len(P&g.a[v])) if P|X else None
  for v in list(P-(g.a[u] if u is not None else set())):
   yield from go(R|{v},P&g.a[v],X&g.a[v]);P.remove(v);X.add(v)
 yield from go(set(),set(g),set())
