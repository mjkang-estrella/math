class Graph:
 def __init__(self,n=0):self.a={i:set() for i in range(n)}
 def __iter__(self):return iter(self.a)
 def __len__(self):return len(self.a)
 def add_edge(self,x,y):self.a.setdefault(x,set()).add(y);self.a.setdefault(y,set()).add(x)
 def add_edges_from(self,es):
  for x,y in es:self.add_edge(x,y)
 def remove_edge(self,x,y):self.a[x].remove(y);self.a[y].remove(x)
 def has_edge(self,x,y):return y in self.a[x]
 def degree(self,x):return len(self.a[x])
 def edges(self):return [(x,y) for x in self for y in self.a[x] if x<y]
 def number_of_edges(self):return sum(map(len,self.a.values()))//2
 def copy(self):
  H=Graph();H.a={x:set(v) for x,v in self.a.items()};return H
def cycle_graph(n):
 G=Graph(n);G.add_edges_from((i,(i+1)%n) for i in range(n));return G
def relabel_nodes(G,f):
 H=Graph();H.a={f(x):{f(y) for y in G.a[x]} for x in G};return H
def convert_node_labels_to_integers(G):
 d={x:i for i,x in enumerate(G)};return relabel_nodes(G,d.__getitem__)
def compose(G,H):
 J=G.copy();J.add_edges_from(H.edges());return J
def complete_bipartite_graph(a,b):
 G=Graph(a+b);G.add_edges_from((i,j) for i in range(a) for j in range(a,a+b));return G
def add_path(G,vs):G.add_edges_from(zip(vs,vs[1:]))
def non_edges(G):return [(x,y) for x in G for y in G if x<y and not G.has_edge(x,y)]
def from_prufer_sequence(s):
 n=len(s)+2;d=[1]*n
 for x in s:d[x]+=1
 G=Graph(n)
 for x in s:
  y=next(i for i in range(n) if d[i]==1);G.add_edge(x,y);d[x]-=1;d[y]-=1
 u,v=[i for i in range(n) if d[i]==1];G.add_edge(u,v);return G
def k_core(G,k):
 H=G.copy()
 while True:
  gone=[x for x in H if H.degree(x)<k]
  if not gone:return H
  for x in gone:
   for y in list(H.a[x]):H.a[y].remove(x)
   del H.a[x]
def line_graph(G):
 es=G.edges();H=Graph(len(es))
 H.add_edges_from((i,j) for i in range(len(es)) for j in range(i) if set(es[i])&set(es[j]));return H
