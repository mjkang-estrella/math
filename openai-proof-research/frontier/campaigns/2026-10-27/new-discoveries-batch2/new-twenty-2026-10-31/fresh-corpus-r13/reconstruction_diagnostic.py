import networkx as nx,itertools,json,time,pathlib
w=pathlib.Path(__file__).parent
hs=[]
for h in nx.graph_atlas_g():
 if len(h)>1 and nx.is_connected(h) and h.number_of_edges()>0:
  cards=[]
  for e in h.edges:
   c=h.copy();c.remove_edge(*e);cards.append(c)
  if all(nx.is_isomorphic(cards[0],c) for c in cards):hs.append(h)
for g in [nx.complete_graph(4),nx.complete_graph(5),nx.cubical_graph(),nx.petersen_graph(),nx.octahedral_graph(),nx.dodecahedral_graph()]:
 h=nx.Graph(); h.add_nodes_from(g.nodes)
 for i,(a,b) in enumerate(g.edges):h.add_edges_from([(a,len(g)+i),(b,len(g)+i)])
 if len(h)<=30:hs.append(h)
res=[]
for h in hs:
 g=nx.disjoint_union(h,h);e=next(iter(g.edges));p=g.degree(e[0])+g.degree(e[1])-2;c=g.copy();c.remove_edge(*e)
 blockers=[];seen=[]
 for a,b in nx.non_edges(c):
  if c.degree(a)+c.degree(b)!=p:continue
  t=c.copy();t.add_edge(a,b)
  if nx.is_isomorphic(t,g) or any(nx.is_isomorphic(t,s) for s in seen):continue
  seen.append(t); mult=0
  for x,y in t.edges:
   if t.degree(x)+t.degree(y)-2!=p:continue
   d=t.copy();d.remove_edge(x,y)
   if sorted(dict(d.degree()).values())==sorted(dict(c.degree()).values()) and nx.is_isomorphic(d,c):mult+=1
  if mult>=2:blockers.append({'added':[a,b],'multiplicity':mult,'edges':list(t.edges)})
 row={'nH':len(h),'mH':h.number_of_edges(),'degreeH':sorted(dict(h.degree()).values()),'edgesH':list(h.edges),'blockers':blockers};res.append(row)
 print(len(h),h.number_of_edges(),row['degreeH'],[b['multiplicity'] for b in blockers],flush=True)
(w/'reconstruction-diagnostics.json').write_text(json.dumps(res,indent=2))
