import pathlib,sys,itertools,json,time,random
D=pathlib.Path(__file__).resolve().parents[1];sys.dont_write_bytecode=True;sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'));import networkx as nx
start=time.monotonic();out={'method':'Exact Cayley BFS on edge-subset F2 space, generators induced edge sets; atlas through6 and bounded seeded random7..10 m<=15','tested':0,'by_order':{},'counterexamples':[]};r=random.Random(363000)
def gen():
 yield from (g for g in nx.graph_atlas_g() if 0<len(g)<=6)
 for n in range(7,11):
  for j in range(50):
   g=nx.gnm_random_graph(n,r.randrange(n-1,16),seed=r);yield g
for g in gen():
 if time.monotonic()-start>100:break
 n=len(g);E=list(g.edges());m=len(E);delta=max(dict(g.degree()).values());gens={sum(1<<j for j,(u,v) in enumerate(E) if s>>u&1 and s>>v&1) for s in range(1<<n)}-{0}
 seen={0};front={0};diam=0
 while len(seen)<1<<m:
  front={x^y for x in front for y in gens}-seen;seen|=front;diam+=1
 out['tested']+=1;out['by_order'][str(n)]=out['by_order'].get(str(n),0)+1
 if diam>delta:out['counterexamples'].append({'n':n,'edges':E,'diameter':diam,'delta':delta});break
 (D/'outputs/inversion.json').write_text(json.dumps(out,indent=2))
out['wall_seconds']=time.monotonic()-start;(D/'outputs/inversion.json').write_text(json.dumps(out,indent=2));print(out)
