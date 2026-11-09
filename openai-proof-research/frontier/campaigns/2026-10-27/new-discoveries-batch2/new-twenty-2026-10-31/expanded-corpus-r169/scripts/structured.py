import pathlib,sys,json,time
D=pathlib.Path(__file__).resolve().parents[1];sys.dont_write_bytecode=True;sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'));import networkx as nx,z3
start=time.monotonic();out={'scope':'Proper open conflict-free edge colorings on seeded random regular graphs; exact SMT with8s instance timeout; diagnostic only','rows':[],'counterexamples':[]}
for degree in [3,4,5,6]:
 for n in [10,14,20,30]:
  if time.monotonic()-start>100:break
  g=nx.random_regular_graph(degree,n,seed=169+degree*100+n);E=list(g.edges());c=[z3.Int('c'+str(i)) for i in range(len(E))];s=z3.Solver();s.set(timeout=8000);k=degree+3
  s.add(*[z3.And(x>=0,x<k) for x in c]);inc={v:[i for i,e in enumerate(E) if v in e] for v in g}
  for v in g:s.add(z3.Distinct([c[i] for i in inc[v]]))
  for i,(u,v) in enumerate(E):
   nei=(set(inc[u])|set(inc[v]))-{i};s.add(z3.Or([z3.And([c[j]!=c[t] for t in nei if t!=j]) for j in nei]))
  for j,e in enumerate(inc[0]):s.add(c[e]==j)
  ans=str(s.check());out['rows'].append({'degree':degree,'n':n,'m':len(E),'result':ans})
  if ans=='unsat':out['counterexamples'].append({'n':n,'edges':E})
  (D/'outputs/structured.json').write_text(json.dumps(out,indent=2))
out['wall_seconds']=time.monotonic()-start;(D/'outputs/structured.json').write_text(json.dumps(out,indent=2));print(out)
