import pathlib,sys,itertools,json,time
D=pathlib.Path(__file__).resolve().parents[1];sys.dont_write_bytecode=True;sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'));sys.path.insert(0,str(D/'scripts'));import networkx as nx;from finite import solve,adj
start=time.monotonic();out={'scope':'graph atlas through7; exact chromatic number, odd simple-path edge packing avoiding other terminals; per packing cap 100000 nodes','tested':0,'nontrivial':0,'unknown':[],'counterexamples':[]}
for gi,g in enumerate(nx.graph_atlas_g()):
 n=len(g)
 if not n:continue
 if time.monotonic()-start>100:break
 a=[set(g[v]) for v in range(n)];chi=next(k for k in range(1,n+1) if solve(a,k)[0]);out['tested']+=1
 if chi<=3:continue # Bipartite or odd cycle yields the required immersion.
 out['nontrivial']+=1;E=list(g.edges());ix={tuple(sorted(e)):j for j,e in enumerate(E)};found=False;unknown=False
 for T in itertools.combinations([v for v in g if g.degree(v)>=chi-1],chi):
  options=[]
  for u,v in itertools.combinations(T,2):
   h=g.copy();h.remove_nodes_from(set(T)-{u,v});paths=[]
   for p in nx.all_simple_paths(h,u,v):
    if (len(p)-1)%2:paths.append(sum(1<<ix[tuple(sorted((s,t)))] for s,t in zip(p,p[1:])))
   options.append(paths)
  options.sort(key=len);nodes=[0]
  def rec(j,used):
   nodes[0]+=1
   if nodes[0]>100000:raise TimeoutError
   if j==len(options):return True
   return any(rec(j+1,used|p) for p in options[j] if not used&p)
  try:found=rec(0,0)
  except TimeoutError:unknown=True
  if found:break
 if not found:
  if unknown:out['unknown'].append(gi)
  else:out['counterexamples'].append({'atlas':gi,'edges':E,'chi':chi});break
 (D/'outputs/immersion.json').write_text(json.dumps(out,indent=2))
out['wall_seconds']=time.monotonic()-start;(D/'outputs/immersion.json').write_text(json.dumps(out,indent=2));print(out)
