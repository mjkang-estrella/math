import pathlib,sys,time,json
D=pathlib.Path(__file__).resolve().parents[1];sys.dont_write_bytecode=True;sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'));import networkx as nx
start=time.monotonic();out={'scope':'graph atlas all nonempty orders<=7; exact disjoint fort packing and zero forcing; not maximum nullity or fractional LP','tested':0,'by_order':{},'violations':[],'histogram':{}}
for g in nx.graph_atlas_g():
 n=len(g)
 if not n:continue
 N=[sum(1<<v for v in g[u]) for u in range(n)];full=(1<<n)-1
 forts=[s for s in range(1,full+1) if all((N[v]&s).bit_count()!=1 for v in range(n) if not s>>v&1)]
 minimal=[s for s in forts if not any(t!=s and t&s==t for t in forts)]
 dp=[0]*(1<<n)
 for s in range(1,full+1):dp[s]=max([0]+[1+dp[s^f] for f in minimal if f&s==f])
 Z=min(s.bit_count() for s in range(full+1) if all(s&f for f in minimal));ft=dp[full]
 out['tested']+=1;out['by_order'][str(n)]=out['by_order'].get(str(n),0)+1;key=str((ft,Z));out['histogram'][key]=out['histogram'].get(key,0)+1
 if ft>Z:out['violations'].append({'n':n,'edges':list(g.edges())})
out['wall_seconds']=time.monotonic()-start;(D/'outputs/fort.json').write_text(json.dumps(out,indent=2));print(out)
