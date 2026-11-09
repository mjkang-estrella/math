import pathlib,sys,json,itertools,time
D=pathlib.Path(__file__).resolve().parents[1];sys.dont_write_bytecode=True;sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'));import networkx as nx
start=time.monotonic();out={'scope':'Connected graph atlas through7; dismantlable cop-win graphs with domination number>1; k=Delta; exact monotone game attractor where feasible','tested':0,'skipped_size':0,'wins':0,'counterexamples':[],'rows':[]}
def dismantle(g):
 h=g.copy()
 while len(h)>1:
  pair=next(((u,v) for u in h for v in h if u!=v and (set(h[u])|{u})<=(set(h[v])|{v})),None)
  if pair is None:return False
  h.remove_node(pair[0])
 return True
for gi,g in enumerate(nx.graph_atlas_g()):
 if time.monotonic()-start>100:break
 n=len(g)
 if n<2 or not nx.is_connected(g) or max(dict(g.degree()).values())==n-1 or not dismantle(g):continue
 k=max(dict(g.degree()).values());E=list(g.edges());m=len(E)
 P=list(itertools.combinations_with_replacement(range(m),k))
 if len(P)*n>1500:out['skipped_size']+=1;continue
 idx={p:i for i,p in enumerate(P)};inc=[{j for j,e in enumerate(E) if v in e} for v in range(n)]
 edgeN=[{j for j,f in enumerate(E) if set(e)&set(f)} for e in E]
 moves=[set(idx[tuple(sorted(z))] for z in itertools.product(*(edgeN[j] for j in p))) for p in P]
 C=set();R=set()
 for i,p in enumerate(P):
  for v in range(n):
   if inc[v]<=set(p):C.add((i,v));R.add((i,v))
 rounds=0
 while True:
  rounds+=1;nc=set(C);nr=set(R)
  for i,p in enumerate(P):
   for v in range(n):
    if (i,v) not in C and any((j,v) in R for j in moves[i]):nc.add((i,v))
    if (i,v) not in R:
     rv=[v]+[w for w in g[v] if E.index(tuple(sorted((v,w)))) not in p]
     if all((i,w) in C for w in rv):nr.add((i,v))
  if C==nc and R==nr:break
  C,R=nc,nr
  if time.monotonic()-start>100:break
 if time.monotonic()-start>100:out['unfinished']=gi;break
 win=any(all((i,v) in C for v in range(n)) for i in range(len(P)))
 out['tested']+=1;out['wins']+=win;out['rows'].append({'atlas':gi,'n':n,'m':m,'k':k,'placements':len(P),'rounds':rounds,'win':win})
 if not win:out['counterexamples'].append({'atlas':gi,'edges':E});break
 (D/'outputs/contain.json').write_text(json.dumps(out,indent=2))
out['wall_seconds']=time.monotonic()-start;(D/'outputs/contain.json').write_text(json.dumps(out,indent=2));print(out)
