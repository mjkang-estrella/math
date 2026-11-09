import pathlib,sys,json,itertools,time,random
sys.path.insert(0,str(pathlib.Path(__file__).parent));from finite import adj,solve,graphs
D=pathlib.Path(__file__).resolve().parents[1];r=random.Random(360376);start=time.monotonic();out={'graphs':0,'precolorings':0,'by_order':{},'unknown':[],'counterexamples':[]}
for n,E,key in graphs('extension'):
 if time.monotonic()-start>100:break
 if not E:continue
 k=max(map(len,adj(n,E)))+1
 P=E+[(u+n,v+n) for u,v in E]+[(u,u+n) for u in range(n)];a=adj(2*n,P)
 # Exact endpoint distance >=3 means no endpoints equal, adjacent, or at distance2.
 near=[]
 for v in range(2*n):near.append({v}|a[v]|set().union(*(a[w] for w in a[v])))
 compatible={(i,j) for i,j in itertools.combinations(range(len(P)),2) if all(v not in near[u] for u in P[i] for v in P[j])}
 line=adj(len(P),[(i,j) for i,j in itertools.combinations(range(len(P)),2) if set(P[i])&set(P[j])])
 cases=[]
 for i,j in sorted(compatible):
  cases.extend([{i:0,j:0},{i:0,j:1}])
  for z in range(j+1,len(P)):
   if (i,z) in compatible and (j,z) in compatible:
    cases.extend([{i:0,j:0,z:0},{i:0,j:0,z:1},{i:0,j:1,z:0},{i:0,j:1,z:1},{i:0,j:1,z:2}])
 if len(cases)>100:r.shuffle(cases);cases=cases[:100]
 out['graphs']+=1;out['by_order'][str(n)]=out['by_order'].get(str(n),0)+1
 for pre in cases:
  if max(pre.values())>=k:continue
  ok,nodes=solve(line,k,pre=pre,cap=10000);out['precolorings']+=1
  if ok is None:out['unknown'].append({'key':key,'pre':pre})
  if ok is False:out['counterexamples'].append({'key':key,'n':n,'edges':E,'prism_edges':P,'pre':pre});break
 if out['counterexamples']:break
 (D/'outputs/extension.json').write_text(json.dumps(out,indent=2))
out['wall_seconds']=time.monotonic()-start;(D/'outputs/extension.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='unknown'})
