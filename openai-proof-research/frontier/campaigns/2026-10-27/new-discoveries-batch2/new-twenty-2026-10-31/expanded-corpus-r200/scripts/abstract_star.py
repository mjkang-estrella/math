import itertools as it,pathlib,json,sys,time
D=pathlib.Path(__file__).resolve().parents[1];m=int(sys.argv[1]);q=int(sys.argv[2]);kind=sys.argv[3];V=list(it.product(range(3 if kind=='ternary' else 2),repeat=m));top=2 if kind=='ternary' else 1
N=len(V);idx={v:i for i,v in enumerate(V)};inv=[idx[tuple(top-a for a in v)] for v in V];M=[[idx[tuple(min(a,b) for a,b in zip(x,y))] for y in V] for x in V];J=[[idx[tuple(max(a,b) for a,b in zip(x,y))] for y in V] for x in V];le=[[M[i][j]==i for j in range(N)] for i in range(N)];orbs=sorted(set(min(i,inv[i]) for i in range(N)));oi={k:j for j,k in enumerate(orbs)};nweights=0;ninputs=0;start=time.monotonic()
for vals in it.product(range(q),repeat=len(orbs)):
 w=[vals[oi[min(i,inv[i])]] for i in range(N)]
 if any(w[M[i][j]]+w[J[i][j]]>w[i]+w[j] for i in range(N) for j in range(i)):continue
 nweights+=1;L={x:[u for u in range(N) if u!=inv[u] and le[u][x] and w[u]<=w[x] and all(w[M[y][u]]<=w[y] for y in range(N) if le[y][x])] for x in range(N)}
 for X in it.combinations([x for x in range(N) if x!=inv[x]],3):
  ninputs+=1;found=False
  for us in it.product(*(L[x] for x in X)):
   if any(not le[us[i]][inv[us[j]]] for i in range(3) for j in range(i)):continue
   if all(us[i]==M[M[X[i]][inv[us[(i+1)%3]]]][inv[us[(i+2)%3]]] for i in range(3)):
    found=True;break
  if not found:
   o={'V':V,'weights':w,'X':[V[x] for x in X],'admissible':[[V[u] for u in L[x]] for x in X]};(D/f'outputs/abstract-obstruction-{kind}-{m}-{q}.json').write_text(json.dumps(o,indent=2));print('OBSTRUCTION',o,flush=True);sys.exit(1)
 if nweights%100==0:print(nweights,ninputs,flush=True)
o={'kind':kind,'dimension':m,'weight_range':list(range(q)),'involution_orbits':len(orbs),'order_functions':nweights,'input_triples':ninputs,'seconds':time.monotonic()-start,'counterexamples':[]};print(o);(D/f'outputs/abstract-star-{kind}-{m}-{q}.json').write_text(json.dumps(o,indent=2))
