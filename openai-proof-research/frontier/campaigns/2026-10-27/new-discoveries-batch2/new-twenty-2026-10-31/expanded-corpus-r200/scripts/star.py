import itertools as it,json,pathlib,sys,time
D=pathlib.Path(__file__).resolve().parents[1]; m=int(sys.argv[1]);arity=int(sys.argv[2]);rows=[];start=time.monotonic()
V=list(it.product(range(3),repeat=m));inv=lambda x:tuple(2-a for a in x);meet=lambda x,y:tuple(min(a,b) for a,b in zip(x,y));le=lambda x,y:all(a<=b for a,b in zip(x,y));order=lambda x:x.count(1)
edges=list(it.combinations(range(m),2))
for mask in range(1<<len(edges)):
 E=[e for j,e in enumerate(edges) if mask>>j&1];U=[s for s in V if all({s[a],s[b]}!={0,2} for a,b in E)]
 L={x:[u for u in U if u!=inv(u) and le(u,x) and order(u)<=order(x) and all(order(meet(y,u))<=order(y) for y in U if le(y,x))] for x in U}
 count=0
 for X in it.combinations([x for x in U if x!=inv(x)],arity):
  count+=1;ok=False
  for us in it.product(*(L[x] for x in X)):
   if any(not le(us[i],inv(us[j])) for i in range(arity) for j in range(i)):continue
   if all(us[i]==tuple(min([X[i][v]]+[2-us[j][v] for j in range(arity) if i!=j]) for v in range(m)) for i in range(arity)):
    ok=True;break
  if not ok:
   print(json.dumps({'counterexample':{'m':m,'edges':E,'X':X,'admissible':[[u for u in L[x]] for x in X]}}),flush=True);sys.exit(1)
 rows.append({'graph_mask':mask,'universe_size':len(U),'input_sets_checked':count})
 print(json.dumps(rows[-1]),flush=True)
(D/f'outputs/star-strict-m{m}-a{arity}.json').write_text(json.dumps({'m':m,'arity':arity,'rows':rows,'elapsed':time.monotonic()-start,'counterexamples':[]},indent=2))
