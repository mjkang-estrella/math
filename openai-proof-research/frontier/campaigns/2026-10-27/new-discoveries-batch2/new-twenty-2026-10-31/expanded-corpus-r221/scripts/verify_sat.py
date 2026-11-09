import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for p in sorted((D/'outputs').glob('*.cnf')):
 key=p.stem;logs=list((D/'logs').glob(key+'-solve.log'))
 if key.startswith('latin-'):
  logs=list((D/'logs').glob('latin-solve-'+key[6:]+'.log'))
  if key=='latin-4-2-2-1-1-1':logs=[D/'logs/latin-solve-422111.log']
 if key=='onecrossing30':logs=[D/'logs/onecrossing30-solve.log']
 assert len(logs)==1,(key,logs)
 lines=logs[0].read_text().splitlines();assert 's SATISFIABLE' in lines
 assignment={abs(int(s)):int(s)>0 for l in lines if l.startswith('v ') for s in l[2:].split() if int(s)!=0}
 count=0
 for l in p.read_text().splitlines():
  if l.startswith(('p','c')):continue
  c=list(map(int,l.split()))[:-1];assert any(assignment.get(abs(x))==(x>0) for x in c);count+=1
 out.append({'cnf':str(p.relative_to(D)),'log':str(logs[0].relative_to(D)),'clauses_verified':count,'assignment_variables':len(assignment)})
 if key.startswith('onecrossing'):
  o=json.loads(p.with_suffix('.json').read_text());fs=o['faces'];n=len({v for f in fs for v in f});edges={tuple(sorted(e)) for f in fs for e in itertools.combinations(f,2)};assert n-len(edges)+len(fs)==2
  for v in range(n):
   es=[tuple(x for x in f if x!=v) for f in fs if v in f];adj={}
   for a,b in es:adj.setdefault(a,set()).add(b);adj.setdefault(b,set()).add(a)
   assert all(len(s)==2 for s in adj.values());todo=[next(iter(adj))];seen=set(todo)
   for x in todo:
    for y in adj[x]:
     if y not in seen:seen.add(y);todo.append(y)
   assert len(seen)==len(adj)
  out[-1].update(sphere_link_tests=True,crossing_cases=len(o['cases']),n=n)
(D/'outputs/sat-verification.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
