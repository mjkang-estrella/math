import importlib.util,pathlib,random,itertools,json
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('w',D/'scripts/weak_search.py');w=importlib.util.module_from_spec(s);s.loader.exec_module(w);rng=random.Random(437225)
for n in range(10,19):
 passed=unknown=weakcount=0;unclear=[]
 for z in range(5000):
  p=rng.choice([.16,.22,.28,.34,.40]);a=[0]*n
  for i,j in itertools.combinations(range(n),2):
   if rng.random()<p:w.toggle(a,i,j)
  if not w.weak(a):continue
  weakcount+=1;ok,ops=w.reduce(a)
  if ok:passed+=1
  elif ok is None:unknown+=1;unclear.append(a)
  else:print(json.dumps({'FAIL':True,'n':n,'trial':z,'adjacency':a,'ops':ops}),flush=True);raise SystemExit()
 row={'n':n,'random_graphs':5000,'weak':weakcount,'reduction_pass':passed,'capped':unknown,'capped_adjacency':unclear};print(json.dumps(row),flush=True)
