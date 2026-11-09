import pathlib,json,random,itertools,subprocess,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(159);out=[]
solver='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical'
for trial in range(400):
 n=[10,15,20,30,40][trial%5];k=3+(trial//5)%3
 adj=[0]*n;es=set()
 if trial<200:
  for v in range(1,n):es.add((rng.randrange(v),v))
  for a,b in itertools.combinations(range(n),2):
   if rng.random()<[.06,.12,.2,.35][trial%4]:es.add((a,b))
 else:
  # Connected chains and trees of planted k-cliques with sparse cross-edges.
  for base in range(0,n,k):
   es.update(itertools.combinations(range(base,min(base+k,n)),2))
   if base:es.add((rng.randrange(base),base))
  for _ in range(trial%11):
   a,b=sorted(rng.sample(range(n),2));es.add((a,b))
 for a,b in es:adj[a]|=1<<b;adj[b]|=1<<a
 req=set()
 for co in itertools.combinations(range(n),k):
  s=sum(1<<x for x in co)
  if all(adj[v]&s==s^(1<<v) for v in co):
   t=s
   for v in co:t|=adj[v]
   req.add(t)
 q=k+1;vid=lambda v,c:v*q+c+1
 clauses=[]
 for v in range(n):
  clauses.append([vid(v,c) for c in range(q)])
  for c,d in itertools.combinations(range(q),2):clauses.append([-vid(v,c),-vid(v,d)])
 for t in sorted(req):
  for c in range(q):clauses.append([vid(v,c) for v in range(n) if t>>v&1])
 path=D/'tmp/isolation.cnf';path.write_text(f'p cnf {n*q} {len(clauses)}\n'+'\n'.join(' '.join(map(str,l))+' 0' for l in clauses)+'\n')
 r=subprocess.run([solver,str(path)],capture_output=True,text=True,timeout=3)
 (D/f'logs/isolation-sat-{trial}.log').write_text(r.stdout+r.stderr)
 model={int(x) for l in r.stdout.splitlines() if l.startswith('v ') for x in l.split()[1:] if int(x)>0}
 col=[next((c for c in range(q) if vid(v,c) in model),-1) for v in range(n)]
 ok=r.returncode==10 and all(c>=0 for c in col) and all({col[v] for v in range(n) if t>>v&1}==set(range(q)) for t in req)
 row={'trial':trial,'n':n,'k':k,'edges':sorted(es),'clique_neighborhood_count':len(req),'solver_exit':r.returncode,'verified_witness':col if ok else None}
 out.append(row)
 if not ok:print('NEEDS_REVIEW',row,flush=True);break
 if trial%50==49:print('completed',trial+1,flush=True)
(D/'outputs/isolation-sat.json').write_text(json.dumps(out))
print('complete samples',len(out),'all SAT models independently verified')
