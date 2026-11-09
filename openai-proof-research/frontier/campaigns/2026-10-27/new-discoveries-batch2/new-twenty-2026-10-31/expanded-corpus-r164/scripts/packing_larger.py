import pathlib,json,random,subprocess,itertools,sys,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(1642026);solver='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical'
per=int(sys.argv[1]);records=[]
for n in range(42,72,2):
 for typ in [0,1]:
  for it in range(per):
   for attempt in range(10000):
    edges=[]
    if typ==0:
     for _ in range(3):
      p=list(range(n));rng.shuffle(p);edges.extend(tuple(sorted(p[j:j+2])) for j in range(0,n,2))
    else:
     p=list(range(n))*3;rng.shuffle(p);edges=[tuple(sorted(p[j:j+2])) for j in range(0,3*n,2)]
    if len(set(edges))==3*n//2 and all(u!=v for u,v in edges):break
   else:continue
   edges=sorted(edges);m=len(edges);k=5 if typ==0 else 6;v=lambda e,c:e*k+c+1
   clauses=[];adj=[set() for _ in range(n)]
   for u,w in edges:adj[u].add(w);adj[w].add(u)
   for e in range(m):
    clauses.append([v(e,c) for c in range(k)])
    for a,b in itertools.combinations(range(k),2):clauses.append([-v(e,a),-v(e,b)])
   for e,f in itertools.combinations(range(m),2):
    u,w=edges[e];x,y=edges[f];near=bool({u,w}&{x,y});strong=near or bool((adj[u]|adj[w])&{x,y})
    for c in range(k):
     if near or (c>=2 and strong):clauses.append([-v(e,c),-v(f,c)])
   p=D/'tmp/packing.cnf';p.write_text('p cnf %d %d\n'%(m*k,len(clauses))+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
   r=subprocess.run([solver,'-q','-t','2',str(p)],capture_output=True,text=True)
   rec={'n':n,'type':'three_matchings' if typ==0 else 'configuration','iteration':it,'edges':edges,'returncode':r.returncode}
   if r.returncode==10:
    pos={int(x) for l in r.stdout.splitlines() if l.startswith('v ') for x in l[2:].split() if int(x)>0}
    assert all(any((x>0 and x in pos) or (x<0 and -x not in pos) for x in c) for c in clauses)
    rec['colors']=[next(c for c in range(k) if v(e,c) in pos) for e in range(m)]
   else:
    (D/'outputs'/('packing-problem-%d-%d-%d.cnf'%(n,typ,it))).write_text(p.read_text());rec['log']=r.stdout
   records.append(rec)
  print(n,typ,len(records),flush=True)
  (D/'outputs/packing-larger.json').write_text(json.dumps(records))
